use crate as sylt_std;

use std::cell::RefCell;
use std::io::Write;
use std::net::{TcpListener, TcpStream};
use std::ops::DerefMut;
use std::sync::{Arc, Mutex};
use std::thread;
use sylt_common::{error::RuntimeError, RuntimeContext, Type, Value};

const DEFAULT_PORT: u16 = 8588;

//TODO(gu): Some type aliases here would go a long way.
std::thread_local! {
    static RPC_QUEUE: Arc<Mutex<Vec<(Value, Value)>>> = Arc::new(Mutex::new(Vec::new()));
    static SERVER_HANDLE: RefCell<Option<Arc<Mutex<TcpStream>>>> = RefCell::new(None);
    static CLIENT_HANDLES: RefCell<Option<Arc<Mutex<Vec<Arc<Mutex<TcpStream>>>>>>> = RefCell::new(None); // yikes
}

/// Starts a server that listens for new connections. Returns true if server startup succeeded, false otherwise.
#[sylt_macro::sylt_link(n_rpc_start_server, "sylt_std::network")]
pub fn n_rpc_start_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    if ctx.typecheck {
        return Ok(Value::Bool(true));
    }

    let values = ctx.machine.stack_from_base(ctx.stack_base);
    let port = match values.as_ref() {
        [Value::Int(port)] => *port as u16,
        _ => DEFAULT_PORT,
    };
    let listener = TcpListener::bind(("127.0.0.1", port)).unwrap();
    let handles = Arc::new(Mutex::new(Vec::new()));
    let listener_handles = Arc::clone(&handles);
    thread::spawn(move || {
        for connection in listener.incoming() {
            if let Ok(stream) = connection {
                let stream = Arc::new(Mutex::new(stream));
                listener_handles.lock().unwrap().push(stream);
            }
        }
    });
    CLIENT_HANDLES.with(|global_handles| {
        global_handles.borrow_mut().insert(handles);
    });
    Ok(Value::Bool(true))
}

/// Connects to a server. Returns true if connection succeeded, false otherwise.
#[sylt_macro::sylt_link(n_rpc_connect, "sylt_std::network")]
pub fn n_rpc_connect(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    if ctx.typecheck {
        return Ok(Value::Bool(true));
    }

    // Get the ip and port from the arguments.
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    let socket_addr = match values.as_ref() {
        [Value::String(ip), Value::Int(port)] => (ip.as_str(), *port as u16),
        [Value::String(ip)] => (ip.as_str(), DEFAULT_PORT),
        _ => {
            return Err(RuntimeError::ExternTypeMismatch(
                "n_rpc_connect".to_string(),
                values.iter().map(Type::from).collect(),
            ));
        }
    };
    // Connect to the server.
    let stream = Arc::new(Mutex::new(
        TcpStream::connect(socket_addr).unwrap(), //TODO(gu): Error handling
    ));
    // Store the stream so we can send to it later.
    SERVER_HANDLE.with(|server_handle| {
        server_handle.borrow_mut().insert(Arc::clone(&stream));
    });
    // Start a thread that receives values from the network and puts them on the queue.
    //todo!()
    Ok(Value::Bool(true))
}

#[sylt_macro::sylt_link(n_rpc_is_server, "sylt_std::network")]
pub fn n_rpc_is_server(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        CLIENT_HANDLES.with(|handles| handles.borrow().is_some()),
    ))
}

#[sylt_macro::sylt_link(n_rpc_connected_clients, "sylt_std::network")]
pub fn n_rpc_connected_clients(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Int(CLIENT_HANDLES.with(|handles| {
        handles
            .borrow()
            .as_ref()
            .map(|handles| handles.lock().unwrap().len() as i64)
            .unwrap_or(0)
    })))
}

#[sylt_macro::sylt_link(n_rpc_is_client, "sylt_std::network")]
pub fn n_rpc_is_client(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        SERVER_HANDLE.with(|handle| handle.borrow().is_some()),
    ))
}

/// Performs a RPC on all connected clients. Returns true if sending succeeded, false otherwise.
#[sylt_macro::sylt_link(n_rpc_clients, "sylt_std::network")]
pub fn n_rpc_clients(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    match values.as_ref() {
        [callable, Value::List(rpc_args)] => {}
        _ => {}
    }
    todo!()
}

/// Performs a RPC on the connected server. Returns true if sending succeeded, false otherwise.
#[sylt_macro::sylt_link(n_rpc, "sylt_std::network")]
pub fn n_rpc_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    match values.as_ref() {
        [callable, args] if matches!(args, Value::List(_))=> {
            SERVER_HANDLE.with(|handle| {
                if let Some(server) = handle.borrow().as_ref() {
                    server.lock().unwrap().write(&bincode::serialize(&(callable, args)).unwrap()).unwrap();
                    Ok(Value::Bool(true))
                } else {
                    Ok(Value::Bool(false))
                }
            })
        }
        _ => {
            return Err(RuntimeError::ExternTypeMismatch(
                "n_rpc_server".to_string(),
                values.iter().map(Type::from).collect(),
            ));
        }
    }
}

#[sylt_macro::sylt_link(n_rpc_resolve, "sylt_std::network")]
pub fn n_rpc_resolve(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    if ctx.typecheck {
        return Ok(Value::Nil);
    }

    let queue = RPC_QUEUE.with(|queue| {
        Some(std::mem::replace(
            queue.lock().ok()?.deref_mut(),
            Vec::new(),
        ))
    });
    let queue = queue.unwrap(); //TODO(gu): Return error
    for element in queue {
        let args = if let Value::List(args) = element.1 {
            args
        } else {
            panic!();
        };
        // Create a vec of references to the list. This is kinda weird but it's needed since
        // the runtime usually doesn't work with owned values, which these values are since
        // they're cloned from the network.
        let args = args.borrow();
        let borrowed_args: Vec<_> = args.iter().collect();
        ctx.machine.eval_call(element.0, &borrowed_args).unwrap();
    }
    Ok(Value::Nil)
}

sylt_macro::sylt_link_gen!("sylt_std::network");
