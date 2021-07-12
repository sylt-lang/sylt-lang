use crate as sylt_std;

use std::cell::RefCell;
use std::io::Write;
use std::net::{TcpListener, TcpStream};
use std::ops::DerefMut;
use std::sync::{Arc, Mutex};
use std::thread;
use sylt_common::owned_value::OwnedValue;
use sylt_common::{error::RuntimeError, RuntimeContext, Type, Value};

const DEFAULT_PORT: u16 = 8588;

std::thread_local! {
    static RPC_QUEUE: Arc<Mutex<Vec<(OwnedValue, OwnedValue)>>> = Arc::new(Mutex::new(Vec::new()));
    static SERVER_HANDLE: RefCell<Option<TcpStream>> = RefCell::new(None);
    static CLIENT_HANDLES: RefCell<Option<Arc<Mutex<Vec<TcpStream>>>>> = RefCell::new(None);
}

#[sylt_macro::sylt_doc(n_rpc_start_server, "Starts an RPC server on the specified port, returning success status.", [One(Int(port))] Type::Bool)]
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
    // Bind the server.
    let listener = match TcpListener::bind(("127.0.0.1", port)) {
        Ok(listener) => listener,
        Err(e) => {
            println!("Error binding server to TCP: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };

    let handles = Arc::new(Mutex::new(Vec::new()));
    CLIENT_HANDLES.with(|global_handles| {
        global_handles.borrow_mut().insert(Arc::clone(&handles));
    });

    let queue = RPC_QUEUE.with(|queue| Arc::clone(queue));
    thread::spawn(move || {
        for connection in listener.incoming() {
            if let Ok(stream) = connection {
                match stream.try_clone() {
                    Ok(stream) => handles
                        .lock()
                        .unwrap()
                        .push(stream),
                    Err(e) => {
                        println!("Error accepting TCP connection: {:?}", e);
                        println!("Ignoring");
                        continue;
                    }
                }
                let queue = Arc::clone(&queue);
                thread::spawn(move || {
                    // listen to communication from remote
                    loop {
                        let (callable, args) = match bincode::deserialize_from(&stream) {
                            Ok(values) => values,
                            Err(e) => {
                                println!("Error reading from client: {:?}", e);
                                return;
                            }
                        };
                        queue.lock().unwrap().push((callable, args));
                    }
                });
            }
        }
    });
    Ok(Value::Bool(true))
}

#[sylt_macro::sylt_doc(n_rpc_connect, "Connects to an RPC server on the specified IP and port.", [One(String(ip)), One(Int(port))] Type::Bool)]
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
    let stream = match TcpStream::connect(socket_addr) {
        Ok(stream) => stream,
        Err(e) => {
            println!("Error connecting to server: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };
    // Store the stream so we can send to it later.
    match stream.try_clone() {
        Ok(stream) => {
            SERVER_HANDLE.with(|server_handle| {
                server_handle
                    .borrow_mut()
                    .insert(stream);
            });
        },
        Err(e) => {
            println!("Error connecting to server: {:?}", e);
            return Ok(Value::Bool(false));
        },
    }
    // Start a thread that receives values from the network and puts them on the queue.
    //todo!()
    Ok(Value::Bool(true))
}

#[sylt_macro::sylt_doc(n_rpc_is_server, "Returns whether we've started a server or not.", [] Type::Bool)]
#[sylt_macro::sylt_link(n_rpc_is_server, "sylt_std::network")]
pub fn n_rpc_is_server(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        CLIENT_HANDLES.with(|handles| handles.borrow().is_some()),
    ))
}

#[sylt_macro::sylt_doc(n_rpc_connected_clients, "Returns how many clients are currently connected.", [] Type::Int)]
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

#[sylt_macro::sylt_doc(n_rpc_is_client, "Returns whether we've connected to a client or not.", [] Type::Bool)]
#[sylt_macro::sylt_link(n_rpc_is_client, "sylt_std::network")]
pub fn n_rpc_is_client(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        SERVER_HANDLE.with(|handle| handle.borrow().is_some()),
    ))
}

#[sylt_macro::sylt_doc(n_rpc_clients, "Performs an RPC on all connected clients.", [One(Value(callable)), One(List(args))] Type::Unknown)]
#[sylt_macro::sylt_link(n_rpc_clients, "sylt_std::network")]
pub fn n_rpc_clients(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    match values.as_ref() {
        [callable, Value::List(rpc_args)] => {}
        _ => {}
    }
    todo!()
}

#[sylt_macro::sylt_doc(n_rpc_server, "Performs an RPC on the connected server, returning success status.", [One(Value(callable)), One(List(args))] Type::Bool)]
#[sylt_macro::sylt_link(n_rpc_server, "sylt_std::network")]
pub fn n_rpc_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    match values.as_ref() {
        [callable, args] if matches!(args, Value::List(_)) => SERVER_HANDLE.with(|handle| {
            if let Some(mut server) = handle.borrow().as_ref() {
                let serialized = match bincode::serialize(&(callable, args)) {
                    Ok(serialized) => serialized,
                    Err(e) => {
                        println!("Error serializing values: {:?}", e);
                        return Ok(Value::Bool(false));
                    }
                };
                match server.write(&serialized) {
                    Ok(_) => Ok(Value::Bool(true)),
                    Err(e) => {
                        println!("Error sending data to server {:?}", e);
                        Ok(Value::Bool(false))
                    },
                }
            } else {
                Ok(Value::Bool(false))
            }
        }),
        _ => {
            return Err(RuntimeError::ExternTypeMismatch(
                "n_rpc_server".to_string(),
                values.iter().map(Type::from).collect(),
            ));
        }
    }
}

#[sylt_macro::sylt_doc(n_rpc_resolve, "Resolves the queued RPCs that has been received since the last resolve.", [] Type::Void)]
#[sylt_macro::sylt_link(n_rpc_resolve, "sylt_std::network")]
pub fn n_rpc_resolve(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    if ctx.typecheck {
        return Ok(Value::Nil);
    }

    let queue = RPC_QUEUE.with(|queue| {
        std::mem::replace(
            queue.lock().unwrap().deref_mut(),
            Vec::new(),
        )
    });
    let queue: Vec<_> = queue
        .into_iter()
        .map(|(v1, v2)| (v1.into(), v2.into()))
        .collect();
    for element in queue {
        let args = if let Value::List(args) = element.1 {
            args
        } else {
            println!("Tried to resolve non-list argument {:?}", element.1);
            continue;
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
