use crate as sylt_std;

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::io::Write;
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::ops::DerefMut;
use std::rc::Rc;
use std::str::FromStr;
use std::sync::{Arc, Mutex};
use std::thread;
use sylt_common::flat_value::{FlatValue, FlatValuePack};
use sylt_common::{error::RuntimeError, RuntimeContext, Value};

const DEFAULT_PORT: u16 = 8588;

type RPC = Vec<FlatValuePack>;

std::thread_local! {
    static RPC_QUEUE: Arc<Mutex<Vec<(RPC, Option<SocketAddr>)>>> = Arc::new(Mutex::new(Vec::new()));
    static SERVER_HANDLE: RefCell<Option<TcpStream>> = RefCell::new(None);
    static CLIENT_HANDLES: Arc<Mutex<Option<HashMap<SocketAddr, (TcpStream, bool)>>>> = Arc::new(Mutex::new(None));
    static CURRENT_REQUEST_SOCKET_ADDR: RefCell<Option<SocketAddr>> = RefCell::new(None);
}

/// Listen for new connections and accept them.
fn rpc_listen(
    listener: TcpListener,
    queue: Arc<Mutex<Vec<(RPC, Option<SocketAddr>)>>>,
    handles: Arc<Mutex<Option<HashMap<SocketAddr, (TcpStream, bool)>>>>,
) {
    loop {
        if let Ok((stream, addr)) = listener.accept() {
            match stream.try_clone() {
                Ok(stream) => {
                    if let Some(handles) = handles.lock().unwrap().as_mut() {
                        handles.insert(addr, (stream, true));
                    } else {
                        eprintln!(
                            "Server has been shutdown, ignoring connection from {:?}",
                            addr
                        );
                        if let Err(e) = stream.shutdown(Shutdown::Both) {
                            eprintln!("Error disconnecting client {:?}: {:?}", addr, e)
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Error accepting TCP connection: {:?}", e);
                    eprintln!("Ignoring");
                    continue;
                }
            }
            let queue = Arc::clone(&queue);
            thread::spawn(move || rpc_handle_stream(stream, Some(addr), queue));
        }
    }
}

/// Receive RPC values from a stream and queue them locally.
fn rpc_handle_stream(
    stream: TcpStream,
    socket_addr: Option<SocketAddr>,
    queue: Arc<Mutex<Vec<(RPC, Option<SocketAddr>)>>>,
) {
    loop {
        let rpc = match bincode::deserialize_from(&stream) {
            Ok(rpc) => rpc,
            Err(e) => {
                eprintln!("Error reading from client: {:?}", e);
                return;
            }
        };
        queue.lock().unwrap().push((rpc, socket_addr));
    }
}

#[sylt_macro::sylt_link(n_rpc_start_server, "sylt_std::network", "fn int -> bool")]
pub fn n_rpc_start_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    // Get the port from the arguments.
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    let port = match values.as_ref() {
        [Value::Int(port)] => *port as u16,
        _ => DEFAULT_PORT,
    };
    // Bind the server.
    let listener = match TcpListener::bind(("0.0.0.0", port)) {
        Ok(listener) => listener,
        Err(e) => {
            eprintln!("Error binding server to TCP: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };

    // Initialize the thread local with our list of client handles.
    CLIENT_HANDLES.with(|global_handles| {
        let _ = global_handles.lock().unwrap().insert(HashMap::new());
    });

    // Start listening for new clients.
    let rpc_queue = RPC_QUEUE.with(|queue| Arc::clone(queue));
    let handles = CLIENT_HANDLES.with(|handles| Arc::clone(handles));
    thread::spawn(|| rpc_listen(listener, rpc_queue, handles));

    Ok(Value::Bool(true))
}

#[sylt_macro::sylt_link(n_rpc_stop_server, "sylt_std::network", "fn -> bool")]
pub fn n_rpc_stop_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    if n_rpc_is_server(ctx)? == Value::Bool(false) {
        return Ok(Value::Bool(false));
    }

    CLIENT_HANDLES.with(|handles| {
        if let Some(handles) = handles.lock().unwrap().as_mut().take() {
            for (addr, (stream, _)) in handles {
                if let Err(e) = stream.shutdown(Shutdown::Both) {
                    eprintln!("Error disconnecting client {:?}: {:?}", addr, e);
                }
            }
        }
    });

    Ok(Value::Bool(true))
}

//NOTE(gu): We don't force a disconnect.
#[sylt_macro::sylt_link(n_rpc_connect, "sylt_std::network", "fn str, int -> bool")]
pub fn n_rpc_connect(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    // Get the ip and port from the arguments.
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    let socket_addr = match values.as_ref() {
        [Value::String(ip), Value::Int(port)] => (ip.as_str(), *port as u16),
        [Value::String(ip)] => (ip.as_str(), DEFAULT_PORT),
        _ => {
            return Err(RuntimeError::ExternArgsMismatch(
                "n_rpc_connect".to_string(),
                values.to_vec(),
            ));
        }
    };
    // Connect to the server.
    let stream = match TcpStream::connect(socket_addr) {
        Ok(stream) => stream,
        Err(e) => {
            eprintln!("Error connecting to server: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };
    // Store the stream so we can send to it later.
    match stream.try_clone() {
        Ok(stream) => {
            SERVER_HANDLE.with(|server_handle| {
                let _ = server_handle.borrow_mut().insert(stream);
            });
        }
        Err(e) => {
            eprintln!("Error connecting to server: {:?}", e);
            return Ok(Value::Bool(false));
        }
    }

    // Handle incoming RPCs by putting them on the queue.
    let rpc_queue = RPC_QUEUE.with(|queue| Arc::clone(queue));
    thread::spawn(|| rpc_handle_stream(stream, None, rpc_queue));

    Ok(Value::Bool(true))
}

#[sylt_macro::sylt_link(n_rpc_is_server, "sylt_std::network", "fn -> bool")]
pub fn n_rpc_is_server(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        CLIENT_HANDLES.with(|handles| handles.lock().unwrap().is_some()),
    ))
}

#[sylt_macro::sylt_link(n_rpc_connected_clients, "sylt_std::network", "fn -> int")]
pub fn n_rpc_connected_clients(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Int(CLIENT_HANDLES.with(|handles| {
        handles
            .lock()
            .unwrap()
            .as_ref()
            .map(|handles| handles.len() as i64)
            .unwrap_or(0)
    })))
}

#[sylt_macro::sylt_link(n_rpc_is_client, "sylt_std::network", "fn -> bool")]
pub fn n_rpc_is_client(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    Ok(Value::Bool(
        SERVER_HANDLE.with(|handle| handle.borrow().is_some()),
    ))
}

/// Parse args given to an external function as rpc arguments, i.e. one callable followed by 0..n arguments.
fn get_rpc_args(
    ctx: RuntimeContext<'_>,
    arg_offset: usize,
    func_name: &str,
) -> Result<Vec<FlatValuePack>, RuntimeError> {
    let values = ctx.machine.stack_from_base(ctx.stack_base);
    let flat_values: Vec<FlatValuePack> = values[arg_offset..]
        .iter()
        .map(|v| FlatValue::pack(v))
        .collect();

    if flat_values.len() != 0 {
        Ok(flat_values)
    } else {
        Err(RuntimeError::ExternArgsMismatch(
            func_name.to_string(),
            values.to_vec(),
        ))
    }
}

#[sylt_macro::sylt_link(n_rpc_clients, "sylt_std::network", "fn *X, [*Y] -> void")]
pub fn n_rpc_clients(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    // Serialize the RPC.
    let serialized = match bincode::serialize(&get_rpc_args(ctx, 0, "n_rpc_clients")?) {
        Ok(serialized) => serialized,
        Err(e) => {
            eprintln!("Error serializing values: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };

    // Send the serialized data to all clients.
    CLIENT_HANDLES.with(|client_handles| {
        if let Some(streams) = client_handles.lock().unwrap().as_mut() {
            for (_, (stream, keep)) in streams.iter_mut() {
                if let Err(e) = stream.write(&serialized) {
                    eprintln!("Error sending data to a client: {:?}", e);
                    *keep = false;
                }
            }
            streams.retain(|_, (_, keep)| *keep);
        } else {
            eprintln!("A server hasn't been started");
        }
    });

    Ok(Value::Nil)
}

#[sylt_macro::sylt_link(n_rpc_client_ip, "sylt_std::network", "fn *X, [*Y] -> bool")]
pub fn n_rpc_client_ip(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    let ip = match ctx.machine.stack_from_base(ctx.stack_base).get(0) {
        Some(Value::String(s)) => SocketAddr::from_str(s.as_ref()).unwrap(),
        _ => {
            return Ok(Value::Bool(false)); // TODO(gu): Type error here, probably.
        }
    };

    // Serialize the RPC.
    let serialized = match bincode::serialize(&get_rpc_args(ctx, 1, "n_rpc_client_ip")?) {
        Ok(serialized) => serialized,
        Err(e) => {
            eprintln!("Error serializing values: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };

    CLIENT_HANDLES.with(|client_handles| {
        if let Some(streams) = client_handles.lock().unwrap().as_mut() {
            if let Entry::Occupied(mut o) = streams.entry(ip) {
                let (stream, _) = o.get_mut();
                if let Err(e) = stream.write(&serialized) {
                    eprintln!("Error sending data to a specific client {:?}: {:?}", ip, e);
                    o.remove();
                }
                Ok(Value::Bool(true))
            } else {
                Ok(Value::Bool(false))
            }
        } else {
            eprintln!("A server hasn't been started");
            Ok(Value::Bool(false))
        }
    })
}

// TODO(gu): This doc is wrong since this takes variadic arguments.
#[sylt_macro::sylt_link(n_rpc_server, "sylt_std::network", "fn *X, *Y -> bool")]
pub fn n_rpc_server(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    // Serialize the RPC.
    let serialized = match bincode::serialize(&get_rpc_args(ctx, 0, "n_rpc_server")?) {
        Ok(serialized) => serialized,
        Err(e) => {
            eprintln!("Error serializing values: {:?}", e);
            return Ok(Value::Bool(false));
        }
    };

    // Send the serialized data to the server.
    SERVER_HANDLE.with(|server_handle| {
        if let Some(mut stream) = server_handle.borrow().as_ref() {
            match stream.write(&serialized) {
                Ok(_) => Ok(Value::Bool(true)),
                Err(e) => {
                    eprintln!("Error sending data to server: {:?}", e);
                    Ok(Value::Bool(false))
                }
            }
        } else {
            Ok(Value::Bool(false))
        }
    })
}

#[sylt_macro::sylt_link(n_rpc_disconnect, "sylt_std::network", "fn -> void")]
pub fn n_rpc_disconnect(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    SERVER_HANDLE.with(|server_handle| {
        if let Some(handle) = server_handle.borrow_mut().take() {
            if let Err(e) = handle.shutdown(Shutdown::Both) {
                eprintln!("Error disconnecting from server: {:?}", e);
            }
        }
    });

    Ok(Value::Nil)
}

#[sylt_macro::sylt_link(n_rpc_current_request_ip, "sylt_std::network", "fn -> str")]
pub fn n_rpc_current_request_ip(_: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    CURRENT_REQUEST_SOCKET_ADDR.with(|current| {
        Ok(Value::String(Rc::new(
            current
                .borrow()
                .map(|socket| socket.to_string())
                .unwrap_or("".to_string()),
        )))
    })
}

sylt_macro::extern_function!(
    "sylt_std::network",
    split_ip,
    ? "",
    -> "fn str -> (str, int)",
    [String(ip_port)] => {
        let addr = SocketAddr::from_str(ip_port.as_str()).unwrap();
        Ok(Value::Tuple(Rc::new(vec![
            Value::String(Rc::new(addr.ip().to_string())),
            Value::Int(addr.port() as i64),
        ])))
    },
);

#[sylt_macro::sylt_link(n_rpc_resolve, "sylt_std::network", "fn -> void")]
pub fn n_rpc_resolve(ctx: RuntimeContext<'_>) -> Result<Value, RuntimeError> {
    // Take the current queue.
    let queue =
        RPC_QUEUE.with(|queue| std::mem::replace(queue.lock().unwrap().deref_mut(), Vec::new()));

    // Convert the queue into Values that can be evaluated.
    let queue = queue
        .into_iter()
        .map(|(rpc, addr)| (rpc.iter().map(FlatValue::unpack).collect::<Vec<_>>(), addr));

    // Evaluate each RPC one a time.
    for (values, addr) in queue {
        if values.is_empty() {
            eprintln!("Tried to resolve empty RPC");
            continue;
        }
        CURRENT_REQUEST_SOCKET_ADDR.with(|current| *current.borrow_mut() = addr);
        // Create a vec of references to the argument list. This is kinda weird
        // but it's needed since the runtime usually doesn't handle owned
        // values.
        let borrowed_values: Vec<_> = values.iter().collect();
        if let Err(e) = ctx
            .machine
            .eval_call(values[0].clone(), &borrowed_values[1..])
        {
            eprintln!("{}", e);
            panic!("Error evaluating received RPC");
        }
        CURRENT_REQUEST_SOCKET_ADDR.with(|current| current.borrow_mut().take());
    }
    Ok(Value::Nil)
}

sylt_macro::sylt_link_gen!("sylt_std::network");
