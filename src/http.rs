// src/http.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

#![allow(unsafe_op_in_unsafe_fn)]
use axum::{
    body::{Bytes, Body},
    http::{HeaderMap, Method, StatusCode},
    response::IntoResponse,
    routing::any,
    Router,
};
use once_cell::sync::Lazy;
use futures_util::stream::StreamExt;
use tokio_stream::wrappers::ReceiverStream;
use tokio::net::TcpListener;
use serde_json;
use reqwest;
use core::ptr::read_unaligned;
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::{runtime::Runtime, sync::{oneshot, mpsc}};
use ahash::AHashMap as HashMap;
use parking_lot::Mutex;
use rclite::Arc;

use crate::event_loop::EVENT_LOOP;
use crate::gc::NAPALM_GC;
use crate::value::{
    ObjHeader, TAG_STRING, TAG_OBJECT, BoxedStr, make_smi, is_imm, smi_to_i64, fmt_value, dbg_addr, dbg_classify,
};
use crate::runtime::{wir_obj_get_str, wir_obj_set_str, wir_obj_new, wir_is_str};
use crate::native_promises::{wir_deferred_new, wir_deferred_resolve, wir_deferred_reject};

/// -------- Tokio runtime on a dedicated thread (net/io) --------
#[cfg(feature = "gc")]
static TOKIO_RT: Lazy<Runtime> = Lazy::new(|| {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_name("napalm-net")
        .on_thread_start(|| unsafe { NAPALM_GC.bind_current_thread(); })
        .build()
        .expect("tokio runtime")
});

#[cfg(not(feature = "gc"))]
static TOKIO_RT: Lazy<Runtime> = Lazy::new(|| {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_name("napalm-net")
        .build()
        .expect("tokio runtime")
});

/// -------- simple ID counters --------
static NEXT_SERVER_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_REQ_ID:    AtomicU64 = AtomicU64::new(1);
fn rand_id() -> u64 { NEXT_SERVER_ID.fetch_add(1, Ordering::Relaxed) }
fn next_req_id() -> u64 { NEXT_REQ_ID.fetch_add(1, Ordering::Relaxed) }

/// -------- route registry (kept as GC roots; see http_with_root_slots()) --------
#[derive(Clone)]
struct Route {
    method: String,
    tokens: Vec<Token>,
    handler_closure: i64,    // VM closure value
}

#[derive(Clone)]
enum Token { Lit(String), Param(String) }

struct ServerEntry {
    addr: String,
    dispatch_closure: i64,   // VM closure used by net thread to enqueue microtasks
    routes: Vec<Route>,
}

static SERVERS: Lazy<Mutex<HashMap<u64, Arc<ServerEntry>>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

/// Map (server_id, req_id) -> response sender (no VM values inside)
static RESP_SENDERS: Lazy<Mutex<HashMap<(u64,u64), oneshot::Sender<ResponseMsg>>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

/// Streaming data channels: VM writes -> net thread streams
static STREAM_RX: Lazy<Mutex<HashMap<(u64,u64), mpsc::Receiver<Vec<u8>>>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));
static STREAM_TX: Lazy<Mutex<HashMap<(u64,u64), mpsc::Sender<Vec<u8>>>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

/// Keep owned byte buffers alive for strings we create on the VM side.
static HTTP_BYTES_KEEPALIVE: Lazy<Mutex<Vec<Box<[u8]>>>> =
    Lazy::new(|| Mutex::new(Vec::new()));

/// ---------- Messages crossing threads (pure Rust data) ----------
pub struct ReqMsg {
    pub server_id: u64,
    pub req_id:    u64,
    pub method:    String,
    pub path:      String,
    pub body:      Vec<u8>,
    pub headers:   Vec<(String,String)>,
}

pub struct ResponseMsg {
    pub status:  u16,
    pub body:    Vec<u8>,
    pub headers: Vec<(String,String)>,
}

// --- GC roots for in-flight HTTP deferreds (store as usize to be Send/Sync) ---
type RootSlot = i64; // holds a Box<i64> pointer

/// Small helper used by HTTP client to deliver results on the VM thread.
#[repr(C)]
struct HttpResult {
    deferred: RootSlot,
    status:   i64,    // SMI
    body:     Vec<u8>,
    headers:  Vec<(String,String)>,
    is_err:   bool,
    as_json:  bool,
}

static DEFERRED_ROOTS: Lazy<Mutex<Vec<RootSlot>>> = Lazy::new(|| Mutex::new(Vec::new()));

fn root_deferred(d: i64) -> RootSlot {
    let slot_ptr: *mut i64 = Box::into_raw(Box::new(d)); // slot the GC can rewrite
    let u = slot_ptr as i64;
    DEFERRED_ROOTS.lock().push(u);
    u
}

fn unroot_deferred(slot: RootSlot) {
    // remove from the list
    let mut v = DEFERRED_ROOTS.lock();
    if let Some(i) = v.iter().position(|&p| p == slot) {
        v.swap_remove(i);
    }
    drop(v);
    // free the slot
    unsafe { drop(Box::from_raw(slot as *mut i64)); }
}

/// ---- tiny utils ----
#[inline(always)]
unsafe fn argv_read(argv: *const i64, idx: usize) -> i64 {
    // Use an unaligned 64-bit load to avoid SIGBUS on aarch64 when argv isn’t 8-byte aligned.
    read_unaligned(argv.add(idx))
}

#[inline(always)]
unsafe fn boxedstr_to_string(p: i64) -> String {
    let s = &*(p as *const BoxedStr);
    let bytes = std::slice::from_raw_parts(s.data, s.len);
    String::from_utf8_lossy(bytes).into_owned()
}

#[inline(always)]
fn static_str_value(s: &'static str) -> i64 {
    use crate::value::box_str_borrowed;
    box_str_borrowed(s.as_bytes())
}

fn box_str_keepalive(bytes: Vec<u8>) -> i64 {
    use crate::value::box_str_borrowed;
    let boxed: Box<[u8]> = bytes.into_boxed_slice();
    let ptr = boxed.as_ptr();
    let len = boxed.len();
    // SAFETY: we keep 'boxed' alive globally.
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    let v = box_str_borrowed(slice);
    HTTP_BYTES_KEEPALIVE.lock().push(boxed);
    v
}

/// Convert a VM value to (status, body, headers). Supports:
///  - string → 200 + utf8 bytes
///  - object {status?, body?, headers?} where:
///      status = SMI, body = string; headers = array of [key, value] pairs (strings)
fn value_to_response(v: i64) -> (u16, Vec<u8>, Vec<(String,String)>) {
    #[cfg(debug_assertions)]
    eprintln!("[http] value_to_response: v={} ({})", dbg_addr(v), dbg_classify(v));

    // string?
    unsafe {
        if v == 0 {
            // treat as empty body (or 204 if you prefer)
            return (200, Vec::new(), vec![]);
        }
        if wir_is_str(v) != 0 {
            let s = &*(v as *const BoxedStr);
            let bytes = std::slice::from_raw_parts(s.data, s.len);
            return (200, bytes.to_vec(), vec![]);
        }
        let hdr = &*(v as *const ObjHeader);
        if hdr.tag != TAG_OBJECT {
            // not an object → just stringify
            return (200, fmt_value(v).into_bytes(), vec![]);
        }
    }

    let status_key  = static_str_value("status");
    let body_key    = static_str_value("body");
    let headers_key = static_str_value("headers");

    let mut status_u16: u16 = 200;
    let mut body_out: Vec<u8> = Vec::new();
    let mut headers_out: Vec<(String,String)> = Vec::new();

    unsafe {
        // status
        let s = wir_obj_get_str(v, status_key);
        if s != 0 && is_imm(s) {
            let st = smi_to_i64(s);
            if (100..=599).contains(&st) { status_u16 = st as u16; }
        }

        // body
        let b = wir_obj_get_str(v, body_key);
        if b != 0 && wir_is_str(b) != 0 {
            let bs = &*(b as *const BoxedStr);
            let bytes = std::slice::from_raw_parts(bs.data, bs.len);
            body_out = bytes.to_vec();
        } else if b != 0 {
            body_out = fmt_value(b).into_bytes();
        }

        // headers: expect array of [k,v] pairs
        unsafe extern "C" {
            fn wir_array_len(arr: i64) -> i64;
            fn wir_array_get(arr: i64, idx: i64) -> i64;
        }
        let h = wir_obj_get_str(v, headers_key);
        if h != 0 {
            let n = smi_to_i64(wir_array_len(h)).max(0) as usize;
            for i in 0..n {
                let pair = wir_array_get(h, make_smi(i as i64));
                let k = wir_array_get(pair, make_smi(0));
                let val = wir_array_get(pair, make_smi(1));
                if wir_is_str(k) != 0 && wir_is_str(val) != 0 {
                    let ks = &*(k as *const BoxedStr);
                    let vs = &*(val as *const BoxedStr);
                    let kb = std::slice::from_raw_parts(ks.data, ks.len);
                    let vb = std::slice::from_raw_parts(vs.data, vs.len);
                    headers_out.push((
                        String::from_utf8_lossy(kb).into_owned(),
                        String::from_utf8_lossy(vb).into_owned(),
                    ));
                }
            }
        }
    }

    if body_out.is_empty() {
        body_out = fmt_value(v).into_bytes();
    }
    (status_u16, body_out, headers_out)
}

/// Send a response back to net thread for (server_id, req_id)
fn send_response(server_id: u64, req_id: u64, status: u16, body: Vec<u8>, headers: Vec<(String,String)>) {
    let tx = {
        let mut g = RESP_SENDERS.lock();
        g.remove(&(server_id, req_id))
    };
    if let Some(tx) = tx {
        let _ = tx.send(ResponseMsg { status, body, headers });
    } else {
        eprintln!("[http] missing response sender for ({server_id},{req_id})");
    }
}

/// Map a return value into ResponseMsg and send.
fn send_immediate_response(server_id: u64, req_id: u64, v: i64) {
    let (st, body, headers) = value_to_response(v);
    send_response(server_id, req_id, st, body, headers);
}

/// Promise-like detection: check obj["then"] first; else treat as private promise pointer.
fn is_promise_like(v: i64) -> bool {
    #[cfg(debug_assertions)]
    eprintln!("[http] is_promise_like? v={} ({})", dbg_addr(v), dbg_classify(v));

    // null or immediate → not a promise
    if v == 0 || (v & 1) == 1 { return false; }

    unsafe {
        let hdr = &*(v as *const ObjHeader);

        #[cfg(debug_assertions)]
        eprintln!("[http]   tag={}", hdr.tag);

        // strings are not promises
        if hdr.tag == TAG_STRING { return false; }
        // your native/private Promise uses tag 0
        if hdr.tag == 0 { return true; }
        // Only objects may be "thenables"
        if hdr.tag == TAG_OBJECT {
            let then = wir_obj_get_str(v, static_str_value("then"));

            #[cfg(debug_assertions)]
            eprintln!("[http]   .then present? {}", then != 0);

            return then != 0;
        }
        false
    }
}

/// Attach then/catch that send (sid,rid) when fulfilled/rejected.
fn attach_then_catch(promise: i64, sid: u64, rid: u64) {
    unsafe extern "C" { fn wir_call_closure(clo: i64, argv: *const i64, argc: i64) -> i64; }
    extern "C" fn on_f(argv: *const i64, argc: usize) -> i64 {
        unsafe {
            let sid = argv_read(argv, 0) as u64;
            let rid = argv_read(argv, 1) as u64;
            let val = argv_read(argv, 2);
            let (st, body, headers) = value_to_response(val);
            send_response(sid, rid, st, body, headers);
        }
        0
    }
    extern "C" fn on_r(argv: *const i64, argc: usize) -> i64 {
        unsafe {
            let sid = argv_read(argv, 0) as u64;
            let rid = argv_read(argv, 1) as u64;
            let val = argv_read(argv, 2);
            let mut body = format!("rejected: {}", fmt_value(val)).into_bytes();
            send_response(sid, rid, 500, std::mem::take(&mut body), vec![]);
        }
        0
    }

    let f = crate::value::closure_new(on_f as usize, 2);
    let r = crate::value::closure_new(on_r as usize, 2);
    unsafe {
        crate::value::closure_set_env_slot(f, 0, sid as i64);
        crate::value::closure_set_env_slot(f, 1, rid as i64);
        crate::value::closure_set_env_slot(r, 0, sid as i64);
        crate::value::closure_set_env_slot(r, 1, rid as i64);
    }

    unsafe {
        let then_fun = wir_obj_get_str(promise, static_str_value("then"));
        if then_fun != 0 {
            let argv = [f, r];
            let _ = wir_call_closure(then_fun, argv.as_ptr(), 2);
        } else {
            let _ = crate::native_promises::wir_promise_then(promise, f, r);
        }
    }
}

/// ------------- FFI: create server, add routes, listen -------------

#[unsafe(no_mangle)]
pub extern "C" fn wir_server_create(addr_ptr: i64) -> i64 {
    extern "C" fn dispatch_tramp(argv: *const i64, argc: usize) -> i64 {
        crate::http::vm_dispatch(argv, argc)
    }

    let addr = unsafe { boxedstr_to_string(addr_ptr) };
    let server_id = rand_id();

    let dispatch_closure = crate::value::closure_new(dispatch_tramp as usize, 0);
    let entry = Arc::new(ServerEntry { addr, dispatch_closure, routes: Vec::new() });
    SERVERS.lock().insert(server_id, entry);
    server_id as i64
}

/// method_ptr = BoxedStr ("GET" | "POST"...)
/// pattern_arr = WIR array of BoxedStr tokens:
///   - literal segments ("/", "user", "/foo")
///   - parameters must start with ':' (e.g. ":id")
#[unsafe(no_mangle)]
pub extern "C" fn wir_server_add_route(
    server_id: i64, method_ptr: i64, pattern_arr: i64, handler: i64
) -> i64 {
    let method = unsafe { boxedstr_to_string(method_ptr) };

    let mut tokens: Vec<Token> = Vec::new();
    unsafe {
        unsafe extern "C" {
            fn wir_array_len(arr: i64) -> i64;
            fn wir_array_get(arr: i64, idx: i64) -> i64;
        }
        let n = smi_to_i64(wir_array_len(pattern_arr)).max(0) as usize;
        for i in 0..n {
            let v = wir_array_get(pattern_arr, make_smi(i as i64));
            if wir_is_str(v) == 0 { continue; }
            let s = boxedstr_to_string(v);
            for seg in s.split('/').filter(|x| !x.is_empty()) {
                if let Some(name) = seg.strip_prefix(':') {
                    tokens.push(Token::Param(name.to_string()));
                } else {
                    tokens.push(Token::Lit(seg.to_string()));
                }
            }
        }
    }

    let mut g = SERVERS.lock();
    let entry = g.get_mut(&(server_id as u64)).expect("server");
    Arc::get_mut(entry).expect("no other refs").routes.push(Route { method, tokens, handler_closure: handler });
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_server_listen(server_id: i64) -> i64 {
    let server_id = server_id as u64;
    let entry = SERVERS.lock().get(&server_id).cloned().expect("server");
    let addr = entry.addr.clone();
    let dispatch_closure = entry.dispatch_closure;

    TOKIO_RT.spawn(async move {
        let app = Router::new().route(
            "/{*path}",
            any(move |method: Method, uri: axum::http::Uri, headers: HeaderMap, body: Bytes| {
                let entry = entry.clone();
                async move {
                    let req_id = next_req_id();
                    let path = uri.path().to_string();

                    let (tx, rx) = oneshot::channel::<ResponseMsg>();
                    RESP_SENDERS.lock().insert((server_id, req_id), tx);

                    let mut hdrs_vec = Vec::with_capacity(headers.len());
                    for (k, v) in headers.iter() {
                        let key = k.as_str().to_string();
                        let val = v.to_str().unwrap_or_default().to_string();
                        hdrs_vec.push((key, val));
                    }

                    let msg = Box::new(ReqMsg {
                        server_id, req_id,
                        method: method.as_str().to_string(),
                        path,
                        body: body.to_vec(),
                        headers: hdrs_vec,
                    });
                    let arg = (&*msg as *const ReqMsg as usize) as i64;
                    std::mem::forget(msg);

                    EVENT_LOOP.enqueue_microtask(entry.dispatch_closure, arg);

                    match rx.await {
                        Ok(r) => {
                            if let Some(rx_stream) = STREAM_RX.lock().remove(&(server_id, req_id)) {
                                use futures_util::stream::StreamExt;
                                let stream = tokio_stream::wrappers::ReceiverStream::new(rx_stream)
                                    .map(|chunk| Ok::<Bytes, std::io::Error>(Bytes::from(chunk)));
                                let mut resp = axum::response::Response::builder()
                                    .status(StatusCode::from_u16(r.status).unwrap_or(StatusCode::OK));
                                for (k, v) in r.headers { resp = resp.header(k, v); }
                                resp.body(Body::from_stream(stream)).unwrap()
                            } else {
                                let mut res = axum::response::Response::builder()
                                    .status(StatusCode::from_u16(r.status).unwrap_or(StatusCode::OK));
                                for (k, v) in r.headers { res = res.header(k, v); }
                                res.body(Body::from(r.body)).unwrap()
                            }
                        }
                        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "VM dropped response").into_response(),
                    }
                }
            }),
        );

        // NEW: Axum 0.7 serve
        let listener = TcpListener::bind(&addr).await.unwrap();
        if let Err(e) = axum::serve(listener, app.into_make_service()).await {
            eprintln!("[http] server error: {e}");
        }
    });

    0
}
/// ---------- Route matching & VM dispatch (runs on VM thread) ----------

fn match_route<'a>(routes: &'a [Route], method: &str, path: &str) -> Option<(&'a Route, HashMap<String,String>)> {
    let segs: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    for r in routes {
        if !r.method.eq_ignore_ascii_case(method) { continue; }
        let mut params = HashMap::new();
        let mut i = 0usize;
        let mut ok = true;

        for t in &r.tokens {
            if i >= segs.len() { ok = false; break; }
            match t {
                Token::Lit(s) => {
                    if segs[i] != s { ok = false; break; }
                }
                Token::Param(name) => {
                    params.insert(name.clone(), segs[i].to_string());
                }
            }
            i += 1;
        }
        if ok && i == segs.len() {
            return Some((r, params));
        }
    }
    None
}

// Runs on the VM thread as a microtask; safe to touch VM heap.
#[unsafe(no_mangle)]
pub extern "C" fn vm_dispatch(argv: *const i64, _argc: usize) -> i64 {
    use crate::value::*;
    unsafe {
        let arg = argv_read(argv, 0);
        let mut req: Box<ReqMsg> = Box::from_raw(arg as *mut ReqMsg); // take ownership

        // 1) Build VM Request object
        let req_obj = wir_obj_new();
        // method/path/body
        let method_v = box_str_keepalive(std::mem::take(&mut req.method).into_bytes());
        let path_v   = box_str_keepalive(std::mem::take(&mut req.path).into_bytes());
        let body_v   = box_str_keepalive(std::mem::take(&mut req.body));
        wir_obj_set_str(req_obj, static_str_value("method"), method_v);
        wir_obj_set_str(req_obj, static_str_value("path"),   path_v);
        wir_obj_set_str(req_obj, static_str_value("body"),   body_v);

        // headers object
        let hdrs_obj = wir_obj_new();
        for (k, v) in std::mem::take(&mut req.headers) {
            let kv = box_str_keepalive(k.into_bytes());
            let vv = box_str_keepalive(v.into_bytes());
            wir_obj_set_str(hdrs_obj, kv, vv);
        }
        wir_obj_set_str(req_obj, static_str_value("headers"), hdrs_obj);

        // params = {} (filled after match)
        let params = wir_obj_new();

        // 2) Route match
        let entry = SERVERS.lock().get(&req.server_id).cloned().expect("server");
        let Some((route, filled_params)) = match_route(&entry.routes, &method_to_str(method_v), &value_to_str(path_v)) else {
            send_response(req.server_id, req.req_id, 404, b"Not Found".to_vec(), vec![]);
            return 0;
        };
        for (k,v) in filled_params {
            wir_obj_set_str(params, box_str_keepalive(k.into_bytes()), box_str_keepalive(v.into_bytes()));
        }
        wir_obj_set_str(req_obj, static_str_value("params"), params);

        // expose ids for streaming helpers
        wir_obj_set_str(req_obj, static_str_value("serverId"), make_smi(req.server_id as i64));
        wir_obj_set_str(req_obj, static_str_value("reqId"),    make_smi(req.req_id as i64));

        // 3) Call handler(req)
        unsafe extern "C" { fn wir_call_closure(clo: i64, argv: *const i64, argc: i64) -> i64; }
        let argv = [req_obj];
        let ret = wir_call_closure(route.handler_closure, argv.as_ptr(), 1);

        #[cfg(debug_assertions)]
        eprintln!("[http] route returned v={} ({})", dbg_addr(ret), dbg_classify(ret));

        // 4) Return mapping
        if is_promise_like(ret) {
            attach_then_catch(ret, req.server_id, req.req_id);
        } else {
            send_immediate_response(req.server_id, req.req_id, ret);
        }
    }
    0
}

#[inline]
fn method_to_str(v: i64) -> String {
    unsafe {
        let s = &*(v as *const BoxedStr);
        let b = std::slice::from_raw_parts(s.data, s.len);
        String::from_utf8_lossy(b).into_owned()
    }
}
#[inline]
fn value_to_str(v: i64) -> String { method_to_str(v) }

/// ---------- HTTP client: request/get/post (+ JSON) ----------

static HTTP_RESOLVE_CLO: Lazy<i64> = Lazy::new(|| {
    extern "C" fn http_resolve_tramp(argv: *const i64, _argc: usize) -> i64 {
        unsafe {
            let arg = argv_read(argv, 0);
            let hr: Box<HttpResult> = Box::from_raw(arg as *mut HttpResult);

            // Read the up-to-date promise pointer from the slot (GC will have updated this).
            let slot: *mut i64 = hr.deferred as *mut i64;
            let deferred: i64 = *slot;

            #[cfg(debug_assertions)]
            eprintln!(
                "[http] resolve_tramp slot={:?} -> {} ({}) is_err={} as_json={}",
                slot,
                crate::value::dbg_addr(deferred),
                crate::value::dbg_classify(deferred),
                hr.is_err,
                hr.as_json
            );

            if hr.is_err {
                let _ = wir_deferred_reject(deferred, 0);
                unroot_deferred(hr.deferred);   // free the slot now that we're done
                return 0;
            }

            let obj = wir_obj_new();
            wir_obj_set_str(obj, static_str_value("status"), make_smi(hr.status));

            // headers
            let hdrs_obj = wir_obj_new();
            for (k, v) in hr.headers.iter() {
                wir_obj_set_str(
                    hdrs_obj,
                    box_str_keepalive(k.clone().into_bytes()),
                    box_str_keepalive(v.clone().into_bytes()),
                );
            }
            wir_obj_set_str(obj, static_str_value("headers"), hdrs_obj);

            // body / json
            if hr.as_json {
                if let Some(jv) = json_bytes_to_vm(&hr.body) {
                    wir_obj_set_str(obj, static_str_value("json"), jv);
                } else {
                    let body_v = box_str_keepalive(hr.body);
                    wir_obj_set_str(obj, static_str_value("body"), body_v);
                }
            } else {
                let body_v = box_str_keepalive(hr.body);
                wir_obj_set_str(obj, static_str_value("body"), body_v);
            }

            let _ = wir_deferred_resolve(deferred, obj);

            // Done with this request — stop rooting the promise
            unroot_deferred(hr.deferred);
        }
        0
    }
    crate::value::closure_new(http_resolve_tramp as usize, 0)
});

#[inline(always)]
fn http_resolve_closure() -> i64 { *HTTP_RESOLVE_CLO }

fn collect_headers_from_arr(arr: i64) -> Vec<(String,String)> {
    let mut out = Vec::new();
    unsafe {
        unsafe extern "C" {
            fn wir_array_len(arr: i64) -> i64;
            fn wir_array_get(arr: i64, idx: i64) -> i64;
        }
        if arr == 0 { return out; }
        let n = smi_to_i64(wir_array_len(arr)).max(0) as usize;
        for i in 0..n {
            let pair = wir_array_get(arr, make_smi(i as i64));
            let k = wir_array_get(pair, make_smi(0));
            let v = wir_array_get(pair, make_smi(1));
            if wir_is_str(k) != 0 && wir_is_str(v) != 0 {
                let ks = &*(k as *const BoxedStr);
                let vs = &*(v as *const BoxedStr);
                let kb = std::slice::from_raw_parts(ks.data, ks.len);
                let vb = std::slice::from_raw_parts(vs.data, vs.len);
                out.push((
                    String::from_utf8_lossy(kb).into_owned(),
                    String::from_utf8_lossy(vb).into_owned(),
                ));
            }
        }
    }
    out
}

fn spawn_request(method: String, url: String, body: Option<Vec<u8>>, headers: Vec<(String,String)>, as_json: bool) -> i64 {
    let d = wir_deferred_new();
    let dslot = root_deferred(d);               // <-- KEEP A ROOT SLOT

    TOKIO_RT.spawn(async move {
        let client = reqwest::Client::new();
        let mut req = client.request(method.parse().unwrap_or(reqwest::Method::GET), &url);
        if let Some(b) = body.clone() { req = req.body(b); }
        for (k, v) in &headers { req = req.header(k, v); }

        let res = req.send().await;
        match res {
            Ok(r) => {
                let status = r.status().as_u16() as i64;
                let mut hdrs = Vec::with_capacity(r.headers().len());
                for (k, v) in r.headers().iter() {
                    hdrs.push((k.as_str().to_string(), v.to_str().unwrap_or_default().to_string()));
                }
                let body = r.bytes().await.unwrap_or_default().to_vec();
                let msg = Box::new(HttpResult {
                    deferred: dslot,
                    status, body, headers: hdrs,
                    is_err: false, as_json
                });
                let arg = Box::into_raw(msg) as i64;
                EVENT_LOOP.enqueue_microtask(http_resolve_closure(), arg);
            }
            Err(_) => {
                let msg = Box::new(HttpResult {
                    deferred: dslot,
                    status: 0, body: Vec::new(), headers: vec![],
                    is_err: true, as_json
                });
                let arg = Box::into_raw(msg) as i64;
                EVENT_LOOP.enqueue_microtask(http_resolve_closure(), arg);
            }
        }
    });

    d
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_get(url_ptr: i64) -> i64 {
    let url = unsafe { boxedstr_to_string(url_ptr) };
    spawn_request("GET".to_string(), url, None, vec![], false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_get_json(url_ptr: i64) -> i64 {
    let url = unsafe { boxedstr_to_string(url_ptr) };
    spawn_request("GET".to_string(), url, None, vec![("accept".into(), "application/json".into())], true)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_post(url_ptr: i64, body_ptr: i64, headers_arr: i64) -> i64 {
    let url = unsafe { boxedstr_to_string(url_ptr) };
    let body = if body_ptr != 0 {
        Some(unsafe {
            let s = &*(body_ptr as *const BoxedStr);
            std::slice::from_raw_parts(s.data, s.len).to_vec()
        })
    } else { None };
    let headers = collect_headers_from_arr(headers_arr);
    spawn_request("POST".into(), url, body, headers, false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_request(method_ptr: i64, url_ptr: i64, body_ptr: i64, headers_arr: i64, as_json: i64) -> i64 {
    let method = unsafe { boxedstr_to_string(method_ptr) };
    let url    = unsafe { boxedstr_to_string(url_ptr) };
    let body = if body_ptr != 0 {
        Some(unsafe {
            let s = &*(body_ptr as *const BoxedStr);
            std::slice::from_raw_parts(s.data, s.len).to_vec()
        })
    } else { None };
    let headers = collect_headers_from_arr(headers_arr);
    spawn_request(method, url, body, headers, as_json != 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_post_json(url_ptr: i64, json_str_ptr: i64, headers_arr: i64) -> i64 {
    let url = unsafe { boxedstr_to_string(url_ptr) };
    let mut headers = collect_headers_from_arr(headers_arr);
    // ensure content-type if not set
    if !headers.iter().any(|(k,_)| k.eq_ignore_ascii_case("content-type")) {
        headers.push(("content-type".into(), "application/json".into()));
    }
    let body = if json_str_ptr != 0 {
        Some(unsafe {
            let s = &*(json_str_ptr as *const BoxedStr);
            std::slice::from_raw_parts(s.data, s.len).to_vec()
        })
    } else { Some(b"null".to_vec()) };
    spawn_request("POST".into(), url, body, headers, true)
}

/// ---------- Server-side streaming: start/write/end ----------

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_start_stream(server_id_smi: i64, req_id_smi: i64, status_smi: i64, headers_arr: i64) -> i64 {
    let sid = smi_to_i64(server_id_smi) as u64;
    let rid = smi_to_i64(req_id_smi) as u64;
    let status = smi_to_i64(status_smi) as u16;
    let headers = collect_headers_from_arr(headers_arr);

    let (tx, rx) = mpsc::channel::<Vec<u8>>(32);
    STREAM_TX.lock().insert((sid, rid), tx);
    STREAM_RX.lock().insert((sid, rid), rx);

    // send header-only response to flip the route into streaming mode
    send_response(sid, rid, status, Vec::new(), headers);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_stream_write(server_id_smi: i64, req_id_smi: i64, chunk_ptr: i64) -> i64 {
    let sid = smi_to_i64(server_id_smi) as u64;
    let rid = smi_to_i64(req_id_smi) as u64;
    let Some(tx) = STREAM_TX.lock().get(&(sid, rid)).cloned() else { return 0; };
    let bytes = unsafe {
        let s = &*(chunk_ptr as *const BoxedStr);
        std::slice::from_raw_parts(s.data, s.len).to_vec()
    };
    let _ = tx.try_send(bytes);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_stream_end(server_id_smi: i64, req_id_smi: i64) -> i64 {
    let sid = smi_to_i64(server_id_smi) as u64;
    let rid = smi_to_i64(req_id_smi) as u64;
    STREAM_TX.lock().remove(&(sid, rid)); // dropping sender closes the stream
    0
}

/// Convenience: start stream using fields on `req` (serverId/reqId)
#[unsafe(no_mangle)]
pub extern "C" fn wir_http_start_stream_from_req(req_obj: i64, status_smi: i64, headers_arr: i64) -> i64 {
    unsafe {
        let sid = wir_obj_get_str(req_obj, static_str_value("serverId"));
        let rid = wir_obj_get_str(req_obj, static_str_value("reqId"));
        wir_http_start_stream(sid, rid, status_smi, headers_arr)
    }
}

/// ---------- JSON decode (server & client helper) ----------

fn json_to_vm(v: &serde_json::Value) -> i64 {
    unsafe {
        unsafe extern "C" {
            fn wir_array_new(len: i64) -> i64;
            fn wir_array_push(arr: i64, val: i64) -> i64;
        }
        match v {
            serde_json::Value::Null => 0,
            serde_json::Value::Bool(b) => if *b { 1 } else { 0 },
            serde_json::Value::Number(n) => {
                // prefer SMI when exact i64; else boxed f64
                if let Some(i) = n.as_i64() { make_smi(i) }
                else {
                    let f = n.as_f64().unwrap_or(0.0);
                    crate::jit::wir_box_f64_runtime(f.to_bits())
                }
            }
            serde_json::Value::String(s) => {
                box_str_keepalive(s.clone().into_bytes())
            }
            serde_json::Value::Array(a) => {
                let arr = wir_array_new(make_smi(0));
                for x in a {
                    let vx = json_to_vm(x);
                    let _ = wir_array_push(arr, vx);
                }
                arr
            }
            serde_json::Value::Object(m) => {
                let o = wir_obj_new();
                for (k, x) in m.iter() {
                    let key = box_str_keepalive(k.clone().into_bytes());
                    let vx  = json_to_vm(x);
                    wir_obj_set_str(o, key, vx);
                }
                o
            }
        }
    }
}

fn json_bytes_to_vm(bytes: &[u8]) -> Option<i64> {
    match serde_json::from_slice::<serde_json::Value>(bytes) {
        Ok(v) => Some(json_to_vm(&v)),
        Err(_) => None,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_json_parse(str_ptr: i64) -> i64 {
    unsafe {
        if str_ptr == 0 || wir_is_str(str_ptr) == 0 { return 0; }
        let s = &*(str_ptr as *const BoxedStr);
        let bytes = std::slice::from_raw_parts(s.data, s.len);
        match serde_json::from_slice::<serde_json::Value>(bytes) {
            Ok(v) => json_to_vm(&v),
            Err(_) => 0,
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_http_send_json(status_smi: i64, body_val: i64, headers_arr: i64) -> i64 {
    use crate::value::{make_smi};

    // 1) Normalize status
    let mut status = smi_to_i64(status_smi);
    if !(100..=599).contains(&status) {
        status = 200;
    }

    // 2) Collect headers (array of [k, v]) and ensure content-type
    let mut headers = collect_headers_from_arr(headers_arr);
    if !headers.iter().any(|(k,_)| k.eq_ignore_ascii_case("content-type")) {
        headers.push(("content-type".into(), "application/json".into()));
    }

    // 3) Encode body: if it's already a VM string, reuse it; otherwise fall back
    //    to fmt_value(..) (best-effort; upgrade to a real JSON serializer later).
    let body_str_val = unsafe {
        if wir_is_str(body_val) != 0 {
            // Already a string → use as-is
            body_val
        } else {
            // Fallback: stringify the value and send that as the body
            box_str_keepalive(fmt_value(body_val).into_bytes())
        }
    };

    // 4) Build `{ status, body, headers }` object on the VM heap
    unsafe {
        unsafe extern "C" {
            fn wir_array_new(len: i64) -> i64;
            fn wir_array_push(arr: i64, val: i64) -> i64;
        }

        let obj = wir_obj_new();

        // status
        wir_obj_set_str(obj, static_str_value("status"), make_smi(status));

        // body (string)
        wir_obj_set_str(obj, static_str_value("body"), body_str_val);

        // headers: array of [key, value] pairs
        let hdrs_arr_vm = wir_array_new(make_smi(0));
        for (k, v) in headers {
            let pair = wir_array_new(make_smi(0));
            let k_vm = box_str_keepalive(k.into_bytes());
            let v_vm = box_str_keepalive(v.into_bytes());
            let _ = wir_array_push(pair, k_vm);
            let _ = wir_array_push(pair, v_vm);
            let _ = wir_array_push(hdrs_arr_vm, pair);
        }
        wir_obj_set_str(obj, static_str_value("headers"), hdrs_arr_vm);

        // Return the response object; vm_dispatch will map it to an HTTP response.
        obj
    }
}

/// --------- GC integration: expose root slots to the collector ---------
/// Call this from your GC's root scanning hook, similar to EVENT_LOOP.with_root_slots.
pub fn http_with_root_slots<F: FnMut(*mut i64)>(mut f: F) {
    let p = &*HTTP_RESOLVE_CLO as *const i64 as *mut i64;

    #[cfg(debug_assertions)]
    {
        let cur = unsafe { *p };
        eprintln!("[http] root deferred slot {:?} -> {}", p, crate::value::dbg_addr(cur));
    }

    f(p);

    let g = SERVERS.lock();
    for entry in g.values() {
        let p = &entry.dispatch_closure as *const i64 as *mut i64;
        f(p);
        for r in &entry.routes {
            let p = &r.handler_closure as *const i64 as *mut i64;
            f(p);
        }
    }
}
