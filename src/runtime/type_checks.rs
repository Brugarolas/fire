use super::*;
use crate::front::types::{RtCheck, TypeLiteral};
use std::collections::{HashMap as StdMap, HashSet as StdSet};
use std::sync::Arc;

// Schemas contain no VM values and therefore need no GC roots.
static SCHEMAS: OnceLock<RwLock<StdMap<String, Arc<RtCheck>>>> = OnceLock::new();

#[unsafe(no_mangle)]
pub extern "C" fn wir_type_matches(value: i64, schema: i64) -> i64 {
    let Some(text) = (unsafe { boxedstr_to_string(schema) }) else { return BOOL_FALSE; };
    let cache = SCHEMAS.get_or_init(|| RwLock::new(StdMap::new()));
    let cached = cache.read().get(&text).cloned();
    let schema = match cached {
        Some(schema) => schema,
        None => {
            let Ok(schema) = serde_json::from_str::<RtCheck>(&text) else { return BOOL_FALSE; };
            let schema = Arc::new(schema);
            cache.write().insert(text, schema.clone());
            schema
        }
    };
    let mut definitions = StdMap::new();
    collect_definitions(&schema, &mut definitions);
    bool_to_value(matches_type(value, &schema, &definitions, &mut StdSet::new(), 0))
}

fn collect_definitions<'a>(check: &'a RtCheck, defs: &mut StdMap<&'a str, &'a RtCheck>) {
    match check {
        RtCheck::Define(name, inner) => { defs.insert(name, inner); collect_definitions(inner, defs); }
        RtCheck::Elements(inner) | RtCheck::SetElements(inner) => collect_definitions(inner, defs),
        RtCheck::MapEntries(k, v) => { collect_definitions(k, defs); collect_definitions(v, defs); }
        RtCheck::Tuple(items) | RtCheck::AnyOf(items) => {
            for item in items { collect_definitions(item, defs); }
        }
        RtCheck::Properties(items) => { for (_, _, item) in items { collect_definitions(item, defs); } }
        _ => {}
    }
}

fn matches_type(
    value: i64,
    check: &RtCheck,
    defs: &StdMap<&str, &RtCheck>,
    active: &mut StdSet<(i64, String)>,
    depth: usize,
) -> bool {
    // Cycles are recognized by (object, schema). The depth limit also bounds
    // hostile acyclic inputs without risking a Rust stack overflow.
    if depth > 256 { return false; }
    let tag = heap_tag(value);
    let test = |v, c: &RtCheck, active: &mut StdSet<(i64, String)>| matches_type(v, c, defs, active, depth + 1);
    match check {
        RtCheck::Any => true,
        RtCheck::Never => false,
        RtCheck::Number => is_imm(value) || tag == Some(TAG_BOXED_F64),
        RtCheck::Str => tag == Some(TAG_STRING),
        RtCheck::Bool => v::is_bool(value),
        RtCheck::Null => value == NULL,
        RtCheck::Array => tag == Some(TAG_ARRAY),
        RtCheck::Map => tag == Some(TAG_MAP),
        RtCheck::Set => tag == Some(TAG_SET),
        RtCheck::Function => tag == Some(TAG_CLOSURE),
        RtCheck::Literal(TypeLiteral::Number(n)) => search_number(value).is_some_and(|v| v == *n),
        RtCheck::Literal(TypeLiteral::Bool(b)) => value == bool_to_value(*b),
        RtCheck::Literal(TypeLiteral::String(s)) => {
            tag == Some(TAG_STRING) && unsafe { boxedstr_to_string(value) }.as_ref() == Some(s)
        }
        RtCheck::AnyOf(items) => items.iter().any(|c| test(value, c, active)),
        RtCheck::Elements(element) => tag == Some(TAG_ARRAY) && unsafe {
            (*(value as *const BoxedArray)).buf.iter().all(|v| test(*v, element, active))
        },
        RtCheck::Tuple(items) => tag == Some(TAG_ARRAY) && unsafe {
            let values = &(*(value as *const BoxedArray)).buf;
            values.len() == items.len() && values.iter().zip(items).all(|(v, c)| test(*v, c, active))
        },
        RtCheck::MapEntries(key, val) => tag == Some(TAG_MAP) && unsafe {
            (*(value as *const BoxedMap)).map.iter().all(|(k, v)| test(k.0, key, active) && test(v.0, val, active))
        },
        RtCheck::SetElements(element) => tag == Some(TAG_SET) && unsafe {
            (*(value as *const BoxedSet)).set.iter().all(|v| test(v.0, element, active))
        },
        RtCheck::Shape(names) => tag == Some(TAG_OBJECT) && unsafe {
            names.iter().all(|name| v::obj_has_str(value, name) == BOOL_TRUE)
        },
        RtCheck::Properties(members) => tag == Some(TAG_OBJECT) && unsafe {
            members.iter().all(|(name, optional, check)| {
                if v::obj_has_str(value, name) != BOOL_TRUE { return *optional; }
                test(v::obj_get_str(value, name), check, active)
            })
        },
        RtCheck::Define(name, inner) => {
            let key = (value, name.clone());
            if !active.insert(key.clone()) { return true; }
            let result = test(value, inner, active);
            active.remove(&key);
            result
        }
        RtCheck::Ref(name) => match defs.get(name.as_str()) {
            Some(inner) => {
                let key = (value, name.clone());
                if !active.insert(key.clone()) { return true; }
                let result = test(value, inner, active);
                active.remove(&key);
                result
            }
            None => false,
        },
    }
}
