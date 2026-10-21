use cargo_djinn::models;
use serde_json::{json, Value};

fn strmap() -> Value {
    serde_json::from_str(include_str!("fixtures/models/strmap.json")).unwrap()
}

fn counterexamples() -> Value {
    serde_json::from_str(include_str!("fixtures/models/unsound-hashing.json")).unwrap()
}

fn functions(ir: &mut Value) -> &mut Vec<Value> {
    ir["translated"]["fun_decls"].as_array_mut().unwrap()
}

fn named(decl: &Value, name: &str) -> bool {
    decl["item_meta"]["name"]
        .as_array()
        .unwrap()
        .iter()
        .any(|p| p["Ident"][0] == name)
}

fn remove_function(ir: &mut Value, function: &str) {
    functions(ir).retain(|f| !named(f, function));
}

fn alter(value: &mut Value, change: &mut impl FnMut(&mut Value)) {
    change(value);
    match value {
        Value::Array(values) => values.iter_mut().for_each(|v| alter(v, change)),
        Value::Object(fields) => fields.values_mut().for_each(|v| alter(v, change)),
        _ => {}
    }
}

#[test]
fn concrete_standard_maps_are_supported() {
    models::validate_usage(&strmap()).unwrap();
}

#[test]
fn scalar_hash_cannot_erase_observable_writes() {
    let error = models::validate_usage(&counterexamples()).unwrap_err();
    assert!(error.contains("direct hashing"), "{error}");
}

#[test]
fn map_cannot_skip_a_user_hash_callback() {
    let mut ir = counterexamples();
    remove_function(&mut ir, "hash_is_noop");
    let error = models::validate_usage(&ir).unwrap_err();
    assert!(error.contains("concrete integer key"), "{error}");
}

#[test]
fn generic_keys_and_custom_hash_builders_are_rejected() {
    for parameter in ["key", "hasher"] {
        let mut ir = strmap();
        // The actual compiler fixture uses u32 keys and RandomState (ID 7).
        let random_state = ir["translated"]["type_decls"]
            .as_array()
            .unwrap()
            .iter()
            .find(|d| named(d, "RandomState"))
            .unwrap()["def_id"]
            .as_u64()
            .unwrap();
        for f in functions(&mut ir) {
            if f["item_meta"]["is_local"] != true {
                continue;
            }
            alter(f, &mut |node| {
                if (parameter == "key"
                    && node["Untagged"]["Scalar"]["Integer"]["Unsigned"] == "U32")
                    || (parameter == "hasher" && node["Untagged"]["Adt"]["id"] == random_state)
                {
                    *node = json!({"Untagged": {"TypeVar": {"Free": 0}}});
                }
            });
        }
        let error = models::validate_usage(&ir).unwrap_err();
        assert!(error.contains("unsupported"), "{parameter}: {error}");
    }
}

#[test]
fn custom_borrowed_queries_are_rejected_even_with_primitive_keys() {
    let mut ir = strmap();
    for f in functions(&mut ir) {
        if f["item_meta"]["is_local"] != true {
            continue;
        }
        alter(&mut f["body"], &mut |node| {
            if node["kind"]["Fun"].is_number()
                && node["generics"]["types"]
                    .as_array()
                    .is_some_and(|a| a.len() == 6)
            {
                node["generics"]["types"][4] = json!({"Untagged": {"TypeVar": {"Free": 0}}});
            }
        });
    }
    let error = models::validate_usage(&ir).unwrap_err();
    assert!(error.contains("same integer query type"), "{error}");
}

#[test]
fn local_types_cannot_impersonate_standard_hashers() {
    let mut ir = strmap();
    for ty in ir["translated"]["type_decls"].as_array_mut().unwrap() {
        if named(ty, "RandomState") {
            ty["item_meta"]["is_local"] = json!(true);
        }
    }
    assert!(models::validate_usage(&ir)
        .unwrap_err()
        .contains("callbacks are unsupported"));
}

#[test]
fn unknown_compiler_encodings_fail_closed() {
    let mut ir = strmap();
    ir["translated"]["options"]["no_dedup_serialized_ast"] = json!(false);
    assert!(models::validate_usage(&ir)
        .unwrap_err()
        .contains("no-dedup"));
    let mut ir = strmap();
    ir["translated"]["type_decls"] = Value::Null;
    assert!(models::validate_usage(&ir).is_err());
    let mut ir = strmap();
    for f in functions(&mut ir) {
        if named(f, "get") && f["generics"]["types"].as_array().unwrap().len() == 6 {
            f["generics"]["types"][4]["name"] = json!("NewCallback");
        }
    }
    assert!(models::validate_usage(&ir)
        .unwrap_err()
        .contains("unsupported compiler signature"));
    let mut ir = strmap();
    for f in functions(&mut ir) {
        for part in f["item_meta"]["name"].as_array_mut().unwrap() {
            if part["Impl"]["Ty"].is_object() {
                part["Impl"]["Ty"]["skip_binder"] = json!({"UnknownTypeEncoding": 0});
            }
        }
    }
    assert!(models::validate_usage(&ir)
        .unwrap_err()
        .contains("unsupported Charon HashMap declaration"));
}
