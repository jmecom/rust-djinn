//! Check the domain of the map abstraction against Charon's resolved types.
//!
//! Source spelling is insufficient here: aliases, generic helpers, method
//! references and borrowed queries can all hide a user callback. Charon has
//! already resolved these uses, so inspect its non-deduplicated compiler IR
//! before installing any trusted models. Unknown type/signature shapes fail
//! closed; they must never widen the supported domain.

use serde_json::Value;
use std::collections::{HashMap, HashSet};

const MAP: &str = "std::collections::hash::map::HashMap";
const RANDOM_STATE: &str = "std::hash::random::RandomState";
const GLOBAL: &str = "alloc::alloc::Global";
const DEFAULT_HASHER: &str = "std::hash::random::DefaultHasher";
const DOMAIN: &str = "HashMap models require a concrete integer key, the same integer query type, std::hash::RandomState, and the global allocator; custom or unresolved Hash, Eq, Borrow and BuildHasher callbacks are unsupported";

struct Method {
    name: String,
    parameters: Vec<String>,
}

struct Usage {
    types: HashMap<u64, String>,
    methods: HashMap<u64, Method>,
    hashing: HashSet<u64>,
}

/// Validate model assumptions in the exact compiler output consumed by Aeneas.
/// The caller must ask Charon for `--no-dedup-serialized-ast`.
pub fn validate_usage(llbc: &Value) -> Result<(), String> {
    let ir = &llbc["translated"];
    if ir["options"]["no_dedup_serialized_ast"] != true {
        return Err("trusted-model audit requires Charon --no-dedup-serialized-ast".into());
    }
    let declarations = |field| {
        ir[field]
            .as_array()
            .ok_or_else(|| format!("unsupported Charon schema: missing {field}"))
    };
    let type_decls = declarations("type_decls")?;
    let fun_decls = declarations("fun_decls")?;
    let mut usage = Usage {
        types: HashMap::new(),
        methods: HashMap::new(),
        hashing: HashSet::new(),
    };
    for decl in type_decls.iter().filter(|d| !d.is_null()) {
        // A local type cannot become a standard-library model merely by
        // choosing matching module/crate names.
        if decl["item_meta"]["is_local"] == false {
            usage
                .types
                .insert(id(decl)?, name(&decl["item_meta"]["name"])?);
        }
    }
    for decl in fun_decls.iter().filter(|d| !d.is_null()) {
        let path = name(&decl["item_meta"]["name"])?;
        let function_id = id(decl)?;
        if path.starts_with("core::hash::") || path.starts_with("std::hash::random::") {
            usage.hashing.insert(function_id);
        }
        // Inherent HashMap methods, not similarly named local functions or
        // the map's drop-glue declaration. Identify the impl's self type by ID.
        let owner = decl["item_meta"]["name"]
            .as_array()
            .into_iter()
            .flatten()
            .find_map(|part| {
                let ty = inline(&part["Impl"]["Ty"]["skip_binder"]);
                usage.type_name(&ty["Adt"])
            });
        if owner == Some(MAP) {
            let parameters = decl["generics"]["types"]
                .as_array()
                .ok_or_else(|| format!("unsupported HashMap signature: {path}"))?
                .iter()
                .map(|p| {
                    p["name"]
                        .as_str()
                        .map(str::to_owned)
                        .ok_or_else(|| format!("unsupported HashMap parameter: {path}"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            usage.methods.insert(
                function_id,
                Method {
                    name: path,
                    parameters,
                },
            );
        } else if path.starts_with("std::collections::hash::map::")
            && matches!(
                path.rsplit("::").next(),
                Some("new" | "len" | "is_empty" | "insert" | "get" | "contains_key" | "remove")
            )
        {
            return Err(format!("unsupported Charon HashMap declaration: {path}"));
        }
    }
    for decl in fun_decls.iter().filter(|d| !d.is_null()) {
        let context = name(&decl["item_meta"]["name"])?;
        // Foreign opaque declarations necessarily have generic signatures.
        // Check their concrete references below, rather than rejecting the
        // standard library's generic API itself.
        if decl["item_meta"]["is_local"] == true {
            usage
                .walk(&decl["signature"])
                .map_err(|e| format!("{context}: {e}"))?;
        }
        usage
            .walk(&decl["body"])
            .map_err(|e| format!("{context}: {e}"))?;
    }
    for decl in type_decls
        .iter()
        .filter(|d| d["item_meta"]["is_local"] == true)
    {
        // Covers maps hidden inside user structs/enums, including generic
        // containers whose callback types cannot yet be resolved.
        usage.walk(&decl["kind"]).map_err(|e| {
            format!(
                "{}: {e}",
                name(&decl["item_meta"]["name"]).unwrap_or_default()
            )
        })?;
    }
    Ok(())
}

fn id(decl: &Value) -> Result<u64, String> {
    decl["def_id"]
        .as_u64()
        .ok_or_else(|| "unsupported Charon declaration ID".into())
}

fn name(path: &Value) -> Result<String, String> {
    let parts = path
        .as_array()
        .ok_or_else(|| "unsupported Charon item name".to_owned())?;
    let mut names = Vec::new();
    for part in parts {
        if let Some(ident) = part.get("Ident") {
            names.push(ident[0].as_str().ok_or("unsupported Charon identifier")?);
        } else if !part["Impl"].is_object() && !part["Builtin"].is_array() {
            return Err("unsupported Charon name component".into());
        }
    }
    Ok(names.join("::"))
}

fn inline(value: &Value) -> &Value {
    value.get("Untagged").unwrap_or(value)
}

fn integer(ty: &Value) -> Option<&str> {
    let ty = &inline(ty)["Scalar"]["Integer"];
    let (signed, unsigned) = (ty["Signed"].as_str(), ty["Unsigned"].as_str());
    match (signed, unsigned) {
        (Some(n @ ("I8" | "I16" | "I32" | "I64" | "I128" | "Isize")), None) => Some(n),
        (None, Some(n @ ("U8" | "U16" | "U32" | "U64" | "U128" | "Usize"))) => Some(n),
        _ => None,
    }
}

impl Usage {
    fn type_name(&self, adt: &Value) -> Option<&str> {
        adt["id"]
            .as_u64()
            .and_then(|i| self.types.get(&i))
            .map(String::as_str)
    }

    fn named_type(&self, ty: &Value, expected: &str) -> bool {
        let adt = &inline(ty)["Adt"];
        self.type_name(adt) == Some(expected)
            && adt["generics"]["types"]
                .as_array()
                .is_some_and(Vec::is_empty)
    }

    fn map_type(&self, adt: &Value) -> Result<(), String> {
        if self.type_name(adt) != Some(MAP) {
            return Ok(());
        }
        let args = adt["generics"]["types"].as_array().ok_or(DOMAIN)?;
        if args.len() != 4
            || integer(&args[0]).is_none()
            || !self.named_type(&args[2], RANDOM_STATE)
            || !self.named_type(&args[3], GLOBAL)
        {
            return Err(DOMAIN.into());
        }
        Ok(())
    }

    fn method(&self, method: &Method, reference: &Value) -> Result<(), String> {
        let args = reference["generics"]["types"].as_array().ok_or(DOMAIN)?;
        let expected: &[&str] = match method.name.rsplit("::").next() {
            Some("new") => &["K", "V"],
            Some("len" | "is_empty") => &["K", "V", "S", "A"],
            Some("insert") => &["K", "V", "S", "A", "Clause2_Hasher"],
            Some("get" | "contains_key" | "remove") => &["K", "V", "S", "A", "Q", "Clause2_Hasher"],
            _ => return Err(format!("{}: unsupported HashMap operation", method.name)),
        };
        if args.len() != method.parameters.len() || method.parameters != expected {
            return Err(format!(
                "{}: unsupported compiler signature; {DOMAIN}",
                method.name
            ));
        }
        let key = integer(&args[0]).ok_or(DOMAIN)?;
        for (parameter, ty) in expected.iter().zip(args) {
            let supported = match *parameter {
                "S" => self.named_type(ty, RANDOM_STATE),
                "A" => self.named_type(ty, GLOBAL),
                "Clause2_Hasher" => self.named_type(ty, DEFAULT_HASHER),
                "Q" => integer(ty) == Some(key),
                _ => true, // K was checked above; V has no callback restriction.
            };
            if !supported {
                return Err(DOMAIN.into());
            }
        }
        Ok(())
    }

    fn walk(&self, node: &Value) -> Result<(), String> {
        match node {
            Value::Object(fields) => {
                if let Some(adt) = fields.get("Adt").filter(|v| v.is_object()) {
                    self.map_type(adt)?;
                }
                // A FunDeclRef appears in calls, function-pointer constants,
                // and drop statements. Inspect all references, not only Call.
                if let Some(function_id) = node["kind"]["Fun"].as_u64() {
                    if self.hashing.contains(&function_id) {
                        return Err("direct hashing has no sound model: Hash/Hasher/BuildHasher helpers are supported only as unused dictionaries of primitive-key HashMap operations".into());
                    }
                    if let Some(method) = self.methods.get(&function_id) {
                        self.method(method, node)?;
                    }
                }
                for child in fields.values() {
                    self.walk(child)?;
                }
            }
            Value::Array(children) => {
                for child in children {
                    self.walk(child)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}
