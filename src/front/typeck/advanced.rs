use super::*;

pub(super) fn literal_base(literal: &TypeLiteral) -> Ty {
    match literal {
        TypeLiteral::Number(_) => Ty::Number,
        TypeLiteral::String(_) => Ty::Str,
        TypeLiteral::Bool(_) => Ty::Bool,
    }
}

pub(super) fn widen_scalar(ty: Ty) -> Ty {
    match ty {
        Ty::Literal(lit) => literal_base(&lit),
        ty => ty,
    }
}

fn unresolved(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) | Ty::Deferred(..) => true,
        Ty::Array(t) | Ty::Set(t) | Ty::Promise(t) => unresolved(t),
        Ty::Tuple(ts) | Ty::Union(ts) | Ty::Named(_, ts) => ts.iter().any(unresolved),
        Ty::Map(k, v) => unresolved(k) || unresolved(v),
        _ => false,
    }
}

impl Checker {
    pub(super) fn normalize(&mut self, ty: Ty) -> Ty {
        match ty {
            Ty::Deferred(expr, bound) if !bound.values().any(unresolved) => self.resolve_in(&expr, &bound),
            ty => ty,
        }
    }

    pub(super) fn resolve_advanced(&mut self, expr: &TypeExpr, map: &StdMap<String, Ty>) -> Ty {
        let defer = || {
            let mut bound = map.clone();
            for (name, _) in &self.type_scope {
                bound.entry(name.clone()).or_insert_with(|| Ty::Param(name.clone()));
            }
            Ty::Deferred(Box::new(expr.clone()), bound)
        };
        let deferred = defer();
        match expr {
            TypeExpr::Literal(lit) => Ty::Literal(lit.clone()),
            TypeExpr::Infer(name) => map.get(name).cloned().unwrap_or_else(|| Ty::Param(name.clone())),
            TypeExpr::Tuple(items) => Ty::Tuple(items.iter().map(|t| self.resolve_in(t, map)).collect()),
            TypeExpr::KeyOf(inner) => {
                let inner = self.resolve_in(inner, map);
                if unresolved(&inner) { return deferred; }
                if let Some((members, _)) = self.members(&inner) {
                    union(members.into_iter().map(|m| Ty::Literal(TypeLiteral::String(m.name))))
                } else if matches!(inner, Ty::Unknown | Ty::Never) {
                    Ty::Never
                } else {
                    self.error(format!("keyof requires an object type, found `{inner}`"));
                    Ty::Never
                }
            }
            TypeExpr::Indexed(object, key) => {
                let object = self.resolve_in(object, map);
                let key = self.resolve_in(key, map);
                if unresolved(&object) || unresolved(&key) { return deferred; }
                self.indexed_type(&object, &key)
            }
            TypeExpr::Mapped { param, keys, value, optional } => {
                let key_ty = self.resolve_in(keys, map);
                if unresolved(&key_ty) { return deferred; }
                let inherited = if let TypeExpr::KeyOf(source) = &**keys {
                    let ty = self.resolve_in(source, map);
                    self.members(&ty).map(|(m, _)| m).unwrap_or_default()
                } else { Vec::new() };
                let keys = match key_ty {
                    Ty::Union(keys) => keys,
                    Ty::Never => Vec::new(),
                    key => vec![key],
                };
                let mut members = Vec::new();
                for key in keys {
                    let name = match &key {
                        Ty::Literal(TypeLiteral::String(s)) => s.clone(),
                        Ty::Literal(TypeLiteral::Number(n)) => n.to_string(),
                        _ => {
                            self.error("mapped type keys must be a finite union of string or number literals".into());
                            continue;
                        }
                    };
                    let mut bound = map.clone();
                    bound.insert(param.clone(), key);
                    let mut ty = self.resolve_in(value, &bound);
                    if *optional == Some(false) { ty = strip_null(&ty); }
                    members.push(Member {
                        optional: optional.unwrap_or_else(|| inherited.iter().any(|m| m.name == name && m.optional)),
                        name, ty, probe: true,
                    });
                }
                Ty::Object(Rc::new(members))
            }
            TypeExpr::Conditional { check, extends, yes, no } => {
                let actual = self.resolve_in(check, map);
                if unresolved(&actual) { return deferred; }
                // Distribution applies only to a bare type parameter.
                if let TypeExpr::Name { name, args } = &**check {
                    if args.is_empty() && map.contains_key(name) {
                        if let Ty::Union(parts) = actual {
                            let mut results = Vec::new();
                            for part in parts {
                                let mut bound = map.clone();
                                bound.insert(name.clone(), part);
                                results.push(self.resolve_in(expr, &bound));
                            }
                            return union(results);
                        }
                        if actual == Ty::Never { return Ty::Never; }
                    }
                }
                let mut inference = Vec::new();
                collect_infer(extends, &mut inference);
                let mut bound = map.clone();
                for name in &inference { bound.insert(name.clone(), Ty::Param(name.clone())); }
                let pattern = self.resolve_in(extends, &bound);
                let mut inferred = StdMap::new();
                self.infer(&pattern, &actual, &inference, &mut inferred);
                for name in &inference {
                    bound.insert(name.clone(), inferred.get(name).cloned().unwrap_or(Ty::Unknown));
                }
                let target = self.normalize(subst(&pattern, &bound));
                if unresolved(&target) { return deferred; }
                if actual == Ty::Any {
                    let a = self.resolve_in(yes, &bound);
                    let b = self.resolve_in(no, map);
                    union([a, b])
                } else if self.compat(&actual, &target).is_ok() {
                    self.resolve_in(yes, &bound)
                } else {
                    self.resolve_in(no, map)
                }
            }
            _ => unreachable!("ordinary types are resolved by resolve_in"),
        }
    }

    fn indexed_type(&mut self, object: &Ty, key: &Ty) -> Ty {
        if let Ty::Union(keys) = key {
            let types: Vec<_> = keys.iter().map(|k| self.indexed_type(object, k)).collect();
            return union(types);
        }
        match (object, key) {
            (Ty::Tuple(items), Ty::Literal(TypeLiteral::Number(n))) if *n >= 0.0 && n.fract() == 0.0 => {
                if let Some(ty) = items.get(*n as usize) { return ty.clone(); }
                self.error(format!("tuple index {n} is out of bounds"));
                Ty::Never
            }
            (Ty::Tuple(items), Ty::Number) => union(items.clone()),
            (Ty::Array(element), Ty::Number | Ty::Literal(TypeLiteral::Number(_))) => (**element).clone(),
            (_, Ty::Literal(TypeLiteral::String(name))) => self.prop_type(object, name),
            (Ty::Any, _) => Ty::Any,
            _ => {
                self.error(format!("type `{key}` cannot index `{object}`"));
                Ty::Never
            }
        }
    }
}

fn collect_infer(expr: &TypeExpr, names: &mut Vec<String>) {
    match expr {
        TypeExpr::Infer(name) => { if !names.contains(name) { names.push(name.clone()); } }
        TypeExpr::Name { args, .. } | TypeExpr::Tuple(args) | TypeExpr::Union(args) => {
            for arg in args { collect_infer(arg, names); }
        }
        TypeExpr::Array(inner) => collect_infer(inner, names),
        TypeExpr::Object(members) => { for member in members { collect_infer(&member.ty, names); } }
        TypeExpr::Function { params, ret, .. } => {
            for param in params { collect_infer(param, names); }
            collect_infer(ret, names);
        }
        _ => {}
    }
}

impl Checker {
    pub(super) fn runtime_check(&mut self, ty: &Ty, active: &mut StdSet<String>) -> Option<RtCheck> {
        let child = |this: &mut Self, ty: &Ty, active: &mut StdSet<String>| {
            this.runtime_check(ty, active).unwrap_or(RtCheck::Any)
        };
        Some(match ty {
            Ty::Any | Ty::Unknown => return None,
            Ty::Never => RtCheck::Never,
            Ty::Literal(lit) => RtCheck::Literal(lit.clone()),
            Ty::Number => RtCheck::Number,
            Ty::Str => RtCheck::Str,
            Ty::Bool => RtCheck::Bool,
            Ty::Null | Ty::Void => RtCheck::Null,
            Ty::Array(element) => RtCheck::Elements(Box::new(child(self, element, active))),
            Ty::Tuple(items) => RtCheck::Tuple(items.iter().map(|t| child(self, t, active)).collect()),
            Ty::Map(key, value) => RtCheck::MapEntries(
                Box::new(child(self, key, active)), Box::new(child(self, value, active)),
            ),
            Ty::Set(element) => RtCheck::SetElements(Box::new(child(self, element, active))),
            Ty::Func(_) => RtCheck::Function,
            Ty::Param(name) => {
                let constraint = self.constraint_of(name)?;
                return self.runtime_check(&constraint, active);
            }
            Ty::Union(items) => RtCheck::AnyOf(items.iter().map(|t| child(self, t, active)).collect()),
            Ty::Object(_) | Ty::Named(..) => {
                let key = ty.to_string();
                if !active.insert(key.clone()) { return Some(RtCheck::Ref(key)); }
                let (members, _) = self.members(ty)?;
                let length_only = !members.is_empty() && members.iter().all(|m| m.name == "length" && m.ty == Ty::Number);
                let properties = RtCheck::Properties(members.into_iter().filter(|m| m.probe)
                    .map(|m| (m.name, m.optional, child(self, &m.ty, active))).collect());
                active.remove(&key);
                let check = if length_only {
                    RtCheck::AnyOf(vec![RtCheck::Str, RtCheck::Array, properties])
                } else { properties };
                RtCheck::Define(key, Box::new(check))
            }
            Ty::Deferred(..) => {
                let normalized = self.normalize(ty.clone());
                if &normalized == ty { return None; }
                return self.runtime_check(&normalized, active);
            }
            Ty::Promise(_) => return None, // Resolved values are checked at await boundaries.
        })
    }
}
