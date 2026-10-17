use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone)]
enum EnumValue {
    Number(f64),
    String(String),
}

impl EnumValue {
    fn expression(&self) -> Expr {
        match self {
            Self::Number(value)
                if *value >= i32::MIN as f64
                    && *value <= i32::MAX as f64
                    && value.fract() == 0.0 =>
            {
                expr_unknown(ExprKind::LitInt(*value as i32))
            }
            Self::Number(value) => expr_unknown(ExprKind::LitF64(*value)),
            Self::String(value) => expr_unknown(ExprKind::Str(value.clone())),
        }
    }
}

impl Parser<'_> {
    pub(super) fn enum_decl(&mut self) -> PResult<Stmt> {
        let start = self.next()?.span.start;
        let token = self.next()?;
        let Tok::Ident(name) = token.tok else {
            return Err(self.make_error("expected enum name", token.span));
        };
        self.expect(Tok::LBrace, "expected '{' after enum name")?;
        let mut members: HashMap<String, EnumValue> = HashMap::default();
        let mut properties = Vec::new();
        let mut previous = EnumValue::Number(-1.0);
        while !self.check(&Tok::RBrace) {
            let token = self.next()?;
            let member_name = match token.tok {
                Tok::Ident(name) | Tok::Str(name) => name,
                Tok::Get => "get".to_string(),
                Tok::Set => "set".to_string(),
                Tok::Catch => "catch".to_string(),
                Tok::Finally => "finally".to_string(),
                Tok::Delete => "delete".to_string(),
                Tok::MapBuiltin => "Map".to_string(),
                Tok::SetBuiltin => "Set".to_string(),
                _ => return Err(self.make_error("expected enum member name", token.span)),
            };
            if member_name.parse::<f64>().is_ok() {
                return Err(self.make_error("enum member names cannot be numeric", token.span));
            }
            if members.contains_key(&member_name) {
                return Err(
                    self.make_error(format!("duplicate enum member '{member_name}'"), token.span)
                );
            }

            let value = if self.matches(&Tok::Eq) {
                let expression = self.expr()?;
                self.enum_constant(&expression, &name, &members)?
            } else {
                match &previous {
                    EnumValue::Number(value) => {
                        let next = value + 1.0;
                        if !next.is_finite() || next == *value {
                            return Err(self.make_error(
                                "enum auto-increment exceeds numeric precision; provide an initializer",
                                token.span,
                            ));
                        }
                        EnumValue::Number(next)
                    }
                    _ => {
                        return Err(self.make_error(
                            "enum member following a string value requires an initializer",
                            token.span,
                        ));
                    }
                }
            };
            properties.push(ObjItem::Prop(
                PropKey::Str(member_name.clone()),
                value.expression(),
            ));
            if let EnumValue::Number(number) = &value {
                let key = if *number == 0.0 {
                    "0".to_string()
                } else {
                    number.to_string()
                };
                properties.push(ObjItem::Prop(
                    PropKey::Str(key),
                    expr_unknown(ExprKind::Str(member_name.clone())),
                ));
            }
            previous = value.clone();
            members.insert(member_name, value);
            if !self.check(&Tok::RBrace) {
                self.expect(Tok::Comma, "expected ',' between enum members")?;
            }
        }
        self.expect(Tok::RBrace, "expected '}' after enum members")?;
        let end = self.toks[self.i - 1].span.end;
        self.matches(&Tok::Semi);
        let init =
            expr_unknown(ExprKind::ObjLit(properties)).with_meta(self.meta_from_range(start..end));
        Ok(self.stmt_from_span(
            start..end,
            StmtKind::Enum {
                name,
                binding: BindingId(next_id()),
                init,
            },
        ))
    }

    fn enum_constant(
        &self,
        expression: &Expr,
        enum_name: &str,
        members: &HashMap<String, EnumValue>,
    ) -> PResult<EnumValue> {
        let invalid = || {
            self.err_here(
                "enum initializer must be a finite numeric/string constant or a previous member",
            )
        };
        let value = match expression.kind() {
            ExprKind::LitInt(value) => EnumValue::Number(*value as f64),
            ExprKind::LitF64(value) => EnumValue::Number(*value),
            ExprKind::Str(value) => EnumValue::String(value.clone()),
            ExprKind::Group(inner) => return self.enum_constant(inner, enum_name, members),
            ExprKind::Ident(name) => members.get(name).cloned().ok_or_else(invalid)?,
            ExprKind::GetProp { recv, name } if matches!(recv.kind(), ExprKind::Ident(name) if name == enum_name) => {
                members.get(name).cloned().ok_or_else(invalid)?
            }
            ExprKind::Index { recv, index } if matches!(recv.kind(), ExprKind::Ident(name) if name == enum_name) =>
            {
                let ExprKind::Str(name) = index.kind() else {
                    return Err(invalid());
                };
                members.get(name).cloned().ok_or_else(invalid)?
            }
            ExprKind::GetBuiltinSize(recv) if matches!(recv.kind(), ExprKind::Ident(name) if name == enum_name) => {
                members.get("size").cloned().ok_or_else(invalid)?
            }
            ExprKind::Unary { op, e } => {
                let EnumValue::Number(value) = self.enum_constant(e, enum_name, members)? else {
                    return Err(invalid());
                };
                EnumValue::Number(match op {
                    UnOp::Neg => -value,
                    UnOp::Pos => value,
                    _ => return Err(invalid()),
                })
            }
            ExprKind::Binary { op, a, b } => {
                let left = self.enum_constant(a, enum_name, members)?;
                let right = self.enum_constant(b, enum_name, members)?;
                match (left, right) {
                    (EnumValue::Number(a), EnumValue::Number(b)) => EnumValue::Number(match op {
                        BinOp::Add => a + b,
                        BinOp::Sub => a - b,
                        BinOp::Mul => a * b,
                        BinOp::Div => a / b,
                        BinOp::Rem => a % b,
                        _ => return Err(invalid()),
                    }),
                    (EnumValue::String(a), EnumValue::String(b)) if *op == BinOp::Add => {
                        EnumValue::String(a + &b)
                    }
                    _ => return Err(invalid()),
                }
            }
            _ => return Err(invalid()),
        };
        if matches!(&value, EnumValue::Number(value) if !value.is_finite()) {
            return Err(invalid());
        }
        Ok(value)
    }
}
