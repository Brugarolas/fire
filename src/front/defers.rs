use super::*;

#[cfg(test)]
mod tests;

impl Parser<'_> {
    pub(super) fn defer_stmt(&mut self) -> PResult<Stmt> {
        let token = self.next()?;
        let kind = if token.tok == Tok::ErrDefer {
            DeferKind::ErrDefer
        } else {
            DeferKind::Defer
        };
        let binding = if kind == DeferKind::ErrDefer && self.matches(&Tok::Pipe) {
            let name = self.next()?;
            let Tok::Ident(binding) = name.tok else {
                return Err(
                    self.make_error("expected exception binding after 'errdefer |'", name.span)
                );
            };
            self.expect(Tok::Pipe, "expected '|' after errdefer exception binding")?;
            Some(binding)
        } else {
            None
        };
        let body = if self.check(&Tok::LBrace) {
            let body = self.block()?;
            self.matches(&Tok::Semi);
            body
        } else {
            let expression = self.expr()?;
            self.expect(Tok::Semi, "expected ';' after deferred expression")?;
            Block {
                stmts: vec![stmt_unknown(StmtKind::Expr(expression))],
            }
        };
        if cleanup_returns(&body) {
            return Err(self.make_error("cannot return from a defer or errdefer body", token.span));
        }
        let end = self.toks[self.i - 1].span.end;
        Ok(self.stmt_from_span(
            token.span.start..end,
            StmtKind::Defer {
                kind,
                binding,
                body,
            },
        ))
    }
}

fn cleanup_returns(block: &Block) -> bool {
    block.stmts.iter().any(|statement| match statement.kind() {
        StmtKind::Return(_) => true,
        StmtKind::If { then_b, else_b, .. } => {
            cleanup_returns(then_b) || else_b.as_ref().is_some_and(cleanup_returns)
        }
        StmtKind::While { body, .. }
        | StmtKind::For { body, .. }
        | StmtKind::Defer { body, .. } => cleanup_returns(body),
        StmtKind::Try {
            try_block,
            catch,
            finally_block,
        } => {
            cleanup_returns(try_block)
                || catch
                    .as_ref()
                    .is_some_and(|clause| cleanup_returns(&clause.body))
                || finally_block.as_ref().is_some_and(cleanup_returns)
        }
        _ => false,
    })
}
