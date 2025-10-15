use crate::diag::{ErrorCode, FrontError, FrontErrorMessage, RegisteredColors, Span, FileId};
use crate::front::{Block, ClassDecl, Expr, ExprKind, FuncDecl, LValue, LValueKind, Program, Stmt, StmtKind};
use crate::helpers::layered::{self, LayeredMap};
use compact_str::CompactString;

/// -------------------------
/// Diagnostics
/// -------------------------

#[derive(Debug, Clone, Default)]
pub struct SymbolInfo {
    /// The span where this variable was declared.
    pub declared_at: Span,
    /// Set to true when the variable is read from.
    pub used: bool,
}

/// The Resolver walks the AST after parsing to perform semantic analysis,
/// such as checking for variable declaration errors.
pub struct Resolver {
    /// The symbol table, using your LayeredMap to manage scopes.
    pub symbols: LayeredMap<String, SymbolInfo>,
    /// The name of the file being processed, for error reporting.
    file_name: CompactString,
}

impl Resolver {
    /// Creates a new Resolver for a given file.
    pub fn new(file_name: CompactString) -> Self {
        let mut layered_map: LayeredMap<String, SymbolInfo> = LayeredMap::new();
        layered_map.insert_cell("print".into(), SymbolInfo { declared_at: Span::new(0,0), used: true }); // Built-in function
        layered_map.insert_cell("this".into(), SymbolInfo { declared_at: Span::new(0,0), used: true }); // Built-in variable

        Self {
            symbols: layered_map,
            file_name,
        }
    }

    /// The main entry point for the resolver. It traverses the entire program AST.
    /// Returns the first error it encounters.
    pub fn resolve_program(&mut self, prog: &Program) -> Result<(), FrontError> {
        // In the future, you could pre-populate the global scope with built-in functions here.

        for func in &prog.functions {
            // First, declare the function in the current (global) scope so it can be called before definition.
            self.declare(func.name.clone(), Span::new(0, 0))?; // Note: Span is not yet available on FuncDecl
        }

        for func in &prog.functions {
            self.resolve_func(func)?;
        }

        for class in &prog.classes {
            self.resolve_class(class)?;
        }

        // After resolving everything, check the global scope for unused variables.
        self.exit_scope()?;

        Ok(())
    }

    /// Resolves a function declaration.
    fn resolve_func(&mut self, func: &FuncDecl) -> Result<(), FrontError> {
        self.enter_scope();
        for param_name in &func.params {
            // Parameters are declared and implicitly used.
            self.declare(param_name.clone(), Span::new(0,0))?; // Note: Need spans on params
            self.mark_as_used(param_name);
        }
        self.resolve_block(&func.body)?;
        self.exit_scope()?;
        Ok(())
    }

    /// Resolves a class declaration.
    fn resolve_class(&mut self, class: &ClassDecl) -> Result<(), FrontError> {
        self.declare(class.name.clone(), Span::new(0,0))?; // Note: Need spans on class decl
        // Future work: resolve members, superclass, etc.
        Ok(())
    }

    /// Resolves a block of statements, which creates a new lexical scope.
    fn resolve_block(&mut self, block: &Block) -> Result<(), FrontError> {
        self.enter_scope();
        for stmt in &block.stmts {
            self.resolve_stmt(stmt)?;
        }
        self.exit_scope()?;
        Ok(())
    }

    /// Resolves a single statement.
    fn resolve_stmt(&mut self, stmt: &Stmt) -> Result<(), FrontError> {
        match &stmt.kind {
            StmtKind::Var { name, init } => {
                // Resolve the initializer expression *before* declaring the variable.
                // This correctly catches `var x = x;`.
                if let Some(initializer) = init {
                    self.resolve_expr(initializer)?;
                }
                self.declare(name.clone(), stmt.meta.span.clone())?;
            }
            StmtKind::Expr(expr) => self.resolve_expr(expr)?,
            StmtKind::If { cond, then_b, else_b } => {
                self.resolve_expr(cond)?;
                self.resolve_block(then_b)?;
                if let Some(else_block) = else_b {
                    self.resolve_block(else_block)?;
                }
            }
            StmtKind::While { cond, body } => {
                self.resolve_expr(cond)?;
                self.resolve_block(body)?;
            }
            StmtKind::For { init, cond, step, body } => {
                self.enter_scope();
                if let Some(init_stmt) = init {
                    self.resolve_stmt(init_stmt)?;
                }
                if let Some(cond_expr) = cond {
                    self.resolve_expr(cond_expr)?;
                }
                if let Some(step_expr) = step {
                    self.resolve_expr(step_expr)?;
                }
                self.resolve_block(body)?;
                self.exit_scope()?;
            }
            StmtKind::Return(Some(expr)) => self.resolve_expr(expr)?,
            StmtKind::Throw(expr) => self.resolve_expr(expr)?,
            // Add other statements like Try/Catch, Defer, etc. here
            _ => {} // For unhandled statements
        }
        Ok(())
    }

    /// Resolves a single expression.
    fn resolve_expr(&mut self, expr: &Expr) -> Result<(), FrontError> {
        match &expr.kind {
            ExprKind::Ident(name) => {
                // Check for usage of an undeclared variable.
                if self.symbols.get(name).is_none() {
                    return Err(FrontError {
                        file_name: self.file_name.clone(),
                        span: expr.meta.span.clone(),
                        message: FrontErrorMessage::plain(format!("Cannot find value `{}` in this scope", name)),
                        code: ErrorCode::NotDefined,
                        labels: vec![],
                        note: None,
                    });
                }
                // Mark the variable as used.
                self.mark_as_used(name);
            }
            ExprKind::Assign(lvalue, rhs) => {
                self.resolve_expr(rhs)?;
                self.resolve_lvalue(lvalue)?;
            }
            ExprKind::Binary { a, b, .. } => {
                self.resolve_expr(a)?;
                self.resolve_expr(b)?;
            }
            ExprKind::Unary { e, .. } => self.resolve_expr(e)?,
            ExprKind::Call { callee, args } => {
                self.resolve_expr(callee)?;
                for arg in args {
                    self.resolve_expr(arg)?;
                }
            }

            ExprKind::GetProp { recv, .. } => self.resolve_expr(recv)?,
            ExprKind::Index { recv, index } => {
                self.resolve_expr(recv)?;
                self.resolve_expr(index)?;
            }
            ExprKind::CallBuiltinMapMethod { recv, args, .. } => {
                self.resolve_expr(recv)?;
                for arg in args {
                    self.resolve_expr(arg)?;
                }
            }
            ExprKind::CallBuiltinSetMethod { recv, args, .. } => {
                self.resolve_expr(recv)?;
                for arg in args {
                    self.resolve_expr(arg)?;
                }
            }
            ExprKind::GetBuiltinSize(recv) => self.resolve_expr(recv)?,
            // Add other expressions recursively
            _ => {} // For unhandled expressions
        }
        Ok(())
    }

    fn resolve_lvalue(&mut self, lvalue: &LValue) -> Result<(), FrontError> {
        match &lvalue.kind {
            LValueKind::Ident(name) => {
                // This is an assignment target. Check it exists and mark as used.
                if self.symbols.get(name).is_none() {
                    return Err(FrontError {
                        file_name: self.file_name.clone(),
                        span: lvalue.meta.span.clone(),
                        message: FrontErrorMessage::plain(format!("Cannot assign to undeclared variable `{}`", name)),
                        code: ErrorCode::NotDefined,
                        labels: vec![],
                        note: None,
                    });
                }
                self.mark_as_used(name);
            }
            LValueKind::GetProp { recv, .. } => self.resolve_expr(recv)?,
            LValueKind::Index { recv, index } => {
                self.resolve_expr(recv)?;
                self.resolve_expr(index)?;
            }
        }
        Ok(())
    }

    // --- Helper Methods ---

    fn enter_scope(&mut self) {
        self.symbols.enter_layer();
    }

    /// Exits a scope and checks for any variables that were declared but not used.
    fn exit_scope(&mut self) -> Result<(), FrontError> {
        let items_in_exited_scope = self.symbols.exit_layer();
        for (name, info) in items_in_exited_scope {
            if !info.used && !name.starts_with('_') {
                return Err(FrontError {
                    file_name: self.file_name.clone(),
                    span: info.declared_at.clone(),
                    message: FrontErrorMessage {
                        text: "Unused variable: `{}`".into(),
                        highlighted_strings: vec![name.into()],
                        color: RegisteredColors::Yellow,
                    },
                    code: ErrorCode::DefinedUnused,
                    labels: vec![],
                    note: Some(FrontErrorMessage::plain("Prefix with an underscore to ignore: `_` or `_myVar`")),
                });
            }
        }
        Ok(())
    }

    /// Declares a new variable in the current scope, checking for redeclarations.
    fn declare(&mut self, name: String, span: Span) -> Result<(), FrontError> {
        if self.symbols.is_in_current_layer(&name) {
            return Err(FrontError {
                file_name: self.file_name.clone(),
                span: span.clone(),
                message: FrontErrorMessage::plain(format!("`{}` is already declared in this scope", name)),
                code: ErrorCode::AlreadyDefined,
                labels: vec![], // Future: add a label pointing to the original declaration
                note: None,
            });
        }
        let info = SymbolInfo { declared_at: span, used: false };
        self.symbols.insert(name, info);
        Ok(())
    }

    /// Marks a variable as 'used' in the symbol table.
    fn mark_as_used(&mut self, name: &String) {
        if let Some(info) = self.symbols.get_mut(name) {
            info.used = true;
        }
    }
}
