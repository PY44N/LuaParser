use std::fmt::Debug;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOpr {
    Add = 0,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Concat,
    Eq,
    LT,
    LE,
    NE,
    GT,
    GE,
    And,
    Or,
    NoBinary,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnaryOpr {
    Minus,
    Not,
    Length,
    NoUnary,
}

#[derive(Debug)]
pub enum Expr {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
    Dots,
    Ident(String),

    /// AttrGet(Object, Key)
    AttrGet(Box<Expr>, Box<Expr>),
    Table(Vec<Field>),
    FuncCall(Box<FuncCall>),
    MethodCall(Box<MethodCall>),

    /// BinaryOp(Operator, Lhs, Rhs)
    BinaryOp(BinaryOpr, Box<Expr>, Box<Expr>),

    /// UnaryOp(Operator, expr)
    UnaryOp(UnaryOpr, Box<Expr>),

    /// Function(ParList, Stmts)
    Function(ParList, Vec<Stmt>),
}

impl Expr {
    pub fn is_vararg(&self) -> bool {
        match self {
            &Expr::Dots => true,
            &Expr::FuncCall(ref call) => !call.adj,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct Field {
    pub key: Option<Expr>,
    pub val: Expr,
}

impl Field {
    pub fn new(key: Option<Expr>, val: Expr) -> Field {
        Field { key, val }
    }
}

#[derive(Debug)]
pub struct ParList {
    pub vargs: bool,
    pub names: Vec<String>,
}

impl ParList {
    pub fn new() -> ParList {
        ParList {
            vargs: false,
            names: Vec::new(),
        }
    }

    pub fn set_vargs(&mut self, vargs: bool) {
        self.vargs = vargs;
    }

    pub fn set_names(&mut self, names: Vec<String>) {
        self.names = names;
    }

    pub fn push_param(&mut self, param: String) {
        self.names.push(param)
    }
}

#[derive(Debug)]
pub struct FuncDef {
    pub name: Vec<Expr>,
    pub body: Vec<Expr>,
}

impl FuncDef {
    pub fn new(name: Expr, body: Expr) -> Box<FuncDef> {
        // TODO: refactor this
        Box::new(FuncDef {
            name: vec![name],
            body: vec![body],
        })
    }
}

#[derive(Debug)]
pub struct MethodDef {
    pub receiver: Expr,
    pub method: String,
    pub body: Expr,
}

impl MethodDef {
    pub fn new(receiver: Expr, method: String, body: Expr) -> Box<MethodDef> {
        Box::new(MethodDef {
            receiver,
            method,
            body,
        })
    }
}

#[derive(Debug)]
pub struct MethodCall {
    pub receiver: Expr,
    pub method: String,
    pub args: Vec<Expr>,
}

impl MethodCall {
    pub fn new(receiver: Expr, method: String, args: Vec<Expr>) -> MethodCall {
        MethodCall {
            receiver,
            method,
            args,
        }
    }
}

#[derive(Debug)]
pub struct FuncCall {
    pub func: Expr,
    pub args: Vec<Expr>,
    pub adj: bool,
}

impl FuncCall {
    pub fn new(func: Expr, args: Vec<Expr>) -> FuncCall {
        FuncCall {
            func,
            args,
            adj: false,
        }
    }
}

#[derive(Debug)]
pub struct IfThenElse {
    pub condition: Expr,
    pub then: Vec<Stmt>,
    pub els: Vec<Stmt>,
}

impl IfThenElse {
    pub fn new(condition: Expr, then: Vec<Stmt>, els: Vec<Stmt>) -> IfThenElse {
        IfThenElse {
            condition,
            then,
            els,
        }
    }

    pub fn set_els(&mut self, els: Vec<Stmt>) {
        self.els = els;
    }
}

#[derive(Debug)]
pub struct NumberFor {
    pub name: String,
    pub init: Expr,
    pub limit: Expr,
    pub step: Expr,
    pub stmts: Vec<Stmt>,
}

impl NumberFor {
    pub fn new(
        name: String,
        init: Expr,
        limit: Expr,
        step: Expr,
        stmts: Vec<Stmt>,
    ) -> Box<NumberFor> {
        Box::new(NumberFor {
            name,
            init,
            limit,
            step,
            stmts,
        })
    }
}

#[derive(Debug)]
pub struct GenericFor {
    pub names: Vec<String>,
    pub exprs: Vec<Expr>,
    pub stmts: Vec<Stmt>,
}

impl GenericFor {
    pub fn new(names: Vec<String>, exprs: Vec<Expr>, stmts: Vec<Stmt>) -> Box<GenericFor> {
        Box::new(GenericFor {
            names,
            exprs,
            stmts,
        })
    }
}

#[derive(Debug)]
pub enum Stmt {
    /// Assign(Lhs, Rhs)
    Assign(Vec<Expr>, Vec<Expr>),

    /// LocalAssign(Names, Exprs)
    LocalAssign(Vec<String>, Vec<Expr>),
    FuncCall(Expr),
    MethodCall(Expr),
    DoBlock(Vec<Stmt>),

    /// While(Condition, Stmts)
    While(Expr, Vec<Stmt>),

    /// Repeat(Condition, Stmts)
    Repeat(Expr, Vec<Stmt>),
    If(IfThenElse),
    NumberFor(Box<NumberFor>),
    GenericFor(Box<GenericFor>),
    FuncDef(Box<FuncDef>),
    MethodDef(Box<MethodDef>),
    Return(Vec<Expr>),
    Break,
}
