use std::fmt::Debug;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
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
pub enum UnaryOperator {
    Minus,
    Not,
    Length,
    NoUnary,
}

#[derive(Debug)]
pub enum Expression {
    True,
    False,
    Nil,
    Number(f64),
    String(String),
    Dots,
    Ident(String),

    /// AttrGet(Object, Key)
    AttrGet(Box<Expression>, Box<Expression>),
    Table(Vec<Field>),
    FuncCall(Box<FunctionCall>),
    MethodCall(Box<MethodCall>),

    /// BinaryOp(Operator, Lhs, Rhs)
    BinaryOp(BinaryOperator, Box<Expression>, Box<Expression>),

    /// UnaryOp(Operator, expr)
    UnaryOp(UnaryOperator, Box<Expression>),

    /// Function(ParList, Stmts)
    Function(ParameterList, Vec<Statement>),
}

impl Expression {
    pub fn is_vararg(&self) -> bool {
        match self {
            &Expression::Dots => true,
            &Expression::FuncCall(ref call) => !call.adj,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct Field {
    pub key: Option<Expression>,
    pub val: Expression,
}

impl Field {
    pub fn new(key: Option<Expression>, val: Expression) -> Field {
        Field { key, val }
    }
}

#[derive(Debug)]
pub struct ParameterList {
    pub vargs: bool,
    pub names: Vec<String>,
}

impl ParameterList {
    pub fn new() -> ParameterList {
        ParameterList {
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
pub struct FunctionDefinition {
    pub name: Vec<Expression>,
    pub body: Vec<Expression>,
}

impl FunctionDefinition {
    pub fn new(name: Expression, body: Expression) -> Box<FunctionDefinition> {
        // TODO: refactor this
        Box::new(FunctionDefinition {
            name: vec![name],
            body: vec![body],
        })
    }
}

#[derive(Debug)]
pub struct MethodDefinition {
    pub receiver: Expression,
    pub method: String,
    pub body: Expression,
}

impl MethodDefinition {
    pub fn new(receiver: Expression, method: String, body: Expression) -> Box<MethodDefinition> {
        Box::new(MethodDefinition {
            receiver,
            method,
            body,
        })
    }
}

#[derive(Debug)]
pub struct MethodCall {
    pub receiver: Expression,
    pub method: String,
    pub args: Vec<Expression>,
}

impl MethodCall {
    pub fn new(receiver: Expression, method: String, args: Vec<Expression>) -> MethodCall {
        MethodCall {
            receiver,
            method,
            args,
        }
    }
}

#[derive(Debug)]
pub struct FunctionCall {
    pub func: Expression,
    pub args: Vec<Expression>,
    pub adj: bool,
}

impl FunctionCall {
    pub fn new(func: Expression, args: Vec<Expression>) -> FunctionCall {
        FunctionCall {
            func,
            args,
            adj: false,
        }
    }
}

#[derive(Debug)]
pub struct IfThenElse {
    pub condition: Expression,
    pub then: Vec<Statement>,
    pub els: Vec<Statement>,
}

impl IfThenElse {
    pub fn new(condition: Expression, then: Vec<Statement>, els: Vec<Statement>) -> IfThenElse {
        IfThenElse {
            condition,
            then,
            els,
        }
    }

    pub fn set_els(&mut self, els: Vec<Statement>) {
        self.els = els;
    }
}

#[derive(Debug)]
pub struct NumberFor {
    pub name: String,
    pub init: Expression,
    pub limit: Expression,
    pub step: Expression,
    pub stmts: Vec<Statement>,
}

impl NumberFor {
    pub fn new(
        name: String,
        init: Expression,
        limit: Expression,
        step: Expression,
        stmts: Vec<Statement>,
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
    pub exprs: Vec<Expression>,
    pub stmts: Vec<Statement>,
}

impl GenericFor {
    pub fn new(
        names: Vec<String>,
        exprs: Vec<Expression>,
        stmts: Vec<Statement>,
    ) -> Box<GenericFor> {
        Box::new(GenericFor {
            names,
            exprs,
            stmts,
        })
    }
}

#[derive(Debug)]
pub enum Statement {
    /// Assign(Lhs, Rhs)
    Assign(Vec<Expression>, Vec<Expression>),

    /// LocalAssign(Names, Exprs)
    LocalAssign(Vec<String>, Vec<Expression>),
    FuncCall(Expression),
    MethodCall(Expression),
    DoBlock(Vec<Statement>),

    /// While(Condition, Stmts)
    While(Expression, Vec<Statement>),

    /// Repeat(Condition, Stmts)
    Repeat(Expression, Vec<Statement>),
    If(IfThenElse),
    NumberFor(Box<NumberFor>),
    GenericFor(Box<GenericFor>),
    FuncDef(Box<FunctionDefinition>),
    MethodDef(Box<MethodDefinition>),
    Return(Vec<Expression>),
    Break,
}
