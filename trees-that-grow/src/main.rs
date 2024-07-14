#![feature(never_type)]

// translated from https://www.reddit.com/r/haskell/comments/13or8t9/comment/jl6986w/

// we just assume these types exist for simplicity
struct Ty; // a type
struct Name; // a name

trait Ext {
    type Var;
    type App;
    type Lambda;
    type ExprX;
}

enum Expr<P: Ext> {
    Var(<P as Ext>::Var, Name),
    App(<P as Ext>::App, Box<Self>, Box<Self>),
    Lambda(<P as Ext>::Lambda, Name, Box<Self>),
    ExprX(<P as Ext>::ExprX),
}

// passes
struct Parsed;
struct Typed;

impl Ext for Parsed {
    type Var = ();
    type App = ();
    type Lambda = ();
    type ExprX = !;
}

// unfortunately, it seems like rust won't let us exclude the
// uninhabited variant when pattern matching
fn smth_for_parsed_expr(expr: Expr<Parsed>) -> String {
    match expr {
        Expr::Var(_, _) => todo!(),
        Expr::App(_, _, _) => todo!(),
        Expr::Lambda(_, _, _) => todo!(),
        Expr::ExprX(_) => todo!(),
    }
}

impl Ext for Typed {
    type Var = Ty;
    type App = Ty;
    type Lambda = Ty;
    type ExprX = TypedExprExtension;
}

enum TypedExprExtension {
    TypeAbstraction(Name, Box<Expr<Typed>>),
    TypeApplication(Box<Expr<Typed>>, Ty),
}

fn main() {
    println!("Hello, world!");
}
