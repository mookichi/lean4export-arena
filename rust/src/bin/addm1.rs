use olean::value::{Arenas, Expr, ExprNode};
use olean::OLean;
fn walk(arenas: &Arenas, e: Expr, d: usize) {
    let indent = "  ".repeat(d);
    match arenas.exprs.node(e) {
        ExprNode::Lam(n, t, b, _) => {
            println!("{indent}lam {} :", arenas.names.to_string_plain(n));
            walk(arenas, Expr(t), d+1);
            walk(arenas, Expr(b), d+1);
        }
        ExprNode::ForallE(n, t, b, _) => {
            println!("{indent}forallE {} :", arenas.names.to_string_plain(n));
            walk(arenas, Expr(t), d+1);
            walk(arenas, Expr(b), d+1);
        }
        ExprNode::App(f, a) => {
            println!("{indent}app");
            walk(arenas, Expr(f), d+1);
            walk(arenas, Expr(a), d+1);
        }
        ExprNode::Const(n, _) => println!("{indent}const {}", arenas.names.to_string_plain(n)),
        ExprNode::BVar(i) => println!("{indent}bvar {i}"),
        ExprNode::MData(kv, inner) => {
            println!(
                "{indent}mdata {:?}",
                arenas.exprs.kv(kv).iter().map(|(k,_)| arenas.names.to_string_plain(*k)).collect::<Vec<_>>()
            );
            walk(arenas, Expr(inner), d+1);
        }
        other => println!("{indent}{other:?}"),
    }
}
fn main() {
    let base = "/home/mookichi/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean/Init/Prelude";
    let mut bytes = Vec::new();
    for p in [".olean", ".olean.server", ".olean.private"] {
        if let Ok(b) = std::fs::read(format!("{base}{p}")) { bytes.push(b); }
    }
    let olean = OLean::parse_parts(bytes).unwrap();
    let mut arenas = Arenas::new();
    let mut d = olean::decode::Decoder::new(olean.region(), true, &mut arenas);
    let md = d.module_data_lite(2).unwrap();
    for c in &md.constants {
        if arenas.names.to_string_plain(c.name()) == "Nat.add.match_1" {
            if let olean::value::ConstantInfo::Defn(v) = c {
                walk(&arenas, v.value, 0);
            }
        }
    }
}
