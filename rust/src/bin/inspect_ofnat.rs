use olean::export::load_env;
use olean::value::{ConstantInfo, Expr, ExprNode, Name};

fn main() {
    let module = std::env::args().nth(1).unwrap_or("Phase0Test".into());
    let roots: Vec<std::path::PathBuf> = vec!["/run/media/mookichi/ssd2/dev/lean4export/.lake/build/lib/lean".into(), "/home/mookichi/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean".into()];
    let (env, mut arenas) = load_env(&module, &roots).unwrap();
    println!("constants: {}", env.constants.len());
    for n in ["OfNat", "OfNat.mk", "OfNat.rec", "OfNat.ofNat"] {
        let name = arenas.names.intern_path(&[n]);
        match env.find(&name) {
            Some(ci) => println!("{n}: {}", describe(&arenas, ci)),
            None => println!("{n}: NOT FOUND"),
        }
    }
}

fn describe(arenas: &olean::value::Arenas, ci: &ConstantInfo) -> String {
    let nm = |n: Name| arenas.names.to_string_plain(n);
    match ci {
        ConstantInfo::Induct(v) => format!(
            "Induct name={} level_params={:?} num_params={} ctors={:?} all={:?} ty={}",
            nm(v.val.name), v.val.level_params.iter().map(|&x| nm(x)).collect::<Vec<_>>(), v.num_params,
            v.ctors.iter().map(|&x| nm(x)).collect::<Vec<_>>(), v.all.iter().map(|&x| nm(x)).collect::<Vec<_>>(),
            expr_desc(arenas, v.val.ty)
        ),
        ConstantInfo::Ctor(v) => format!(
            "Ctor name={} induct={} level_params={:?} num_params={} ty={}",
            nm(v.val.name), nm(v.induct), v.val.level_params.iter().map(|&x| nm(x)).collect::<Vec<_>>(),
            v.num_params, expr_desc(arenas, v.val.ty)
        ),
        ConstantInfo::Rec(v) => format!(
            "Rec name={} level_params={:?} rules={} ty={}",
            nm(v.val.name), v.val.level_params.iter().map(|&x| nm(x)).collect::<Vec<_>>(),
            v.rules.len(), expr_desc(arenas, v.val.ty)
        ),
        ConstantInfo::Defn(v) => format!("Defn name={} ty={}", nm(v.val.name), expr_desc(arenas, v.val.ty)),
        ConstantInfo::Axiom(v) => format!("Axiom name={} ty={}", nm(v.val.name), expr_desc(arenas, v.val.ty)),
        _ => "other".to_string(),
    }
}

fn expr_desc(arenas: &olean::value::Arenas, e: Expr) -> String {
    let nm = |n: Name| arenas.names.to_string_plain(n);
    match arenas.exprs.node(e) {
        ExprNode::Sort(l) => format!("sort({:?})", l),
        ExprNode::Const(n, us) => format!("const({}, {:?})", nm(n), arenas.exprs.level_list(us).len()),
        ExprNode::ForallE(n, t, b, _) => format!("∀({} : {}, {})", nm(n), expr_desc(arenas, Expr(t)), expr_desc(arenas, Expr(b))),
        ExprNode::Lam(n, t, b, _) => format!("λ({} : {}, {})", nm(n), expr_desc(arenas, Expr(t)), expr_desc(arenas, Expr(b))),
        ExprNode::App(f, a) => format!("({} {})", expr_desc(arenas, Expr(f)), expr_desc(arenas, Expr(a))),
        ExprNode::BVar(i) => format!("#{i}"),
        ExprNode::MData(_, e2) => format!("mdata({})", expr_desc(arenas, Expr(e2))),
        ExprNode::Proj(s, i, e2) => format!("proj({}, {i}, {})", nm(s), expr_desc(arenas, Expr(e2))),
        ExprNode::LetE(n, _, v, b, _) => format!("let {} := {} in {}", nm(n), expr_desc(arenas, Expr(v)), expr_desc(arenas, Expr(b))),
        ExprNode::FVar(n) => format!("fvar({})", nm(n)),
        ExprNode::MVar(n) => format!("mvar({})", nm(n)),
        ExprNode::Lit(l) => format!("lit({:?})", l),
    }
}
