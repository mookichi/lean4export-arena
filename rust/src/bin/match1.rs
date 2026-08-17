use olean::value::Arenas;
use olean::OLean;
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
        if arenas.names.to_string_plain(c.name()).ends_with("match_1") {
            if let olean::value::ConstantInfo::Defn(v) = c {
                println!("DEF {} value =", arenas.names.to_string_plain(c.name()));
                println!("{}", arenas.expr_debug(v.value));
            }
        }
    }
}
