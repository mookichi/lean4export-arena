//! Load the Mathlib environment and print the arena table sizes + RSS.
//! Usage: mem_breakdown <module> [--lean-path <root> ...]
use olean::export::load_env;

fn rss_mb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmRSS:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|v| v.parse::<u64>().ok())
        })
        .unwrap_or(0)
        / 1024
}

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let mut module = "Mathlib".to_string();
    let mut roots = Vec::new();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--lean-path" => {
                i += 1;
                roots.push(std::path::PathBuf::from(&args[i]));
            }
            _ if i == 1 => module = args[i].clone(),
            _ => return Err(format!("unknown arg {}", args[i])),
        }
        i += 1;
    }
    let start = std::time::Instant::now();
    let (_env, arenas) = load_env(&module, &roots)?;
    println!("loaded {} in {:?}", module, start.elapsed());
    println!("rss_total={}MB", rss_mb());
    println!(
        "env_exprs={} scratch_exprs={}",
        arenas.exprs.env_len(),
        arenas.exprs.len() - arenas.exprs.env_len()
    );
    println!(
        "level_lists={} lits={} kvs={}",
        arenas.exprs.level_list_count(),
        arenas.exprs.lit_count(),
        arenas.exprs.kv_count()
    );
    println!(
        "names={} levels={} strings={}",
        arenas.names.len(),
        arenas.levels.len(),
        arenas.names.str_count()
    );
    println!(
        "expr_node_bytes={}MB level_list_bytes={}MB lit_bytes={}MB kv_bytes={}MB",
        arenas.exprs.env_len() * std::mem::size_of::<olean::value::ExprNode>() / (1024 * 1024),
        arenas.exprs.level_list_count() * 16 / (1024 * 1024),
        arenas.exprs.lit_count() * 32 / (1024 * 1024),
        arenas.exprs.kv_count() * 24 / (1024 * 1024),
    );
    Ok(())
}
