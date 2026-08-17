//! `lean4export-rs` CLI.
//!
//! Phase 1: read a `.olean` file and dump the decoded `ModuleData` summary
//! so it can be cross-checked against Lean's own `readModuleData`.

use std::process::ExitCode;

use olean::value::{Arenas, DataValue, Expr, Name};
use olean::OLean;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: lean4export-rs <module.olean> [--full] [--names] [--constnames]");
        eprintln!("       lean4export-rs --export <module> [--export-mdata] [--export-unsafe] [--lean-path <dir>]");
        eprintln!("                       [--only <name> ...] [--only-prefix <prefix> ...] [--limit <N>]");
        return ExitCode::from(2);
    }
    let export_mode = args.iter().any(|a| a == "--export");

    // Decode on a thread with a large stack: deeply nested expressions
    // (thousands of binders) recurse deeply in the decoder.
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            if export_mode {
                run_export(&args)
            } else {
                run_inspect(&args)
            }
        })
        .expect("spawn decoder thread");
    match handle.join() {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(msg)) => {
            eprintln!("error: {msg}");
            ExitCode::from(1)
        }
        Err(_) => {
            eprintln!("error: decoder thread panicked");
            ExitCode::from(1)
        }
    }
}

/// `--export <module>`: load the module's environment and render NDJSON.
fn run_export(args: &[String]) -> Result<(), String> {
    let i = args.iter().position(|a| a == "--export").unwrap();
    let module = args.get(i + 1).ok_or("--export requires a module name")?;
    let export_mdata = args.iter().any(|a| a == "--export-mdata");
    let export_unsafe = args.iter().any(|a| a == "--export-unsafe");

    // `--limit <N>`: stop after N non-internal constants (debugging).
    let limit: Option<usize> = args
        .iter()
        .position(|a| a == "--limit")
        .and_then(|j| args.get(j + 1))
        .and_then(|s| s.parse::<usize>().ok());

    // `--only <name> [--only <name> ...]`: dump only these constants
    // (matching `Main.lean`'s explicit-constant mode). Names are parsed as
    // component lists and interned after the environment is loaded.
    let only_parts: Vec<Vec<String>> = {
        let mut v = Vec::new();
        let mut j = 0;
        while j < args.len() {
            if args[j] == "--only" {
                if let Some(s) = args.get(j + 1) {
                    v.push(parse_name_arg(s)?);
                    j += 2;
                    continue;
                }
            }
            j += 1;
        }
        v
    };

    // `--only-prefix <prefix> [--only-prefix <prefix> ...]`: dump every
    // constant whose `to_lean_string` name starts with the prefix (e.g.
    // `--only-prefix Nat.` selects all `Nat.*` constants). Combined with
    // `--only`, both selections are unioned.
    let only_prefixes: Vec<String> = {
        let mut v = Vec::new();
        let mut j = 0;
        while j < args.len() {
            if args[j] == "--only-prefix" {
                if let Some(s) = args.get(j + 1) {
                    v.push(s.clone());
                    j += 2;
                    continue;
                }
            }
            j += 1;
        }
        v
    };

    let mut roots: Vec<std::path::PathBuf> = Vec::new();
    let mut j = 0;
    while j < args.len() {
        if args[j] == "--lean-path" {
            if let Some(dir) = args.get(j + 1) {
                roots.push(std::path::PathBuf::from(dir));
                j += 2;
                continue;
            }
        }
        j += 1;
    }
    // Default roots: the project's lake build dir, then the toolchain lib.
    roots.push(std::path::PathBuf::from(".lake/build/lib/lean"));
    if let Ok(sysroot) = std::env::var("LEAN_SYSROOT") {
        roots.push(std::path::PathBuf::from(sysroot).join("lib/lean"));
    } else if let Some(prefix) = lean_prefix() {
        roots.push(prefix.join("lib/lean"));
    }

    let t0 = std::time::Instant::now();
    let (env, mut arenas) = olean::export::load_env(module, &roots)?;
    eprintln!(
        "loaded env: {} constants, {} expr nodes in {:?}",
        env.constants.len(),
        arenas.exprs.env_len(),
        t0.elapsed()
    );
    let opts = olean::export::ExportOptions {
        export_mdata,
        export_unsafe,
    };
    let only: Option<Vec<Name>> = if only_parts.is_empty() && only_prefixes.is_empty() {
        None
    } else {
        let mut names: Vec<Name> = only_parts
            .iter()
            .map(|parts| {
                let parts: Vec<&str> = parts.iter().map(|s| s.as_str()).collect();
                arenas.names.intern_path(&parts)
            })
            .collect();
        if !only_prefixes.is_empty() {
            for (n, _) in &env.constants {
                // Skip internal names (`_...`, numerals) just like the
                // full-export path: `--only-prefix Nat.` should select the
                // public `Nat.*` constants, not Lean's internal
                // `Nat.add._unsafe_rec`/`Nat._sunfold` machinery (which
                // nanoda rejects as partial/unsafe definitions).
                if arenas.names.is_internal(*n) {
                    continue;
                }
                let s = arenas.names.to_lean_string(*n);
                if only_prefixes.iter().any(|p| s.starts_with(p)) {
                    names.push(*n);
                }
            }
        }
        Some(names)
    };
    let only = only.as_deref();
    let mut out = std::io::BufWriter::new(std::io::stdout());
    {
        let mut exporter = olean::export::Exporter::new(&env, &mut arenas, opts, &mut out);
        exporter.export_all("4.30.0", "d024af099ca4bf2c86f649261ebf59565dc8c622", only, limit)?;
    }
    eprintln!("export done in {:?}", t0.elapsed());
    use std::io::Write;
    out.flush().map_err(|e| e.to_string())
}

/// Parse a dotted name argument like `Phase0Test.Even` into its components.
fn parse_name_arg(s: &str) -> Result<Vec<String>, String> {
    let parts: Vec<String> = s
        .split('.')
        .filter(|p| !p.is_empty())
        .map(|p| p.to_string())
        .collect();
    if parts.is_empty() {
        return Err(format!("empty name argument: {s}"));
    }
    Ok(parts)
}

/// `lean --print-prefix`, for finding the toolchain lib dir.
fn lean_prefix() -> Option<std::path::PathBuf> {
    let out = std::process::Command::new("lean")
        .arg("--print-prefix")
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?;
    Some(std::path::PathBuf::from(s.trim()))
}

fn run_inspect(args: &[String]) -> Result<(), String> {
    let path = args[1].clone();
    let full = args.iter().any(|a| a == "--full");
    let names_only = args.iter().any(|a| a == "--names");
    let constnames_only = args.iter().any(|a| a == "--constnames");
    let walk_only = args.iter().any(|a| a == "--walk");
    let mdata_only = args.iter().any(|a| a == "--mdata");
    run(&path, full, names_only, constnames_only, walk_only, mdata_only)
}

fn run(path: &str, full: bool, names_only: bool, constnames_only: bool, walk_only: bool, mdata_only: bool) -> Result<(), String> {
    let bytes = std::fs::read(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    let olean = OLean::parse(&bytes).map_err(|e| format!("bad header: {e}"))?;

    println!("file:            {path}");
    println!("lean version:    {}", olean.header.lean_version);
    println!("githash:         {}", olean.header.githash);
    println!("base_addr:       {:#x}", olean.header.base_addr);
    println!("uses GMP mpz:    {}", olean.header.uses_gmp());

    if walk_only {
        let report = olean::region::walk(olean.region(), olean::region::WalkBudget::default())
            .map_err(|e| format!("walk failed: {e}"))?;
        println!("objects={} ctors={} arrays={} strings={} mpz={}", report.objects, report.ctors, report.arrays, report.strings, report.mpz);
        return Ok(());
    }

    let dm = olean.decode().map_err(|e| format!("decode failed: {e}"))?;
    let md = &dm.data;
    let arenas = &dm.arenas;

    if mdata_only {
        for c in &md.constants {
            let mut found = Vec::new();
            collect_mdata(arenas, c.ty_expr(), &mut found);
            if let Some(v) = c.value_expr() {
                collect_mdata(arenas, v, &mut found);
            }
            for (entries, _) in found {
                let mut items: Vec<(String, String)> = entries
                    .iter()
                    .map(|(k, v)| (arenas.names.to_string_plain(*k), v.repr_str(arenas)))
                    .collect();
                items.sort();
                let json = items
                    .iter()
                    .map(|(k, v)| format!("\"{k}\":\"{v}\""))
                    .collect::<Vec<_>>()
                    .join(",");
                println!("{} | {{{json}}}", arenas.names.to_string_plain(c.name()));
            }
        }
        return Ok(());
    }

    if names_only {
        for c in &md.constants {
            println!("{}", arenas.names.to_string_plain(c.name()));
        }
        return Ok(());
    }
    if constnames_only {
        for &n in &md.const_names {
            println!("{}", arenas.names.to_string_plain(n));
        }
        return Ok(());
    }

    println!("isModule:        {}", md.is_module);
    println!("imports:         {}", md.imports.len());
    for imp in &md.imports {
        println!(
            "  {} (importAll={})",
            arenas.names.to_string_plain(imp.module),
            imp.import_all
        );
    }
    println!("constNames:      {}", md.const_names.len());
    println!("constants:       {}", md.constants.len());
    println!("extraConstNames: {}", md.extra_const_names.len());
    println!("entries:         {}", md.entries.len());

    if full {
        for c in &md.constants {
            println!("  {:?}", c);
        }
    } else {
        println!("constants (first 200):");
        for (i, c) in md.constants.iter().enumerate() {
            if i >= 200 {
                println!("  ... and {} more", md.constants.len() - 200);
                break;
            }
            println!("  {}", arenas.names.to_string_plain(c.name()));
        }
    }
    Ok(())
}

fn collect_mdata<'a>(
    arenas: &'a Arenas,
    e: Expr,
    out: &mut Vec<(&'a [(Name, DataValue)], Expr)>,
) {
    use olean::value::ExprNode;
    match arenas.exprs.node(e) {
        ExprNode::MData(kv, inner) => {
            out.push((arenas.exprs.kv(kv), Expr(inner)));
            collect_mdata(arenas, Expr(inner), out);
        }
        ExprNode::App(f, a) => {
            collect_mdata(arenas, Expr(f), out);
            collect_mdata(arenas, Expr(a), out);
        }
        ExprNode::Lam(_, t, b, _) => {
            collect_mdata(arenas, Expr(t), out);
            collect_mdata(arenas, Expr(b), out);
        }
        ExprNode::ForallE(_, t, b, _) => {
            collect_mdata(arenas, Expr(t), out);
            collect_mdata(arenas, Expr(b), out);
        }
        ExprNode::LetE(_, t, v, b, _) => {
            collect_mdata(arenas, Expr(t), out);
            collect_mdata(arenas, Expr(v), out);
            collect_mdata(arenas, Expr(b), out);
        }
        ExprNode::Proj(_, _, s) => collect_mdata(arenas, Expr(s), out),
        _ => {}
    }
}
