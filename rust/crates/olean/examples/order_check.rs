// Print the export order of non-internal constants around index 5000.
use olean::export::load_env;
use olean::value::Name;

fn main() {
    let mut roots: Vec<std::path::PathBuf> = Vec::new();
    roots.push(std::path::PathBuf::from("/run/media/mookichi/ssd2/dev/lean4export/.lake/build/lib/lean"));
    if let Ok(sysroot) = std::env::var("LEAN_SYSROOT") {
        roots.push(std::path::PathBuf::from(sysroot).join("lib/lean"));
    }
    let (env, arenas) = load_env("Lean", &roots).expect("load");
    let names: Vec<Name> = env.constants.iter().map(|(n, _)| *n).collect();
    let nonint: Vec<(usize, Name)> = names
        .iter()
        .enumerate()
        .filter(|(_, n)| !arenas.names.is_internal(**n))
        .map(|(i, &n)| (i, n))
        .collect();
    for (i, (idx, n)) in nonint.iter().enumerate() {
        if (4990..5015).contains(&i) {
            println!("nonint#{} (raw_idx={}) {}", i, idx, arenas.names.to_lean_string(*n));
        }
    }
    println!("total non-internal: {}", nonint.len());
}
