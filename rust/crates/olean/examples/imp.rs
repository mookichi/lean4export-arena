use olean::OLean;
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let bytes = std::fs::read(&args[1]).unwrap();
    let olean = OLean::parse(&bytes).unwrap();
    let dm = olean.decode().unwrap();
    for i in &dm.data.imports {
        println!("{} importAll={}", dm.arenas.names.to_string_plain(i.module), i.import_all);
    }
}
