use std::env;
use std::path::Path;

fn main() {
    if env::var("CARGO_FEATURE_CBINDGEN").is_ok() {
        return;
    }
    let build_dir = env::var("OUT_DIR").expect("Target directory unspecified");
    let outdir = Path::new(&build_dir).join("../../uapi/");
    let config =
        cbindgen::Config::from_file("../../cbindgen_uapi.toml").expect("Configuration not found");
    if std::fs::create_dir_all(&outdir).is_err() {
        // path already exists, continue
    }
    cbindgen::Builder::new()
        .with_crate(".")
        .with_config(config)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(outdir.join("uapi.h"));
}
