use std::env;
use std::path::PathBuf;

fn main() {
    let bindings = bindgen::Builder::default()
        .header("managers_meta.h")
        .clang_args(["-I../../../../uapi/include/", "-I../../../include/"])
        .clang_args([
            "-DCONFIG_MAX_SHM_PER_TASK=1",
            "-DCONFIG_MAX_DEV_PER_TASK=1",
            "-DCONFIG_MAX_DMA_STREAMS_PER_TASK=1",
            "-DCONFIG_BUILD_TARGET_DEBUG=1",
        ])
        .use_core();

    let bindings = bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .derive_default(true)
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
