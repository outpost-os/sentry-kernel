use std::env;
use std::path::PathBuf;

fn main() {
    let outdir_include = format!("-I{}/../../", env::var("OUT_DIR").unwrap());
    let outdir_uapi_include = format!("-I{}/../../uapi/", env::var("OUT_DIR").unwrap());
    let bindings = bindgen::Builder::default()
        .header("managers_meta.h")
        .clang_args([
            "-I../../../../uapi/include/",
            "-I../../../include/",
            outdir_include.as_str(),
            outdir_uapi_include.as_str(),
        ])
        .clang_args([
            "-DCONFIG_MAX_SHM_PER_TASK=1",
            "-DCONFIG_MAX_DEV_PER_TASK=1",
            "-DCONFIG_MAX_DMA_STREAMS_PER_TASK=1",
            "-DCONFIG_BUILD_TARGET_DEBUG=1",
            "-DCONFIG_NUM_MPU_REGIONS=8",
        ])
        .raw_line("use systypes::*;")
        .blocklist_type("([a-z]+h_t)")
        .blocklist_function("(strtod)")
        .blocklist_function("(strtold)")
        .blocklist_function("(qecvt)")
        .blocklist_function("(qfcvt)")
        .blocklist_function("(qgcvt)")
        .blocklist_function("(qecvt_r)")
        .blocklist_function("(qfcvt_r)")
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
