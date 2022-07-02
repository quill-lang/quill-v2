use std::{
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};

/// Automatically generate the automated test module.
pub fn main() {
    println!("cargo:rerun-if-changed=tests");
    let out_dir = std::env::var("OUT_DIR").unwrap();
    let destination = std::path::Path::new(&out_dir).join("tests.rs");
    let f = std::fs::File::create(&destination).unwrap();

    // Scan for every test.
    let f = &mut BufWriter::new(f);
    scan_dir(f, &PathBuf::from("tests/src"), &PathBuf::new());
}

fn scan_dir(f: &mut impl Write, root: &Path, suffix: &Path) {
    // Walk through the directory, adding tests as we go.
    for entry in std::fs::read_dir(root.join(suffix)).unwrap() {
        let entry = entry.unwrap();
        let ty = entry.file_type().unwrap();
        if ty.is_dir() {
            // Recurse to see if this directory contains a test module.
            scan_dir(f, root, &suffix.join(entry.file_name()));
        } else if ty.is_file() && entry.file_name().to_string_lossy().ends_with(".sexp") {
            // This should be turned into a unit test.
            let path = suffix
                .join(entry.file_name())
                .to_string_lossy()
                .replace('\\', "/");
            let name = path.replace('/', "_").replace(".sexp", "");
            write!(
                f,
                r#"
                    #[test]
                    fn {name}() {{
                        run_test("{path}");
                    }}
                    "#,
                name = name,
                path = path,
            )
            .unwrap();
        }
    }
}
