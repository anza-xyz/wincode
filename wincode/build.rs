use std::io::Result;

mod codegen;

fn main() -> Result<()> {
    codegen::generate()?;

    println!("cargo:rerun-if-changed=codegen/mod.rs");
    println!("cargo:rerun-if-changed=codegen/tuple.rs");
    println!("cargo:rerun-if-changed=build.rs");
    Ok(())
}
