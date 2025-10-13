//! Codegen for the `wincode` crate.
use std::{
    env,
    fs::File,
    io::{BufWriter, Error, Result},
    path::{Path, PathBuf},
};

mod tuple;

/// Generate tuple implementations for `SchemaWrite` and `SchemaRead`.
fn generate_tuples(out_dir: &Path) -> Result<()> {
    let out_file = File::create(out_dir.join("tuples.rs"))?;
    let mut out = BufWriter::new(out_file);
    tuple::generate(16, &mut out)
}

pub(crate) fn generate() -> Result<()> {
    let out_dir =
        PathBuf::from(env::var_os("OUT_DIR").ok_or_else(|| Error::other("OUT_DIR not set"))?);

    generate_tuples(&out_dir)?;
    Ok(())
}
