
use std::{env::args, fs, io::Write};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

mod bstr;
use bstr::Bstr;

mod kernel;
mod fmt;
mod export;
mod doc;

#[cfg(test)]
mod tests_export;

use kernel::{Env, ErrorKind, verify, load_prelude};
use export::export_named;
use doc::doc_main;


// == Configuration and cache security ==

// CACHE_DIR should be collision free. Should not be a common
// name like "lib", ".lib", "theorems" or "proofs".
// CACHE_MARKER *must* be collision free.
const CACHE_DIR: &str = ".nd_cache"; 
const CACHE_MARKER: &str = ".nd_proof_checker_cache";
const MANIFEST_FILE: &str = "manifest.txt";


// == Manifest data structures and parser ==

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreludeConfig {
    Default,
    None,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Manifest {
    pub prelude: PreludeConfig,
    pub auto_rule: bool,
    pub modules: Vec<(String, Vec<String>)>,
}

impl Default for Manifest {
    fn default() -> Self {
        Self {
            prelude: PreludeConfig::Default,
            auto_rule: true,
            modules: Vec::new(),
        }
    }
}

fn parse_manifest(s: &str) -> Manifest {
    let mut clean = String::new();
    for line in s.lines() {
        let code = line.split('#').next().unwrap_or("");
        clean.push_str(code);
        clean.push('\n');
    }

    let mut manifest = Manifest::default();
    let mut rest = clean.as_str();

    while let Some(start) = rest.find(|c| c == '(' || c == '[') {
        let delimiter = rest.as_bytes()[start];
        let after_start = &rest[start + 1..];

        if delimiter == b'(' {
            // Module declaration: (Name), (Name:) oder (Name: Dep1 Dep2)
            if let Some(end) = after_start.find(')') {
                let inner = after_start[..end].trim();
                if !inner.is_empty() {
                    let (name, deps) = match inner.split_once(':') {
                        Some((name_part, deps_part)) => (
                            name_part.trim().to_string(),
                            deps_part
                                .split_whitespace()
                                .map(|d| d.to_string())
                                .collect(),
                        ),
                        None => (inner.to_string(), Vec::new()),
                    };
                    if !name.is_empty() {
                        manifest.modules.push((name, deps));
                    }
                }
                rest = &after_start[end + 1..];
            } else {
                break;
            }
        } else if delimiter == b'[' {
            // Configuration entry: [key = value]
            if let Some(end) = after_start.find(']') {
                let inner = after_start[..end].trim();
                if let Some((key_part, val_part)) = inner.split_once('=') {
                    let key = key_part.trim();
                    let val = val_part.trim();
                    match key {
                        "prelude" => {
                            if val == "none" {
                                manifest.prelude = PreludeConfig::None;
                            } else if val == "default" {
                                manifest.prelude = PreludeConfig::Default;
                            } else {
                                manifest.prelude = PreludeConfig::Custom(
                                    val.to_string());
                            }
                        }
                        "auto_rule" => {
                            if let Ok(b) = val.parse::<bool>() {
                                manifest.auto_rule = b;
                            }
                        }
                        _ => {}
                    }
                }
                rest = &after_start[end + 1..];
            } else {
                break;
            }
        }
    }

    manifest
}

fn load_manifest() -> Result<Option<Manifest>, String> {
    if !Path::new(MANIFEST_FILE).is_file() {
        return Ok(None);
    }
    match fs::read_to_string(MANIFEST_FILE) {
        Ok(content) => Ok(Some(parse_manifest(&content))),
        Err(e) => Err(format!("Could not read '{}': {}",
            MANIFEST_FILE, e)),
    }
}

fn manifest_not_found() {
    eprintln!("Error: '{}' not found in current directory.", MANIFEST_FILE);
}


// == Cache management and export ==

fn ensure_cache_dir() -> Result<(), String> {
    let dir = Path::new(CACHE_DIR);
    let marker = dir.join(CACHE_MARKER);
    if !dir.exists() {
        fs::create_dir_all(dir)
            .map_err(|e| format!("Could not create directory '{}': {}",
            CACHE_DIR, e))?;
        fs::write(&marker, b"nd cache directory\n")
            .map_err(|e| format!("Could not write marker: {}", e))?;
    } else if !marker.exists() {
        return Err(format!(
            "Directory '{}' exists but is missing marker '{}'. Refusing to touch it.",
            CACHE_DIR, CACHE_MARKER
        ));
    }
    Ok(())
}

fn clear_cache() -> ExitCode {
    let dir = Path::new(CACHE_DIR);
    if !dir.exists() {
        return ExitCode::SUCCESS;
    }
    let marker = dir.join(CACHE_MARKER);
    if !marker.exists() {
        eprintln!(
            "Safety error: '{}' exists but marker file '{}' is missing.\n\
             Aborting deletion to protect non-cache files.",
            CACHE_DIR, CACHE_MARKER
        );
        return ExitCode::FAILURE;
    }
    if let Err(e) = fs::remove_dir_all(dir) {
        eprintln!("Could not remove directory '{}': {}", CACHE_DIR, e);
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn export_all(modules: &[(String, Vec<String>)]) -> ExitCode {
    if let Err(e) = ensure_cache_dir() {
        eprintln!("{}", e);
        return ExitCode::FAILURE;
    }

    for (name, _) in modules {
        let in_file = format!("{}.txt", name);
        let src = match fs::read(&in_file) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("Could not read '{}': {}", in_file, e);
                return ExitCode::FAILURE;
            }
        };
        let exported = export_named(&src);
        let out_file = Path::new(CACHE_DIR).join(format!("{}.txt", name));
        if let Err(e) = fs::write(&out_file, &exported) {
            eprintln!("Could not write '{}': {}", out_file.display(), e);
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}

fn list_all(modules: &[(String, Vec<String>)]) -> ExitCode {
    for (idx, (name, _)) in modules.iter().enumerate() {
        let in_file = format!("{}.txt", name);
        let src = match fs::read(&in_file) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("Could not read '{}': {}", in_file, e);
                return ExitCode::FAILURE;
            }
        };
        let exported = export_named(&src);
        let mut stdout = std::io::stdout().lock();
        let _ = stdout.write_all(&exported);
        let _ = stdout.write_all(b"\n");
        if idx + 1 < modules.len() {
            let _ = stdout.write_all(b"\n");
        }
    }
    ExitCode::SUCCESS
}

fn write_atomic(path: &Path, content: &[u8]) -> Result<(), std::io::Error> {
    let file_name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("file.txt");

    // Create hidden temp file in the same directory to ensure it is
    // on the same filesystem
    let temp_path = path.with_file_name(format!(".{}.tmp.{}",
        file_name, std::process::id()));

    // Write content and flush to disk
    let write_result = (|| {
        let mut file = fs::File::create(&temp_path)?;
        file.write_all(content)?;
        file.sync_all()?;
        Ok(())
    })();

    if let Err(e) = write_result {
        let _ = fs::remove_file(&temp_path);
        return Err(e);
    }

    // Atomically replace destination (file handle must be closed
    // before rename, especially on Windows)
    if let Err(e) = fs::rename(&temp_path, path) {
        let _ = fs::remove_file(&temp_path);
        return Err(e);
    }

    Ok(())
}

fn format_module(
    input_arg: &str,
    manifest: &Manifest
) -> ExitCode {
    let input_path = Path::new(input_arg);

    // 1. Extension check: reject non-.txt files
    // (prevents tab-completion typos like main.rs)
    if let Some(ext) = input_path.extension() {
        if ext != "txt" {
            eprintln!(
                "Safety error: '{}' does not have a '.txt' extension.\n\
                 Formatting is restricted to proof files.",
                input_arg
            );
            return ExitCode::FAILURE;
        }
    }

    // 2. Extract module name
    let mod_name = match input_path.file_stem().and_then(|s| s.to_str()) {
        Some(name) => name,
        None => {
            eprintln!("Error: Invalid file name '{}'.", input_arg);
            return ExitCode::FAILURE;
        }
    };

    // 3. Manifest check: module must be registered
    let is_in_manifest = manifest.modules.iter().any(|(name, _)| name == mod_name)
        || matches!(&manifest.prelude, PreludeConfig::Custom(p) if p == mod_name);

    if !is_in_manifest {
        eprintln!(
            "Safety error: Module '{}' is not defined in '{}'.\n\
             Formatting is only permitted for registered modules.",
            mod_name, MANIFEST_FILE
        );
        return ExitCode::FAILURE;
    }

    // 4. Resolve actual input file path
    let target_in = if input_path.is_file() {
        input_path.to_path_buf()
    } else if input_path.with_extension("txt").is_file() {
        input_path.with_extension("txt")
    } else {
        eprintln!("Error: Could not find input file for module '{}'.", mod_name);
        return ExitCode::FAILURE;
    };

    // 5. Read, format, and write
    let src = match fs::read(&target_in) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("Could not read file '{}': {}", target_in.display(), e);
            return ExitCode::FAILURE;
        }
    };

    let formatted = fmt::format_source_code(&src);

    if let Err(e) = write_atomic(&target_in, &formatted) {
        eprintln!("Could not write to '{}': {}", target_in.display(), e);
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}


// == Verification and helper routines ==

fn verify_bytes(env: &mut Env, file_display: &str, s: &[u8]) -> Result<(), ()> {
    if let Err(e) = verify(env, s) {
        let kind = match e.kind {
            ErrorKind::Syntax => "Syntax",
            ErrorKind::Type => "Type",
            ErrorKind::Logic => "Logic",
        };
        println!("{} error in {}, line {}:\n{}", kind, file_display,
            e.line + 1, e.info);
        return Err(());
    }
    Ok(())
}

fn verify_file(env: &mut Env, path: &Path, is_dependency: bool) -> Result<(), ()> {
    let s = match fs::read(path) {
        Ok(v) => v,
        Err(e) => {
            if is_dependency {
                println!(
                    "Could not read dependency file '{}' ({}).\n\
                     Hint: Run 'nd -e' first to generate the library in '{}'.",
                    path.display(), e.kind(), CACHE_DIR
                );
            } else {
                println!("Could not read file {}, error kind: {}.",
                    path.display(), e.kind());
            }
            return Err(());
        }
    };
    verify_bytes(env, &path.display().to_string(), &s)
}

fn init_env(auto_rule: bool, prelude: &PreludeConfig) -> Result<Env, ()> {
    let mut env = Env::new();
    env.auto_rule = auto_rule;
    match prelude {
        PreludeConfig::Default => {
            load_prelude(&mut env);
        }
        PreludeConfig::None => {}
        PreludeConfig::Custom(mod_name) => {
            let file_name = format!("{}.txt", mod_name);
            let path = Path::new(&file_name);
            verify_file(&mut env, path, false)?;
        }
    }
    Ok(env)
}

fn run_doc(modules: &[(String, Vec<String>)]) -> ExitCode {
    let files: Vec<String> = modules.iter().map(|(m, _)|
        format!("{}.txt", m)).collect();
    let result = doc_main(&files);
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE
    }
}

fn print_help() {
    println!(
"The natural deduction proof checker (as of 4th Nov. 2026)

Usage:
  nd                         Verify all modules defined in manifest.txt
  nd <file> [...]            Verify one or more proof modules
  nd -e, --export            Export all theorems to ./{cache}/
  nd -c, --clear             Clear library cache in ./{cache}/

  nd -d, --dir <dir> [...]   Change working directory
  nd -f <input>              Format source code
  nd -p, --plain [...]       Verify without prelude       
  nd -m, --manual [...]      Verify without auto rule

  nd --doc                   Generate documentation
  nd -l, --list              Export all theorems to stdout
  nd -h, --help              Show this help text

Examples:
  nd                         Verify all modules in sequence
  nd proofs.txt              Verify proofs.txt (loading deps from ./{cache}/)
  nd -d ./tests              Verify modules in ./tests/
  nd -e                      Build the theorem cache",
        cache = CACHE_DIR);
}


// == Main function and CLI control ==

fn main() -> ExitCode {
    let argv: Vec<String> = args().collect();

    let mut work_dir: Option<PathBuf> = None;
    let mut do_export = false;
    let mut do_clear = false;
    let mut do_list = false;
    let mut do_doc = false;
    let mut do_help = false;
    let mut flag_plain = false;
    let mut flag_manual = false;
    let mut format_arg: Option<String> = None;
    let mut files = Vec::new();

    // 1. Parse command-line arguments
    let mut idx = 1;
    while idx < argv.len() {
        let arg = &argv[idx];
        match arg.as_str() {
            "-h" | "--help" => do_help = true,
            "-e" | "--export" => do_export = true,
            "-c" | "--clear" => do_clear = true,
            "-l" | "--list" => do_list = true,
            "-p" | "--plain" => flag_plain = true,
            "-m" | "--manual" => flag_manual = true,
            "--doc" => do_doc = true,
            "-d" | "--dir" => {
                idx += 1;
                if idx < argv.len() {
                    work_dir = Some(PathBuf::from(&argv[idx]));
                } else {
                    eprintln!("Error: -d / --dir requires a directory path.");
                    return ExitCode::FAILURE;
                }
            }
            "-f" => {
                idx += 1;
                if idx < argv.len() && !argv[idx].starts_with('-') {
                    let in_path = argv[idx].clone();
                    format_arg = Some(in_path);
                } else {
                    eprintln!("Error: -f requires an input file module.");
                    return ExitCode::FAILURE;
                }
            }
            _ => {
                if arg.starts_with('-') {
                    eprintln!("Unknown option '{}'. Use -h for help.", arg);
                    return ExitCode::FAILURE;
                }
                files.push(arg.clone());
            }
        }
        idx += 1;
    }

    if do_help {
        print_help();
        return ExitCode::SUCCESS;
    }

    // 2. Change working directory if specified
    if let Some(target_dir) = work_dir {
        if let Err(e) = std::env::set_current_dir(&target_dir) {
            eprintln!("Could not change directory to '{}': {}", target_dir.display(), e);
            return ExitCode::FAILURE;
        }
    }

    // 3. Clear cache (-c)
    if do_clear {
        if !files.is_empty() || format_arg.is_some() {
            eprintln!("Error: -c / --clear cannot be combined with file arguments or other actions.");
            return ExitCode::FAILURE;
        }
        return clear_cache();
    }

    // 4. Load manifest (if present)
    let manifest = match load_manifest() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::FAILURE;
        }
    };

    // Determine effective auto_rule and prelude settings
    // (CLI flags override manifest)
    let use_auto_rule = if flag_manual {
        false
    } else if let Some(ref m) = manifest {
        m.auto_rule
    } else {
        true
    };

    let prelude_config = if flag_plain {
        PreludeConfig::None
    } else if let Some(ref m) = manifest {
        m.prelude.clone()
    } else {
        PreludeConfig::Default
    };

    // 5. Formatting mode (-f)
    if let Some(in_file) = format_arg {
        if !files.is_empty() || do_export || do_list || do_doc {
            eprintln!("Error: -f cannot be combined with verification files or other actions.");
            return ExitCode::FAILURE;
        }
        let Some(ref m) = manifest else {
            eprintln!(
                "Safety error: '{}' not found in current directory.\n\
                 Formatting is restricted to modules defined in the manifest.",
                MANIFEST_FILE);
            return ExitCode::FAILURE;
        };
        return format_module(&in_file, m);
    }

    // 6. Batch actions (-e, -l, --doc)
    if do_export {
        let modules = match manifest {
            Some(ref m) => &m.modules,
            None => {
                manifest_not_found();
                return ExitCode::FAILURE;
            }
        };
        return export_all(modules);
    }

    if do_list {
        let modules = match manifest {
            Some(ref m) => &m.modules,
            None => {
                manifest_not_found();
                return ExitCode::FAILURE;
            }
        };
        return list_all(modules);
    }

    if do_doc {
        let modules = match manifest {
            Some(ref m) => &m.modules,
            None => {
                manifest_not_found();
                return ExitCode::FAILURE;
            }
        };
        return run_doc(modules);
    }

    // 7. Verification
    if !files.is_empty() {
        // Case 1: Files explicitly specified
        let manifest_map: Option<HashMap<String, Vec<String>>> = manifest
            .as_ref()
            .map(|m| m.modules.iter().cloned().collect());

        for file_arg in &files {
            let path = Path::new(file_arg);
            let mod_name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or(file_arg);

            // Determine target file path (e.g. "proofs" -> "proofs.txt")
            let target_path = if path.is_file() {
                path.to_path_buf()
            } else if path.with_extension("txt").is_file() {
                path.with_extension("txt")
            } else {
                path.to_path_buf()
            };

            // Each file receives a fresh Env with prelude
            let mut env = match init_env(use_auto_rule, &prelude_config) {
                Ok(env) => env,
                Err(()) => return ExitCode::FAILURE,
            };

            if let Some(ref map) = manifest_map {
                let deps = match map.get(mod_name) {
                    Some(deps) => deps,
                    None => {
                        eprintln!(
                            "Error: Module '{}' is not defined in {}.\n\
                             Please add it to the manifest or verify standalone without manifest.txt.",
                            mod_name, MANIFEST_FILE
                        );
                        return ExitCode::FAILURE;
                    }
                };

                // First load dependencies from cache
                for dep in deps {
                    let dep_file = Path::new(CACHE_DIR).join(format!("{}.txt", dep));
                    if verify_file(&mut env, &dep_file, true).is_err() {
                        return ExitCode::FAILURE;
                    }
                }
            }

            // Then check the actual module
            if verify_file(&mut env, &target_path, false).is_err() {
                return ExitCode::FAILURE;
            }
        }
    } else {
        // Case 2: No file specified
        match manifest {
            Some(ref m) => {
                // Check all modules in sequence in a SHARED Env
                let mut env = match init_env(use_auto_rule, &prelude_config) {
                    Ok(env) => env,
                    Err(()) => return ExitCode::FAILURE,
                };

                for (name, _) in &m.modules {
                    let file_name = format!("{}.txt", name);
                    let target_path = Path::new(&file_name);
                    if verify_file(&mut env, target_path, false).is_err() {
                        return ExitCode::FAILURE;
                    }
                }
            }
            None => {
                // No manifest and no arguments -> show help
                print_help();
                return ExitCode::SUCCESS;
            }
        }
    }

    ExitCode::SUCCESS
}
