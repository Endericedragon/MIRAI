// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// This provides an implementation for the "cargo mirai" subcommand.
// The mirai subcommand is the same as "cargo check" but with three differences:
// 1) It implicitly adds the options "--cfg mirai -Z always_encode_mir" to the rustc invocation.
// 2) It calls mirai rather than rustc for all the targets of the current package.
// 3) It runs cargo test --no-run for test targets.

// 可以运行`cargo metadata`看看里面的信息，很多东西在MIRAI的输出JSON里都能看到
use cargo_metadata::{Package, Target};
use std::ffi::OsString;
use std::ops::Index;
use std::path::Path;
use std::process::Command;

const CARGO_MIRAI_HELP: &str = r#"Static analysis tool for Rust programs

Usage:
    cargo mirai
"#;

pub fn main() {
    if std::env::args().any(|a| a == "--help" || a == "-h") {
        println!("{}", CARGO_MIRAI_HELP);
        return;
    }
    if std::env::args().any(|a| a == "--version" || a == "-V") {
        let version_info = rustc_tools_util::get_version_info!();
        println!("{version_info}");
        return;
    }
    // 注意nth(1)实际上是第二个，因为它是从0开始索引的
    match std::env::args().nth(1).as_ref().map(AsRef::<str>::as_ref) {
        Some(s) if s.ends_with("mirai") => {
            // Get here for the top level cargo execution, i.e. "cargo mirai".
            call_cargo();
        }
        Some(s) if s.ends_with("rustc") => {
            // 'cargo rustc ..' redirects here because RUSTC_WRAPPER points to this binary.
            // execute rustc with MIRAI applicable parameters for dependencies and call MIRAI
            // to analyze targets in the current package.
            call_rustc_or_mirai();
        }
        Some(arg) => {
            eprintln!(
                "`cargo-mirai` called with invalid first argument: {arg}; please only invoke this binary through `cargo mirai`"
            );
        }
        _ => {
            eprintln!(
                "`cargo-mirai` called without first argument; please only invoke this binary through `cargo mirai`"
            );
        }
    }
}

/// Read the toml associated with the current directory and
/// recursively execute cargo for each applicable package target/workspace member in the toml
fn call_cargo() {
    let manifest_path =
        get_arg_flag_value("--manifest-path").map(|m| Path::new(&m).canonicalize().unwrap());
    // cargo_metadata::MetadataCommand是一个专门执行cargo metadata的struct
    let mut cmd = cargo_metadata::MetadataCommand::new();
    if let Some(ref manifest_path) = manifest_path {
        // 给cmd实例设置Cargo.toml所在的路径，一会就逮着这个项目一通库库分析
        cmd.manifest_path(manifest_path);
    }

    let metadata = if let Ok(metadata) = cmd.exec() {
        metadata // 这东西的格式和cargo metadata的格式一样，只不过把JSON风格的键值对换成了rust struct风格的表示罢了
    } else {
        eprintln!("Could not obtain Cargo metadata; likely an ill-formed manifest");
        std::process::exit(1);
    };

    // 关于root package，可以参考rust语言圣经中的 https://course.rs/cargo/reference/workspaces.html
    // 简而言之，如果一个Package的Cargo.toml又包含[package]又包含[workspace]，那么它就是该workspace的root package。
    if let Some(root) = metadata.root_package() {
        call_cargo_on_each_package_target(root);
        return;
    }

    // There is no root, this must be a workspace, so call_cargo_on_each_package_target on each workspace member
    for package_id in &metadata.workspace_members {
        let package = metadata.index(package_id);
        call_cargo_on_each_package_target(package);
    }
}

/// 对Package中的每个target调用call_cargo_on_target
/// 若--lib被指定，则只对lib型的 target调用
/// 至于target长啥样，可以参考本仓库根目录的cargo_metadata.json
fn call_cargo_on_each_package_target(package: &Package) {
    let lib_only = get_arg_flag_presence("--lib");
    for target in &package.targets {
        let kind = target
            .kind
            .get(0)
            .expect("bad cargo metadata: target::kind");
        if lib_only && kind != "lib" {
            // 跳过非lib的目标，如果用户已经制定了--lib的话
            continue;
        }
        call_cargo_on_target(target, kind);
    }
}

fn call_cargo_on_target(target: &Target, kind: &str) {
    // Build a cargo command for target
    // 其实就是准备运行一次cargo xxx命令，先从环境变量中找，找不到就直接指定为cargo
    // 这样一来，就需要在环境变量Path中配置cargo的路径了
    let mut cmd =
        Command::new(std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")));
    // kind是字符串，可以取值"bin", "lib", "test", "bench"（应该是benchmark的缩写）等
    match kind {
        "bin" => {
            cmd.arg("check");
            // target都是有名字的，例如syn 1.0.109的name就是syn
            cmd.arg("--bin").arg(&target.name);
        }
        "lib" => {
            cmd.arg("check");
            cmd.arg("--lib");
        }
        "test" => {
            cmd.arg("test");
            cmd.arg("--test").arg(&target.name);
            // no-run = 编译完成后不要立即运行测试
            cmd.arg("--no-run");
        }
        _ => {
            return;
        }
    }

    // 跳过前两个，因为一般第一个是MIRAI自己，第二个刚才在main函数里以nth(1)的形式用过了
    let mut args = std::env::args().skip(2);
    // Add cargo args to cmd until first `--`.
    for arg in args.by_ref() {
        if arg == "--" {
            break;
        }
        if arg == "--lib" {
            continue;
        }
        cmd.arg(arg);
    }

    // Serialize the remaining args into an environment variable.
    let args_vec: Vec<String> = args.collect();
    let env_string_value_for_debug = serde_json::to_string(&args_vec).expect("failed to serialize args");
    // println!("MIRAI_FLAGS = {}", env_string_value_for_debug);
    if !args_vec.is_empty() {
        cmd.env(
            "MIRAI_FLAGS",
            env_string_value_for_debug,
        );
    }

    // Force cargo to recompile all dependencies with MIRAI friendly flags
    cmd.env("RUSTFLAGS", "--cfg mirai -Z always_encode_mir");

    // Replace the rustc executable through RUSTC_WRAPPER environment variable so that rustc
    // calls generated by cargo come back to cargo-mirai.
    // 就是当前进程的可执行文件的路径，例如D:\...\rust-pg.exe这种，当然在Linux底下肯定不会是exe啦
    let path = std::env::current_exe().expect("current executable path invalid");
    // 底下一大坨环境变量的值，马上就会在call_rustc_or_mirai里用上
    cmd.env("RUSTC_WRAPPER", path);

    // Communicate the name of the root crate to the calls to cargo-mirai that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("MIRAI_CRATE", target.name.replace('-', "_"));

    // Communicate the target kind of the root crate to the calls to cargo-mirai that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("MIRAI_KIND", kind);

    // Set the tool chain to be compatible with mirai
    if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }

    // Execute cmd
    let exit_status = cmd
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

/// 若当前命令行参数中包含了 `--crate-name` 和 `--crate-type`，且值与环境变量MIRAI_CRATE和MIRAI_KIND相匹配，
/// 则调用call_mirai；否则，若命令行参数不含--test，则调用rustc，否则啥也不干。
fn call_rustc_or_mirai() {
    if let Some(crate_name) = get_arg_flag_value("--crate-name") {
        if let Ok(mirai_crate) = std::env::var("MIRAI_CRATE") {
            if crate_name.eq(&mirai_crate) {
                if let Ok(kind) = std::env::var("MIRAI_KIND") {
                    if let Some(t) = get_arg_flag_value("--crate-type") {
                        if kind.eq(&t) {
                            call_mirai();
                            return;
                        }
                    }
                    if get_arg_flag_value("--test").is_some() {
                        call_mirai();
                        return;
                    }
                }
                return;
            }
        }
    }
    if get_arg_flag_value("--test").is_none() {
        call_rustc();
    }
}

/// 调用MIRAI。根据运行mirai --help的输出，这个mirai应该和main.rs里的内容有关，且Cargo.toml的内容也印证了这一点。
fn call_mirai() {
    let mut path = std::env::current_exe().expect("current executable path invalid");
    let extension = path.extension().map(|e| e.to_owned());
    // 前往path的父目录。如果path指向一个文件，则转而指向该文件所在的目录
    path.pop(); // remove the cargo_mirai bit
    path.push("mirai");
    if let Some(ext) = extension {
        // 看上去好像是为了支持Windows特意做的后缀适配，它温我哭
        path.set_extension(ext);
    }
    let mut cmd = Command::new(path);
    // 按照国际惯例，先跳过前两个
    cmd.args(std::env::args().skip(2));
    // 从这里开始，控制权就被交到了main.rs所编译获得的可执行文件mirai手中了
    let exit_status = cmd
        .spawn()
        .expect("could not run mirai")
        .wait()
        .expect("failed to wait for mirai");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

/// 看上去就是很正常地调用了rustc而已
fn call_rustc() {
    // todo: invoke the rust compiler for the appropriate tool chain?
    let mut cmd =
        Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc")));
    cmd.args(std::env::args().skip(2));
    let exit_status = cmd
        .spawn()
        .expect("could not run rustc")
        .wait()
        .expect("failed to wait for rustc");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

/// 检验输入的命令行参数中是否包含了 `--name`（其实是name，因为一般name自带"--"）
fn get_arg_flag_presence(name: &str) -> bool {
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return false,
        };
        if arg.starts_with(name) {
            return true;
        }
    }
}

/// 按照name，获取`--name value` 或 `--name=value` 中的value
fn get_arg_flag_value(name: &str) -> Option<String> {
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return None,
        };
        if !arg.starts_with(name) {
            continue;
        }
        // Strip `name`.
        let suffix = &arg[name.len()..];
        if suffix.is_empty() {
            // 形如 `--name value` 这样的参数
            // This argument is `name` and the next one is the value.
            return args.next();
        } else if let Some(arg_value) = suffix.strip_prefix('=') {
            // 形如 `--name=value` 这样的参数
            return Some(arg_value.to_owned());
        }
    }
}
