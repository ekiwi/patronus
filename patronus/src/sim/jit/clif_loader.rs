// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use cranelift::codegen::ir::{self, UserExternalName, entities, function};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{self, Module};
use cranelift::prelude::*;
use rustc_hash::FxHashMap;
use std::path::Path;

const STUB_FUNCTION_NAME: &str = stringify!(noncolocated_rust_lib_call_stub);
const DUMMY_GV_STUB_NAME: &str = "GV_STUB";
const DUMMY_GV_STUB_VALUE: u8 = 0x0;
const LOAD_PATH_ENV_VAR: &str = "CLIF_DIRECTORY";

extern "C" fn noncolocated_rust_lib_call_stub() -> ! {
    eprintln!("enter unreachable rust lib call stub!");
    std::process::exit(1);
}

pub(super) struct LoadedFuncInfo {
    pub(super) id: module::FuncId,
    #[cfg(feature = "inline")]
    pub(super) content: function::Function,
}

pub(super) type SymTab = FxHashMap<String, LoadedFuncInfo>;

#[expect(dead_code)]
enum ClifProfile {
    Opt,
    UnOpt,
}

impl ClifProfile {
    fn extension_name(&self) -> &'static str {
        match self {
            Self::Opt => "opt.clif",
            Self::UnOpt => "unopt.clif",
        }
    }
}

#[derive(Clone)]
struct ParsedClifFunction {
    symbol: String,
    content: function::Function,
}

pub(crate) fn register_precompiled_clif_function(
    module: &mut JITModule,
    ctx: &mut codegen::Context,
) -> Option<SymTab> {
    let Ok(target_dir) = std::env::var(LOAD_PATH_ENV_VAR) else {
        eprintln!(
            "directory for precompiled clif files has not been specified, try set `{LOAD_PATH_ENV_VAR}` environment variable"
        );
        return None;
    };
    let parsed_functions =
        collect_clif_functions_with_profile(target_dir, ClifProfile::Opt).collect::<Vec<_>>();
    let loaded_functions = ParsedClifFunctionLoader::new(module, ctx, &parsed_functions).finalize();
    eprintln!(
        "{} clif functions compiled AOT were loaded",
        loaded_functions.len()
    );
    Some(loaded_functions)
}

pub(crate) fn register_symbol_lookup_fallback(builder: &mut JITBuilder) {
    builder.symbol_lookup_fn(Box::new(|name| {
        if name.starts_with(STUB_FUNCTION_NAME) {
            Some(noncolocated_rust_lib_call_stub as *const u8)
        } else if name.eq(DUMMY_GV_STUB_NAME) {
            Some(&DUMMY_GV_STUB_VALUE as *const u8)
        } else {
            None
        }
    }));
}

fn collect_clif_functions_with_profile(
    target_dir: impl AsRef<Path>,
    profile: ClifProfile,
) -> impl Iterator<Item = ParsedClifFunction> {
    let walker = walkdir::WalkDir::new(target_dir).into_iter();
    walker
        .filter_map(|e| e.ok())
        .filter_map(move |e| {
            let path = e.path().as_os_str().to_str()?;
            if try_extract_multi_extension::<2>(path)?.eq(profile.extension_name()) {
                Some(e)
            } else {
                None
            }
        })
        .flat_map(move |e| {
            let clif_ir_text =
                std::fs::read_to_string(e.path()).expect("fail to read clif ir file");
            let test = cranelift_reader::parse_test(
                &clif_ir_text,
                cranelift_reader::ParseOptions::default(),
            )
            .expect("fail to parse clif ir");
            test.functions
                .into_iter()
                .map(|(content, detail)| ParsedClifFunction {
                    content,
                    symbol: probe_function_symbol(&detail.comments)
                        .expect("function symbol not found")
                        .to_string(),
                })
                .collect::<Vec<_>>()
        })
}

fn probe_function_symbol<'a>(comments: &[cranelift_reader::Comment<'a>]) -> Option<&'a str> {
    let symbol = probe_comment_with_leading_token(
        comments,
        "symbol",
        Some(|entity| matches!(entity, entities::AnyEntity::Function)),
    );
    assert!(symbol.len() <= 1);
    symbol.into_iter().next()
}

fn probe_comment_with_leading_token<'a, F>(
    comments: &[cranelift_reader::Comment<'a>],
    token: &str,
    attached_entities_filter: Option<F>,
) -> Vec<&'a str>
where
    F: Fn(entities::AnyEntity) -> bool,
{
    comments
        .iter()
        .filter(|comment| {
            attached_entities_filter
                .as_ref()
                .is_none_or(|filter| filter(comment.entity))
        })
        .filter_map(|comment| {
            comment
                .text
                .find(token)
                .map(|idx| comment.text[idx + token.len()..].trim())
        })
        .collect()
}

fn try_extract_multi_extension<const N: usize>(path: &str) -> Option<&str> {
    path.rmatch_indices('.')
        .nth(N - 1)
        .map(|(idx, _)| &path[idx + 1..])
}

struct ParsedClifFunctionLoader<'a> {
    module: &'a mut JITModule,
    ctx: &'a mut codegen::Context,
    parsed_functions: &'a [ParsedClifFunction],
    user_ext_name_remap: FxHashMap<UserExternalName, UserExternalName>,
    dummy_gv_stub: UserExternalName,
}

impl<'a> ParsedClifFunctionLoader<'a> {
    fn new(
        module: &'a mut JITModule,
        ctx: &'a mut codegen::Context,
        parsed_functions: &'a [ParsedClifFunction],
    ) -> Self {
        let data_id = module
            .declare_data(DUMMY_GV_STUB_NAME, module::Linkage::Local, true, false)
            .expect("fail to declare data");
        Self {
            module,
            ctx,
            parsed_functions,
            user_ext_name_remap: FxHashMap::default(),
            dummy_gv_stub: UserExternalName {
                namespace: 1,
                index: data_id.as_u32(),
            },
        }
    }

    fn finalize(mut self) -> SymTab {
        let mut symtab = FxHashMap::default();
        let mut func_info: Vec<(String, module::FuncId)> = vec![];
        for ParsedClifFunction { symbol, content } in self.parsed_functions {
            // linkage type is marked as `Preemptible` for safety.
            // `Local` encourages JIT to use pc-relative call, which may not be feasible for large design.
            let func_id = self
                .module
                .declare_function(
                    symbol,
                    module::Linkage::Preemptible,
                    &content.stencil.signature,
                )
                .expect("fail to declare function");
            let original_user_ext_name = content
                .name
                .get_user()
                .expect("expect user function")
                .clone();
            func_info.push((symbol.clone(), func_id));
            self.register_ext_user_name_remap_info(
                original_user_ext_name,
                module::FuncOrDataId::Func(func_id),
            );
        }
        self.stub_rustc_lib_call();
        let fixed_functions: Vec<_> = self
            .parsed_functions
            .iter()
            .map(|parsed| {
                let mut function = parsed.content.clone();
                self.fixup_ext_data_ref(&mut function);
                function
            })
            .collect();

        for ((symbol, id), function) in func_info.into_iter().zip(fixed_functions) {
            symtab.insert(
                symbol,
                LoadedFuncInfo {
                    id,
                    #[cfg(feature = "inline")]
                    content: relax_ext_func_call_mode(function.clone()),
                },
            );
            self.ctx.func = function;
            self.module
                .define_function(id, self.ctx)
                .expect("fail to load parsed function");
            self.module.clear_context(self.ctx);
        }
        self.module
            .finalize_definitions()
            .expect("fail to finalize");
        symtab
    }

    /// HACK: cranelift internally maps a FuncId/DataId to ExtData by creating a UserExternalName with 0/1 namespace
    /// and index equals to FuncId/DataId
    /// For each parsed function, we try to remap the original `UserExternalName` to the corrected name in the current module
    fn register_ext_user_name_remap_info(
        &mut self,
        original_user_ext_name: UserExternalName,
        new_id: module::FuncOrDataId,
    ) {
        let (namespace, index) = match new_id {
            module::FuncOrDataId::Func(func_id) => (0, func_id.as_u32()),
            module::FuncOrDataId::Data(data_id) => (1, data_id.as_u32()),
        };
        self.user_ext_name_remap.insert(
            original_user_ext_name,
            UserExternalName { namespace, index },
        );
    }

    /// Redirect non-colocated function call, mainly the rustc panic runtime to a dummy stub function
    fn stub_rustc_lib_call(&mut self) {
        for ParsedClifFunction { content, .. } in self.parsed_functions {
            let noncolocated_ext_fn: Vec<(&UserExternalName, &ir::Signature)> = content
                .stencil
                .dfg
                .ext_funcs
                .values()
                .filter_map(|ext_data| {
                    if !ext_data.colocated
                        && let ir::ExternalName::User(name_ref) = ext_data.name
                    {
                        Some((
                            &content.params.user_named_funcs()[name_ref],
                            &content.stencil.dfg.signatures[ext_data.signature],
                        ))
                    } else {
                        None
                    }
                })
                .collect();
            for (ext_user_name, signature) in noncolocated_ext_fn {
                let canonical_symbol = format!("{STUB_FUNCTION_NAME}_{ext_user_name}");
                let func_id = self
                    .module
                    .declare_function(&canonical_symbol, module::Linkage::Local, signature)
                    .expect("fail to declare function");
                self.register_ext_user_name_remap_info(
                    ext_user_name.clone(),
                    module::FuncOrDataId::Func(func_id),
                );
            }
        }
    }

    /// Remap external reference, including function and data reference, in parsed clif function to references declared in current module.
    /// All references to external global variable (shown as `gv` in clif file) are redirected to a dummy address.
    /// We assume that all those references are not critical for function correctness and are mainly used for debugging/panic purposes.
    /// Therefore, they are unlikely to be accessed during JIT runtime.
    fn fixup_ext_data_ref(&mut self, function: &mut function::Function) {
        let legacy_user_named_funcs = function.params.user_named_funcs().clone();
        for (name_ref, original_user_ext_name) in legacy_user_named_funcs {
            function.params.reset_user_func_name(
                name_ref,
                self.user_ext_name_remap[&original_user_ext_name].clone(),
            );
        }
        if !function.stencil.global_values.is_empty() {
            let dummy_gv_ref = self
                .ctx
                .func
                .params
                .ensure_user_func_name(self.dummy_gv_stub.clone());
            for sym in function.stencil.global_values.values_mut() {
                if let ir::GlobalValueData::Symbol {
                    name: ir::ExternalName::User(name_ref),
                    colocated,
                    ..
                } = sym
                {
                    *name_ref = dummy_gv_ref;
                    *colocated = false;
                } else {
                    panic!("only support user external global value data");
                }
            }
        }
    }
}

#[cfg(feature = "inline")]
/// Downgrades pc relative call instruction to an absolute jump.
/// For large design, the compiled code size might grow out of the supported range of a pc relative jump,
/// which might cause problem when IR gets inlined.
fn relax_ext_func_call_mode(mut function: function::Function) -> function::Function {
    for ir::ExtFuncData { colocated, .. } in function.stencil.dfg.ext_funcs.values_mut() {
        *colocated = false;
    }
    function
}
