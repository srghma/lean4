#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]

pub mod leanh {
    pub use lean_runtime_common::leanh::*;
}

pub mod lean_imports_rs {
    pub use lean_runtime_common::lean_imports_rs::*;
}

pub mod r#gen {
    pub use lean_gen_init::r#gen::Init;
    pub use lean_gen_std::r#gen::Std;
    pub use lean_gen_lean::r#gen::Lean;
    pub mod Lake {
        pub mod index {
            include!("../../lean_runtime/src/gen/Lake.rs");
        }
        pub use index::*;
        pub mod Build {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/Build.rs");
            }
            pub use index::*;
            pub mod Actions {
                include!("../../lean_runtime/src/gen/Lake/Build/Actions.rs");
            }
            pub mod Common {
                include!("../../lean_runtime/src/gen/Lake/Build/Common.rs");
            }
            pub mod Context {
                include!("../../lean_runtime/src/gen/Lake/Build/Context.rs");
            }
            pub mod Data {
                include!("../../lean_runtime/src/gen/Lake/Build/Data.rs");
            }
            pub mod Executable {
                include!("../../lean_runtime/src/gen/Lake/Build/Executable.rs");
            }
            pub mod ExternLib {
                include!("../../lean_runtime/src/gen/Lake/Build/ExternLib.rs");
            }
            pub mod Facets {
                include!("../../lean_runtime/src/gen/Lake/Build/Facets.rs");
            }
            pub mod Fetch {
                include!("../../lean_runtime/src/gen/Lake/Build/Fetch.rs");
            }
            pub mod Index {
                include!("../../lean_runtime/src/gen/Lake/Build/Index.rs");
            }
            pub mod Info {
                include!("../../lean_runtime/src/gen/Lake/Build/Info.rs");
            }
            pub mod Infos {
                include!("../../lean_runtime/src/gen/Lake/Build/Infos.rs");
            }
            pub mod InitFacets {
                include!("../../lean_runtime/src/gen/Lake/Build/InitFacets.rs");
            }
            pub mod InputFile {
                include!("../../lean_runtime/src/gen/Lake/Build/InputFile.rs");
            }
            pub mod Job {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/Build/Job.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("../../lean_runtime/src/gen/Lake/Build/Job/Basic.rs");
                }
                pub mod Monad {
                    include!("../../lean_runtime/src/gen/Lake/Build/Job/Monad.rs");
                }
                pub mod Register {
                    include!("../../lean_runtime/src/gen/Lake/Build/Job/Register.rs");
                }
            }
            pub mod Key {
                include!("../../lean_runtime/src/gen/Lake/Build/Key.rs");
            }
            pub mod Library {
                include!("../../lean_runtime/src/gen/Lake/Build/Library.rs");
            }
            pub mod Module {
                include!("../../lean_runtime/src/gen/Lake/Build/Module.rs");
            }
            pub mod ModuleArtifacts {
                include!("../../lean_runtime/src/gen/Lake/Build/ModuleArtifacts.rs");
            }
            pub mod Package {
                include!("../../lean_runtime/src/gen/Lake/Build/Package.rs");
            }
            pub mod Run {
                include!("../../lean_runtime/src/gen/Lake/Build/Run.rs");
            }
            pub mod Store {
                include!("../../lean_runtime/src/gen/Lake/Build/Store.rs");
            }
            pub mod Target {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/Build/Target.rs");
                }
                pub use index::*;
                pub mod Basic {
                    include!("../../lean_runtime/src/gen/Lake/Build/Target/Basic.rs");
                }
                pub mod Fetch {
                    include!("../../lean_runtime/src/gen/Lake/Build/Target/Fetch.rs");
                }
            }
            pub mod Targets {
                include!("../../lean_runtime/src/gen/Lake/Build/Targets.rs");
            }
            pub mod Topological {
                include!("../../lean_runtime/src/gen/Lake/Build/Topological.rs");
            }
            pub mod Trace {
                include!("../../lean_runtime/src/gen/Lake/Build/Trace.rs");
            }
        }
        pub mod CLI {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/CLI.rs");
            }
            pub use index::*;
            pub mod Actions {
                include!("../../lean_runtime/src/gen/Lake/CLI/Actions.rs");
            }
            pub mod Build {
                include!("../../lean_runtime/src/gen/Lake/CLI/Build.rs");
            }
            pub mod BuiltinLint {
                include!("../../lean_runtime/src/gen/Lake/CLI/BuiltinLint.rs");
            }
            pub mod Error {
                include!("../../lean_runtime/src/gen/Lake/CLI/Error.rs");
            }
            pub mod Help {
                include!("../../lean_runtime/src/gen/Lake/CLI/Help.rs");
            }
            pub mod Init {
                include!("../../lean_runtime/src/gen/Lake/CLI/Init.rs");
            }
            pub mod Main {
                include!("../../lean_runtime/src/gen/Lake/CLI/Main.rs");
            }
            pub mod Serve {
                include!("../../lean_runtime/src/gen/Lake/CLI/Serve.rs");
            }
            pub mod Shake {
                include!("../../lean_runtime/src/gen/Lake/CLI/Shake.rs");
            }
            pub mod Translate {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/CLI/Translate.rs");
                }
                pub use index::*;
                pub mod Lean {
                    include!("../../lean_runtime/src/gen/Lake/CLI/Translate/Lean.rs");
                }
                pub mod Toml {
                    include!("../../lean_runtime/src/gen/Lake/CLI/Translate/Toml.rs");
                }
            }
        }
        pub mod Config {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/Config.rs");
            }
            pub use index::*;
            pub mod Artifact {
                include!("../../lean_runtime/src/gen/Lake/Config/Artifact.rs");
            }
            pub mod Cache {
                include!("../../lean_runtime/src/gen/Lake/Config/Cache.rs");
            }
            pub mod ConfigDecl {
                include!("../../lean_runtime/src/gen/Lake/Config/ConfigDecl.rs");
            }
            pub mod ConfigTarget {
                include!("../../lean_runtime/src/gen/Lake/Config/ConfigTarget.rs");
            }
            pub mod Context {
                include!("../../lean_runtime/src/gen/Lake/Config/Context.rs");
            }
            pub mod Defaults {
                include!("../../lean_runtime/src/gen/Lake/Config/Defaults.rs");
            }
            pub mod Dependency {
                include!("../../lean_runtime/src/gen/Lake/Config/Dependency.rs");
            }
            pub mod Dynlib {
                include!("../../lean_runtime/src/gen/Lake/Config/Dynlib.rs");
            }
            pub mod Env {
                include!("../../lean_runtime/src/gen/Lake/Config/Env.rs");
            }
            pub mod ExternLib {
                include!("../../lean_runtime/src/gen/Lake/Config/ExternLib.rs");
            }
            pub mod ExternLibConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/ExternLibConfig.rs");
            }
            pub mod FacetConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/FacetConfig.rs");
            }
            pub mod Glob {
                include!("../../lean_runtime/src/gen/Lake/Config/Glob.rs");
            }
            pub mod InputFile {
                include!("../../lean_runtime/src/gen/Lake/Config/InputFile.rs");
            }
            pub mod InputFileConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/InputFileConfig.rs");
            }
            pub mod InstallPath {
                include!("../../lean_runtime/src/gen/Lake/Config/InstallPath.rs");
            }
            pub mod Kinds {
                include!("../../lean_runtime/src/gen/Lake/Config/Kinds.rs");
            }
            pub mod LakeConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/LakeConfig.rs");
            }
            pub mod LakefileConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/LakefileConfig.rs");
            }
            pub mod Lang {
                include!("../../lean_runtime/src/gen/Lake/Config/Lang.rs");
            }
            pub mod LeanConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/LeanConfig.rs");
            }
            pub mod LeanExe {
                include!("../../lean_runtime/src/gen/Lake/Config/LeanExe.rs");
            }
            pub mod LeanExeConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/LeanExeConfig.rs");
            }
            pub mod LeanLib {
                include!("../../lean_runtime/src/gen/Lake/Config/LeanLib.rs");
            }
            pub mod LeanLibConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/LeanLibConfig.rs");
            }
            pub mod Meta {
                include!("../../lean_runtime/src/gen/Lake/Config/Meta.rs");
            }
            pub mod MetaClasses {
                include!("../../lean_runtime/src/gen/Lake/Config/MetaClasses.rs");
            }
            pub mod Module {
                include!("../../lean_runtime/src/gen/Lake/Config/Module.rs");
            }
            pub mod Monad {
                include!("../../lean_runtime/src/gen/Lake/Config/Monad.rs");
            }
            pub mod Opaque {
                include!("../../lean_runtime/src/gen/Lake/Config/Opaque.rs");
            }
            pub mod OutFormat {
                include!("../../lean_runtime/src/gen/Lake/Config/OutFormat.rs");
            }
            pub mod Package {
                include!("../../lean_runtime/src/gen/Lake/Config/Package.rs");
            }
            pub mod PackageConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/PackageConfig.rs");
            }
            pub mod Pattern {
                include!("../../lean_runtime/src/gen/Lake/Config/Pattern.rs");
            }
            pub mod Script {
                include!("../../lean_runtime/src/gen/Lake/Config/Script.rs");
            }
            pub mod TargetConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/TargetConfig.rs");
            }
            pub mod Workspace {
                include!("../../lean_runtime/src/gen/Lake/Config/Workspace.rs");
            }
            pub mod WorkspaceConfig {
                include!("../../lean_runtime/src/gen/Lake/Config/WorkspaceConfig.rs");
            }
        }
        pub mod DSL {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/DSL.rs");
            }
            pub use index::*;
            pub mod Attributes {
                include!("../../lean_runtime/src/gen/Lake/DSL/Attributes.rs");
            }
            pub mod AttributesCore {
                include!("../../lean_runtime/src/gen/Lake/DSL/AttributesCore.rs");
            }
            pub mod Config {
                include!("../../lean_runtime/src/gen/Lake/DSL/Config.rs");
            }
            pub mod DeclUtil {
                include!("../../lean_runtime/src/gen/Lake/DSL/DeclUtil.rs");
            }
            pub mod Extensions {
                include!("../../lean_runtime/src/gen/Lake/DSL/Extensions.rs");
            }
            pub mod Key {
                include!("../../lean_runtime/src/gen/Lake/DSL/Key.rs");
            }
            pub mod Meta {
                include!("../../lean_runtime/src/gen/Lake/DSL/Meta.rs");
            }
            pub mod Package {
                include!("../../lean_runtime/src/gen/Lake/DSL/Package.rs");
            }
            pub mod Require {
                include!("../../lean_runtime/src/gen/Lake/DSL/Require.rs");
            }
            pub mod Script {
                include!("../../lean_runtime/src/gen/Lake/DSL/Script.rs");
            }
            pub mod Syntax {
                include!("../../lean_runtime/src/gen/Lake/DSL/Syntax.rs");
            }
            pub mod Targets {
                include!("../../lean_runtime/src/gen/Lake/DSL/Targets.rs");
            }
            pub mod VerLit {
                include!("../../lean_runtime/src/gen/Lake/DSL/VerLit.rs");
            }
        }
        pub mod Load {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/Load.rs");
            }
            pub use index::*;
            pub mod Config {
                include!("../../lean_runtime/src/gen/Lake/Load/Config.rs");
            }
            pub mod Lean {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/Load/Lean.rs");
                }
                pub use index::*;
                pub mod Elab {
                    include!("../../lean_runtime/src/gen/Lake/Load/Lean/Elab.rs");
                }
                pub mod Eval {
                    include!("../../lean_runtime/src/gen/Lake/Load/Lean/Eval.rs");
                }
            }
            pub mod Manifest {
                include!("../../lean_runtime/src/gen/Lake/Load/Manifest.rs");
            }
            pub mod Materialize {
                include!("../../lean_runtime/src/gen/Lake/Load/Materialize.rs");
            }
            pub mod Package {
                include!("../../lean_runtime/src/gen/Lake/Load/Package.rs");
            }
            pub mod Resolve {
                include!("../../lean_runtime/src/gen/Lake/Load/Resolve.rs");
            }
            pub mod Toml {
                include!("../../lean_runtime/src/gen/Lake/Load/Toml.rs");
            }
            pub mod Workspace {
                include!("../../lean_runtime/src/gen/Lake/Load/Workspace.rs");
            }
        }
        pub mod Reservoir {
            include!("../../lean_runtime/src/gen/Lake/Reservoir.rs");
        }
        pub mod Toml {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/Toml.rs");
            }
            pub use index::*;
            pub mod Data {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Data.rs");
                }
                pub use index::*;
                pub mod DateTime {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Data/DateTime.rs");
                }
                pub mod Dict {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Data/Dict.rs");
                }
                pub mod Value {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Data/Value.rs");
                }
            }
            pub mod Decode {
                include!("../../lean_runtime/src/gen/Lake/Toml/Decode.rs");
            }
            pub mod Elab {
                pub mod index {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Elab.rs");
                }
                pub use index::*;
                pub mod Expression {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Elab/Expression.rs");
                }
                pub mod Value {
                    include!("../../lean_runtime/src/gen/Lake/Toml/Elab/Value.rs");
                }
            }
            pub mod Encode {
                include!("../../lean_runtime/src/gen/Lake/Toml/Encode.rs");
            }
            pub mod Grammar {
                include!("../../lean_runtime/src/gen/Lake/Toml/Grammar.rs");
            }
            pub mod Load {
                include!("../../lean_runtime/src/gen/Lake/Toml/Load.rs");
            }
            pub mod ParserUtil {
                include!("../../lean_runtime/src/gen/Lake/Toml/ParserUtil.rs");
            }
        }
        pub mod Util {
            pub mod index {
                include!("../../lean_runtime/src/gen/Lake/Util.rs");
            }
            pub use index::*;
            pub mod Binder {
                include!("../../lean_runtime/src/gen/Lake/Util/Binder.rs");
            }
            pub mod Casing {
                include!("../../lean_runtime/src/gen/Lake/Util/Casing.rs");
            }
            pub mod Cli {
                include!("../../lean_runtime/src/gen/Lake/Util/Cli.rs");
            }
            pub mod Cycle {
                include!("../../lean_runtime/src/gen/Lake/Util/Cycle.rs");
            }
            pub mod Date {
                include!("../../lean_runtime/src/gen/Lake/Util/Date.rs");
            }
            pub mod EquipT {
                include!("../../lean_runtime/src/gen/Lake/Util/EquipT.rs");
            }
            pub mod Error {
                include!("../../lean_runtime/src/gen/Lake/Util/Error.rs");
            }
            pub mod EStateT {
                include!("../../lean_runtime/src/gen/Lake/Util/EStateT.rs");
            }
            pub mod Exit {
                include!("../../lean_runtime/src/gen/Lake/Util/Exit.rs");
            }
            pub mod Family {
                include!("../../lean_runtime/src/gen/Lake/Util/Family.rs");
            }
            pub mod FilePath {
                include!("../../lean_runtime/src/gen/Lake/Util/FilePath.rs");
            }
            pub mod Git {
                include!("../../lean_runtime/src/gen/Lake/Util/Git.rs");
            }
            pub mod IO {
                include!("../../lean_runtime/src/gen/Lake/Util/IO.rs");
            }
            pub mod JsonObject {
                include!("../../lean_runtime/src/gen/Lake/Util/JsonObject.rs");
            }
            pub mod Lift {
                include!("../../lean_runtime/src/gen/Lake/Util/Lift.rs");
            }
            pub mod Lock {
                include!("../../lean_runtime/src/gen/Lake/Util/Lock.rs");
            }
            pub mod Log {
                include!("../../lean_runtime/src/gen/Lake/Util/Log.rs");
            }
            pub mod MainM {
                include!("../../lean_runtime/src/gen/Lake/Util/MainM.rs");
            }
            pub mod Message {
                include!("../../lean_runtime/src/gen/Lake/Util/Message.rs");
            }
            pub mod Name {
                include!("../../lean_runtime/src/gen/Lake/Util/Name.rs");
            }
            pub mod NativeLib {
                include!("../../lean_runtime/src/gen/Lake/Util/NativeLib.rs");
            }
            pub mod Opaque {
                include!("../../lean_runtime/src/gen/Lake/Util/Opaque.rs");
            }
            pub mod OpaqueType {
                include!("../../lean_runtime/src/gen/Lake/Util/OpaqueType.rs");
            }
            pub mod OrderedTagAttribute {
                include!("../../lean_runtime/src/gen/Lake/Util/OrderedTagAttribute.rs");
            }
            pub mod OrdHashSet {
                include!("../../lean_runtime/src/gen/Lake/Util/OrdHashSet.rs");
            }
            pub mod Proc {
                include!("../../lean_runtime/src/gen/Lake/Util/Proc.rs");
            }
            pub mod RBArray {
                include!("../../lean_runtime/src/gen/Lake/Util/RBArray.rs");
            }
            pub mod Reservoir {
                include!("../../lean_runtime/src/gen/Lake/Util/Reservoir.rs");
            }
            pub mod Store {
                include!("../../lean_runtime/src/gen/Lake/Util/Store.rs");
            }
            pub mod StoreInsts {
                include!("../../lean_runtime/src/gen/Lake/Util/StoreInsts.rs");
            }
            pub mod String {
                include!("../../lean_runtime/src/gen/Lake/Util/String.rs");
            }
            pub mod Task {
                include!("../../lean_runtime/src/gen/Lake/Util/Task.rs");
            }
            pub mod Url {
                include!("../../lean_runtime/src/gen/Lake/Util/Url.rs");
            }
            pub mod Version {
                include!("../../lean_runtime/src/gen/Lake/Util/Version.rs");
            }
        }
        pub mod Version {
            include!("../../lean_runtime/src/gen/Lake/Version.rs");
        }
    }
    pub mod LakeMain {
        include!("../../lean_runtime/src/gen/LakeMain.rs");
    }
}
