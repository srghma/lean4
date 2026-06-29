#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(
    unused_variables,
    unused_assignments,
    unused_parens,
    unused_mut,
    unused_imports
)]

pub use gen_init::r#gen::Init;
pub use gen_lean::r#gen::Lean;
pub use gen_std::r#gen::Std;
pub mod Lake {
    pub mod index {
        include!("gen/Lake.rs");
    }
    pub use index::*;
    pub mod Build {
        pub mod index {
            include!("gen/Lake/Build.rs");
        }
        pub use index::*;
        pub mod Actions {
            include!("gen/Lake/Build/Actions.rs");
        }
        pub mod Common {
            include!("gen/Lake/Build/Common.rs");
        }
        pub mod Context {
            include!("gen/Lake/Build/Context.rs");
        }
        pub mod Data {
            include!("gen/Lake/Build/Data.rs");
        }
        pub mod Executable {
            include!("gen/Lake/Build/Executable.rs");
        }
        pub mod ExternLib {
            include!("gen/Lake/Build/ExternLib.rs");
        }
        pub mod Facets {
            include!("gen/Lake/Build/Facets.rs");
        }
        pub mod Fetch {
            include!("gen/Lake/Build/Fetch.rs");
        }
        pub mod Index {
            include!("gen/Lake/Build/Index.rs");
        }
        pub mod Info {
            include!("gen/Lake/Build/Info.rs");
        }
        pub mod Infos {
            include!("gen/Lake/Build/Infos.rs");
        }
        pub mod InitFacets {
            include!("gen/Lake/Build/InitFacets.rs");
        }
        pub mod InputFile {
            include!("gen/Lake/Build/InputFile.rs");
        }
        pub mod Job {
            pub mod index {
                include!("gen/Lake/Build/Job.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lake/Build/Job/Basic.rs");
            }
            pub mod Monad {
                include!("gen/Lake/Build/Job/Monad.rs");
            }
            pub mod Register {
                include!("gen/Lake/Build/Job/Register.rs");
            }
        }
        pub mod Key {
            include!("gen/Lake/Build/Key.rs");
        }
        pub mod Library {
            include!("gen/Lake/Build/Library.rs");
        }
        pub mod Module {
            include!("gen/Lake/Build/Module.rs");
        }
        pub mod ModuleArtifacts {
            include!("gen/Lake/Build/ModuleArtifacts.rs");
        }
        pub mod Package {
            include!("gen/Lake/Build/Package.rs");
        }
        pub mod Run {
            include!("gen/Lake/Build/Run.rs");
        }
        pub mod Store {
            include!("gen/Lake/Build/Store.rs");
        }
        pub mod Target {
            pub mod index {
                include!("gen/Lake/Build/Target.rs");
            }
            pub use index::*;
            pub mod Basic {
                include!("gen/Lake/Build/Target/Basic.rs");
            }
            pub mod Fetch {
                include!("gen/Lake/Build/Target/Fetch.rs");
            }
        }
        pub mod Targets {
            include!("gen/Lake/Build/Targets.rs");
        }
        pub mod Topological {
            include!("gen/Lake/Build/Topological.rs");
        }
        pub mod Trace {
            include!("gen/Lake/Build/Trace.rs");
        }
    }
    pub mod CLI {
        pub mod index {
            include!("gen/Lake/CLI.rs");
        }
        pub use index::*;
        pub mod Actions {
            include!("gen/Lake/CLI/Actions.rs");
        }
        pub mod Build {
            include!("gen/Lake/CLI/Build.rs");
        }
        pub mod BuiltinLint {
            include!("gen/Lake/CLI/BuiltinLint.rs");
        }
        pub mod Error {
            include!("gen/Lake/CLI/Error.rs");
        }
        pub mod Help {
            include!("gen/Lake/CLI/Help.rs");
        }
        pub mod Init {
            include!("gen/Lake/CLI/Init.rs");
        }
        pub mod Main {
            include!("gen/Lake/CLI/Main.rs");
        }
        pub mod Serve {
            include!("gen/Lake/CLI/Serve.rs");
        }
        pub mod Shake {
            include!("gen/Lake/CLI/Shake.rs");
        }
        pub mod Translate {
            pub mod index {
                include!("gen/Lake/CLI/Translate.rs");
            }
            pub use index::*;
            pub mod Lean {
                include!("gen/Lake/CLI/Translate/Lean.rs");
            }
            pub mod Toml {
                include!("gen/Lake/CLI/Translate/Toml.rs");
            }
        }
    }
    pub mod Config {
        pub mod index {
            include!("gen/Lake/Config.rs");
        }
        pub use index::*;
        pub mod Artifact {
            include!("gen/Lake/Config/Artifact.rs");
        }
        pub mod Cache {
            include!("gen/Lake/Config/Cache.rs");
        }
        pub mod ConfigDecl {
            include!("gen/Lake/Config/ConfigDecl.rs");
        }
        pub mod ConfigTarget {
            include!("gen/Lake/Config/ConfigTarget.rs");
        }
        pub mod Context {
            include!("gen/Lake/Config/Context.rs");
        }
        pub mod Defaults {
            include!("gen/Lake/Config/Defaults.rs");
        }
        pub mod Dependency {
            include!("gen/Lake/Config/Dependency.rs");
        }
        pub mod Dynlib {
            include!("gen/Lake/Config/Dynlib.rs");
        }
        pub mod Env {
            include!("gen/Lake/Config/Env.rs");
        }
        pub mod ExternLib {
            include!("gen/Lake/Config/ExternLib.rs");
        }
        pub mod ExternLibConfig {
            include!("gen/Lake/Config/ExternLibConfig.rs");
        }
        pub mod FacetConfig {
            include!("gen/Lake/Config/FacetConfig.rs");
        }
        pub mod Glob {
            include!("gen/Lake/Config/Glob.rs");
        }
        pub mod InputFile {
            include!("gen/Lake/Config/InputFile.rs");
        }
        pub mod InputFileConfig {
            include!("gen/Lake/Config/InputFileConfig.rs");
        }
        pub mod InstallPath {
            include!("gen/Lake/Config/InstallPath.rs");
        }
        pub mod Kinds {
            include!("gen/Lake/Config/Kinds.rs");
        }
        pub mod LakeConfig {
            include!("gen/Lake/Config/LakeConfig.rs");
        }
        pub mod LakefileConfig {
            include!("gen/Lake/Config/LakefileConfig.rs");
        }
        pub mod Lang {
            include!("gen/Lake/Config/Lang.rs");
        }
        pub mod LeanConfig {
            include!("gen/Lake/Config/LeanConfig.rs");
        }
        pub mod LeanExe {
            include!("gen/Lake/Config/LeanExe.rs");
        }
        pub mod LeanExeConfig {
            include!("gen/Lake/Config/LeanExeConfig.rs");
        }
        pub mod LeanLib {
            include!("gen/Lake/Config/LeanLib.rs");
        }
        pub mod LeanLibConfig {
            include!("gen/Lake/Config/LeanLibConfig.rs");
        }
        pub mod Meta {
            include!("gen/Lake/Config/Meta.rs");
        }
        pub mod MetaClasses {
            include!("gen/Lake/Config/MetaClasses.rs");
        }
        pub mod Module {
            include!("gen/Lake/Config/Module.rs");
        }
        pub mod Monad {
            include!("gen/Lake/Config/Monad.rs");
        }
        pub mod Opaque {
            include!("gen/Lake/Config/Opaque.rs");
        }
        pub mod OutFormat {
            include!("gen/Lake/Config/OutFormat.rs");
        }
        pub mod Package {
            include!("gen/Lake/Config/Package.rs");
        }
        pub mod PackageConfig {
            include!("gen/Lake/Config/PackageConfig.rs");
        }
        pub mod Pattern {
            include!("gen/Lake/Config/Pattern.rs");
        }
        pub mod Script {
            include!("gen/Lake/Config/Script.rs");
        }
        pub mod TargetConfig {
            include!("gen/Lake/Config/TargetConfig.rs");
        }
        pub mod Workspace {
            include!("gen/Lake/Config/Workspace.rs");
        }
        pub mod WorkspaceConfig {
            include!("gen/Lake/Config/WorkspaceConfig.rs");
        }
    }
    pub mod DSL {
        pub mod index {
            include!("gen/Lake/DSL.rs");
        }
        pub use index::*;
        pub mod Attributes {
            include!("gen/Lake/DSL/Attributes.rs");
        }
        pub mod AttributesCore {
            include!("gen/Lake/DSL/AttributesCore.rs");
        }
        pub mod Config {
            include!("gen/Lake/DSL/Config.rs");
        }
        pub mod DeclUtil {
            include!("gen/Lake/DSL/DeclUtil.rs");
        }
        pub mod Extensions {
            include!("gen/Lake/DSL/Extensions.rs");
        }
        pub mod Key {
            include!("gen/Lake/DSL/Key.rs");
        }
        pub mod Meta {
            include!("gen/Lake/DSL/Meta.rs");
        }
        pub mod Package {
            include!("gen/Lake/DSL/Package.rs");
        }
        pub mod Require {
            include!("gen/Lake/DSL/Require.rs");
        }
        pub mod Script {
            include!("gen/Lake/DSL/Script.rs");
        }
        pub mod Syntax {
            include!("gen/Lake/DSL/Syntax.rs");
        }
        pub mod Targets {
            include!("gen/Lake/DSL/Targets.rs");
        }
        pub mod VerLit {
            include!("gen/Lake/DSL/VerLit.rs");
        }
    }
    pub mod Load {
        pub mod index {
            include!("gen/Lake/Load.rs");
        }
        pub use index::*;
        pub mod Config {
            include!("gen/Lake/Load/Config.rs");
        }
        pub mod Lean {
            pub mod index {
                include!("gen/Lake/Load/Lean.rs");
            }
            pub use index::*;
            pub mod Elab {
                include!("gen/Lake/Load/Lean/Elab.rs");
            }
            pub mod Eval {
                include!("gen/Lake/Load/Lean/Eval.rs");
            }
        }
        pub mod Manifest {
            include!("gen/Lake/Load/Manifest.rs");
        }
        pub mod Materialize {
            include!("gen/Lake/Load/Materialize.rs");
        }
        pub mod Package {
            include!("gen/Lake/Load/Package.rs");
        }
        pub mod Resolve {
            include!("gen/Lake/Load/Resolve.rs");
        }
        pub mod Toml {
            include!("gen/Lake/Load/Toml.rs");
        }
        pub mod Workspace {
            include!("gen/Lake/Load/Workspace.rs");
        }
    }
    pub mod Reservoir {
        include!("gen/Lake/Reservoir.rs");
    }
    pub mod Toml {
        pub mod index {
            include!("gen/Lake/Toml.rs");
        }
        pub use index::*;
        pub mod Data {
            pub mod index {
                include!("gen/Lake/Toml/Data.rs");
            }
            pub use index::*;
            pub mod DateTime {
                include!("gen/Lake/Toml/Data/DateTime.rs");
            }
            pub mod Dict {
                include!("gen/Lake/Toml/Data/Dict.rs");
            }
            pub mod Value {
                include!("gen/Lake/Toml/Data/Value.rs");
            }
        }
        pub mod Decode {
            include!("gen/Lake/Toml/Decode.rs");
        }
        pub mod Elab {
            pub mod index {
                include!("gen/Lake/Toml/Elab.rs");
            }
            pub use index::*;
            pub mod Expression {
                include!("gen/Lake/Toml/Elab/Expression.rs");
            }
            pub mod Value {
                include!("gen/Lake/Toml/Elab/Value.rs");
            }
        }
        pub mod Encode {
            include!("gen/Lake/Toml/Encode.rs");
        }
        pub mod Grammar {
            include!("gen/Lake/Toml/Grammar.rs");
        }
        pub mod Load {
            include!("gen/Lake/Toml/Load.rs");
        }
        pub mod ParserUtil {
            include!("gen/Lake/Toml/ParserUtil.rs");
        }
    }
    pub mod Util {
        pub mod index {
            include!("gen/Lake/Util.rs");
        }
        pub use index::*;
        pub mod Binder {
            include!("gen/Lake/Util/Binder.rs");
        }
        pub mod Casing {
            include!("gen/Lake/Util/Casing.rs");
        }
        pub mod Cli {
            include!("gen/Lake/Util/Cli.rs");
        }
        pub mod Cycle {
            include!("gen/Lake/Util/Cycle.rs");
        }
        pub mod Date {
            include!("gen/Lake/Util/Date.rs");
        }
        pub mod EquipT {
            include!("gen/Lake/Util/EquipT.rs");
        }
        pub mod Error {
            include!("gen/Lake/Util/Error.rs");
        }
        pub mod EStateT {
            include!("gen/Lake/Util/EStateT.rs");
        }
        pub mod Exit {
            include!("gen/Lake/Util/Exit.rs");
        }
        pub mod Family {
            include!("gen/Lake/Util/Family.rs");
        }
        pub mod FilePath {
            include!("gen/Lake/Util/FilePath.rs");
        }
        pub mod Git {
            include!("gen/Lake/Util/Git.rs");
        }
        pub mod IO {
            include!("gen/Lake/Util/IO.rs");
        }
        pub mod JsonObject {
            include!("gen/Lake/Util/JsonObject.rs");
        }
        pub mod Lift {
            include!("gen/Lake/Util/Lift.rs");
        }
        pub mod Lock {
            include!("gen/Lake/Util/Lock.rs");
        }
        pub mod Log {
            include!("gen/Lake/Util/Log.rs");
        }
        pub mod MainM {
            include!("gen/Lake/Util/MainM.rs");
        }
        pub mod Message {
            include!("gen/Lake/Util/Message.rs");
        }
        pub mod Name {
            include!("gen/Lake/Util/Name.rs");
        }
        pub mod NativeLib {
            include!("gen/Lake/Util/NativeLib.rs");
        }
        pub mod Opaque {
            include!("gen/Lake/Util/Opaque.rs");
        }
        pub mod OpaqueType {
            include!("gen/Lake/Util/OpaqueType.rs");
        }
        pub mod OrderedTagAttribute {
            include!("gen/Lake/Util/OrderedTagAttribute.rs");
        }
        pub mod OrdHashSet {
            include!("gen/Lake/Util/OrdHashSet.rs");
        }
        pub mod Proc {
            include!("gen/Lake/Util/Proc.rs");
        }
        pub mod RBArray {
            include!("gen/Lake/Util/RBArray.rs");
        }
        pub mod Reservoir {
            include!("gen/Lake/Util/Reservoir.rs");
        }
        pub mod Store {
            include!("gen/Lake/Util/Store.rs");
        }
        pub mod StoreInsts {
            include!("gen/Lake/Util/StoreInsts.rs");
        }
        pub mod String {
            include!("gen/Lake/Util/String.rs");
        }
        pub mod Task {
            include!("gen/Lake/Util/Task.rs");
        }
        pub mod Url {
            include!("gen/Lake/Util/Url.rs");
        }
        pub mod Version {
            include!("gen/Lake/Util/Version.rs");
        }
    }
    pub mod Version {
        include!("gen/Lake/Version.rs");
    }
}
pub mod LakeMain {
    pub mod index {
        include!("gen/LakeMain.rs");
    }
    pub use index::*;
}
