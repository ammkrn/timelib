import Lake
open Lake DSL

package Timelib where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  moreServerOptions :=#[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Timelib

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

-- @ 58f072
--require mathlib from ".."/"Mathlib4"
