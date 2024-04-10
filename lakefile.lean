import Lake
open Lake DSL

package Timelib where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  moreServerOptions :=#[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Timelib

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

-- @ 58f072
--require mathlib from ".."/"Mathlib4"
