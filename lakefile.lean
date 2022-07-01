import Lake
open Lake DSL

package Timelib where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
  
@[defaultTarget]
lean_lib Timelib

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"58f072fdbfd5dd77c98d8393a489ed3eff383ac8"

-- @ 58f072
--require mathlib from ".."/"Mathlib4"
