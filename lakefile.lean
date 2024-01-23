import Lake
open Lake DSL

package Timelib where
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]

@[default_target]
lean_lib Timelib

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"9a07518812fc1acc04d6ec70762f63c58081906a"

-- @ 58f072
--require mathlib from ".."/"Mathlib4"
