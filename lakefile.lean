import Lake
open Lake DSL

package Timelib

@[defaultTarget]
lean_lib Timelib

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

--require mathlib from ".."/"Mathlib4"
