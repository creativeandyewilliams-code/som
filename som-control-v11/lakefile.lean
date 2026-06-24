import Lake
open Lake DSL

package «som-control-v11» where
  name := "som-control-v11"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib «SomControlV11» where
