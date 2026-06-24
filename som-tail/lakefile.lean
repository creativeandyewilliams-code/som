import Lake
open Lake DSL

package «som-tail» where
  name := "som-tail"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib «SomTail» where
