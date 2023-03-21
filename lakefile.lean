import Lake

open Lake DSL

package Gym

@[default_target]
lean_lib Gym

@[default_target]
lean_exe repl where
  root := `Gym.REPL

require std from git "https://github.com/leanprover/std4" @ "main"