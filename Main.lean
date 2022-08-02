import LeanGym

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let [decl] ← pure args | throw (IO.userError "usage: lean-gym <decl>")
  let decl := parseName decl
  let problem : Gym.Problem := { decl := decl, currNamespace := decl.getRoot }
  Gym.replFor problem
