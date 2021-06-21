/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

An extremely bare-bones REPL for proving in Lean4.

Usage: `lean-gym <declName>` will load `Init` and start a proving environment for `declName`
which expects commands in the form of `<branchId> <tactic-string>`

It is straightforward to extend this to also take:
- module imports
- open declarations
- the current namespace

However, there is currently no way to import *until* a given declaration.
We also currently do no checking that the proof avoids circularity.

Note: unlike most RL environments, we use persistent datastructures and
so we store all active tactic states rather than relying on the user
to recompute each path on every action.

Example (circular) run of `lean-gym Nat.add_comm`:

{"state": "⊢ ∀ (n m : Nat), n + m = m + n",
 "proved": false,
 "error": null,
 "branchId": 0}

> 0 intros

{"state": "n✝ m✝ : Nat\n⊢ n✝ + m✝ = m✝ + n✝",
 "proved": false,
 "error": null,
 "branchId": 1}

> 1 rewrite [Nat.add_comm]

{"state": "n✝ m✝ : Nat\n⊢ m✝ + n✝ = m✝ + n✝",
 "proved": false,
 "error": null,
 "branchId": 2}

> 2 rfl

{"state": null, "proved": true, "error": null, "branchId": null}
-/
import Lean
import Std.Data.HashMap

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open Std (HashMap)

namespace Gym

abbrev BranchId : Type := Nat

structure Context where

structure State where
  branches : HashMap BranchId Tactic.SavedState := {}
  nextId   : BranchId := 0

abbrev GymM := ReaderT Context (StateRefT State TermElabM)

structure Problem where
  decl          : Name
  -- TODO: parse these from command-line
  imports       : List Import   := [{ module := `Init : Import }]
  openDecls     : List OpenDecl := []
  currNamespace : Name          := Name.anonymous

structure Response : Type where
  branchId : Option Nat    := none
  state    : Option String := none
  error    : Option String := none
  proved   : Bool          := false
  deriving ToJson

partial def replFor (problem : Problem) : IO Unit := do
  let termElabM : TermElabM Unit := do
    match (← getEnv).find? problem.decl with
    | none       => throwError "decl {problem.decl} not found"
    | some cInfo =>
      if ¬ (← isProp cInfo.type) then throwError "decl {problem.decl} not a theorem"
      let mvar ← mkFreshExprMVar (some cInfo.type) (kind := MetavarKind.natural)
      let termState : Term.SavedState ← Term.saveState
      let tacticState : Tactic.SavedState := { term := termState, tactic := ⟨[mvar.mvarId!]⟩ }
      let context := {}
      let state := { branches := HashMap.empty.insert 0 tacticState, nextId := 1 }
      (welcome *> repl).run context |>.run' state

  let metaM : MetaM Unit := termElabM.run'
  let coreM : CoreM Unit := metaM.run'

  let env ← importModules problem.imports {} 0
  let coreCtx   : Core.Context := { currNamespace := problem.currNamespace, openDecls := problem.openDecls }
  let coreState : Core.State := { env := env }

  let ((), _) ← coreM.toIO coreCtx coreState
  pure ()

where
  welcome : GymM Unit := do
    println! "{toJson (← responseForBranch 0)}"

  ppTacticState (s : Tactic.SavedState) : GymM Format := do
    let mut result : Format := Format.nil
    for goal in s.tactic.goals do
      result := result ++ (← Meta.ppGoal goal)
    return result

  responseForBranch (id : BranchId) : GymM Response := do
    let some savedState ← pure ((← get).branches.find? id) | throwError "invalid branch id: {id}"
    if savedState.tactic.goals.isEmpty then pure ({ proved := true } : Response)
    else pure { branchId := id, state := toString (← ppTacticState savedState) }

  repl : GymM Unit := do
    IO.print "> "
    let cmd : String ← (← IO.getStdin).getLine
    let response ← processCmd cmd
    println! "{toJson response}"
    repl

  processCmd (cmd : String) : GymM Response := do
    let pos := cmd.find (· == ' ')
    let id : Nat ← parseNat (cmd.toSubstring.take pos).toString
    let some savedState ←  pure ((← get).branches.find? id) | throwError "unknown 'id': {id}"
    let tacticString : String := cmd.toSubstring.drop (pos + 1) |>.toString
    match Parser.runParserCategory (← getEnv) `tactic tacticString "<stdin>" with
    | Except.error e => pure { error := some e }
    | Except.ok stx  => do
      savedState.term.restore
      let tac : TacticM Unit := set savedState.tactic *> evalTactic stx
      let mvarId : MVarId := savedState.tactic.goals.head!
      let unsolvedGoals ← Tactic.run mvarId tac
      let nextId := (← get).nextId
      let savedState : Tactic.SavedState := { term := (← Term.saveState), tactic := ⟨unsolvedGoals⟩ }
      modify fun s => { s with branches := s.branches.insert nextId savedState, nextId := nextId + 1 }
      responseForBranch nextId

  parseNat (s : String) : GymM Nat :=
    match s.toNat? with
    | some k => pure k
    | none   => throwError "String '{s}' cannot be converted to Nat"

end Gym

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous

def main (args : List String) : IO Unit := do
  let some LEAN_PATH ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH not set")
  initSearchPath LEAN_PATH
  let [decl] ← pure args | throw (IO.userError "usage: lean-gym <decl>")
  let problem : Gym.Problem := { decl := parseName decl }
  Gym.replFor problem
