# lean-gym

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

```
{"goals": ["⊢ ∀ (n m : Nat), n + m = m + n"], "errors": [], "branchId": 0}
> {"runTactic": [0, "intro n m"]}
{"goals": ["n m : Nat\n⊢ n + m = m + n"], "errors": [], "branchId": 1}
> {"runTactic": [1, "rw [Nat.add_comm]"]}
{"goals": [], "errors": [], "branchId": 2}
```