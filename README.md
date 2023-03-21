# lean-gym

## Usage

```lean
lake exe repl Nat.add_comm
```

will start a REPL, which you can interact with as in:

```lean
{"goals": ["⊢ ∀ (n m : Nat), n + m = m + n"], "errors": [], "branchId": 0}
> {"runTactic": [0, "intro n m"]}
{"goals": ["n m : Nat\n⊢ n + m = m + n"], "errors": [], "branchId": 1}
> {"runTactic": [1, "rw [Nat.add_comm]"]}
{"goals": [], "errors": [], "branchId": 2}
```
