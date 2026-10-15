# Lean formalization: event compression for vehicle scheduling on a line

This repository is the Lean 4 formalization accompanying the paper

> Bo Hu and Xiaoyu Liu. *An O(n log n) Algorithm for the Open Vehicle
> Scheduling Problem on a Line with Release Times, with a Machine-Checked
> Proof.* 2026.

A vehicle moves at unit speed on a line, starting at `s` at time `0`. Each
request at a real position must be visited no earlier than its release time.
The vehicle need not return. The objective is the earliest time by which
every request has been served. The development proves that the event-driven
algorithm of the paper returns this optimum for every input, that its main
loop halts within `8m + 10` iterations (`m` distinct request positions), and
that its loop costs `O(m log m)` in the standard cost model. These results
hold under every rule for breaking ties among queue minima.

Lean 4.34.0, Mathlib `v4.34.0`. 299 theorems, about 6,100 lines. The build has
no warnings, and every theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## Main theorems

| Theorem | File | Statement | Paper |
|---|---|---|---|
| `lineSolve_isLeast` | `ReleasePath/Line.lean` | `lineSolve reqs s` is the least finish time of a feasible plan | Theorem 1 |
| `lineSolve_iterations` | `ReleasePath/Line.lean` | the event loop halts within `8m + 10` iterations | Theorem 2 |
| `lineSolve_cost` | `ReleasePath/Line.lean` | the loop costs at most `(8m + 10)(1 + 3⌈log₂(m + 4)⌉)`, charging `⌈log₂(q + 1)⌉` per heap operation on a queue of `q` entries and the actual comparisons of each binary search | Theorem 2 |
| `lineSolve_anyTie` | `ReleasePath/AnyTie.lean` | for `m ≥ 2`, every run that extracts an arbitrary minimum entry in each iteration has at most `8m + 10` iterations, never gets stuck before halting, satisfies the same cost bound, and on halting holds `lineSolve reqs s` | Theorem 2 |

## What to read to check the statements

Only the definitions used in the statements need human review. The kernel
checks everything else.

* `ReleasePath/Routes.lean`, at the top: `Request`, `Plan`, `timedRoute`,
  `serves`, `feasible`. A plan is a list of timed visits followed by a
  terminal visit; consecutive visits must leave enough travel time (extra time
  is waiting); every request needs a visit at its position no earlier than its
  release.
* `ReleasePath/Line.lean`: `lineDist x y = |x - y|`; `LineFinishTimes reqs s`,
  the finish times of feasible plans on `ℝ` from `s` at time `0` that may end
  anywhere; `lineSolve`, the algorithm.
* `ReleasePath/AnyTie.lean` (for `lineSolve_anyTie` only): `AnyStep`,
  `AnyRun`, `haltCost`, read together with `popStep`, `Halts` and `Halted` in
  `ReleasePath/Machine.lean` and `ReleasePath/Correctness.lean`.

## Structure

`lineSolve` ranks the start and the request positions and calls `solve`
(`ReleasePath/Main.lean`), a state machine that follows Algorithm 1 of the
paper line by line: duplicate merging, the record scans, binary-search skips,
lazy deletion, and preinserted waiting entries. `solve` is proved correct in a
more general form, and `Line.lean` specializes it.

| File | Content |
|---|---|
| `Routes.lean` | plans, record chains, elimination, cutoff counting |
| `Exactness.lean` | local exactness (Lemma 5) |
| `Machine.lean`, `Effects.lean` | the queue machine and the effect of each operation |
| `Invariant.lean` | the rank-based invariant and its preservation (Definition 7, Lemma 9) |
| `Correctness.lean` | initialization and halting (Lemmas 8, 10) |
| `Termination.lean` | admissible keys and the potential (Section 9) |
| `Preprocess.lean`, `Main.lean` | preprocessing, `solve`, the general theorems |
| `Finite.lean` | the two-pointer cutoff table equals the cutoff used in the proof |
| `Cost.lean` | the cost model and the cost bound |
| `Line.lean` | the theorems for the model of the paper |
| `AnyTie.lean` | the theorems for every tie-breaking rule |

## Build and audit

```text
# requires elan (the Lean toolchain manager)
lake exe cache get                  # download the Mathlib build cache
lake build                          # build all modules
python tools/gen_audit.py           # write audit/AuditAll.lean
lake env lean audit/AuditAll.lean   # print the axioms of every theorem
```

`audit/audit_all.txt` is the output of the last step on our machine.

## Not formalized

* The correspondence between the Lean definitions and a Python reference
  implementation is by inspection.
* Heap operations are charged by the cost model, not verified against a heap
  implementation; building the initial queue (`O(m)`) is not counted.
* The equivalence of continuous trajectories with timed-visit plans is argued
  in Section 3 of the paper.

## License

Apache License 2.0, see `LICENSE`.
