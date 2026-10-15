import ReleasePath.Line

/-!
# Arbitrary tie-breaking

`run` extracts the first minimum of the queue (`List.argmin`). Here every
iteration may extract *any* entry of minimum time, as a binary heap with an
arbitrary tie rule would. `AnyRun C R L D n k c c'` records `n` such
iterations from `c` to `c'` with total cost `k` (charged by `stepCost`).

* `solve_anyTie`: from the initial configuration, every such run has at most
  `8m+10` iterations, can be continued while it has not halted, costs at most
  `(8m+10)(1+3⌈log₂(m+4)⌉)` including the final halting extraction, and, once
  halted, holds the answer `solve`.
* `lineSolve_anyTie`: the same on the symmetric line.
-/

namespace ReleasePath

open Classical

noncomputable section

/-- One iteration under an arbitrary tie rule: a minimum entry `e` that does
not trigger halting is extracted and processed. -/
def AnyStep (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (e : Entry) (c' : Cfg) : Prop :=
  e ∈ c.queue ∧ (∀ e' ∈ c.queue, e.time C ≤ e'.time C) ∧ ¬ Halts C c e ∧
    c' = popStep C R L D c e

/-- `n` iterations under an arbitrary tie rule, with total cost `k`. -/
inductive AnyRun (C : EventData) (R L D : ℕ → ℝ) : ℕ → ℕ → Cfg → Cfg → Prop
  | nil (c : Cfg) : AnyRun C R L D 0 0 c c
  | cons {n k : ℕ} {c c' c'' : Cfg} (e : Entry) :
      AnyStep C R L D c e c' → AnyRun C R L D n k c' c'' →
      AnyRun C R L D (n + 1) (stepCost C R L c e + k) c c''

/-- Cost of the final, halting extraction (none if the queue is empty). -/
def haltCost (c : Cfg) : ℕ := if c.queue = [] then 0 else 1 + heapCost c.queue.length

variable {R L D : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

theorem stepCost_le (Q K : ℕ)
    (hK : 1 + 2 * heapCost Q + heapCost (max (C.size false) (C.size true)) ≤ K)
    (c : Cfg) (e : Entry) (hc : c.queue.length ≤ Q) : stepCost C R L c e ≤ K := by
  have h1 : heapCost c.queue.length ≤ heapCost Q := heapCost_mono hc
  cases e with
  | normal side i j t =>
    have hs : searchCost C R L ⟨side, i, j, t⟩ ≤
        heapCost (max (C.size false) (C.size true)) := by
      refine le_trans (searchCost_le C R L _) (heapCost_mono ?_)
      cases side
      · exact le_max_left _ _
      · exact le_max_right _ _
    simp only [stepCost]
    split_ifs <;> omega
  | wait side i => simp only [stepCost]; omega

/-- Along any run: the potential pays for the iterations, the cost is at most
`K` per iteration, the queue never grows, and the invariants persist. -/
theorem anyRun_facts (H : ChainHyp R L C) (hD : GoalCost R L goals D) (Q K : ℕ)
    (hK : 1 + 2 * heapCost Q + heapCost (max (C.size false) (C.size true)) ≤ K) :
    ∀ {n k : ℕ} {c c'' : Cfg}, AnyRun C R L D n k c c'' →
      ∀ clk, Inv C goals start c clk → CInv C c clk → c.queue.length ≤ Q →
        n + potential C c'' ≤ potential C c ∧ k ≤ n * K ∧ c''.queue.length ≤ Q ∧
          ∃ clk', Inv C goals start c'' clk' ∧ CInv C c'' clk' := by
  intro n k c c'' hrun
  induction hrun with
  | nil c =>
    intro clk inv ci hc
    exact ⟨by omega, by omega, hc, clk, inv, ci⟩
  | @cons n k c c' c'' e hstep _ ih =>
    intro clk inv ci hc
    obtain ⟨he, hmin, _, rfl⟩ := hstep
    have shape := post_shape (D := D) H inv he
    have hdec := potential_decreases inv ci he shape
    have hlen := le_trans (popStep_length (D := D) H inv he) hc
    obtain ⟨h1, h2, h3, h4⟩ :=
      ih _ (inv_step H hD inv he hmin) (cinv_step inv ci he shape) hlen
    have hs := stepCost_le (R := R) (L := L) Q K hK c e hc
    refine ⟨by omega, ?_, h3, h4⟩
    rw [Nat.succ_mul]; omega

/-- A run that has not halted can always take another step. -/
theorem anyStep_exists (c : Cfg) (h : ¬ Halted C c) : ∃ e c', AnyStep C R L D c e c' := by
  cases ha : c.queue.argmin (Entry.time C) with
  | none => exact absurd (Or.inl (List.argmin_eq_none.mp ha)) h
  | some e =>
    have he := List.argmin_mem ha
    have hmin : ∀ e' ∈ c.queue, e.time C ≤ e'.time C :=
      fun e' he' => List.le_of_mem_argmin he' ha
    refine ⟨e, _, he, hmin, fun hh => h (Or.inr ⟨e, he, hmin, hh⟩), rfl⟩

theorem solve_eq_eventSolve (reqs : List (Request ℕ)) (start : ℕ) (hn : 2 ≤ itemCount reqs) :
    solve R L reqs start D = (eventSolve (mkData R L reqs) R L D start).getD 0 := by
  have h0 : itemCount reqs ≠ 0 := by omega
  have h1 : itemCount reqs ≠ 1 := by omega
  unfold solve
  simp only [h0, h1, ↓reduceIte]

/-- **Arbitrary tie-breaking.** With at least two distinct positions, every
run of the event machine that extracts an arbitrary minimum entry in each
iteration has at most `8m+10` iterations, never gets stuck before halting,
costs at most `(8m+10)(1+3⌈log₂(m+4)⌉)` including its final extraction, and on
halting holds the answer of `solve`. -/
theorem solve_anyTie (hR : StrictMono R) (hL : StrictMono L) (reqs : List (Request ℕ))
    (start : ℕ) (goals : Set ℕ) (D : ℕ → ℝ) (hD : GoalCost R L goals D)
    (hn : 2 ≤ itemCount reqs) :
    ∀ n k c, AnyRun (mkData R L reqs) R L D n k (initCfg (mkData R L reqs) start) c →
      n ≤ 8 * itemCount reqs + 10 ∧
      k + haltCost c ≤ (8 * itemCount reqs + 10) * (1 + 3 * Nat.clog 2 (itemCount reqs + 4)) ∧
      (¬ Halted (mkData R L reqs) c → ∃ e c', AnyStep (mkData R L reqs) R L D c e c') ∧
      (Halted (mkData R L reqs) c → c.ans = some (solve R L reqs start D)) := by
  intro n k c hrun
  set C := mkData R L reqs with hC
  have H : ChainHyp R L C := mkData_chainHyp (reqs := reqs) hR hL (by omega)
  have hfuel : eventFuel C ≤ 8 * itemCount reqs + 10 :=
    (solve_iterations hR hL reqs start goals D hD (by omega)).1
  obtain ⟨_, hs, _⟩ := mkData_eq (reqs := reqs) hR.monotone hL.monotone
  have hb := record_count_bound R L hR.monotone hL.monotone (items reqs) (itemCount reqs)
    (items_pos_le reqs)
  have hab : C.size false + C.size true ≤ itemCount reqs + 1 := by
    rw [hC, hs, mkSize_false, mkSize_true, lidx_length_eq, ridx_length_eq]; exact hb
  set Q := C.size false + C.size true + 2 with hQ
  set K := 1 + 3 * Nat.clog 2 (itemCount reqs + 4) with hKdef
  have h1 : heapCost Q ≤ Nat.clog 2 (itemCount reqs + 4) := Nat.clog_mono_right 2 (by omega)
  have h2 : heapCost (max (C.size false) (C.size true)) ≤ Nat.clog 2 (itemCount reqs + 4) :=
    Nat.clog_mono_right 2 (by omega)
  have hK : 1 + 2 * heapCost Q + heapCost (max (C.size false) (C.size true)) ≤ K := by omega
  have hQ0 : (initCfg C start).queue.length ≤ Q := by
    simp only [initCfg, List.length_cons, waitEntries_length, hQ]; omega
  obtain ⟨hpot, hcost, hlen, clk', inv', _⟩ :=
    anyRun_facts (goals := goals) (start := start) H hD Q K hK hrun _ (init_inv H) init_cinv hQ0
  have hinit : potential C (initCfg C start) ≤ eventFuel C := init_potential H
  refine ⟨by omega, ?_, anyStep_exists c, ?_⟩
  · -- a nonempty final queue contributes to the potential, leaving room for one more step
    unfold haltCost
    split_ifs with hq
    · calc k + 0 ≤ n * K := by omega
        _ ≤ (8 * itemCount reqs + 10) * K := Nat.mul_le_mul_right _ (by omega)
    · have hpos : 0 < potential C c := by
        unfold potential
        have := List.length_pos_of_ne_nil hq
        omega
      have hh : heapCost c.queue.length ≤ heapCost Q := heapCost_mono hlen
      calc k + (1 + heapCost c.queue.length) ≤ (n + 1) * K := by rw [Nat.succ_mul]; omega
        _ ≤ (8 * itemCount reqs + 10) * K := Nat.mul_le_mul_right _ (by omega)
  · intro hh
    obtain ⟨A, hA, hleast⟩ := halt_optimal H hD inv' hh
    obtain ⟨A', hA', hleast'⟩ := eventSolve_isLeast (goals := goals) (start := start) H hD
    rw [hA, solve_eq_eventSolve reqs start hn, ← hC, hA', Option.getD_some,
      hleast.unique hleast']

/-- **Arbitrary tie-breaking on the line.** -/
theorem lineSolve_anyTie (reqs : List (Request ℝ)) (s : ℝ)
    (hn : 2 ≤ (reqs.map Request.position).toFinset.card) :
    let C := mkData (lineCoord reqs s) (lineCoord reqs s) (lineReqs reqs s)
    let m := (reqs.map Request.position).toFinset.card
    ∀ n k c, AnyRun C (lineCoord reqs s) (lineCoord reqs s) (fun _ => 0) n k
        (initCfg C (lineRank reqs s s)) c →
      n ≤ 8 * m + 10 ∧
      k + haltCost c ≤ (8 * m + 10) * (1 + 3 * Nat.clog 2 (m + 4)) ∧
      (¬ Halted C c → ∃ e c', AnyStep C (lineCoord reqs s) (lineCoord reqs s) (fun _ => 0) c e c') ∧
      (Halted C c → c.ans = some (lineSolve reqs s)) := by
  have hm := lineCoord_strictMono (reqs := reqs) (s := s)
  intro C m
  have hcount : itemCount (lineReqs reqs s) = m := itemCount_lineReqs
  have hn' : 2 ≤ itemCount (lineReqs reqs s) := by rw [hcount]; exact hn
  rw [← hcount]
  exact solve_anyTie hm hm (lineReqs reqs s) (lineRank reqs s s) Set.univ (fun _ => 0)
    (goalCost_univ hm.monotone hm.monotone) hn'

end

end ReleasePath
