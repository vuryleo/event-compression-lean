import ReleasePath.Main

/-!
# Total cost in the standard cost model

The machine is instrumented with a cost counter that mirrors its control flow:

* every iteration pays `1` plus two heap operations (one extraction and at most
  one insertion), each charged `⌈log₂(queue length + 1)⌉`;
* the halting iteration pays `1` plus one extraction;
* a fresh normal entry additionally pays the comparisons actually made by the
  binary search `upperBound` (bounded by `upperBound_comparisons`).

Heap operations are charged by convention (the queue is modelled as a list);
binary-search comparisons are counted exactly. With the iteration bound and
the fact that the queue never grows, the event phase costs at most
`(8m+10) · (1 + 3⌈log₂(m+4)⌉)`.
-/

namespace ReleasePath

open Classical

noncomputable section

/-- Cost of one heap operation on a queue of length `n`. -/
def heapCost (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

/-- Comparisons made by the binary-search skip of state `s`. -/
def searchCost (C : EventData) (R L : ℕ → ℝ) (s : EventState) : ℕ :=
  (upperBound (eventOffset C R L s.side) (eventThreshold R L s C) s.i (C.size s.side - s.i)).2

def stepCost (C : EventData) (R L : ℕ → ℝ) (c : Cfg) : Entry → ℕ
  | .normal side i j t =>
    1 + 2 * heapCost c.queue.length +
      (if Stale (c.best side i j) t then 0 else searchCost C R L ⟨side, i, j, t⟩)
  | .wait _ _ => 1 + 2 * heapCost c.queue.length

/-- Cost of running the machine with fuel `n`; same control flow as `run`. -/
def runCost (C : EventData) (R L D : ℕ → ℝ) : ℕ → Cfg → ℕ
  | 0, _ => 0
  | n + 1, c =>
    match c.queue.argmin (Entry.time C) with
    | none => 0
    | some e =>
      if Halts C c e then 1 + heapCost c.queue.length
      else stepCost C R L c e + runCost C R L D n (popStep C R L D c e)

theorem heapCost_mono {a b : ℕ} (h : a ≤ b) : heapCost a ≤ heapCost b :=
  Nat.clog_mono_right 2 (by omega)

theorem searchCost_le (C : EventData) (R L : ℕ → ℝ) (s : EventState) :
    searchCost C R L s ≤ heapCost (C.size s.side) := by
  apply upperBound_comparisons
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (C.size s.side + 1)
  unfold heapCost
  omega

/-- The queue never grows. -/
theorem popStep_length (H : ChainHyp R L C) {goals : Set ℕ} {start : ℕ} {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue) :
    (popStep C R L D c e).queue.length ≤ c.queue.length := by
  have hlen := List.length_erase_of_mem he
  have hpos : 0 < c.queue.length := List.length_pos_of_mem he
  rcases post_shape (D := D) H inv he with ⟨hq, _⟩ | ⟨_, _, _, _, hq, _⟩
  · rw [hq]; omega
  · rw [hq, List.length_cons]; omega

theorem runCost_le (H : ChainHyp R L C) {goals : Set ℕ} {start : ℕ} (hD : GoalCost R L goals D)
    (Q K : ℕ) (hK : 1 + 2 * heapCost Q + heapCost (max (C.size false) (C.size true)) ≤ K) :
    ∀ n c clk, Inv C goals start c clk → c.queue.length ≤ Q →
      runCost C R L D n c ≤ n * K := by
  have hheap : ∀ c : Cfg, c.queue.length ≤ Q → heapCost c.queue.length ≤ heapCost Q :=
    fun c h => heapCost_mono h
  have hsearch : ∀ s : EventState, searchCost C R L s ≤
      heapCost (max (C.size false) (C.size true)) := by
    intro s
    refine le_trans (searchCost_le C R L s) (heapCost_mono ?_)
    cases s.side
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hstep : ∀ c e, c.queue.length ≤ Q → stepCost C R L c e ≤ K := by
    intro c e hc
    have h1 := hheap c hc
    cases e with
    | normal side i j t =>
      simp only [stepCost]
      split_ifs
      · omega
      · have := hsearch ⟨side, i, j, t⟩; omega
    | wait side i => simp only [stepCost]; omega
  intro n
  induction n with
  | zero => intro c clk _ _; simp [runCost]
  | succ n ih =>
    intro c clk inv hc
    simp only [runCost]
    cases ha : c.queue.argmin (Entry.time C) with
    | none => simp
    | some e =>
      simp only
      have he := List.argmin_mem ha
      have hmin : ∀ e' ∈ c.queue, e.time C ≤ e'.time C :=
        fun e' he' => List.le_of_mem_argmin he' ha
      split_ifs
      · have := hheap c hc
        rw [Nat.succ_mul]; omega
      · have hs := hstep c e hc
        have hrest := ih _ _ (inv_step H hD inv he hmin)
          (le_trans (popStep_length H inv he) hc)
        rw [Nat.succ_mul]; omega

/-- Total cost of the event phase. -/
def eventCost (C : EventData) (R L D : ℕ → ℝ) (start : ℕ) : ℕ :=
  runCost C R L D (eventFuel C) (initCfg C start)

theorem eventCost_le (H : ChainHyp R L C) {goals : Set ℕ} {start : ℕ}
    (hD : GoalCost R L goals D) :
    eventCost C R L D start ≤ eventFuel C *
      (1 + 2 * heapCost (C.size false + C.size true + 2) +
        heapCost (max (C.size false) (C.size true))) := by
  apply runCost_le (goals := goals) H hD _ _ le_rfl _ _ _ (init_inv H)
  simp only [initCfg, List.length_cons, waitEntries_length]
  omega

/-- **Cost bound.** On at least one distinct position, the event phase of
`solve` costs at most `(8m+10)(1+3⌈log₂(m+4)⌉)` in the standard cost model,
so `O(m log m)`. -/
theorem solve_cost (hR : StrictMono R) (hL : StrictMono L) (reqs : List (Request ℕ))
    (start : ℕ) (goals : Set ℕ) (D : ℕ → ℝ) (hD : GoalCost R L goals D)
    (hn : 0 < itemCount reqs) :
    eventCost (mkData R L reqs) R L D start ≤
      (8 * itemCount reqs + 10) * (1 + 3 * Nat.clog 2 (itemCount reqs + 4)) := by
  have H := mkData_chainHyp (reqs := reqs) hR hL hn
  have hfuel := (solve_iterations hR hL reqs start goals D hD hn).1
  have hc := eventCost_le (start := start) H hD
  obtain ⟨_, hs, _⟩ := mkData_eq (reqs := reqs) hR.monotone hL.monotone
  have hb := record_count_bound R L hR.monotone hL.monotone (items reqs) (itemCount reqs)
    (items_pos_le reqs)
  have hab : (mkData R L reqs).size false + (mkData R L reqs).size true ≤ itemCount reqs + 1 := by
    rw [hs, mkSize_false, mkSize_true, lidx_length_eq, ridx_length_eq]; exact hb
  have h1 : heapCost ((mkData R L reqs).size false + (mkData R L reqs).size true + 2) ≤
      Nat.clog 2 (itemCount reqs + 4) := Nat.clog_mono_right 2 (by omega)
  have h2 : heapCost (max ((mkData R L reqs).size false) ((mkData R L reqs).size true)) ≤
      Nat.clog 2 (itemCount reqs + 4) := Nat.clog_mono_right 2 (by omega)
  calc eventCost (mkData R L reqs) R L D start
      ≤ eventFuel (mkData R L reqs) * (1 + 2 * heapCost ((mkData R L reqs).size false +
          (mkData R L reqs).size true + 2) +
          heapCost (max ((mkData R L reqs).size false) ((mkData R L reqs).size true))) := hc
    _ ≤ (8 * itemCount reqs + 10) * (1 + 3 * Nat.clog 2 (itemCount reqs + 4)) :=
      Nat.mul_le_mul hfuel (by omega)

end

end ReleasePath
