import ReleasePath.Preprocess

/-!
# Main theorem

`solve R L reqs start D` is the complete algorithm: merge duplicate
positions, handle zero and one distinct position directly, otherwise build
the two record chains and run the event machine for `8(a+b)+2` iterations.

* `solve_isLeast`: for strictly increasing prefix metrics `R`, `L` (positive
  directed edge costs), any request list, any start, and any goal set whose
  distance function is `D`, `solve` is the least finish time over all
  feasible plans.
* `solve_iterations`: the event loop halts within `8m+10` iterations, where
  `m` is the number of distinct request positions.
-/

namespace ReleasePath

open Classical

noncomputable section

/-- The complete algorithm, mirroring `event_solve` of the reference code. -/
def solve (R L : ℕ → ℝ) (reqs : List (Request ℕ)) (start : ℕ) (D : ℕ → ℝ) : ℝ :=
  if itemCount reqs = 0 then D start
  else if itemCount reqs = 1 then
    max (pathDist R L start (items reqs 0).position) (items reqs 0).release +
      D (items reqs 0).position
  else (eventSolve (mkData R L reqs) R L D start).getD 0

/-- Finish times of feasible plans for the original instance. -/
def FinishTimes (R L : ℕ → ℝ) (reqs : List (Request ℕ)) (start : ℕ) (goals : Set ℕ) : Set ℝ :=
  {T | ∃ p : Plan ℕ, feasible (pathDist R L) start 0 {q | q ∈ reqs} goals p ∧ p.finish = T}

variable {R L : ℕ → ℝ}

/-- Every listed visit, in particular a service visit, leaves enough time to
reach the terminal. -/
theorem visit_to_finish (hR : Monotone R) (hL : Monotone L) (goal y : ℕ) (finish τ : ℝ) :
    ∀ (vs : List (ℕ × ℝ)) x t, timedRoute (pathDist R L) x t (vs ++ [(goal, finish)]) →
      (y, τ) ∈ vs ++ [(goal, finish)] → τ + pathDist R L y goal ≤ finish := by
  intro vs
  induction vs with
  | nil =>
    intro x t _ hm
    simp only [List.nil_append, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [pathDist_self]; simp
  | cons v rest ih =>
    intro x t hroute hm
    rcases List.mem_cons.mp hm with heq | hm
    · subst heq
      exact timedRoute_visit_lower_bound (pathDist R L) (pathDist_triangle R L hR hL) _ goal
        finish _ _ hroute.2 (by simp)
    · exact ih v.1 v.2 hroute.2 hm

theorem feasible_items_iff (reqs : List (Request ℕ)) (x : ℕ) (t : ℝ) (goals : Set ℕ)
    (p : Plan ℕ) :
    feasible (pathDist R L) x t (originalRequests (items reqs) (itemCount reqs)) goals p ↔
      feasible (pathDist R L) x t {q | q ∈ reqs} goals p := by
  unfold feasible
  rw [serves_items_iff]

/-- Turn a least-`InitBy`-style bound into `IsLeast` over exact finish times. -/
theorem isLeast_of_finishBy (reqs : List (Request ℕ)) (start : ℕ) (goals : Set ℕ) (A : ℝ)
    (P : ℝ → Prop)
    (hP : ∀ T, P T ↔ ∃ p : Plan ℕ, feasible (pathDist R L) start 0 {q | q ∈ reqs} goals p ∧
      p.finish ≤ T)
    (hA : IsLeast {T | P T} A) : IsLeast (FinishTimes R L reqs start goals) A := by
  obtain ⟨p, hp, hpA⟩ := (hP A).mp hA.1
  refine ⟨⟨⟨p.visits, p.terminal, A⟩, ?_, rfl⟩, ?_⟩
  · exact feasible_delay_finish _ _ _ _ _ _ _ _ _ hpA hp
  · rintro T ⟨q, hq, rfl⟩
    exact hA.2 ((hP _).mpr ⟨q, hq, le_rfl⟩)

theorem itemCount_zero_iff (reqs : List (Request ℕ)) : itemCount reqs = 0 ↔ reqs = [] := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil reqs hne
    obtain ⟨k, hk, _⟩ := items_cover reqs q hq
    omega
  · rintro rfl
    simp [itemCount, positions]

/-- **Main theorem.** -/
theorem solve_isLeast (hR : StrictMono R) (hL : StrictMono L) (reqs : List (Request ℕ))
    (start : ℕ) (goals : Set ℕ) (D : ℕ → ℝ) (hD : GoalCost R L goals D) :
    IsLeast (FinishTimes R L reqs start goals) (solve R L reqs start D) := by
  have mR := hR.monotone
  have mL := hL.monotone
  unfold solve
  split_ifs with h0 h1
  · -- no requests
    have hnil := (itemCount_zero_iff reqs).mp h0
    subst hnil
    obtain ⟨g, hg, hgd⟩ := (hD start).2
    refine ⟨⟨⟨[], g, D start⟩, ⟨⟨by simp [hgd], trivial⟩, by intro q hq; simp at hq, hg⟩, rfl⟩, ?_⟩
    rintro T ⟨p, hp, rfl⟩
    have hb := timedRoute_visit_lower_bound (pathDist R L) (pathDist_triangle R L mR mL) _
      p.terminal p.finish start 0 hp.1 (by simp)
    have := (hD start).1 p.terminal hp.2.2
    linarith
  · -- one distinct position
    have hk0 : 0 < itemCount reqs := by omega
    set q := items reqs 0 with hqdef
    have orig : originalRequests (items reqs) (itemCount reqs) = {q} := by
      ext a
      simp only [originalRequests, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have : i = 0 := by omega
        subst this; rfl
      · rintro rfl; exact ⟨0, hk0, rfl⟩
    obtain ⟨g, hg, hgd⟩ := (hD q.position).2
    refine ⟨⟨⟨[(q.position, max (pathDist R L start q.position) q.release)], g, _⟩, ?_, rfl⟩, ?_⟩
    · rw [← feasible_items_iff, orig]
      refine ⟨⟨by simp, by simp [hgd], trivial⟩, ?_, hg⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨(q.position, max (pathDist R L start q.position) q.release), by simp, rfl,
        le_max_right _ _⟩
    · rintro T ⟨p, hp, rfl⟩
      rw [← feasible_items_iff, orig] at hp
      obtain ⟨v, hv, hvp, hvr⟩ := hp.2.1 q rfl
      have h1 := timedRoute_visit_lower_bound (pathDist R L) (pathDist_triangle R L mR mL) _
        v.1 v.2 start 0 hp.1 hv
      have h2 := visit_to_finish mR mL p.terminal v.1 p.finish v.2 p.visits start 0 hp.1 hv
      have h3 := (hD q.position).1 p.terminal hp.2.2
      rw [hvp] at h1 h2
      have hmax : max (pathDist R L start q.position) q.release ≤ v.2 :=
        max_le (by linarith) hvr
      linarith
  · -- the event machine
    have hn : 0 < itemCount reqs := by omega
    have H := mkData_chainHyp (reqs := reqs) hR hL hn
    obtain ⟨A, hA, hleast⟩ := eventSolve_isLeast (start := start) H hD
    rw [hA, Option.getD_some]
    apply isLeast_of_finishBy reqs start goals A _ _ hleast
    intro T
    obtain ⟨_, _, hd⟩ := mkData_eq (reqs := reqs) mR mL
    unfold InitBy
    rw [hd, mkData_pending mR mL]
    constructor
    · rintro ⟨g, f, hf, vs, hvs⟩
      obtain ⟨ws, hws⟩ := (scanned_elimination_iff R L mR mL (items reqs) (itemCount reqs)
        (items_pos_le reqs) start 0 goals g f).mp ⟨vs, hvs⟩
      exact ⟨⟨ws, g, f⟩, (feasible_items_iff reqs start 0 goals _).mp hws, hf⟩
    · rintro ⟨p, hp, hf⟩
      obtain ⟨vs, hvs⟩ := (scanned_elimination_iff R L mR mL (items reqs) (itemCount reqs)
        (items_pos_le reqs) start 0 goals p.terminal p.finish).mpr
        ⟨p.visits, (feasible_items_iff reqs start 0 goals _).mpr hp⟩
      exact ⟨p.terminal, p.finish, hf, vs, hvs⟩

/-! ### Goal-cost instances -/

/-- Unrestricted termination: any vertex may be the terminal, `D = 0`. -/
theorem goalCost_univ (hR : Monotone R) (hL : Monotone L) :
    GoalCost R L Set.univ (fun _ => 0) := by
  intro v
  exact ⟨fun g _ => pathDist_nonneg R L hR hL v g, v, Set.mem_univ v, pathDist_self R L v⟩

/-- A finite nonempty terminal set, with `D v = min_{q ∈ Q} d(v, q)`. -/
theorem goalCost_finset (Q : Finset ℕ) (hQ : Q.Nonempty) :
    GoalCost R L (↑Q) (fun v => Q.inf' hQ (pathDist R L v)) := by
  intro v
  refine ⟨fun g hg => Finset.inf'_le _ hg, ?_⟩
  obtain ⟨g, hg, heq⟩ := Finset.exists_mem_eq_inf' hQ (pathDist R L v)
  exact ⟨g, hg, heq.symm⟩

/-! ### Iteration bound in terms of the input -/

theorem lidx_length_eq (reqs : List (Request ℕ)) :
    (lidx R reqs).length = (leftRecordIndices R (items reqs) (itemCount reqs)).card := by
  have hnd : (lidx R reqs).Nodup := (increasingRecords_pairwise _ _).imp (fun h => ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext k
  simp only [List.mem_toFinset, leftRecordIndices, Finset.mem_filter, Finset.mem_range]
  rw [show k ∈ lidx R reqs ↔ _ from leftRecordScan_mem R (items reqs) _ k]
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

theorem ridx_length_eq (reqs : List (Request ℕ)) :
    (ridx L reqs).length = (rightRecordIndices L (items reqs) (itemCount reqs)).card := by
  have hnd : (ridx L reqs).Nodup :=
    (rightRecordScan_pairwise _ _ _).imp (fun h => ne_of_gt h)
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext k
  simp only [List.mem_toFinset, rightRecordIndices, Finset.mem_filter, Finset.mem_range]
  rw [show k ∈ ridx L reqs ↔ _ from rightRecordScan_mem L (items reqs) _ k]
  exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

/-- **Iteration bound.** On at least two distinct positions, the event loop
of `solve` halts within `8m + 10` iterations, `m` = number of distinct
positions. Each iteration performs one queue extraction, at most one
insertion, and at most one binary search. -/
theorem solve_iterations (hR : StrictMono R) (hL : StrictMono L) (reqs : List (Request ℕ))
    (start : ℕ) (goals : Set ℕ) (D : ℕ → ℝ) (hD : GoalCost R L goals D)
    (hn : 0 < itemCount reqs) :
    eventFuel (mkData R L reqs) ≤ 8 * itemCount reqs + 10 ∧
      Halted (mkData R L reqs)
        (run (mkData R L reqs) R L D (eventFuel (mkData R L reqs))
          (initCfg (mkData R L reqs) start)) := by
  have H := mkData_chainHyp (reqs := reqs) hR hL hn
  refine ⟨?_, event_halts (goals := goals) H hD⟩
  obtain ⟨_, hs, _⟩ := mkData_eq (reqs := reqs) hR.monotone hL.monotone
  have hb := record_count_bound R L hR.monotone hL.monotone (items reqs) (itemCount reqs)
    (items_pos_le reqs)
  unfold eventFuel
  rw [hs, mkSize_false, mkSize_true, lidx_length_eq, ridx_length_eq]
  omega

end

end ReleasePath
