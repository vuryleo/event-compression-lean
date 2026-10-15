import ReleasePath.Main

/-!
# Finite paths and the two-pointer cutoff table

* `solve_isLeast_finite`: on a finite path `{0, …, N-1}` (all request
  positions, the start, and all goals below `N`), plans may be confined to the
  path without changing the optimum, so `solve` is also the finite-path optimum.
  Plans are clamped at vertex `N-1`; clamping never lengthens a directed leg.
* `pointerTable_eq_eventCutoff`: the reference implementation's two-pointer
  loop computes exactly the cutoff `eventCutoff` used by the machine.
-/

namespace ReleasePath

open Classical

noncomputable section

/-! ### Clamping to a finite path -/

def clampV (N v : ℕ) : ℕ := min v (N - 1)

theorem mono_clamp_sub {f : ℕ → ℝ} (hf : Monotone f) (M : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    f (min y M) - f (min x M) ≤ f y - f x := by
  rcases le_total y M with hy | hy
  · rw [min_eq_left hy, min_eq_left (le_trans hxy hy)]
  · rw [min_eq_right hy]
    rcases le_total x M with hx | hx
    · rw [min_eq_left hx]
      have := hf hy
      linarith
    · rw [min_eq_right hx]
      have := hf hxy
      linarith

theorem pathDist_clamp_le {R L : ℕ → ℝ} (hR : Monotone R) (hL : Monotone L) (N x y : ℕ) :
    pathDist R L (clampV N x) (clampV N y) ≤ pathDist R L x y := by
  unfold clampV
  rcases le_total x y with hxy | hyx
  · rw [pathDist_right R L (min_le_min_right _ hxy), pathDist_right R L hxy]
    exact mono_clamp_sub hR _ hxy
  · rw [pathDist_left R L (min_le_min_right _ hyx), pathDist_left R L hyx]
    exact mono_clamp_sub hL _ hyx

theorem clampV_of_lt {N v : ℕ} (h : v < N) : clampV N v = v := by
  unfold clampV; omega

theorem clampV_lt {N : ℕ} (hN : 0 < N) (v : ℕ) : clampV N v < N := by
  unfold clampV; omega

theorem timedRoute_clamp {R L : ℕ → ℝ} (hR : Monotone R) (hL : Monotone L) (N : ℕ) :
    ∀ (vs : List (ℕ × ℝ)) x t, timedRoute (pathDist R L) x t vs →
      timedRoute (pathDist R L) (clampV N x) t (vs.map (fun v => (clampV N v.1, v.2))) := by
  intro vs
  induction vs with
  | nil => intro _ _ _; trivial
  | cons v rest ih =>
    intro x t h
    refine ⟨?_, ih v.1 v.2 h.2⟩
    have := pathDist_clamp_le hR hL N x v.1
    have := h.1
    simp only
    linarith

/-- Finish times of plans confined to the finite path `{0, …, N-1}`. -/
def FiniteFinishTimes (R L : ℕ → ℝ) (N : ℕ) (reqs : List (Request ℕ)) (start : ℕ)
    (goals : Set ℕ) : Set ℝ :=
  {T | ∃ p : Plan ℕ, feasible (pathDist R L) start 0 {q | q ∈ reqs} goals p ∧
    (∀ v ∈ p.visits, v.1 < N) ∧ p.terminal < N ∧ p.finish = T}

/-- **Finite-path version of the main theorem.** -/
theorem solve_isLeast_finite {R L : ℕ → ℝ} (hR : StrictMono R) (hL : StrictMono L)
    (N : ℕ) (reqs : List (Request ℕ)) (start : ℕ) (goals : Set ℕ) (D : ℕ → ℝ)
    (hD : GoalCost R L goals D) (hreq : ∀ q ∈ reqs, q.position < N) (hs : start < N)
    (hgoal : ∀ g ∈ goals, g < N) :
    IsLeast (FiniteFinishTimes R L N reqs start goals) (solve R L reqs start D) := by
  have main := solve_isLeast hR hL reqs start goals D hD
  have hN : 0 < N := by omega
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hfin⟩ := main.1
    refine ⟨⟨p.visits.map (fun v => (clampV N v.1, v.2)), clampV N p.terminal, p.finish⟩,
      ⟨?_, ?_, ?_⟩, ?_, clampV_lt hN _, hfin⟩
    · have h := timedRoute_clamp hR.monotone hL.monotone N _ start 0 hp.1
      rw [clampV_of_lt hs] at h
      simpa only [List.map_append, List.map_cons, List.map_nil] using h
    · intro q hq
      obtain ⟨v, hv, hvp, hvr⟩ := hp.2.1 q hq
      refine ⟨(clampV N v.1, v.2), ?_, ?_, hvr⟩
      · rcases List.mem_append.mp hv with hv | hv
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
        · simp only [List.mem_singleton] at hv
          subst hv
          exact List.mem_append_right _ (by simp)
      · simp only
        rw [hvp]
        exact clampV_of_lt (hreq q hq)
    · simp only
      rw [clampV_of_lt (hgoal _ hp.2.2)]
      exact hp.2.2
    · intro v hv
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
      exact clampV_lt hN _
  · rintro T ⟨p, hp, _, _, rfl⟩
    exact main.2 ⟨p, hp, rfl⟩

/-! ### The two-pointer cutoff table -/

/-- Advance the pointer `j` past opposite entries released no later than `thr`
(the inner `while` loop of the reference code), with fuel. -/
def advance (rel : ℕ → ℝ) (b : ℕ) (thr : ℝ) : ℕ → ℕ → ℕ
  | 0, j => j
  | f + 1, j => if j < b ∧ rel j ≤ thr then advance rel b thr f (j + 1) else j

theorem advance_cutoff (rel : ℕ → ℝ) (b : ℕ) (thr : ℝ)
    (hmono : ∀ i j, i ≤ j → j < b → rel i ≤ rel j) :
    ∀ f j, j ≤ b → b - j ≤ f → (∀ h, h < j → rel h ≤ thr) →
      IsCutoff rel b thr (advance rel b thr f j) := by
  intro f
  induction f with
  | zero =>
    intro j hj hf hpre
    have : j = b := by omega
    subst this
    simp only [advance]
    exact ⟨le_rfl, hpre, fun h hh hb => absurd hb (by omega)⟩
  | succ f ih =>
    intro j hj hf hpre
    simp only [advance]
    split_ifs with hc
    · apply ih (j + 1) (by omega) (by omega)
      intro h hh
      rcases Nat.lt_or_ge h j with hlt | hge
      · exact hpre h hlt
      · have : h = j := by omega
        subst this; exact hc.2
    · refine ⟨hj, hpre, ?_⟩
      intro h hjh hhb
      have hnot : ¬ rel j ≤ thr := fun hr => hc ⟨by omega, hr⟩
      exact lt_of_lt_of_le (lt_of_not_ge hnot) (hmono j h hjh hhb)

/-- The two-pointer table of the reference implementation (`opposite`). -/
def pointerTable (C : EventData) (side : Bool) : ℕ → ℕ
  | 0 => advance (fun k => (C.chain (!side) k).release) (C.size (!side))
      (C.chain side 0).release (C.size (!side)) 0
  | x + 1 => advance (fun k => (C.chain (!side) k).release) (C.size (!side))
      (C.chain side (x + 1)).release (C.size (!side)) (pointerTable C side x)

theorem cutoff_unique (rel : ℕ → ℝ) (b : ℕ) (thr : ℝ) {k₁ k₂ : ℕ}
    (h₁ : IsCutoff rel b thr k₁) (h₂ : IsCutoff rel b thr k₂) : k₁ = k₂ :=
  le_antisymm (cutoff_monotone rel b k₁ k₂ thr thr le_rfl h₁ h₂)
    (cutoff_monotone rel b k₂ k₁ thr thr le_rfl h₂ h₁)

theorem pointerTable_cutoff (C : EventData) (side : Bool) :
    ∀ x, x < C.size side →
      IsCutoff (fun k => (C.chain (!side) k).release) (C.size (!side))
        (C.chain side x).release (pointerTable C side x) := by
  have hm := C.release_mono (!side)
  intro x
  induction x with
  | zero =>
    intro _
    exact advance_cutoff _ _ _ hm _ 0 (Nat.zero_le _) (by omega) (fun h hh => absurd hh (by omega))
  | succ x ih =>
    intro hx
    have prev := ih (by omega)
    apply advance_cutoff _ _ _ hm _ _ prev.1 (by omega)
    intro h hh
    exact le_trans (prev.2.1 h hh) (C.release_mono side x (x + 1) (Nat.le_succ x) hx)

/-- **The two-pointer loop computes the cutoff used by the machine.** -/
theorem pointerTable_eq_eventCutoff (C : EventData) (side : Bool) (x : ℕ)
    (hx : x < C.size side) : pointerTable C side x = eventCutoff C side x :=
  cutoff_unique _ _ _ (pointerTable_cutoff C side x hx) (eventCutoff_spec C side x)

/-! ### Nearest-goal costs (the two scans of the reference code) -/

/-- Distance to the nearest allowed terminal on the left and on the right,
as computed by the two linear scans of the reference implementation. -/
def nearestCost (R L : ℕ → ℝ) (Q : Finset ℕ) (v : ℕ) : ℝ :=
  if hl : (Q.filter (· ≤ v)).Nonempty then
    if hr : (Q.filter (v ≤ ·)).Nonempty then
      min (L v - L ((Q.filter (· ≤ v)).max' hl)) (R ((Q.filter (v ≤ ·)).min' hr) - R v)
    else L v - L ((Q.filter (· ≤ v)).max' hl)
  else if hr : (Q.filter (v ≤ ·)).Nonempty then R ((Q.filter (v ≤ ·)).min' hr) - R v
  else 0

/-- **The nearest-goal scans compute the goal-cost function.** -/
theorem goalCost_nearest {R L : ℕ → ℝ} (hR : Monotone R) (hL : Monotone L) (Q : Finset ℕ)
    (hQ : Q.Nonempty) : GoalCost R L (↑Q) (nearestCost R L Q) := by
  intro v
  -- the two candidate terminals and their exact distances
  have leftDist : ∀ hl : (Q.filter (· ≤ v)).Nonempty,
      pathDist R L v ((Q.filter (· ≤ v)).max' hl) = L v - L ((Q.filter (· ≤ v)).max' hl) :=
    fun hl => pathDist_left R L (Finset.mem_filter.mp (Finset.max'_mem _ hl)).2
  have rightDist : ∀ hr : (Q.filter (v ≤ ·)).Nonempty,
      pathDist R L v ((Q.filter (v ≤ ·)).min' hr) = R ((Q.filter (v ≤ ·)).min' hr) - R v :=
    fun hr => pathDist_right R L (Finset.mem_filter.mp (Finset.min'_mem _ hr)).2
  have leftBound : ∀ hl : (Q.filter (· ≤ v)).Nonempty, ∀ g ∈ Q, g ≤ v →
      L v - L ((Q.filter (· ≤ v)).max' hl) ≤ pathDist R L v g := by
    intro hl g hg hgv
    rw [pathDist_left R L hgv]
    have := hL (Finset.le_max' (Q.filter (· ≤ v)) g (Finset.mem_filter.mpr ⟨hg, hgv⟩))
    linarith
  have rightBound : ∀ hr : (Q.filter (v ≤ ·)).Nonempty, ∀ g ∈ Q, v ≤ g →
      R ((Q.filter (v ≤ ·)).min' hr) - R v ≤ pathDist R L v g := by
    intro hr g hg hvg
    rw [pathDist_right R L hvg]
    have := hR (Finset.min'_le (Q.filter (v ≤ ·)) g (Finset.mem_filter.mpr ⟨hg, hvg⟩))
    linarith
  have lmem := fun hl => (Finset.mem_filter.mp (Finset.max'_mem (Q.filter (· ≤ v)) hl)).1
  have rmem := fun hr => (Finset.mem_filter.mp (Finset.min'_mem (Q.filter (v ≤ ·)) hr)).1
  unfold nearestCost
  split_ifs with hl hr hr
  · refine ⟨?_, ?_⟩
    · intro g hg
      rcases le_total g v with hgv | hvg
      · exact le_trans (min_le_left _ _) (leftBound hl g hg hgv)
      · exact le_trans (min_le_right _ _) (rightBound hr g hg hvg)
    · rcases min_choice (L v - L ((Q.filter (· ≤ v)).max' hl))
        (R ((Q.filter (v ≤ ·)).min' hr) - R v) with h | h
      · exact ⟨_, lmem hl, by rw [h, leftDist hl]⟩
      · exact ⟨_, rmem hr, by rw [h, rightDist hr]⟩
  · refine ⟨?_, ⟨_, lmem hl, leftDist hl⟩⟩
    intro g hg
    rcases le_total g v with hgv | hvg
    · exact leftBound hl g hg hgv
    · exact absurd ⟨g, Finset.mem_filter.mpr ⟨hg, hvg⟩⟩ hr
  · refine ⟨?_, ⟨_, rmem hr, rightDist hr⟩⟩
    intro g hg
    rcases le_total g v with hgv | hvg
    · exact absurd ⟨g, Finset.mem_filter.mpr ⟨hg, hgv⟩⟩ hl
    · exact rightBound hr g hg hvg
  · exfalso
    obtain ⟨g, hg⟩ := hQ
    rcases le_total g v with hgv | hvg
    · exact hl ⟨g, Finset.mem_filter.mpr ⟨hg, hgv⟩⟩
    · exact hr ⟨g, Finset.mem_filter.mpr ⟨hg, hvg⟩⟩

end

end ReleasePath
