import Mathlib

/-!
# Route lemmas

The plan model and the route transformations behind the algorithm:
the directed path metric, record elimination, endpoint recurrence, ready
runs and binary jumps, completion, cutoffs, and switch-key counting.
Times are real numbers. A suffix is a finite list of timed visits; waiting
is represented by slack in the travel inequalities. Travel costs may be
direction-dependent. Requests have zero service duration.
-/
namespace ReleasePath

structure Request (Pos : Type) where
  position : Pos
  release : ℝ

structure Plan (Pos : Type) where
  visits : List (Pos × ℝ)
  terminal : Pos
  finish : ℝ

def timedRoute {Pos : Type} (d : Pos → Pos → ℝ) :
    Pos → ℝ → List (Pos × ℝ) → Prop
  | _, _, [] => True
  | x, t, v :: rest => t + d x v.1 ≤ v.2 ∧ timedRoute d v.1 v.2 rest

def serves {Pos : Type} (remaining : Set (Request Pos))
    (visits : List (Pos × ℝ)) : Prop :=
  ∀ q ∈ remaining, ∃ v ∈ visits, v.1 = q.position ∧ q.release ≤ v.2

def feasible {Pos : Type} (d : Pos → Pos → ℝ) (x : Pos) (t : ℝ)
    (remaining : Set (Request Pos)) (goals : Set Pos) (p : Plan Pos) : Prop :=
  timedRoute d x t (p.visits ++ [(p.terminal, p.finish)]) ∧
  serves remaining (p.visits ++ [(p.terminal, p.finish)]) ∧
  p.terminal ∈ goals

/-- The same timed suffix works from an earlier time at the same position. -/
theorem earlier_route {Pos : Type} (d : Pos → Pos → ℝ) (x : Pos)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (vs : List (Pos × ℝ))
    (h : timedRoute d x t₂ vs) : timedRoute d x t₁ vs := by
  cases vs with
  | nil => trivial
  | cons v rest =>
    have hh := h.1
    refine ⟨?_, h.2⟩
    linarith

/-- Earlier arrival and fewer obligations preserve the identical suffix,
including its terminal and its absolute finish time. -/
theorem continuation_dominance {Pos : Type} (d : Pos → Pos → ℝ) (x : Pos)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    {small large : Set (Request Pos)} (hsub : small ⊆ large)
    (goals : Set Pos) (p : Plan Pos)
    (h : feasible d x t₂ large goals p) : feasible d x t₁ small goals p := by
  refine ⟨earlier_route d x ht _ h.1, ?_, h.2.2⟩
  intro q hq
  exact h.2.1 q (hsub hq)

/-- Bookkeeping obligations: unremoved suffixes of the two chains.
The functions are only used on indices below their stated lengths. -/
def pending {Req : Type} (left right : ℕ → Req) (a b i j : ℕ) : Set Req :=
  {q | (∃ k, i ≤ k ∧ k < a ∧ left k = q) ∨
       (∃ k, j ≤ k ∧ k < b ∧ right k = q)}

theorem pending_antitone {Req : Type} (left right : ℕ → Req)
    (a b i : ℕ) {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) :
    pending left right a b i j₂ ⊆ pending left right a b i j₁ := by
  intro q hq
  rcases hq with hleft | ⟨k, hjk, hkb, heq⟩
  · exact Or.inl hleft
  · exact Or.inr ⟨k, le_trans hj hjk, hkb, heq⟩

/-- Specification of a first-later-release index, including sentinel b.
Existence for a sorted finite chain is proved below by cutoff_exists. -/
def IsCutoff (release : ℕ → ℝ) (b : ℕ) (threshold : ℝ) (k : ℕ) : Prop :=
  k ≤ b ∧ (∀ h, h < k → release h ≤ threshold) ∧
    (∀ h, k ≤ h → h < b → threshold < release h)

theorem cutoff_monotone (release : ℕ → ℝ) (b k₁ k₂ : ℕ)
    (r₁ r₂ : ℝ) (hr : r₁ ≤ r₂)
    (h₁ : IsCutoff release b r₁ k₁) (h₂ : IsCutoff release b r₂ k₂) :
    k₁ ≤ k₂ := by
  by_contra hn
  have hk : k₂ < k₁ := by omega
  have hb : k₂ < b := lt_of_lt_of_le hk h₁.1
  have hearly := h₁.2.1 k₂ hk
  have hlate := h₂.2.2 k₂ (le_refl k₂) hb
  linarith

theorem blocked_cutoff_bound (release : ℕ → ℝ) (b j k : ℕ)
    (t nextRelease : ℝ) (hj : j ≤ b) (hblocked : t < nextRelease)
    (hcut : IsCutoff release b nextRelease k)
    (hserved : ∀ h, h < j → release h ≤ t) : j ≤ k := by
  by_contra hn
  have hk : k < j := by omega
  have hkb : k < b := lt_of_lt_of_le hk hj
  have hlate := hcut.2.2 k (le_refl k) hkb
  have hs := hserved k hk
  linarith

/-- The sum of adjacent natural-number increments telescopes. -/
theorem telescope (o : ℕ → ℕ) (hmono : Monotone o) (n : ℕ) :
    (∑ i ∈ Finset.range n, (o (i + 1) - o i)) = o n - o 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 : o 0 ≤ o n := hmono (Nat.zero_le n)
    have hn : o n ≤ o (n + 1) := hmono (Nat.le_succ n)
    omega

/-- One consolidated representative plus an inclusive interval per pivot.
This is the numerical budget for the admissible-key count. -/
theorem switch_budget (o : ℕ → ℕ) (hmono : Monotone o) (n b : ℕ)
    (hmax : o n ≤ b) :
    (∑ i ∈ Finset.range n, (o (i + 1) - o i + 2)) ≤ b + 2 * n := by
  have heq : (∑ i ∈ Finset.range n, (o (i + 1) - o i + 2)) =
      (o n - o 0) + 2 * n := by
    rw [Finset.sum_add_distrib, telescope o hmono]
    simp [Nat.mul_comm]
  rw [heq]
  omega

/-- A bounded nondecreasing release chain has a first-later cutoff,
with the chain length as sentinel. -/
theorem cutoff_exists (release : ℕ → ℝ) (b : ℕ) (r : ℝ)
    (hmono : ∀ i j, i ≤ j → j < b → release i ≤ release j) :
    ∃ k, IsCutoff release b r k := by
  classical
  let P : ℕ → Prop := fun k => k = b ∨ (k < b ∧ r < release k)
  have hex : ∃ k, P k := ⟨b, Or.inl rfl⟩
  have hb : Nat.find hex ≤ b := Nat.find_min' hex (Or.inl rfl)
  refine ⟨Nat.find hex, hb, ?_, ?_⟩
  · intro h hh
    by_contra hn
    have hr : r < release h := lt_of_not_ge hn
    have hhb : h < b := lt_of_lt_of_le hh hb
    exact Nat.find_min hex hh (Or.inr ⟨hhb, hr⟩)
  · intro h hkh hhb
    have hk : Nat.find hex < b := lt_of_le_of_lt hkh hhb
    have hs := Nat.find_spec hex
    rcases hs with hs | hs
    · omega
    · exact lt_of_lt_of_le hs.2 (hmono _ _ hkh hhb)

/-- Destination index first, pending opposite index second, matching
the manuscript's (R, current, pending) convention after dropping R. -/
def normalSwitchKey (o : ℕ → ℕ) (i j : ℕ) : ℕ × ℕ :=
  if j < o i then (o i - 1, i + 1) else (j, i + 1)

def pivotTargets (o : ℕ → ℕ) (i : ℕ) : Finset (ℕ × ℕ) :=
  (insert (o i - 1) (Finset.Icc (o i) (o (i + 1)))).image
    (fun j => (j, i + 1))

/-- A finite superset of normal switch keys. It intentionally includes
some invalid sentinel keys: this can only enlarge the upper bound. -/
def switchKeys (o : ℕ → ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).biUnion (pivotTargets o)

theorem switch_key_covered (o : ℕ → ℕ) (n i j : ℕ)
    (hi : i < n) (hj : j ≤ o (i + 1)) :
    normalSwitchKey o i j ∈ switchKeys o n := by
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  unfold pivotTargets normalSwitchKey
  split_ifs with hlow
  ·
    exact Finset.mem_image.mpr ⟨o i - 1, Finset.mem_insert_self _ _, rfl⟩
  ·
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_insert_of_mem ?_, rfl⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hj⟩

theorem pivot_card_le (o : ℕ → ℕ) (hmono : Monotone o) (i : ℕ) :
    (pivotTargets o i).card ≤ o (i + 1) - o i + 2 := by
  have hm : o i ≤ o (i + 1) := hmono (Nat.le_succ i)
  calc
    (pivotTargets o i).card ≤
        (insert (o i - 1) (Finset.Icc (o i) (o (i + 1)))).card :=
      Finset.card_image_le
    _ ≤ (Finset.Icc (o i) (o (i + 1))).card + 1 := Finset.card_insert_le _ _
    _ = o (i + 1) - o i + 2 := by rw [Nat.card_Icc]; omega

theorem switch_keys_card_le (o : ℕ → ℕ) (hmono : Monotone o)
    (n b : ℕ) (hmax : o n ≤ b) :
    (switchKeys o n).card ≤ b + 2 * n := by
  calc
    (switchKeys o n).card ≤
        ∑ i ∈ Finset.range n, (pivotTargets o i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range n, (o (i + 1) - o i + 2) :=
      Finset.sum_le_sum (fun i _ => pivot_card_le o hmono i)
    _ ≤ b + 2 * n := switch_budget o hmono n b hmax

def pathDist (R L : ℕ → ℝ) (x y : ℕ) : ℝ :=
  if x ≤ y then R y - R x else L x - L y

theorem pathDist_self (R L : ℕ → ℝ) (x : ℕ) : pathDist R L x x = 0 := by
  simp [pathDist]

theorem pathDist_nonneg (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (x y : ℕ) : 0 ≤ pathDist R L x y := by
  unfold pathDist
  split_ifs with h
  · exact sub_nonneg.mpr (hR h)
  · exact sub_nonneg.mpr (hL (by omega))

theorem pathDist_right (R L : ℕ → ℝ) {x y : ℕ} (h : x ≤ y) :
    pathDist R L x y = R y - R x := by simp [pathDist, h]

theorem pathDist_left (R L : ℕ → ℝ) {x y : ℕ} (h : y ≤ x) :
    pathDist R L x y = L x - L y := by
  by_cases hxy : x ≤ y
  · have heq : x = y := le_antisymm hxy h
    subst y
    simp [pathDist]
  · simp [pathDist, hxy]

theorem pathDist_right_add (R L : ℕ → ℝ) {x y z : ℕ}
    (hxy : x ≤ y) (hyz : y ≤ z) :
    pathDist R L x z = pathDist R L x y + pathDist R L y z := by
  rw [pathDist_right R L (le_trans hxy hyz), pathDist_right R L hxy,
      pathDist_right R L hyz]
  ring

theorem pathDist_left_add (R L : ℕ → ℝ) {x y z : ℕ}
    (hyx : y ≤ x) (hzy : z ≤ y) :
    pathDist R L x z = pathDist R L x y + pathDist R L y z := by
  rw [pathDist_left R L (le_trans hzy hyx), pathDist_left R L hyx,
      pathDist_left R L hzy]
  ring

/-- Insert an intermediate point at its earliest arrival time in
a distance-additive first leg, preserving every subsequent absolute time. -/
theorem insert_route_visit {Pos : Type} (d : Pos → Pos → ℝ)
    (x y z : Pos) (t arrival : ℝ) (rest : List (Pos × ℝ))
    (hadd : d x z = d x y + d y z)
    (h : timedRoute d x t ((z, arrival) :: rest)) :
    timedRoute d x t ((y, t + d x y) :: (z, arrival) :: rest) := by
  have hfirst := h.1
  refine ⟨le_refl _, ?_, h.2⟩
  dsimp
  linarith

theorem serves_mono_visits {Pos : Type} (remaining : Set (Request Pos))
    (short long : List (Pos × ℝ)) (hsub : ∀ v ∈ short, v ∈ long)
    (h : serves remaining short) : serves remaining long := by
  intro q hq
  rcases h q hq with ⟨v, hv, hpos, hrelease⟩
  exact ⟨v, hsub v hv, hpos, hrelease⟩

theorem pathDist_pos (R L : ℕ → ℝ) (hR : StrictMono R) (hL : StrictMono L)
    {x y : ℕ} (hne : x ≠ y) : 0 < pathDist R L x y := by
  unfold pathDist
  split_ifs with h
  · exact sub_pos.mpr (hR (by omega))
  · exact sub_pos.mpr (hL (by omega))

theorem pathDist_ge_right_delta (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y : ℕ) :
    R y - R x ≤ pathDist R L x y := by
  unfold pathDist
  split_ifs with h
  · exact le_refl _
  · have hyx : y ≤ x := by omega
    have hr := hR hyx
    have hl := hL hyx
    linarith

theorem pathDist_ge_left_delta (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y : ℕ) :
    L x - L y ≤ pathDist R L x y := by
  unfold pathDist
  split_ifs with h
  · have hr := hR h
    have hl := hL h
    linarith
  · exact le_refl _

theorem pathDist_triangle (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y z : ℕ) :
    pathDist R L x z ≤ pathDist R L x y + pathDist R L y z := by
  by_cases hxz : x ≤ z
  · rw [pathDist_right R L hxz]
    have h1 := pathDist_ge_right_delta R L hR hL x y
    have h2 := pathDist_ge_right_delta R L hR hL y z
    linarith
  · rw [pathDist_left R L (show z ≤ x by omega)]
    have h1 := pathDist_ge_left_delta R L hR hL x y
    have h2 := pathDist_ge_left_delta R L hR hL y z
    linarith

/-- A possibly detouring timed route cannot reach a listed visit earlier
than direct travel. No assumption of a monotone route is made. -/
theorem timedRoute_visit_lower_bound {Pos : Type} (d : Pos → Pos → ℝ)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (vs : List (Pos × ℝ)) (y : Pos) (arrival : ℝ) :
    ∀ x t, timedRoute d x t vs → (y, arrival) ∈ vs → t + d x y ≤ arrival := by
  induction vs with
  | nil => simp
  | cons v rest ih =>
    intro x t hroute hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · cases heq
      exact hroute.1
    · have hfirst := hroute.1
      have hlater := ih v.1 v.2 hroute.2 htail
      have hdist := htri x v.1 y
      linarith

/-- All remaining obligations lie beyond a separating checkpoint. If at
least one obligation remains, an arbitrary feasible plan from the far side
can be continued from the checkpoint at direct-arrival time. The goal may
be on either side. -/
theorem barrier_normalize {Pos : Type} (d : Pos → Pos → ℝ)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (z : Pos) (far : Pos → Prop)
    (hadd : ∀ a b, far a → ¬ far b → d a b = d a z + d z b)
    (remaining : Set (Request Pos)) (goals : Set Pos)
    (hne : ∃ q, q ∈ remaining)
    (hside : ∀ q ∈ remaining, ¬ far q.position)
    (vs : List (Pos × ℝ)) (goal : Pos) (finish : ℝ) :
    ∀ y t, far y → feasible d y t remaining goals ⟨vs, goal, finish⟩ →
      ∃ ws, feasible d z (t + d y z) remaining goals ⟨ws, goal, finish⟩ := by
  classical
  induction vs with
  | nil =>
    intro y t hy h
    rcases hne with ⟨q, hq⟩
    rcases h.2.1 q hq with ⟨v, hv, hp, _⟩
    have hv' : v = (goal, finish) := by simpa using hv
    subst v
    have hp' : goal = q.position := hp
    have hgoal : ¬ far goal := by
      rw [hp']
      exact hside q hq
    have heq := hadd y goal hy hgoal
    have htime := h.1.1
    refine ⟨[], ?_, h.2.1, h.2.2⟩
    change (t + d y z + d z goal ≤ finish) ∧ True
    exact ⟨by linarith, trivial⟩
  | cons v rest ih =>
    intro y t hy h
    by_cases hv : far v.1
    · have hserve : serves remaining (rest ++ [(goal, finish)]) := by
        intro q hq
        rcases h.2.1 q hq with ⟨w, hw, hp, hr⟩
        have hm : w = v ∨ w ∈ rest ++ [(goal, finish)] := by simpa using hw
        rcases hm with heq | hmem
        · subst w
          exact False.elim (hside q hq (by simpa only [← hp] using hv))
        · exact ⟨w, hmem, hp, hr⟩
      have htail : feasible d v.1 v.2 remaining goals ⟨rest, goal, finish⟩ :=
        ⟨h.1.2, hserve, h.2.2⟩
      rcases ih v.1 v.2 hv htail with ⟨ws, hws⟩
      have hfirst := h.1.1
      have hdist := htri y v.1 z
      have ht : t + d y z ≤ v.2 + d v.1 z := by linarith
      exact ⟨ws, continuation_dominance d z ht (Set.Subset.refl remaining)
        goals ⟨ws, goal, finish⟩ hws⟩
    · have heq := hadd y v.1 hy hv
      have hfirst := h.1.1
      refine ⟨v :: rest, ?_, h.2.1, h.2.2⟩
      change (t + d y z + d z v.1 ≤ v.2) ∧ _
      exact ⟨by linarith, h.1.2⟩

/-- If every remaining request is at or left of z, any feasible route
starting right of z can be replaced by a direct approach to z and a suffix,
even when the prescribed terminal is to the right of z. -/
theorem left_barrier_normalize (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (z y : ℕ) (t : ℝ)
    (hy : z < y) (remaining : Set (Request ℕ)) (goals : Set ℕ)
    (hne : ∃ q, q ∈ remaining) (hside : ∀ q ∈ remaining, q.position ≤ z)
    (p : Plan ℕ) (h : feasible (pathDist R L) y t remaining goals p) :
    ∃ ws, feasible (pathDist R L) z (t + pathDist R L y z)
      remaining goals ⟨ws, p.terminal, p.finish⟩ := by
  apply barrier_normalize (pathDist R L) (pathDist_triangle R L hR hL)
    z (fun a => z < a) ?_ remaining goals hne ?_ p.visits p.terminal p.finish y t hy h
  · intro a b ha hb
    exact pathDist_left_add R L (by omega) (by omega)
  · intro q hq
    exact not_lt_of_ge (hside q hq)

/-- The symmetric checkpoint transformation for a left-to-right approach. -/
theorem right_barrier_normalize (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (z y : ℕ) (t : ℝ)
    (hy : y < z) (remaining : Set (Request ℕ)) (goals : Set ℕ)
    (hne : ∃ q, q ∈ remaining) (hside : ∀ q ∈ remaining, z ≤ q.position)
    (p : Plan ℕ) (h : feasible (pathDist R L) y t remaining goals p) :
    ∃ ws, feasible (pathDist R L) z (t + pathDist R L y z)
      remaining goals ⟨ws, p.terminal, p.finish⟩ := by
  apply barrier_normalize (pathDist R L) (pathDist_triangle R L hR hL)
    z (fun a => a < z) ?_ remaining goals hne ?_ p.visits p.terminal p.finish y t hy h
  · intro a b ha hb
    exact pathDist_right_add R L (by omega) (by omega)
  · intro q hq
    exact not_lt_of_ge (hside q hq)

def chainSegment {Req : Type} (c : ℕ → Req) : ℕ → ℕ → List Req
  | _, 0 => []
  | j, n + 1 => c j :: chainSegment c (j + 1) n

theorem chainSegment_mem {Req : Type} (c : ℕ → Req) (n : ℕ) :
    ∀ j q, q ∈ chainSegment c j n ↔ ∃ h, j ≤ h ∧ h < j + n ∧ c h = q := by
  induction n with
  | zero =>
    intro j q
    simp only [chainSegment, List.not_mem_nil, false_iff]
    rintro ⟨h, h1, h2, _⟩
    omega
  | succ n ih =>
    intro j q
    constructor
    · intro hq
      rcases List.mem_cons.mp hq with heq | htail
      · exact ⟨j, le_refl _, by omega, heq.symm⟩
      · rcases (ih (j + 1) q).mp htail with ⟨h, h1, h2, heq⟩
        exact ⟨h, by omega, by omega, heq⟩
    · rintro ⟨h, h1, h2, heq⟩
      by_cases hj : h = j
      · subst h
        exact List.mem_cons.mpr (Or.inl heq.symm)
      · apply List.mem_cons.mpr
        apply Or.inr
        exact (ih (j + 1) q).mpr ⟨h, by omega, by omega, heq⟩

def LeftRecord (R : ℕ → ℝ) (req : ℕ → Request ℕ) (n i : ℕ) : Prop :=
  i < n ∧ ∀ j, j < i →
    (req j).release - R (req j).position <
      (req i).release - R (req i).position

def RightRecord (L : ℕ → ℝ) (req : ℕ → Request ℕ) (n i : ℕ) : Prop :=
  i < n ∧ ∀ j, i < j → j < n →
    (req j).release + L (req j).position <
      (req i).release + L (req i).position

/-- A later left record has a strictly later release than every earlier request. -/
theorem left_record_release (R : ℕ → ℝ) (hR : Monotone R)
    (req : ℕ → Request ℕ) (n i j : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (hi : LeftRecord R req n i) (hji : j < i) :
    (req j).release < (req i).release := by
  have h := hi.2 j hji
  have hd := hR (hpos j i (Nat.le_of_lt hji) hi.1)
  linarith

/-- A right record has a strictly later release than every request to its right. -/
theorem right_record_release (L : ℕ → ℝ) (hL : Monotone L)
    (req : ℕ → Request ℕ) (n i j : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (hi : RightRecord L req n i) (hij : i < j) (hjn : j < n) :
    (req j).release < (req i).release := by
  have h := hi.2 j hij hjn
  have hd := hL (hpos i j (Nat.le_of_lt hij) hjn)
  linarith

/-- Every left-record index lies at or before every right-record index. -/
theorem records_separated (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (req : ℕ → Request ℕ) (n i j : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (hi : LeftRecord R req n i) (hj : RightRecord L req n j) : i ≤ j := by
  by_contra h
  have hji : j < i := by omega
  have h₁ := left_record_release R hR req n i j hpos hi hji
  have h₂ := right_record_release L hL req n j i hpos hj hji hi.1
  linarith

/-- The position-separation hypothesis used by indexed return merging follows from records. -/
theorem record_positions_separated (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L)
    (req : ℕ → Request ℕ) (n i j : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (hi : LeftRecord R req n i) (hj : RightRecord L req n j) :
    (req i).position ≤ (req j).position := by
  exact hpos i j (records_separated R L hR hL req n i j hpos hi hj) hj.1

/-- The chains can share at most one original request index. -/
theorem common_record_unique (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L)
    (req : ℕ → Request ℕ) (n i j : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (hiL : LeftRecord R req n i) (hiR : RightRecord L req n i)
    (hjL : LeftRecord R req n j) (hjR : RightRecord L req n j) : i = j := by
  exact Nat.le_antisymm
    (records_separated R L hR hL req n i j hpos hiL hjR)
    (records_separated R L hR hL req n j i hpos hjL hiR)

/-- A prefix maximum can be chosen to be a strict record, even when offsets tie. -/
theorem prefix_record_max (f : ℕ → ℝ) (i : ℕ) :
    ∃ k, k ≤ i ∧ (∀ j, j < k → f j < f k) ∧
      (∀ j, j ≤ i → f j ≤ f k) := by
  induction i with
  | zero =>
    refine ⟨0, le_rfl, ?_, ?_⟩
    · intro j hj
      omega
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact le_rfl
  | succ i ih =>
    obtain ⟨k, hki, hk, hmax⟩ := ih
    by_cases h : f (i + 1) ≤ f k
    · refine ⟨k, by omega, hk, ?_⟩
      intro j hj
      by_cases hji : j ≤ i
      · exact hmax j hji
      · have : j = i + 1 := by omega
        subst j
        exact h
    · have hlt : f k < f (i + 1) := lt_of_not_ge h
      refine ⟨i + 1, le_rfl, ?_, ?_⟩
      · intro j hj
        exact lt_of_le_of_lt (hmax j (by omega)) hlt
      · intro j hj
        by_cases hji : j ≤ i
        · exact le_trans (hmax j hji) (le_of_lt hlt)
        · have : j = i + 1 := by omega
          subst j
          exact le_rfl

/-- Each request has a left-record witness whose offset is at least its own. -/
theorem left_record_witness (R : ℕ → ℝ) (req : ℕ → Request ℕ)
    (n i : ℕ) (hi : i < n) :
    ∃ k, k ≤ i ∧ LeftRecord R req n k ∧
      (req i).release - R (req i).position ≤
        (req k).release - R (req k).position := by
  obtain ⟨k, hki, hk, hmax⟩ :=
    prefix_record_max (fun j => (req j).release - R (req j).position) i
  exact ⟨k, hki, ⟨by omega, hk⟩, hmax i le_rfl⟩

/-- Reverse the finite input to obtain the symmetric right-record witness. -/
theorem right_record_witness (L : ℕ → ℝ) (req : ℕ → Request ℕ)
    (n i : ℕ) (hi : i < n) :
    ∃ k, i ≤ k ∧ RightRecord L req n k ∧
      (req i).release + L (req i).position ≤
        (req k).release + L (req k).position := by
  let f := fun j => (req (n - 1 - j)).release + L (req (n - 1 - j)).position
  obtain ⟨k, hki, hk, hmax⟩ := prefix_record_max f (n - 1 - i)
  refine ⟨n - 1 - k, by omega, ⟨by omega, ?_⟩, ?_⟩
  · intro j hj hjn
    have hjk : n - 1 - j < k := by omega
    have heq : n - 1 - (n - 1 - j) = j := by omega
    have hh := hk (n - 1 - j) hjk
    simpa only [f, heq] using hh
  · have heq : n - 1 - (n - 1 - i) = i := by omega
    have hh := hmax (n - 1 - i) le_rfl
    simpa only [f, heq] using hh

/-- Declarative sets of retained original indices; no implementation claim. -/
noncomputable def leftRecordIndices (R : ℕ → ℝ) (req : ℕ → Request ℕ)
    (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (LeftRecord R req n)

noncomputable def rightRecordIndices (L : ℕ → ℝ) (req : ℕ → Request ℕ)
    (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (RightRecord L req n)

/-- Count both chains, including their possible common index twice. -/
theorem record_count_bound (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L)
    (req : ℕ → Request ℕ) (n : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position) :
    (leftRecordIndices R req n).card + (rightRecordIndices L req n).card ≤ n + 1 := by
  classical
  let ls := leftRecordIndices R req n
  let rs := rightRecordIndices L req n
  have hunion : ls ∪ rs ⊆ Finset.range n := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_filter.mp hi).1
    · exact (Finset.mem_filter.mp hi).1
  have hcard : (ls ∪ rs).card ≤ n := by
    simpa using Finset.card_le_card hunion
  have hinter : (ls ∩ rs).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hiL, hiR⟩ := Finset.mem_inter.mp hi
    obtain ⟨hjL, hjR⟩ := Finset.mem_inter.mp hj
    exact common_record_unique R L hR hL req n i j hpos
      (Finset.mem_filter.mp hiL).2 (Finset.mem_filter.mp hiR).2
      (Finset.mem_filter.mp hjL).2 (Finset.mem_filter.mp hjR).2
  have heq := Finset.card_union_add_card_inter ls rs
  change ls.card + rs.card ≤ n + 1
  omega

def VisitsRequest (q : Request ℕ) (vs : List (ℕ × ℝ)) : Prop :=
  ∃ v ∈ vs, v.1 = q.position ∧ q.release ≤ v.2

/-- On any route that eventually reaches the other side, insert the request
at the first crossing. Original visits, terminal, and finish are preserved. -/
theorem right_crossing_insert (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (q : Request ℕ) (goal : ℕ) (finish : ℝ) (vs : List (ℕ × ℝ)) :
    ∀ x t, x ≤ q.position → q.release ≤ t + R q.position - R x →
      timedRoute (pathDist R L) x t (vs ++ [(goal, finish)]) →
      (∃ v ∈ vs ++ [(goal, finish)], q.position ≤ v.1) →
      ∃ ws, timedRoute (pathDist R L) x t (ws ++ [(goal, finish)]) ∧
        (∀ v ∈ vs ++ [(goal, finish)], v ∈ ws ++ [(goal, finish)]) ∧
        VisitsRequest q (ws ++ [(goal, finish)]) := by
  induction vs with
  | nil =>
    intro x t hx hr ht hex
    obtain ⟨v, hv, hqv⟩ := hex
    have heq : v = (goal, finish) := by simpa using hv
    subst v
    have hqg : q.position ≤ goal := hqv
    have hrel : q.release ≤ t + pathDist R L x q.position := by
      rw [pathDist_right R L hx]
      linarith
    refine ⟨[(q.position, t + pathDist R L x q.position)], ?_, ?_, ?_⟩
    · exact insert_route_visit (pathDist R L) x q.position goal t finish []
        (pathDist_right_add R L hx hqg) ht
    · intro w hw
      exact List.mem_cons_of_mem _ hw
    · exact ⟨(q.position, t + pathDist R L x q.position), by simp, rfl, hrel⟩
  | cons v rest ih =>
    intro x t hx hr ht hex
    by_cases hqv : q.position ≤ v.1
    · have hrel : q.release ≤ t + pathDist R L x q.position := by
        rw [pathDist_right R L hx]
        linarith
      refine ⟨(q.position, t + pathDist R L x q.position) :: v :: rest, ?_, ?_, ?_⟩
      · exact insert_route_visit (pathDist R L) x q.position v.1 t v.2
          (rest ++ [(goal, finish)]) (pathDist_right_add R L hx hqv) ht
      · intro w hw
        exact List.mem_cons_of_mem _ hw
      · exact ⟨(q.position, t + pathDist R L x q.position), by simp, rfl, hrel⟩
    · have hvq : v.1 ≤ q.position := by omega
      have hdelta := pathDist_ge_right_delta R L hR hL x v.1
      have hfirst := ht.1
      have hrel : q.release ≤ v.2 + R q.position - R v.1 := by linarith
      have htail : ∃ w ∈ rest ++ [(goal, finish)], q.position ≤ w.1 := by
        obtain ⟨w, hw, hqw⟩ := hex
        rcases List.mem_cons.mp hw with heq | hw
        · subst w
          exact False.elim (hqv hqw)
        · exact ⟨w, hw, hqw⟩
      obtain ⟨ws, hws, hsub, hserv⟩ := ih v.1 v.2 hvq hrel ht.2 htail
      refine ⟨v :: ws, ⟨ht.1, hws⟩, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with heq | hw
        · subst w
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)
      · obtain ⟨w, hw, hp, hr⟩ := hserv
        exact ⟨w, List.mem_cons_of_mem _ hw, hp, hr⟩

/-- On any route that eventually reaches the other side, insert the request
at the first crossing. Original visits, terminal, and finish are preserved. -/
theorem left_crossing_insert (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (q : Request ℕ) (goal : ℕ) (finish : ℝ) (vs : List (ℕ × ℝ)) :
    ∀ x t, q.position ≤ x → q.release ≤ t + L x - L q.position →
      timedRoute (pathDist R L) x t (vs ++ [(goal, finish)]) →
      (∃ v ∈ vs ++ [(goal, finish)], v.1 ≤ q.position) →
      ∃ ws, timedRoute (pathDist R L) x t (ws ++ [(goal, finish)]) ∧
        (∀ v ∈ vs ++ [(goal, finish)], v ∈ ws ++ [(goal, finish)]) ∧
        VisitsRequest q (ws ++ [(goal, finish)]) := by
  induction vs with
  | nil =>
    intro x t hx hr ht hex
    obtain ⟨v, hv, hqv⟩ := hex
    have heq : v = (goal, finish) := by simpa using hv
    subst v
    have hqg : goal ≤ q.position := hqv
    have hrel : q.release ≤ t + pathDist R L x q.position := by
      rw [pathDist_left R L hx]
      linarith
    refine ⟨[(q.position, t + pathDist R L x q.position)], ?_, ?_, ?_⟩
    · exact insert_route_visit (pathDist R L) x q.position goal t finish []
        (pathDist_left_add R L hx hqg) ht
    · intro w hw
      exact List.mem_cons_of_mem _ hw
    · exact ⟨(q.position, t + pathDist R L x q.position), by simp, rfl, hrel⟩
  | cons v rest ih =>
    intro x t hx hr ht hex
    by_cases hqv : v.1 ≤ q.position
    · have hrel : q.release ≤ t + pathDist R L x q.position := by
        rw [pathDist_left R L hx]
        linarith
      refine ⟨(q.position, t + pathDist R L x q.position) :: v :: rest, ?_, ?_, ?_⟩
      · exact insert_route_visit (pathDist R L) x q.position v.1 t v.2
          (rest ++ [(goal, finish)]) (pathDist_left_add R L hx hqv) ht
      · intro w hw
        exact List.mem_cons_of_mem _ hw
      · exact ⟨(q.position, t + pathDist R L x q.position), by simp, rfl, hrel⟩
    · have hvq : q.position ≤ v.1 := by omega
      have hdelta := pathDist_ge_left_delta R L hR hL x v.1
      have hfirst := ht.1
      have hrel : q.release ≤ v.2 + L v.1 - L q.position := by linarith
      have htail : ∃ w ∈ rest ++ [(goal, finish)], w.1 ≤ q.position := by
        obtain ⟨w, hw, hqw⟩ := hex
        rcases List.mem_cons.mp hw with heq | hw
        · subst w
          exact False.elim (hqv hqw)
        · exact ⟨w, hw, hqw⟩
      obtain ⟨ws, hws, hsub, hserv⟩ := ih v.1 v.2 hvq hrel ht.2 htail
      refine ⟨v :: ws, ⟨ht.1, hws⟩, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with heq | hw
        · subst w
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)
      · obtain ⟨w, hw, hp, hr⟩ := hserv
        exact ⟨w, List.mem_cons_of_mem _ hw, hp, hr⟩

/-- Two served witnesses on opposite sides suffice to insert an interior
request. Their service order is not prescribed. -/
theorem two_witness_insert (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (p q r : Request ℕ) (hpq : p.position ≤ q.position)
    (hqr : q.position ≤ r.position)
    (hqp : q.release - R q.position ≤ p.release - R p.position)
    (hqr' : q.release + L q.position ≤ r.release + L r.position)
    (goal : ℕ) (finish : ℝ) (vs : List (ℕ × ℝ)) :
    ∀ x t, timedRoute (pathDist R L) x t (vs ++ [(goal, finish)]) →
      VisitsRequest p (vs ++ [(goal, finish)]) →
      VisitsRequest r (vs ++ [(goal, finish)]) →
      ∃ ws, timedRoute (pathDist R L) x t (ws ++ [(goal, finish)]) ∧
        (∀ v ∈ vs ++ [(goal, finish)], v ∈ ws ++ [(goal, finish)]) ∧
        VisitsRequest q (ws ++ [(goal, finish)]) := by
  induction vs with
  | nil =>
    intro x t ht hp hr
    obtain ⟨a, ha, hap, hpa⟩ := hp
    obtain ⟨b, hb, hbr, hrb⟩ := hr
    have hea : a = (goal, finish) := by simpa using ha
    have heb : b = (goal, finish) := by simpa using hb
    subst a
    subst b
    have hpg : goal = p.position := hap
    have hrg : goal = r.position := hbr
    have hqg : q.position = goal := by omega
    have htime : p.release ≤ finish := hpa
    have hrel : q.release ≤ finish := by
      rw [hqg, ← hpg] at hqp
      linarith
    exact ⟨[], ht, fun _ hv => hv, (goal, finish), by simp, hqg.symm, hrel⟩
  | cons v rest ih =>
    intro x t ht hp hr
    have extend : ∀ ws,
        timedRoute (pathDist R L) v.1 v.2 (ws ++ [(goal, finish)]) →
        (∀ w ∈ rest ++ [(goal, finish)], w ∈ ws ++ [(goal, finish)]) →
        VisitsRequest q (ws ++ [(goal, finish)]) →
        ∃ ys, timedRoute (pathDist R L) x t (ys ++ [(goal, finish)]) ∧
          (∀ w ∈ (v :: rest) ++ [(goal, finish)], w ∈ ys ++ [(goal, finish)]) ∧
          VisitsRequest q (ys ++ [(goal, finish)]) := by
      intro ws hws hsub hserv
      refine ⟨v :: ws, ⟨ht.1, hws⟩, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with heq | hw
        · subst w
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw)
      · obtain ⟨w, hw, heq, hrel⟩ := hserv
        exact ⟨w, List.mem_cons_of_mem _ hw, heq, hrel⟩
    by_cases hphead : v.1 = p.position ∧ p.release ≤ v.2
    · by_cases hrhead : v.1 = r.position ∧ r.release ≤ v.2
      · have hqv : q.position = v.1 := by omega
        have hrel : q.release ≤ v.2 := by
          rw [hqv, ← hphead.1] at hqp
          linarith [hphead.2]
        exact ⟨v :: rest, ht, fun _ hv => hv, v, by simp, hqv.symm, hrel⟩
      · have hcross : ∃ w ∈ rest ++ [(goal, finish)], q.position ≤ w.1 := by
          obtain ⟨w, hw, heq, hrel⟩ := hr
          rcases List.mem_cons.mp hw with he | hw
          · subst w
            exact False.elim (hrhead ⟨heq, hrel⟩)
          · exact ⟨w, hw, by rw [heq]; exact hqr⟩
        have hvq : v.1 ≤ q.position := by rw [hphead.1]; exact hpq
        have hrel : q.release ≤ v.2 + R q.position - R v.1 := by
          rw [hphead.1]
          linarith [hphead.2]
        obtain ⟨ws, hws, hsub, hs⟩ :=
          right_crossing_insert R L hR hL q goal finish rest v.1 v.2 hvq hrel ht.2 hcross
        exact extend ws hws hsub hs
    · have hptail : VisitsRequest p (rest ++ [(goal, finish)]) := by
        obtain ⟨w, hw, heq, hrel⟩ := hp
        rcases List.mem_cons.mp hw with he | hw
        · subst w
          exact False.elim (hphead ⟨heq, hrel⟩)
        · exact ⟨w, hw, heq, hrel⟩
      by_cases hrhead : v.1 = r.position ∧ r.release ≤ v.2
      · have hcross : ∃ w ∈ rest ++ [(goal, finish)], w.1 ≤ q.position := by
          obtain ⟨w, hw, heq, _⟩ := hptail
          exact ⟨w, hw, by rw [heq]; exact hpq⟩
        have hqv : q.position ≤ v.1 := by rw [hrhead.1]; exact hqr
        have hrel : q.release ≤ v.2 + L v.1 - L q.position := by
          rw [hrhead.1]
          linarith [hrhead.2]
        obtain ⟨ws, hws, hsub, hs⟩ :=
          left_crossing_insert R L hR hL q goal finish rest v.1 v.2 hqv hrel ht.2 hcross
        exact extend ws hws hsub hs
      · have hrtail : VisitsRequest r (rest ++ [(goal, finish)]) := by
          obtain ⟨w, hw, heq, hrel⟩ := hr
          rcases List.mem_cons.mp hw with he | hw
          · subst w
            exact False.elim (hrhead ⟨heq, hrel⟩)
          · exact ⟨w, hw, heq, hrel⟩
        obtain ⟨ws, hws, hsub, hs⟩ := ih v.1 v.2 ht.2 hptail hrtail
        exact extend ws hws hsub hs

/-- Add one request without changing the terminal or finish time. -/
theorem witness_plan_insert (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (p q r : Request ℕ) (hpq : p.position ≤ q.position)
    (hqr : q.position ≤ r.position)
    (hqp : q.release - R q.position ≤ p.release - R p.position)
    (hqr' : q.release + L q.position ≤ r.release + L r.position)
    (x : ℕ) (t : ℝ) (remaining : Set (Request ℕ)) (goals : Set ℕ)
    (plan : Plan ℕ) (hp : p ∈ remaining) (hr : r ∈ remaining)
    (h : feasible (pathDist R L) x t remaining goals plan) :
    ∃ ws, feasible (pathDist R L) x t (insert q remaining) goals
      ⟨ws, plan.terminal, plan.finish⟩ := by
  obtain ⟨ws, ht, hsub, hserv⟩ := two_witness_insert R L hR hL p q r hpq hqr hqp hqr'
    plan.terminal plan.finish plan.visits x t h.1 (h.2.1 p hp) (h.2.1 r hr)
  refine ⟨ws, ht, ?_, h.2.2⟩
  intro a ha
  rcases ha with heq | ha
  · subst a
    exact hserv
  · exact serves_mono_visits remaining _ _ hsub h.2.1 a ha

/-- Restore finitely many requests while retaining every already served task. -/
theorem restore_witness_list (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (x : ℕ) (t : ℝ) (kept : Set (Request ℕ)) (goals : Set ℕ)
    (goal : ℕ) (finish : ℝ) (todo : List (Request ℕ)) :
    (∀ q ∈ todo, ∃ p ∈ kept, ∃ r ∈ kept,
      p.position ≤ q.position ∧ q.position ≤ r.position ∧
      q.release - R q.position ≤ p.release - R p.position ∧
      q.release + L q.position ≤ r.release + L r.position) →
    ∀ vs, feasible (pathDist R L) x t kept goals ⟨vs, goal, finish⟩ →
      ∃ ws, feasible (pathDist R L) x t (kept ∪ {q | q ∈ todo}) goals
        ⟨ws, goal, finish⟩ := by
  induction todo with
  | nil =>
    intro _ vs h
    exact ⟨vs, by simpa using h⟩
  | cons q todo ih =>
    intro hwitness vs h
    have htailw : ∀ a ∈ todo, ∃ p ∈ kept, ∃ r ∈ kept,
        p.position ≤ a.position ∧ a.position ≤ r.position ∧
        a.release - R a.position ≤ p.release - R p.position ∧
        a.release + L a.position ≤ r.release + L r.position := by
      intro a ha
      exact hwitness a (List.mem_cons_of_mem _ ha)
    obtain ⟨ws, hws⟩ := ih htailw vs h
    obtain ⟨p, hp, r, hr, hpq, hqr, hqp, hqr'⟩ := hwitness q (by simp)
    obtain ⟨ys, hys⟩ := witness_plan_insert R L hR hL p q r hpq hqr hqp hqr'
      x t (kept ∪ {a | a ∈ todo}) goals ⟨ws, goal, finish⟩ (Or.inl hp) (Or.inl hr) hws
    have heq : insert q (kept ∪ {a | a ∈ todo}) = kept ∪ {a | a ∈ q :: todo} := by
      ext a
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, List.mem_cons]
      tauto
    exact ⟨ys, by simpa only [heq] using hys⟩

def originalRequests (req : ℕ → Request ℕ) (n : ℕ) : Set (Request ℕ) :=
  {q | ∃ i, i < n ∧ req i = q}

def recordRequests (R L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) : Set (Request ℕ) :=
  {q | ∃ i, (LeftRecord R req n i ∨ RightRecord L req n i) ∧ req i = q}

theorem record_requests_subset (R L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) :
    recordRequests R L req n ⊆ originalRequests req n := by
  intro q hq
  obtain ⟨i, hi, heq⟩ := hq
  rcases hi with hi | hi
  · exact ⟨i, hi.1, heq⟩
  · exact ⟨i, hi.1, heq⟩

/-- Critical-request reduction preserves each feasible finish and terminal,
for arbitrary starts and arbitrary allowed terminal sets in the finite-visit model. -/
theorem record_elimination_restore (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (req : ℕ → Request ℕ) (n : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (plan : Plan ℕ)
    (h : feasible (pathDist R L) x t (recordRequests R L req n) goals plan) :
    ∃ ws, feasible (pathDist R L) x t (originalRequests req n) goals
      ⟨ws, plan.terminal, plan.finish⟩ := by
  have hw : ∀ q ∈ chainSegment req 0 n,
      ∃ p ∈ recordRequests R L req n, ∃ r ∈ recordRequests R L req n,
        p.position ≤ q.position ∧ q.position ≤ r.position ∧
        q.release - R q.position ≤ p.release - R p.position ∧
        q.release + L q.position ≤ r.release + L r.position := by
    intro q hq
    obtain ⟨i, _, hin, heq⟩ := (chainSegment_mem req n 0 q).mp hq
    have hi : i < n := by omega
    subst q
    obtain ⟨a, hai, ha, hqa⟩ := left_record_witness R req n i hi
    obtain ⟨b, hib, hb, hqb⟩ := right_record_witness L req n i hi
    exact ⟨req a, ⟨a, Or.inl ha, rfl⟩, req b, ⟨b, Or.inr hb, rfl⟩,
      hpos a i hai hi, hpos i b hib hb.1, hqa, hqb⟩
  obtain ⟨ws, hws⟩ := restore_witness_list R L hR hL x t
    (recordRequests R L req n) goals plan.terminal plan.finish (chainSegment req 0 n)
    hw plan.visits h
  have hlist : {q | q ∈ chainSegment req 0 n} = originalRequests req n := by
    ext q
    simp only [Set.mem_ofPred_eq, originalRequests, chainSegment_mem]
    constructor
    · rintro ⟨i, _, hin, heq⟩
      exact ⟨i, by omega, heq⟩
    · rintro ⟨i, hin, heq⟩
      exact ⟨i, by omega, by omega, heq⟩
  have hunion : recordRequests R L req n ∪ originalRequests req n = originalRequests req n :=
    Set.union_eq_right.mpr (record_requests_subset R L req n)
  exact ⟨ws, by simpa only [hlist, hunion] using hws⟩

/-- Equality of feasible terminal/finish pairs; hence any minimum over them
is unchanged. -/
theorem record_elimination_iff (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (req : ℕ → Request ℕ) (n : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t (recordRequests R L req n) goals ⟨vs, goal, finish⟩) ↔
      (∃ vs, feasible (pathDist R L) x t (originalRequests req n) goals ⟨vs, goal, finish⟩) := by
  constructor
  · rintro ⟨vs, hvs⟩
    exact record_elimination_restore R L hR hL req n hpos x t goals ⟨vs, goal, finish⟩ hvs
  · rintro ⟨vs, hvs⟩
    refine ⟨vs, hvs.1, ?_, hvs.2.2⟩
    intro q hq
    exact hvs.2.1 q (record_requests_subset R L req n hq)

/-- Any route serving a mandatory position must pay both legs to the terminal. -/
theorem timedRoute_through_finish (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (goal y : ℕ) (finish arrival : ℝ) (vs : List (ℕ × ℝ)) :
    ∀ x t, timedRoute (pathDist R L) x t (vs ++ [(goal, finish)]) →
      (y, arrival) ∈ vs ++ [(goal, finish)] →
      t + pathDist R L x y + pathDist R L y goal ≤ finish := by
  induction vs with
  | nil =>
    intro x t ht hm
    have heq : (y, arrival) = (goal, finish) := by simpa using hm
    have hy : y = goal := congrArg Prod.fst heq
    subst y
    simpa only [pathDist_self, add_zero] using ht.1
  | cons v rest ih =>
    intro x t ht hm
    rcases List.mem_cons.mp hm with heq | hm
    · have hy : y = v.1 := congrArg Prod.fst heq
      subst y
      have htail := timedRoute_visit_lower_bound (pathDist R L)
        (pathDist_triangle R L hR hL) (rest ++ [(goal, finish)]) goal finish v.1 v.2 ht.2
        (by simp)
      linarith [ht.1]
    · have htail := ih v.1 v.2 ht.2 hm
      have htri := pathDist_triangle R L hR hL x v.1 y
      linarith [ht.1]

theorem mandatory_finish_lower_bound (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x : ℕ) (t : ℝ)
    (remaining : Set (Request ℕ)) (goals : Set ℕ) (plan : Plan ℕ)
    (q : Request ℕ) (hq : q ∈ remaining)
    (h : feasible (pathDist R L) x t remaining goals plan) :
    t + pathDist R L x q.position + pathDist R L q.position plan.terminal ≤ plan.finish := by
  obtain ⟨v, hv, hp, _⟩ := h.2.1 q hq
  have hv' : (q.position, v.2) ∈ plan.visits ++ [(plan.terminal, plan.finish)] := by
    simpa only [← hp] using hv
  exact timedRoute_through_finish R L hR hL plan.terminal q.position plan.finish v.2
    plan.visits x t h.1 hv'

/-- A rightward sweep is feasible under the offset test, including requests
released during the sweep. The terminal may be anywhere. -/
theorem right_completion_feasible (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y goal : ℕ) (t : ℝ)
    (goals : Set ℕ) (hgoal : goal ∈ goals) (hxy : x ≤ y)
    (todo : List (Request ℕ))
    (hpos : ∀ q ∈ todo, x ≤ q.position ∧ q.position ≤ y)
    (hoff : ∀ q ∈ todo, q.release - R q.position ≤ t - R x) :
    ∃ ws, feasible (pathDist R L) x t {q | q ∈ todo} goals
      ⟨ws, goal, t + pathDist R L x y + pathDist R L y goal⟩ := by
  let a : Request ℕ := ⟨x, t⟩
  let b : Request ℕ := ⟨y, t + pathDist R L x y⟩
  let kept : Set (Request ℕ) := {a, b}
  let fin := t + pathDist R L x y + pathDist R L y goal
  have hbase : feasible (pathDist R L) x t kept goals
      ⟨[(x, t), (y, t + pathDist R L x y)], goal, fin⟩ := by
    refine ⟨?_, ?_, hgoal⟩
    · change t + pathDist R L x x ≤ t ∧
        t + pathDist R L x y ≤ t + pathDist R L x y ∧
        t + pathDist R L x y + pathDist R L y goal ≤ fin ∧ True
      simp [pathDist_self, fin]
    · intro q hq
      rcases hq with heq | hq
      · subst q
        exact ⟨(x, t), by simp, rfl, le_rfl⟩
      · have heq : q = b := hq
        subst q
        exact ⟨(y, t + pathDist R L x y), by simp, rfl, le_rfl⟩
  have hw : ∀ q ∈ todo, ∃ p ∈ kept, ∃ r ∈ kept,
      p.position ≤ q.position ∧ q.position ≤ r.position ∧
      q.release - R q.position ≤ p.release - R p.position ∧
      q.release + L q.position ≤ r.release + L r.position := by
    intro q hq
    obtain ⟨hxq, hqy⟩ := hpos q hq
    have h := hoff q hq
    have hRqy := hR hqy
    have hLqy := hL hqy
    refine ⟨a, by simp [kept], b, by simp [kept], hxq, hqy, h, ?_⟩
    change q.release + L q.position ≤ t + pathDist R L x y + L y
    rw [pathDist_right R L hxy]
    linarith
  obtain ⟨ws, hws⟩ := restore_witness_list R L hR hL x t kept goals goal fin todo hw
    [(x, t), (y, t + pathDist R L x y)] hbase
  refine ⟨ws, hws.1, ?_, hws.2.2⟩
  intro q hq
  exact hws.2.1 q (Or.inr hq)

theorem left_completion_feasible (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y goal : ℕ) (t : ℝ)
    (goals : Set ℕ) (hgoal : goal ∈ goals) (hxy : y ≤ x)
    (todo : List (Request ℕ))
    (hpos : ∀ q ∈ todo, y ≤ q.position ∧ q.position ≤ x)
    (hoff : ∀ q ∈ todo, q.release + L q.position ≤ t + L x) :
    ∃ ws, feasible (pathDist R L) x t {q | q ∈ todo} goals
      ⟨ws, goal, t + pathDist R L x y + pathDist R L y goal⟩ := by
  let a : Request ℕ := ⟨y, t + pathDist R L x y⟩
  let b : Request ℕ := ⟨x, t⟩
  let kept : Set (Request ℕ) := {a, b}
  let fin := t + pathDist R L x y + pathDist R L y goal
  have hbase : feasible (pathDist R L) x t kept goals
      ⟨[(x, t), (y, t + pathDist R L x y)], goal, fin⟩ := by
    refine ⟨?_, ?_, hgoal⟩
    · change t + pathDist R L x x ≤ t ∧
        t + pathDist R L x y ≤ t + pathDist R L x y ∧
        t + pathDist R L x y + pathDist R L y goal ≤ fin ∧ True
      simp [pathDist_self, fin]
    · intro q hq
      rcases hq with heq | hq
      · subst q
        exact ⟨(y, t + pathDist R L x y), by simp, rfl, le_rfl⟩
      · have heq : q = b := hq
        subst q
        exact ⟨(x, t), by simp, rfl, le_rfl⟩
  have hw : ∀ q ∈ todo, ∃ p ∈ kept, ∃ r ∈ kept,
      p.position ≤ q.position ∧ q.position ≤ r.position ∧
      q.release - R q.position ≤ p.release - R p.position ∧
      q.release + L q.position ≤ r.release + L r.position := by
    intro q hq
    obtain ⟨hyq, hqx⟩ := hpos q hq
    have h := hoff q hq
    have hRyq := hR hyq
    have hLyq := hL hyq
    refine ⟨a, by simp [kept], b, by simp [kept], hyq, hqx, ?_, h⟩
    change q.release - R q.position ≤ t + pathDist R L x y - R y
    rw [pathDist_left R L hxy]
    linarith
  obtain ⟨ws, hws⟩ := restore_witness_list R L hR hL x t kept goals goal fin todo hw
    [(x, t), (y, t + pathDist R L x y)] hbase
  refine ⟨ws, hws.1, ?_, hws.2.2⟩
  intro q hq
  exact hws.2.1 q (Or.inr hq)

theorem right_completion_optimal (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y goal : ℕ) (t : ℝ)
    (goals : Set ℕ) (hgoal : goal ∈ goals) (hxy : x ≤ y)
    (todo : List (Request ℕ))
    (hpos : ∀ q ∈ todo, x ≤ q.position ∧ q.position ≤ y)
    (hoff : ∀ q ∈ todo, q.release - R q.position ≤ t - R x)
    (hmandatory : ∃ q ∈ todo, q.position = y) :
    (∃ ws, feasible (pathDist R L) x t {q | q ∈ todo} goals
      ⟨ws, goal, t + pathDist R L x y + pathDist R L y goal⟩) ∧
    ∀ vs finish, feasible (pathDist R L) x t {q | q ∈ todo} goals ⟨vs, goal, finish⟩ →
      t + pathDist R L x y + pathDist R L y goal ≤ finish := by
  refine ⟨right_completion_feasible R L hR hL x y goal t goals hgoal hxy todo hpos hoff, ?_⟩
  intro vs finish h
  obtain ⟨q, hq, hqy⟩ := hmandatory
  have hb := mandatory_finish_lower_bound R L hR hL x t {q | q ∈ todo} goals
    ⟨vs, goal, finish⟩ q hq h
  simpa only [hqy] using hb

theorem left_completion_optimal (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (x y goal : ℕ) (t : ℝ)
    (goals : Set ℕ) (hgoal : goal ∈ goals) (hxy : y ≤ x)
    (todo : List (Request ℕ))
    (hpos : ∀ q ∈ todo, y ≤ q.position ∧ q.position ≤ x)
    (hoff : ∀ q ∈ todo, q.release + L q.position ≤ t + L x)
    (hmandatory : ∃ q ∈ todo, q.position = y) :
    (∃ ws, feasible (pathDist R L) x t {q | q ∈ todo} goals
      ⟨ws, goal, t + pathDist R L x y + pathDist R L y goal⟩) ∧
    ∀ vs finish, feasible (pathDist R L) x t {q | q ∈ todo} goals ⟨vs, goal, finish⟩ →
      t + pathDist R L x y + pathDist R L y goal ≤ finish := by
  refine ⟨left_completion_feasible R L hR hL x y goal t goals hgoal hxy todo hpos hoff, ?_⟩
  intro vs finish h
  obtain ⟨q, hq, hqy⟩ := hmandatory
  have hb := mandatory_finish_lower_bound R L hR hL x t {q | q ∈ todo} goals
    ⟨vs, goal, finish⟩ q hq h
  simpa only [hqy] using hb

noncomputable def recordScan (f : ℕ → ℝ) : ℕ → ℕ × List ℕ
  | 0 => (0, [0])
  | n + 1 =>
    let prev := recordScan f n
    if f prev.1 < f (n + 1) then (n + 1, (n + 1) :: prev.2) else prev

/-- The retained head is a prefix maximum; comparisons use its value only. -/
theorem recordScan_max (f : ℕ → ℝ) (n : ℕ) :
    (recordScan f n).1 ≤ n ∧ ∀ j, j ≤ n → f j ≤ f (recordScan f n).1 := by
  induction n with
  | zero =>
    constructor
    · simp [recordScan]
    · intro j hj
      have : j = 0 := by omega
      subst j
      simp [recordScan]
  | succ n ih =>
    by_cases h : f (recordScan f n).1 < f (n + 1)
    · simp only [recordScan, h, ↓reduceIte]
      refine ⟨le_rfl, ?_⟩
      intro j hj
      by_cases hjn : j ≤ n
      · exact le_trans (ih.2 j hjn) (le_of_lt h)
      · have : j = n + 1 := by omega
        subst j
        exact le_rfl
    · simp only [recordScan, h, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      intro j hj
      by_cases hjn : j ≤ n
      · exact ih.2 j hjn
      · have : j = n + 1 := by omega
        subst j
        exact le_of_not_gt h

/-- The simple scan retains exactly the strict records, including the first index. -/
theorem recordScan_mem (f : ℕ → ℝ) (n j : ℕ) :
    j ∈ (recordScan f n).2 ↔ j ≤ n ∧ ∀ k, k < j → f k < f j := by
  induction n with
  | zero =>
    simp [recordScan]
    intro hj
    subst j
    intro k hk
    omega
  | succ n ih =>
    have hmax := recordScan_max f n
    by_cases h : f (recordScan f n).1 < f (n + 1)
    · simp only [recordScan, h, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (heq | hj)
        · subst j
          exact ⟨le_rfl, fun k hk => lt_of_le_of_lt (hmax.2 k (by omega)) h⟩
        · obtain ⟨hjn, hjrec⟩ := ih.mp hj
          exact ⟨by omega, hjrec⟩
      · rintro ⟨hjn, hjrec⟩
        by_cases hj : j = n + 1
        · exact Or.inl hj
        · exact Or.inr (ih.mpr ⟨by omega, hjrec⟩)
    · simp only [recordScan, h, ↓reduceIte]
      constructor
      · intro hj
        obtain ⟨hjn, hjrec⟩ := ih.mp hj
        exact ⟨by omega, hjrec⟩
      · rintro ⟨hjn, hjrec⟩
        have hjne : j ≠ n + 1 := by
          intro heq
          subst j
          exact h (hjrec (recordScan f n).1 (by omega))
        exact ih.mpr ⟨by omega, hjrec⟩

theorem recordScan_pairwise (f : ℕ → ℝ) (n : ℕ) :
    (recordScan f n).2.Pairwise (fun i j => j < i) := by
  induction n with
  | zero => simp [recordScan]
  | succ n ih =>
    by_cases h : f (recordScan f n).1 < f (n + 1)
    · simp only [recordScan, h, ↓reduceIte, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro j hj
      have hjn := ((recordScan_mem f n j).mp hj).1
      omega
    · simpa only [recordScan, h, ↓reduceIte] using ih

noncomputable def increasingRecords (f : ℕ → ℝ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (recordScan f n).2.reverse

theorem increasingRecords_mem (f : ℕ → ℝ) (n j : ℕ) :
    j ∈ increasingRecords f n ↔ j < n ∧ ∀ k, k < j → f k < f j := by
  cases n with
  | zero => simp [increasingRecords]
  | succ n =>
    simp only [increasingRecords, List.mem_reverse, recordScan_mem]
    constructor <;> rintro ⟨hj, hk⟩ <;> exact ⟨by omega, hk⟩

theorem increasingRecords_pairwise (f : ℕ → ℝ) (n : ℕ) :
    (increasingRecords f n).Pairwise (fun i j => i < j) := by
  cases n with
  | zero => simp [increasingRecords]
  | succ n =>
    simpa only [increasingRecords, List.pairwise_reverse] using recordScan_pairwise f n

noncomputable def leftRecordScan (R : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) : List ℕ :=
  increasingRecords (fun i => (req i).release - R (req i).position) n

noncomputable def rightRecordScan (L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) : List ℕ :=
  (increasingRecords
    (fun i => (req (n - 1 - i)).release + L (req (n - 1 - i)).position) n).map
      (fun i => n - 1 - i)

theorem leftRecordScan_mem (R : ℕ → ℝ) (req : ℕ → Request ℕ) (n j : ℕ) :
    j ∈ leftRecordScan R req n ↔ LeftRecord R req n j := by
  exact increasingRecords_mem _ n j

theorem rightRecordScan_mem (L : ℕ → ℝ) (req : ℕ → Request ℕ) (n j : ℕ) :
    j ∈ rightRecordScan L req n ↔ RightRecord L req n j := by
  simp only [rightRecordScan, List.mem_map, increasingRecords_mem]
  constructor
  · rintro ⟨i, ⟨hin, hirec⟩, heq⟩
    refine ⟨by omega, ?_⟩
    intro k hjk hkn
    have hk : n - 1 - k < i := by omega
    have hkrev : n - 1 - (n - 1 - k) = k := by omega
    have hh := hirec (n - 1 - k) hk
    simpa only [hkrev, heq] using hh
  · rintro ⟨hjn, hjrec⟩
    refine ⟨n - 1 - j, ⟨by omega, ?_⟩, by omega⟩
    intro k hk
    have hki : j < n - 1 - k := by omega
    have hkn : n - 1 - k < n := by omega
    have hjrev : n - 1 - (n - 1 - j) = j := by omega
    simpa only [hjrev] using hjrec (n - 1 - k) hki hkn

theorem reversed_indices_pairwise (n : ℕ) (is : List ℕ)
    (horder : is.Pairwise (fun i j => i < j)) (hbound : ∀ i ∈ is, i < n) :
    (is.map (fun i => n - 1 - i)).Pairwise (fun i j => j < i) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih htail (fun j hj => hbound j (List.mem_cons_of_mem _ hj))⟩
    intro j hj
    obtain ⟨k, hk, heq⟩ := List.mem_map.mp hj
    have hik := hhead k hk
    have hkn := hbound k (List.mem_cons_of_mem _ hk)
    omega

theorem rightRecordScan_pairwise (L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) :
    (rightRecordScan L req n).Pairwise (fun i j => j < i) := by
  apply reversed_indices_pairwise
  · exact increasingRecords_pairwise _ n
  · intro i hi
    exact ((increasingRecords_mem _ n i).mp hi).1

def scannedRequests (R L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) : Set (Request ℕ) :=
  {q | q ∈ (leftRecordScan R req n).map req ++ (rightRecordScan L req n).map req}

theorem scannedRequests_eq (R L : ℕ → ℝ) (req : ℕ → Request ℕ) (n : ℕ) :
    scannedRequests R L req n = recordRequests R L req n := by
  ext q
  change (q ∈ (leftRecordScan R req n).map req ++ (rightRecordScan L req n).map req) ↔ _
  simp only [List.mem_append, List.mem_map, leftRecordScan_mem, rightRecordScan_mem]
  constructor
  · rintro (⟨i, hi, heq⟩ | ⟨i, hi, heq⟩)
    · exact ⟨i, Or.inl hi, heq⟩
    · exact ⟨i, Or.inr hi, heq⟩
  · rintro ⟨i, hi, heq⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨i, hi, heq⟩
    · exact Or.inr ⟨i, hi, heq⟩

/-- The running-maximum scan itself preserves feasible terminal/finish pairs. -/
theorem scanned_elimination_iff (R L : ℕ → ℝ)
    (hR : Monotone R) (hL : Monotone L) (req : ℕ → Request ℕ) (n : ℕ)
    (hpos : ∀ u v, u ≤ v → v < n → (req u).position ≤ (req v).position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t (scannedRequests R L req n) goals ⟨vs, goal, finish⟩) ↔
      (∃ vs, feasible (pathDist R L) x t (originalRequests req n) goals ⟨vs, goal, finish⟩) := by
  rw [scannedRequests_eq]
  exact record_elimination_iff R L hR hL req n hpos x t goals goal finish

/-- If both extremes are still visited, already released interior tasks can
be restored even if an earlier prefix had served them and was discarded. -/
theorem restore_early_interval (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (a b : Request ℕ) (todo : List (Request ℕ)) (kept : Set (Request ℕ))
    (ha : a ∈ kept) (hb : b ∈ kept)
    (hpos : ∀ q ∈ todo, a.position ≤ q.position ∧ q.position ≤ b.position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (plan : Plan ℕ)
    (hearly : ∀ q ∈ todo, q ∈ kept ∨ q.release ≤ t)
    (h : feasible (pathDist R L) x t kept goals plan) :
    ∃ ws, feasible (pathDist R L) x t {q | q ∈ todo} goals
      ⟨ws, plan.terminal, plan.finish⟩ := by
  let p : Request ℕ := ⟨a.position, t⟩
  let r : Request ℕ := ⟨b.position, t⟩
  let extra : Set (Request ℕ) := insert p (insert r kept)
  have hvirtual : ∀ c ∈ kept, VisitsRequest ⟨c.position, t⟩
      (plan.visits ++ [(plan.terminal, plan.finish)]) := by
    intro c hc
    obtain ⟨v, hv, hp, _⟩ := h.2.1 c hc
    have ht := timedRoute_visit_lower_bound (pathDist R L)
      (pathDist_triangle R L hR hL) (plan.visits ++ [(plan.terminal, plan.finish)])
      v.1 v.2 x t h.1 (by simpa using hv)
    have hd := pathDist_nonneg R L hR hL x v.1
    exact ⟨v, hv, hp, by dsimp; linarith⟩
  have hextra : feasible (pathDist R L) x t extra goals plan := by
    refine ⟨h.1, ?_, h.2.2⟩
    intro q hq
    rcases hq with heq | hq
    · subst q
      exact hvirtual a ha
    · rcases hq with heq | hq
      · subst q
        exact hvirtual b hb
      · exact h.2.1 q hq
  have hw : ∀ q ∈ todo, ∃ p ∈ extra, ∃ r ∈ extra,
      p.position ≤ q.position ∧ q.position ≤ r.position ∧
      q.release - R q.position ≤ p.release - R p.position ∧
      q.release + L q.position ≤ r.release + L r.position := by
    intro q hq
    rcases hearly q hq with hk | ht
    · have hqe : q ∈ extra := Or.inr (Or.inr hk)
      exact ⟨q, hqe, q, hqe, le_rfl, le_rfl, le_rfl, le_rfl⟩
    · obtain ⟨haq, hqb⟩ := hpos q hq
      have hRa := hR haq
      have hLb := hL hqb
      refine ⟨p, by simp [extra], r, by simp [extra], haq, hqb, ?_, ?_⟩
      · change q.release - R q.position ≤ t - R a.position
        linarith
      · change q.release + L q.position ≤ t + L b.position
        linarith
  obtain ⟨ws, hws⟩ := restore_witness_list R L hR hL x t extra goals
    plan.terminal plan.finish todo hw plan.visits hextra
  refine ⟨ws, hws.1, ?_, hws.2.2⟩
  intro q hq
  exact hws.2.1 q (Or.inr hq)

/-- Any feasible plan can begin by serving one extreme at its earliest
possible service time. All interior obligations may be conservatively retained. -/
theorem endpoint_normalize (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (a b : Request ℕ) (goal : ℕ) (finish : ℝ) (goals : Set ℕ)
    (vs : List (ℕ × ℝ)) :
    ∀ todo : List (Request ℕ), a ∈ todo → b ∈ todo →
      (∀ q ∈ todo, a.position ≤ q.position ∧ q.position ≤ b.position) →
      ∀ x t, feasible (pathDist R L) x t {q | q ∈ todo} goals ⟨vs, goal, finish⟩ →
        (∃ ws, feasible (pathDist R L) a.position (max (t + pathDist R L x a.position) a.release)
          {q | q ∈ todo} goals ⟨ws, goal, finish⟩) ∨
        (∃ ws, feasible (pathDist R L) b.position (max (t + pathDist R L x b.position) b.release)
          {q | q ∈ todo} goals ⟨ws, goal, finish⟩) := by
  classical
  induction vs with
  | nil =>
    intro todo ha _ _ x t h
    obtain ⟨v, hv, hp, hr⟩ := h.2.1 a ha
    have heq : v = (goal, finish) := by simpa using hv
    subst v
    have hga : goal = a.position := hp
    have hrel : a.release ≤ finish := hr
    have htravel : t + pathDist R L x a.position ≤ finish := by simpa only [hga] using h.1.1
    have hmax : max (t + pathDist R L x a.position) a.release ≤ finish := max_le htravel hrel
    refine Or.inl ⟨[], ?_, h.2.1, h.2.2⟩
    change max (t + pathDist R L x a.position) a.release + pathDist R L a.position goal ≤ finish ∧ True
    rw [hga, pathDist_self, add_zero]
    exact ⟨hmax, trivial⟩
  | cons v rest ih =>
    intro todo ha hb hpos x t h
    have at_head : ∀ c : Request ℕ, v.1 = c.position → c.release ≤ v.2 →
        ∃ ws, feasible (pathDist R L) c.position (max (t + pathDist R L x c.position) c.release)
          {q | q ∈ todo} goals ⟨ws, goal, finish⟩ := by
      intro c hc hrel
      have htravel : t + pathDist R L x c.position ≤ v.2 := by simpa only [hc] using h.1.1
      have hmax := max_le htravel hrel
      refine ⟨v :: rest, ?_, h.2.1, h.2.2⟩
      change (max (t + pathDist R L x c.position) c.release + pathDist R L c.position v.1 ≤ v.2) ∧ _
      rw [hc, pathDist_self, add_zero]
      exact ⟨hmax, by simpa only [hc] using h.1.2⟩
    by_cases hva : v.1 = a.position ∧ a.release ≤ v.2
    · exact Or.inl (at_head a hva.1 hva.2)
    by_cases hvb : v.1 = b.position ∧ b.release ≤ v.2
    · exact Or.inr (at_head b hvb.1 hvb.2)
    let kept := todo.filter (fun q => decide (¬ (v.1 = q.position ∧ q.release ≤ v.2)))
    have hakept : a ∈ kept := List.mem_filter.mpr ⟨ha, by simpa only [decide_eq_true_eq] using hva⟩
    have hbkept : b ∈ kept := List.mem_filter.mpr ⟨hb, by simpa only [decide_eq_true_eq] using hvb⟩
    have hsub : ∀ q ∈ kept, q ∈ todo := by
      intro q hq
      exact (List.mem_filter.mp hq).1
    have htail : feasible (pathDist R L) v.1 v.2 {q | q ∈ kept} goals ⟨rest, goal, finish⟩ := by
      refine ⟨h.1.2, ?_, h.2.2⟩
      intro q hq
      have hn : ¬ (v.1 = q.position ∧ q.release ≤ v.2) := by
        exact of_decide_eq_true (List.mem_filter.mp hq).2
      obtain ⟨w, hw, hp, hr⟩ := h.2.1 q (hsub q hq)
      rcases List.mem_cons.mp hw with heq | hw
      · subst w
        exact False.elim (hn ⟨hp, hr⟩)
      · exact ⟨w, hw, hp, hr⟩
    have restore : ∀ c : Request ℕ,
        (∃ ws, feasible (pathDist R L) c.position (max (v.2 + pathDist R L v.1 c.position) c.release)
          {q | q ∈ kept} goals ⟨ws, goal, finish⟩) →
        ∃ ws, feasible (pathDist R L) c.position (max (t + pathDist R L x c.position) c.release)
          {q | q ∈ todo} goals ⟨ws, goal, finish⟩ := by
      intro c hc
      obtain ⟨ws, hws⟩ := hc
      let tc := max (v.2 + pathDist R L v.1 c.position) c.release
      have htct : v.2 ≤ tc := by
        have hd := pathDist_nonneg R L hR hL v.1 c.position
        have hm := le_max_left (v.2 + pathDist R L v.1 c.position) c.release
        dsimp [tc]
        linarith
      have hearly : ∀ q ∈ todo, q ∈ kept ∨ q.release ≤ tc := by
        intro q hq
        by_cases hn : v.1 = q.position ∧ q.release ≤ v.2
        · exact Or.inr (le_trans hn.2 htct)
        · exact Or.inl (List.mem_filter.mpr ⟨hq, by simpa only [decide_eq_true_eq] using hn⟩)
      obtain ⟨ys, hys⟩ := restore_early_interval R L hR hL a b todo {q | q ∈ kept}
        hakept hbkept hpos c.position tc goals ⟨ws, goal, finish⟩ hearly hws
      have htime : max (t + pathDist R L x c.position) c.release ≤ tc := by
        have htri := pathDist_triangle R L hR hL x v.1 c.position
        have hfirst := h.1.1
        have hm := le_max_left (v.2 + pathDist R L v.1 c.position) c.release
        apply max_le
        · dsimp [tc]
          linarith
        · exact le_max_right _ _
      exact ⟨ys, continuation_dominance (pathDist R L) c.position htime
        (Set.Subset.refl _) goals ⟨ys, goal, finish⟩ hys⟩
    rcases ih kept hakept hbkept (fun q hq => hpos q (hsub q hq)) v.1 v.2 htail with hl | hr
    · exact Or.inl (restore a hl)
    · exact Or.inr (restore b hr)

/-- Realize one endpoint-deletion transition by travelling, waiting if needed,
serving the chosen request, and then following the suffix. -/
theorem take_request_plan (R L : ℕ → ℝ) (x : ℕ) (t : ℝ)
    (a : Request ℕ) (remaining : Set (Request ℕ)) (goals : Set ℕ) (plan : Plan ℕ)
    (h : feasible (pathDist R L) a.position
      (max (t + pathDist R L x a.position) a.release) (remaining \ {a}) goals plan) :
    feasible (pathDist R L) x t remaining goals
      ⟨(a.position, max (t + pathDist R L x a.position) a.release) :: plan.visits,
        plan.terminal, plan.finish⟩ := by
  classical
  refine ⟨⟨le_max_left _ _, h.1⟩, ?_, h.2.2⟩
  intro q hq
  by_cases heq : q = a
  · subst q
    exact ⟨(a.position, max (t + pathDist R L x a.position) a.release),
      by simp, rfl, le_max_right _ _⟩
  · obtain ⟨v, hv, hp, hr⟩ := h.2.1 q ⟨hq, heq⟩
    exact ⟨v, List.mem_cons_of_mem _ hv, hp, hr⟩

/-- Exact two-choice endpoint recurrence for an arbitrary finite request list.
The remaining tasks are conservative obligations, not a record of incidental visits. -/
theorem endpoint_recurrence_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (a b : Request ℕ) (todo : List (Request ℕ)) (ha : a ∈ todo) (hb : b ∈ todo)
    (hpos : ∀ q ∈ todo, a.position ≤ q.position ∧ q.position ≤ b.position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t {q | q ∈ todo} goals ⟨vs, goal, finish⟩) ↔
      (∃ vs, feasible (pathDist R L) a.position (max (t + pathDist R L x a.position) a.release)
        ({q | q ∈ todo} \ {a}) goals ⟨vs, goal, finish⟩) ∨
      (∃ vs, feasible (pathDist R L) b.position (max (t + pathDist R L x b.position) b.release)
        ({q | q ∈ todo} \ {b}) goals ⟨vs, goal, finish⟩) := by
  constructor
  · rintro ⟨vs, h⟩
    rcases endpoint_normalize R L hR hL a b goal finish goals vs todo ha hb hpos x t h with hl | hr
    · obtain ⟨ws, hws⟩ := hl
      refine Or.inl ⟨ws, hws.1, ?_, hws.2.2⟩
      intro q hq
      exact hws.2.1 q hq.1
    · obtain ⟨ws, hws⟩ := hr
      refine Or.inr ⟨ws, hws.1, ?_, hws.2.2⟩
      intro q hq
      exact hws.2.1 q hq.1
  · rintro (⟨vs, h⟩ | ⟨vs, h⟩)
    · exact ⟨_, take_request_plan R L x t a {q | q ∈ todo} goals ⟨vs, goal, finish⟩ h⟩
    · exact ⟨_, take_request_plan R L x t b {q | q ∈ todo} goals ⟨vs, goal, finish⟩ h⟩

theorem ready_right_endpoint_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (x : ℕ) (t : ℝ) (a : Request ℕ) (remaining : Set (Request ℕ))
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) (ha : a ∈ remaining)
    (hxa : x ≤ a.position) (hside : ∀ q ∈ remaining, a.position ≤ q.position)
    (hready : a.release ≤ t + pathDist R L x a.position) :
    (∃ vs, feasible (pathDist R L) x t remaining goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) a.position (t + pathDist R L x a.position)
      (remaining \ {a}) goals ⟨vs, goal, finish⟩) := by
  constructor
  · rintro ⟨vs, h⟩
    have hn : ∃ ws, feasible (pathDist R L) a.position (t + pathDist R L x a.position)
        remaining goals ⟨ws, goal, finish⟩ := by
      by_cases heq : x = a.position
      · refine ⟨vs, ?_⟩
        simpa only [heq, pathDist_self, add_zero] using h
      · exact right_barrier_normalize R L hR hL a.position x t (by omega)
          remaining goals ⟨a, ha⟩ hside ⟨vs, goal, finish⟩ h
    obtain ⟨ws, hw⟩ := hn
    exact ⟨ws, hw.1, fun q hq => hw.2.1 q hq.1, hw.2.2⟩
  · rintro ⟨vs, h⟩
    have hmax : max (t + pathDist R L x a.position) a.release =
        t + pathDist R L x a.position := max_eq_left hready
    exact ⟨_, take_request_plan R L x t a remaining goals ⟨vs, goal, finish⟩
      (by simpa only [hmax] using h)⟩

theorem ready_left_endpoint_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (x : ℕ) (t : ℝ) (a : Request ℕ) (remaining : Set (Request ℕ))
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) (ha : a ∈ remaining)
    (hxa : a.position ≤ x) (hside : ∀ q ∈ remaining, q.position ≤ a.position)
    (hready : a.release ≤ t + pathDist R L x a.position) :
    (∃ vs, feasible (pathDist R L) x t remaining goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) a.position (t + pathDist R L x a.position)
      (remaining \ {a}) goals ⟨vs, goal, finish⟩) := by
  constructor
  · rintro ⟨vs, h⟩
    have hn : ∃ ws, feasible (pathDist R L) a.position (t + pathDist R L x a.position)
        remaining goals ⟨ws, goal, finish⟩ := by
      by_cases heq : x = a.position
      · refine ⟨vs, ?_⟩
        simpa only [heq, pathDist_self, add_zero] using h
      · exact left_barrier_normalize R L hR hL a.position x t (by omega)
          remaining goals ⟨a, ha⟩ hside ⟨vs, goal, finish⟩ h
    obtain ⟨ws, hw⟩ := hn
    exact ⟨ws, hw.1, fun q hq => hw.2.1 q hq.1, hw.2.2⟩
  · rintro ⟨vs, h⟩
    have hmax : max (t + pathDist R L x a.position) a.release =
        t + pathDist R L x a.position := max_eq_left hready
    exact ⟨_, take_request_plan R L x t a remaining goals ⟨vs, goal, finish⟩
      (by simpa only [hmax] using h)⟩

noncomputable def upperBound (f : ℕ → ℝ) (threshold : ℝ) (lo len : ℕ) : ℕ × ℕ :=
  if h : len = 0 then (lo, 0)
  else
    let mid := lo + len / 2
    if f mid ≤ threshold then
      let result := upperBound f threshold (mid + 1) (len - (len / 2 + 1))
      (result.1, result.2 + 1)
    else
      let result := upperBound f threshold lo (len / 2)
      (result.1, result.2 + 1)
termination_by len
decreasing_by all_goals omega

theorem upperBound_spec (f : ℕ → ℝ) (threshold : ℝ) (len : ℕ) :
    ∀ lo, (∀ i j, lo ≤ i → i ≤ j → j < lo + len → f i ≤ f j) →
      let k := (upperBound f threshold lo len).1
      lo ≤ k ∧ k ≤ lo + len ∧
        (∀ i, lo ≤ i → i < k → f i ≤ threshold) ∧
        (∀ i, k ≤ i → i < lo + len → threshold < f i) := by
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro lo hmono
    by_cases hz : len = 0
    · subst len
      simp only [upperBound, ↓reduceDIte, Nat.add_zero, le_refl, true_and]
      exact ⟨fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · have hm : len / 2 < len := by omega
      have hr : len - (len / 2 + 1) < len := by omega
      rw [upperBound, dite_eq_right hz]
      dsimp only
      split_ifs with htest
      · obtain ⟨hlo, hhi, hbefore, hafter⟩ :=
          ih (len - (len / 2 + 1)) hr (lo + len / 2 + 1)
            (by intro i j hi hij hj; exact hmono i j (by omega) hij (by omega))
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro i hil hik
          by_cases him : i ≤ lo + len / 2
          · exact le_trans (hmono i (lo + len / 2) hil him (by omega)) htest
          · exact hbefore i (by omega) hik
        · intro i hki hin
          exact hafter i hki (by omega)
      · obtain ⟨hlo, hhi, hbefore, hafter⟩ :=
          ih (len / 2) hm lo
            (by intro i j hi hij hj; exact hmono i j hi hij (by omega))
        refine ⟨hlo, by omega, hbefore, ?_⟩
        intro i hki hin
        by_cases him : i < lo + len / 2
        · exact hafter i hki him
        · exact lt_of_lt_of_le (lt_of_not_ge htest)
            (hmono (lo + len / 2) i (by omega) (by omega) hin)

/-- The binary search makes at most `budget` comparisons on a range shorter
than `2 ^ budget`, i.e. `⌈log₂(len+1)⌉` comparisons. -/
theorem upperBound_comparisons (f : ℕ → ℝ) (threshold : ℝ) (budget : ℕ) :
    ∀ lo len, len < 2 ^ budget → (upperBound f threshold lo len).2 ≤ budget := by
  induction budget with
  | zero =>
    intro lo len hlen
    have hz : len = 0 := by simpa using Nat.eq_zero_of_le_zero (by simpa using hlen)
    subst len
    simp [upperBound]
  | succ budget ih =>
    intro lo len hlen
    by_cases hz : len = 0
    · subst len
      simp [upperBound]
    · have hpow : len < 2 ^ budget * 2 := by simpa only [pow_succ] using hlen
      have hhalf : len / 2 < 2 ^ budget := by omega
      have hright : len - (len / 2 + 1) < 2 ^ budget := by omega
      rw [upperBound, dite_eq_right hz]
      dsimp only
      split_ifs
      · exact Nat.add_le_add_right (ih _ _ hright) 1
      · exact Nat.add_le_add_right (ih _ _ hhalf) 1

theorem right_binary_blocker (R L : ℕ → ℝ) (req : ℕ → Request ℕ)
    (x lo len : ℕ) (t : ℝ)
    (hpos : ∀ i, lo ≤ i → i < lo + len → x ≤ (req i).position)
    (hmono : ∀ i j, lo ≤ i → i ≤ j → j < lo + len →
      (req i).release - R (req i).position ≤ (req j).release - R (req j).position) :
    let k := (upperBound (fun i => (req i).release - R (req i).position)
      (t - R x) lo len).1
    lo ≤ k ∧ k ≤ lo + len ∧
      (∀ i, lo ≤ i → i < k → (req i).release ≤ t + pathDist R L x (req i).position) ∧
      (∀ i, k ≤ i → i < lo + len → t + pathDist R L x (req i).position < (req i).release) := by
  obtain ⟨hlo, hhi, hp, hs⟩ := upperBound_spec
    (fun i => (req i).release - R (req i).position) (t - R x) len lo hmono
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro i hi hik
    have h := hp i hi hik
    rw [pathDist, ite_eq_left (hpos i hi (by omega))]
    linarith
  · intro i hki hin
    have h := hs i hki hin
    rw [pathDist, ite_eq_left (hpos i (by omega) hin)]
    linarith

theorem left_binary_blocker (R L : ℕ → ℝ) (req : ℕ → Request ℕ)
    (x lo len : ℕ) (t : ℝ)
    (hpos : ∀ i, lo ≤ i → i < lo + len → (req i).position ≤ x)
    (hmono : ∀ i j, lo ≤ i → i ≤ j → j < lo + len →
      (req i).release + L (req i).position ≤ (req j).release + L (req j).position) :
    let k := (upperBound (fun i => (req i).release + L (req i).position)
      (t + L x) lo len).1
    lo ≤ k ∧ k ≤ lo + len ∧
      (∀ i, lo ≤ i → i < k → (req i).release ≤ t + pathDist R L x (req i).position) ∧
      (∀ i, k ≤ i → i < lo + len → t + pathDist R L x (req i).position < (req i).release) := by
  obtain ⟨hlo, hhi, hp, hs⟩ := upperBound_spec
    (fun i => (req i).release + L (req i).position) (t + L x) len lo hmono
  have hd : ∀ i, lo ≤ i → i < lo + len →
      pathDist R L x (req i).position = L x - L (req i).position := by
    intro i hil hin
    have hi := hpos i hil hin
    by_cases heq : x = (req i).position
    · simp [heq, pathDist_self]
    · exact ite_eq_right (by omega)
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro i hi hik
    have h := hp i hi hik
    rw [hd i hi (by omega)]
    linarith
  · intro i hki hin
    have h := hs i hki hin
    rw [hd i (by omega) hin]
    linarith

structure EventData where
  chain : Bool → ℕ → Request ℕ
  size : Bool → ℕ
  dist : ℕ → ℕ → ℝ
  nonneg : ∀ x y, 0 ≤ dist x y
  release_mono : ∀ side i j, i ≤ j → j < size side →
    (chain side i).release ≤ (chain side j).release

structure EventState where
  side : Bool
  i : ℕ
  j : ℕ
  t : ℝ

def eventPos (C : EventData) (s : EventState) : ℕ :=
  (C.chain s.side s.i).position

def pathEventData (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (chain : Bool → ℕ → Request ℕ) (size : Bool → ℕ)
    (hrel : ∀ side i j, i ≤ j → j < size side →
      (chain side i).release ≤ (chain side j).release) : EventData :=
  ⟨chain, size, pathDist R L, pathDist_nonneg R L hR hL, hrel⟩

/-- False is the left chain, true is the right chain. Non-final current
indices are spatially distinct from every opposite index, even when the
two chains share their last request. -/
theorem pathEvent_cross_positive (R L : ℕ → ℝ) (hR : StrictMono R) (hL : StrictMono L)
    (C : EventData) (hdist : C.dist = pathDist R L)
    (hleft : ∀ i j, i < j → j < C.size false →
      (C.chain false i).position < (C.chain false j).position)
    (hright : ∀ i j, i < j → j < C.size true →
      (C.chain true j).position < (C.chain true i).position)
    (hsep : ∀ i j, i < C.size false → j < C.size true →
      (C.chain false i).position ≤ (C.chain true j).position)
    (s : EventState) (hn : s.i+1 < C.size s.side) (hj : s.j < C.size (!s.side)) :
    0 < C.dist (eventPos C s) (C.chain (!s.side) s.j).position := by
  rw [hdist]
  apply pathDist_pos R L hR hL
  unfold eventPos
  cases he : s.side with
  | false =>
      simp only [he, Bool.not_false] at *
      have h₁ := hleft s.i (s.i+1) (by omega) hn
      have h₂ := hsep (s.i+1) s.j hn hj
      omega
  | true =>
      simp only [he, Bool.not_true] at *
      have h₁ := hright s.i (s.i+1) (by omega) hn
      have h₂ := hsep s.j (s.i+1) hj hn
      omega

/-- First-later-release mapping (the cutoff `o_S(i)`). The two-pointer table
of the implementation equals it (`pointerTable_eq_eventCutoff`). -/
noncomputable def eventCutoff (C : EventData) (side : Bool) (i : ℕ) : ℕ := by
  classical
  exact Nat.find (cutoff_exists (fun k => (C.chain (!side) k).release)
    (C.size (!side)) (C.chain side i).release (C.release_mono (!side)))

theorem eventCutoff_spec (C : EventData) (side : Bool) (i : ℕ) :
    IsCutoff (fun k => (C.chain (!side) k).release) (C.size (!side))
      (C.chain side i).release (eventCutoff C side i) := by
  classical
  exact Nat.find_spec _

theorem eventCutoff_mono_bounded (C : EventData) (side : Bool) {i j : ℕ}
    (hij : i ≤ j) (hj : j < C.size side) : eventCutoff C side i ≤ eventCutoff C side j := by
  exact cutoff_monotone _ _ _ _ _ _ (C.release_mono side i j hij hj)
    (eventCutoff_spec C side i) (eventCutoff_spec C side j)

/-- Capping at the final valid pivot extends finite-chain monotonicity
to all natural indices, as required by the finite counting lemmas. -/
theorem capped_eventCutoff_mono (C : EventData) (side : Bool) (n : ℕ)
    (hn : n < C.size side) : Monotone (fun i => eventCutoff C side (min i n)) := by
  intro i j hij
  apply eventCutoff_mono_bounded C side
  · omega
  · omega

def dualTodo {Req : Type} (left right : ℕ → Req) (a b i j : ℕ) : List Req :=
  chainSegment left i (a-i) ++ chainSegment right j (b-j)

theorem dualTodo_pending {Req : Type} (left right : ℕ → Req) (a b i j : ℕ)
    (hi : i ≤ a) (hj : j ≤ b) :
    {q | q ∈ dualTodo left right a b i j} = pending left right a b i j := by
  ext q
  simp only [Set.mem_ofPred_eq, dualTodo, List.mem_append, chainSegment_mem,
    pending, Nat.add_sub_of_le hi, Nat.add_sub_of_le hj]

theorem pending_peel {Req : Type} (left right : ℕ → Req) (a b i j : ℕ)
    (hi : i < a) :
    pending left right a b i j = insert (left i) (pending left right a b (i+1) j) := by
  ext q
  constructor
  · rintro (⟨k, hik, hka, heq⟩ | hr)
    · by_cases hk : k = i
      · subst k
        exact Or.inl heq.symm
      · exact Or.inr (Or.inl ⟨k, by omega, hka, heq⟩)
    · exact Or.inr (Or.inr hr)
  · rintro (hq | (⟨k, hik, hka, heq⟩ | hr))
    · exact Or.inl ⟨i, le_refl _, hi, hq.symm⟩
    · exact Or.inl ⟨k, by omega, hka, heq⟩
    · exact Or.inr hr

theorem pending_swap {Req : Type} (left right : ℕ → Req) (a b i j : ℕ) :
    pending left right a b i j = pending right left b a j i := by
  ext q
  exact or_comm

/-- At a request's position after its release, deleting or reinstating its
obligation preserves every terminal/finish pair. Reinstatement inserts an
explicit zero-travel visit; no claim about incidental service is needed. -/
theorem erase_current_iff (R L : ℕ → ℝ) (q : Request ℕ) (t : ℝ)
    (hr : q.release ≤ t) (remaining : Set (Request ℕ)) (goals : Set ℕ)
    (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) q.position t (remaining \ {q}) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) q.position t remaining goals ⟨vs, goal, finish⟩) := by
  constructor
  · rintro ⟨vs, h⟩
    have htime : max (t + pathDist R L q.position q.position) q.release = t := by
      rw [pathDist_self]
      simp only [add_zero, max_eq_left hr]
    have ht : feasible (pathDist R L) q.position
        (max (t + pathDist R L q.position q.position) q.release)
        (remaining \ {q}) goals ⟨vs, goal, finish⟩ := by simpa only [htime] using h
    exact ⟨_, take_request_plan R L q.position t q remaining goals ⟨vs, goal, finish⟩ ht⟩
  · rintro ⟨vs, h⟩
    refine ⟨vs, continuation_dominance (pathDist R L) q.position (le_refl t) ?_
      goals ⟨vs, goal, finish⟩ h⟩
    intro a ha
    exact ha.1

theorem peel_current_iff (R L : ℕ → ℝ) (q : Request ℕ) (t : ℝ)
    (hr : q.release ≤ t) (remaining : Set (Request ℕ)) (goals : Set ℕ)
    (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) q.position t ((insert q remaining) \ {q})
      goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) q.position t remaining goals ⟨vs, goal, finish⟩) := by
  have he : (insert q remaining) \ {q} = remaining \ {q} := by
    ext a
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [he]
  exact erase_current_iff R L q t hr remaining goals goal finish

/-- Exact endpoint recurrence for the union of two inward chains. The
suffixes may share a request. All endpoints and bounds are derived from
the actual pending indices, not postulated separately for an arbitrary set. -/
theorem dual_endpoint_recurrence (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j : ℕ) (hi : i < a) (hj : j < b)
    (hl : ∀ u v, u ≤ v → v < a → (left u).position ≤ (left v).position)
    (hr : ∀ u v, u ≤ v → v < b → (right v).position ≤ (right u).position)
    (sep : ∀ u v, u < a → v < b → (left u).position ≤ (right v).position)
    (x : ℕ) (t : ℝ) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t (pending left right a b i j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left i).position
      (max (t + pathDist R L x (left i).position) (left i).release)
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) ∨
    (∃ vs, feasible (pathDist R L) (right j).position
      (max (t + pathDist R L x (right j).position) (right j).release)
      (pending left right a b i (j+1)) goals ⟨vs, goal, finish⟩) := by
  let todo := dualTodo left right a b i j
  have hset : {q | q ∈ todo} = pending left right a b i j :=
    dualTodo_pending left right a b i j (by omega) (by omega)
  have ha : left i ∈ todo := by
    change left i ∈ {q | q ∈ todo}
    rw [hset]
    exact Or.inl ⟨i, le_refl _, hi, rfl⟩
  have hb : right j ∈ todo := by
    change right j ∈ {q | q ∈ todo}
    rw [hset]
    exact Or.inr ⟨j, le_refl _, hj, rfl⟩
  have hpos : ∀ q ∈ todo, (left i).position ≤ q.position ∧ q.position ≤ (right j).position := by
    intro q hq
    have hq' : q ∈ pending left right a b i j := by rw [← hset]; exact hq
    rcases hq' with ⟨k, hik, hka, heq⟩ | ⟨k, hjk, hkb, heq⟩
    · rw [← heq]
      exact ⟨hl i k hik hka, sep k j hka hj⟩
    · rw [← heq]
      exact ⟨sep i k hi hkb, hr j k hjk hkb⟩
  have base := endpoint_recurrence_iff R L hR hL (left i) (right j) todo ha hb hpos x t goals goal finish
  rw [hset] at base
  have peelRight : pending left right a b i j =
      insert (right j) (pending left right a b i (j+1)) := by
    rw [pending_swap left right a b i j, pending_peel right left b a j i hj,
      pending_swap right left b a (j+1) i]
  have leftEq := peel_current_iff R L (left i)
    (max (t + pathDist R L x (left i).position) (left i).release)
    (le_max_right _ _) (pending left right a b (i+1) j) goals goal finish
  have rightEq := peel_current_iff R L (right j)
    (max (t + pathDist R L x (right j).position) (right j).release)
    (le_max_right _ _) (pending left right a b i (j+1)) goals goal finish
  rw [← pending_peel left right a b i j hi] at leftEq
  rw [← peelRight] at rightEq
  exact base.trans (or_congr leftEq rightEq)

/-- A ready left endpoint of the dual pending set is forced without loss.
The opposite suffix remains present throughout this equivalence. -/
theorem dual_ready_right_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j : ℕ) (hi : i < a)
    (hl : ∀ u v, u ≤ v → v < a → (left u).position ≤ (left v).position)
    (sep : ∀ u v, u < a → v < b → (left u).position ≤ (right v).position)
    (x : ℕ) (t : ℝ) (hx : x ≤ (left i).position)
    (ready : (left i).release ≤ t + pathDist R L x (left i).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t (pending left right a b i j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left i).position
      (t + pathDist R L x (left i).position)
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) := by
  have ha : left i ∈ pending left right a b i j := Or.inl ⟨i, le_refl _, hi, rfl⟩
  have hb : ∀ q ∈ pending left right a b i j, (left i).position ≤ q.position := by
    intro q hq
    rcases hq with ⟨k, hik, hka, heq⟩ | ⟨k, _, hkb, heq⟩
    · rw [← heq]; exact hl i k hik hka
    · rw [← heq]; exact sep i k hi hkb
  have base := ready_right_endpoint_iff R L hR hL x t (left i)
    (pending left right a b i j) goals goal finish ha hx hb ready
  have pe := peel_current_iff R L (left i) _ ready
    (pending left right a b (i+1) j) goals goal finish
  rw [← pending_peel left right a b i j hi] at pe
  exact base.trans pe

theorem dual_ready_left_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j : ℕ) (hj : j < b)
    (hr : ∀ u v, u ≤ v → v < b → (right v).position ≤ (right u).position)
    (sep : ∀ u v, u < a → v < b → (left u).position ≤ (right v).position)
    (x : ℕ) (t : ℝ) (hx : (right j).position ≤ x)
    (ready : (right j).release ≤ t + pathDist R L x (right j).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) x t (pending left right a b i j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (right j).position
      (t + pathDist R L x (right j).position)
      (pending left right a b i (j+1)) goals ⟨vs, goal, finish⟩) := by
  have ha : right j ∈ pending left right a b i j := Or.inr ⟨j, le_refl _, hj, rfl⟩
  have hb : ∀ q ∈ pending left right a b i j, q.position ≤ (right j).position := by
    intro q hq
    rcases hq with ⟨k, _, hka, heq⟩ | ⟨k, hjk, hkb, heq⟩
    · rw [← heq]; exact sep k j hka hj
    · rw [← heq]; exact hr j k hjk hkb
  have base := ready_left_endpoint_iff R L hR hL x t (right j)
    (pending left right a b i j) goals goal finish ha hx hb ready
  have pe : pending left right a b i j =
      insert (right j) (pending left right a b i (j+1)) := by
    rw [pending_swap left right a b i j, pending_peel right left b a j i hj,
      pending_swap right left b a (j+1) i]
  have peq := peel_current_iff R L (right j) _ ready
    (pending left right a b i (j+1)) goals goal finish
  rw [← pe] at peq
  exact base.trans peq

/-- Advancing over any ready prefix preserves all feasible terminal/finish
pairs, with the opposite chain's obligations retained. -/
theorem dual_ready_right_run (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j n : ℕ) (hn : i+n < a)
    (hl : ∀ u v, u ≤ v → v < a → (left u).position ≤ (left v).position)
    (sep : ∀ u v, u < a → v < b → (left u).position ≤ (right v).position)
    (t : ℝ)
    (ready : ∀ k, i < k → k ≤ i+n →
      (left k).release ≤ t + pathDist R L (left i).position (left k).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) (left i).position t
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left (i+n)).position
      (t + pathDist R L (left i).position (left (i+n)).position)
      (pending left right a b (i+n+1) j) goals ⟨vs, goal, finish⟩) := by
  induction n with
  | zero => simp only [pathDist_self, add_zero]
  | succ n ih =>
      have hprev : i+n < a := by omega
      have hp := ih hprev (fun k hk hk' => ready k hk (by omega))
      have hxy := hl i (i+n) (by omega) hprev
      have hyz := hl (i+n) (i+n+1) (by omega) (by omega)
      have he : t + pathDist R L (left i).position (left (i+n)).position +
          pathDist R L (left (i+n)).position (left (i+n+1)).position =
          t + pathDist R L (left i).position (left (i+n+1)).position := by
        rw [pathDist_right_add R L hxy hyz]; ring
      have hrdy : (left (i+n+1)).release ≤
          t + pathDist R L (left i).position (left (i+n)).position +
            pathDist R L (left (i+n)).position (left (i+n+1)).position := by
        rw [he]; exact ready _ (by omega) (by omega)
      have step := dual_ready_right_iff R L hR hL left right a b (i+n+1) j
        (by omega) hl sep (left (i+n)).position
        (t + pathDist R L (left i).position (left (i+n)).position)
        hyz hrdy goals goal finish
      rw [he] at step
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hp.trans step

/-- Search from an already served current index. The returned last-ready
index preserves the opposite chain, even at the common final request. -/
theorem dual_binary_right_jump (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j : ℕ) (hi : i < a)
    (hl : ∀ u v, u ≤ v → v < a → (left u).position ≤ (left v).position)
    (sep : ∀ u v, u < a → v < b → (left u).position ≤ (right v).position)
    (mono : ∀ u v, i ≤ u → u ≤ v → v < a →
      (left u).release - R (left u).position ≤ (left v).release - R (left v).position)
    (t : ℝ) (served : (left i).release ≤ t)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    let k := (upperBound (fun u => (left u).release - R (left u).position)
      (t - R (left i).position) i (a-i)).1
    i < k ∧ k ≤ a ∧
    ((∃ vs, feasible (pathDist R L) (left i).position t
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left (k-1)).position
      (t + pathDist R L (left i).position (left (k-1)).position)
      (pending left right a b k j) goals ⟨vs, goal, finish⟩)) := by
  dsimp only
  let k := (upperBound (fun u => (left u).release - R (left u).position)
    (t - R (left i).position) i (a-i)).1
  obtain ⟨hlo, hhi, hp, hs⟩ := upperBound_spec
    (fun u => (left u).release - R (left u).position) (t - R (left i).position)
    (a-i) i (fun u v hu huv hv => mono u v hu huv (by omega))
  change i ≤ k at hlo
  change k ≤ i+(a-i) at hhi
  have hk : i < k := by
    by_contra h
    have he : k = i := by omega
    have hh := hs i (by change k ≤ i; omega) (by omega)
    linarith
  refine ⟨hk, by omega, ?_⟩
  have hrun := dual_ready_right_run R L hR hL left right a b i j (k-1-i)
    (by omega) hl sep t (by
      intro u hu huk
      have hoff := hp u (by omega) (by change u < k; omega)
      rw [pathDist_right R L (hl i u (by omega) (by omega))]
      linarith) goals goal finish
  have hidx : i+(k-1-i) = k-1 := by omega
  have hnext : i+(k-1-i)+1 = k := by omega
  rw [hnext, hidx] at hrun
  exact hrun

/-- Mirror of the ready-prefix theorem; here the first chain moves left. -/
theorem dual_ready_left_run (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j n : ℕ) (hn : i+n < a)
    (hl : ∀ u v, u ≤ v → v < a → (left v).position ≤ (left u).position)
    (sep : ∀ u v, u < a → v < b → (right v).position ≤ (left u).position)
    (t : ℝ)
    (ready : ∀ k, i < k → k ≤ i+n →
      (left k).release ≤ t + pathDist R L (left i).position (left k).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible (pathDist R L) (left i).position t
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left (i+n)).position
      (t + pathDist R L (left i).position (left (i+n)).position)
      (pending left right a b (i+n+1) j) goals ⟨vs, goal, finish⟩) := by
  induction n with
  | zero => simp only [pathDist_self, add_zero]
  | succ n ih =>
      have hprev : i+n < a := by omega
      have hp := ih hprev (fun k hk hk' => ready k hk (by omega))
      have hxy := hl i (i+n) (by omega) hprev
      have hyz := hl (i+n) (i+n+1) (by omega) (by omega)
      have he : t + pathDist R L (left i).position (left (i+n)).position +
          pathDist R L (left (i+n)).position (left (i+n+1)).position =
          t + pathDist R L (left i).position (left (i+n+1)).position := by
        rw [pathDist_left_add R L hxy hyz]; ring
      have hrdy : (left (i+n+1)).release ≤
          t + pathDist R L (left i).position (left (i+n)).position +
            pathDist R L (left (i+n)).position (left (i+n+1)).position := by
        rw [he]; exact ready _ (by omega) (by omega)
      have step := dual_ready_left_iff R L hR hL right left b a j (i+n+1)
        (by omega) hl (fun u v hu hv => sep v u hv hu) (left (i+n)).position
        (t + pathDist R L (left i).position (left (i+n)).position)
        hyz hrdy goals goal finish
      rw [pending_swap right left b a j (i+n+1),
        pending_swap right left b a j (i+n+1+1)] at step
      rw [he] at step
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hp.trans step

/-- Binary jump in the decreasing-position first chain. -/
theorem dual_binary_left_jump (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (left right : ℕ → Request ℕ) (a b i j : ℕ) (hi : i < a)
    (hl : ∀ u v, u ≤ v → v < a → (left v).position ≤ (left u).position)
    (sep : ∀ u v, u < a → v < b → (right v).position ≤ (left u).position)
    (mono : ∀ u v, i ≤ u → u ≤ v → v < a →
      (left u).release + L (left u).position ≤ (left v).release + L (left v).position)
    (t : ℝ) (served : (left i).release ≤ t)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    let k := (upperBound (fun u => (left u).release + L (left u).position)
      (t + L (left i).position) i (a-i)).1
    i < k ∧ k ≤ a ∧
    ((∃ vs, feasible (pathDist R L) (left i).position t
      (pending left right a b (i+1) j) goals ⟨vs, goal, finish⟩) ↔
    (∃ vs, feasible (pathDist R L) (left (k-1)).position
      (t + pathDist R L (left i).position (left (k-1)).position)
      (pending left right a b k j) goals ⟨vs, goal, finish⟩)) := by
  dsimp only
  let k := (upperBound (fun u => (left u).release + L (left u).position)
    (t + L (left i).position) i (a-i)).1
  obtain ⟨hlo, hhi, hp, hs⟩ := upperBound_spec
    (fun u => (left u).release + L (left u).position) (t + L (left i).position)
    (a-i) i (fun u v hu huv hv => mono u v hu huv (by omega))
  change i ≤ k at hlo
  change k ≤ i+(a-i) at hhi
  have hk : i < k := by
    by_contra h
    have he : k = i := by omega
    have hh := hs i (by change k ≤ i; omega) (by omega)
    linarith
  refine ⟨hk, by omega, ?_⟩
  have hrun := dual_ready_left_run R L hR hL left right a b i j (k-1-i)
    (by omega) hl sep t (by
      intro u hu huk
      have hoff := hp u (by omega) (by change u < k; omega)
      rw [pathDist_left R L (hl i u (by omega) (by omega))]
      linarith) goals goal finish
  have hidx : i+(k-1-i) = k-1 := by omega
  have hnext : i+(k-1-i)+1 = k := by omega
  rw [hnext, hidx] at hrun
  exact hrun

/-- Route meaning of the actual event indices. This is a suffix meaning,
not a claim that an event has already served its historical prefix. -/
def EventSuffix (C : EventData) (s : EventState) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) : Prop :=
  ∃ vs, feasible C.dist (eventPos C s) s.t
    (pending (C.chain s.side) (C.chain (!s.side))
      (C.size s.side) (C.size (!s.side)) (s.i+1) s.j) goals ⟨vs, goal, finish⟩

structure EventGeometry (C : EventData) : Prop where
  left : ∀ u v, u ≤ v → v < C.size false →
    (C.chain false u).position ≤ (C.chain false v).position
  right : ∀ u v, u ≤ v → v < C.size true →
    (C.chain true v).position ≤ (C.chain true u).position
  separated : ∀ u v, u < C.size false → v < C.size true →
    (C.chain false u).position ≤ (C.chain true v).position

theorem event_initial_choices (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (hl : 0 < C.size false) (hr : 0 < C.size true)
    (start : ℕ) (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    (∃ vs, feasible C.dist start 0
      (pending (C.chain false) (C.chain true) (C.size false) (C.size true) 0 0)
      goals ⟨vs, goal, finish⟩) ↔
    EventSuffix C ⟨false, 0, 0,
      max (C.dist start (C.chain false 0).position) (C.chain false 0).release⟩ goals goal finish ∨
    EventSuffix C ⟨true, 0, 0,
      max (C.dist start (C.chain true 0).position) (C.chain true 0).release⟩ goals goal finish := by
  have base := dual_endpoint_recurrence R L hR hL (C.chain false) (C.chain true)
    (C.size false) (C.size true) 0 0 hl hr geometry.left geometry.right geometry.separated
    start 0 goals goal finish
  rw [pending_swap (C.chain false) (C.chain true) (C.size false) (C.size true) 0 (0+1)] at base
  simpa only [EventSuffix, eventPos, Bool.not_false, Bool.not_true, hd, zero_add] using base

/-- Exact two-way route recurrence in the event coordinates. Its max
times specialize to normal arrival or waiting according to the guards. -/
theorem event_suffix_choices (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (hn : s.i+1 < C.size s.side) (hj : s.j < C.size (!s.side))
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
    EventSuffix C ⟨s.side, s.i+1, s.j,
      max (s.t + C.dist (eventPos C s) (C.chain s.side (s.i+1)).position)
        (C.chain s.side (s.i+1)).release⟩ goals goal finish ∨
    EventSuffix C ⟨!s.side, s.j, s.i+1,
      max (s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position)
        (C.chain (!s.side) s.j).release⟩ goals goal finish := by
  cases hs : s.side with
  | false =>
    simp only [hs, Bool.not_false] at hn hj
    have base := dual_endpoint_recurrence R L hR hL (C.chain false) (C.chain true)
      (C.size false) (C.size true) (s.i+1) s.j hn hj
      geometry.left geometry.right geometry.separated (eventPos C s) s.t goals goal finish
    rw [pending_swap (C.chain false) (C.chain true) (C.size false) (C.size true)
      (s.i+1) (s.j+1)] at base
    simpa only [EventSuffix, eventPos, hs, Bool.not_false, Bool.not_true, hd] using base
  | true =>
    simp only [hs, Bool.not_true] at hn hj
    have base := dual_endpoint_recurrence R L hR hL (C.chain false) (C.chain true)
      (C.size false) (C.size true) s.j (s.i+1) hj hn
      geometry.left geometry.right geometry.separated (eventPos C s) s.t goals goal finish
    rw [pending_swap (C.chain false) (C.chain true) (C.size false) (C.size true)
      s.j (s.i+1), pending_swap (C.chain false) (C.chain true) (C.size false) (C.size true)
      s.j (s.i+1+1)] at base
    have flipped := base.trans or_comm
    simpa only [EventSuffix, eventPos, hs, Bool.not_false, Bool.not_true, hd] using flipped

theorem event_blocked_choices (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (hn : s.i+1 < C.size s.side) (hj : s.j < C.size (!s.side))
    (blocked : s.t + C.dist (eventPos C s) (C.chain s.side (s.i+1)).position <
      (C.chain s.side (s.i+1)).release)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
    EventSuffix C ⟨s.side, s.i+1, s.j, (C.chain s.side (s.i+1)).release⟩ goals goal finish ∨
    EventSuffix C ⟨!s.side, s.j, s.i+1,
      max (s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position)
        (C.chain (!s.side) s.j).release⟩ goals goal finish := by
  have h := event_suffix_choices R L hR hL C hd geometry s hn hj goals goal finish
  simpa only [max_eq_right (le_of_lt blocked)] using h

def eventOffset (C : EventData) (R L : ℕ → ℝ) (side : Bool) (k : ℕ) : ℝ :=
  if side then (C.chain side k).release + L (C.chain side k).position
  else (C.chain side k).release - R (C.chain side k).position

def eventThreshold (R L : ℕ → ℝ) (s : EventState) (C : EventData) : ℝ :=
  if s.side then s.t + L (eventPos C s) else s.t - R (eventPos C s)

/-- The binary-search skip preserves `EventSuffix` exactly, on either chain,
including the case where the search exhausts the chain. -/
theorem event_binary_jump (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (hi : s.i < C.size s.side)
    (mono : ∀ u v, s.i ≤ u → u ≤ v → v < C.size s.side →
      eventOffset C R L s.side u ≤ eventOffset C R L s.side v)
    (served : (C.chain s.side s.i).release ≤ s.t)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    let k := (upperBound (eventOffset C R L s.side) (eventThreshold R L s C)
      s.i (C.size s.side - s.i)).1
    s.i < k ∧ k ≤ C.size s.side ∧
    (EventSuffix C s goals goal finish ↔
      EventSuffix C ⟨s.side, k-1, s.j,
        s.t + C.dist (eventPos C s) (C.chain s.side (k-1)).position⟩ goals goal finish) := by
  cases hs : s.side with
  | false =>
    have m : ∀ u v, s.i ≤ u → u ≤ v → v < C.size false →
        (C.chain false u).release - R (C.chain false u).position ≤
        (C.chain false v).release - R (C.chain false v).position := by
      simpa only [eventOffset, hs, Bool.false_eq_true, ↓reduceIte] using mono
    have base := dual_binary_right_jump R L hR hL (C.chain false) (C.chain true)
      (C.size false) (C.size true) s.i s.j (by simpa only [hs] using hi)
      geometry.left geometry.separated m s.t (by simpa only [hs] using served)
      goals goal finish
    dsimp only at base
    obtain ⟨hk, hka, heq⟩ := base
    have he : (upperBound (fun u => (C.chain false u).release - R (C.chain false u).position)
        (s.t - R (C.chain false s.i).position) s.i (C.size false-s.i)).1 - 1 + 1 =
        (upperBound (fun u => (C.chain false u).release - R (C.chain false u).position)
        (s.t - R (C.chain false s.i).position) s.i (C.size false-s.i)).1 := by omega
    have hoff : eventOffset C R L false =
        fun u => (C.chain false u).release - R (C.chain false u).position := rfl
    simpa only [eventThreshold, EventSuffix, eventPos, hs, hoff, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, hd, he] using And.intro hk (And.intro hka heq)
  | true =>
    have m : ∀ u v, s.i ≤ u → u ≤ v → v < C.size true →
        (C.chain true u).release + L (C.chain true u).position ≤
        (C.chain true v).release + L (C.chain true v).position := by
      simpa only [eventOffset, hs, ↓reduceIte] using mono
    have base := dual_binary_left_jump R L hR hL (C.chain true) (C.chain false)
      (C.size true) (C.size false) s.i s.j (by simpa only [hs] using hi)
      geometry.right (fun u v hu hv => geometry.separated v u hv hu)
      m s.t (by simpa only [hs] using served) goals goal finish
    dsimp only at base
    obtain ⟨hk, hka, heq⟩ := base
    have he : (upperBound (fun u => (C.chain true u).release + L (C.chain true u).position)
        (s.t + L (C.chain true s.i).position) s.i (C.size true-s.i)).1 - 1 + 1 =
        (upperBound (fun u => (C.chain true u).release + L (C.chain true u).position)
        (s.t + L (C.chain true s.i).position) s.i (C.size true-s.i)).1 := by omega
    have hoff : eventOffset C R L true =
        fun u => (C.chain true u).release + L (C.chain true u).position := rfl
    simpa only [eventThreshold, EventSuffix, eventPos, hs, hoff, Bool.not_true,
      ↓reduceIte, hd, he] using And.intro hk (And.intro hka heq)

theorem event_ready_run (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (k : ℕ) (hik : s.i ≤ k) (hk : k < C.size s.side)
    (ready : ∀ u, s.i < u → u ≤ k →
      (C.chain s.side u).release ≤ s.t + C.dist (eventPos C s) (C.chain s.side u).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
    EventSuffix C ⟨s.side, k, s.j,
      s.t + C.dist (eventPos C s) (C.chain s.side k).position⟩ goals goal finish := by
  have idx : s.i+(k-s.i) = k := Nat.add_sub_of_le hik
  cases hs : s.side with
  | false =>
    have base := dual_ready_right_run R L hR hL (C.chain false) (C.chain true)
      (C.size false) (C.size true) s.i s.j (k-s.i)
      (by simpa only [idx, hs] using hk) geometry.left geometry.separated s.t
      (by simpa only [idx, hs, hd, eventPos] using ready) goals goal finish
    simpa only [EventSuffix, eventPos, hs, Bool.not_false, hd, idx] using base
  | true =>
    have base := dual_ready_left_run R L hR hL (C.chain true) (C.chain false)
      (C.size true) (C.size false) s.i s.j (k-s.i)
      (by simpa only [idx, hs] using hk) geometry.right
      (fun u v hu hv => geometry.separated v u hv hu) s.t
      (by simpa only [idx, hs, hd, eventPos] using ready) goals goal finish
    simpa only [EventSuffix, eventPos, hs, Bool.not_true, hd, idx] using base

/-- The low-index switch branch may return immediately to cutoff-1.
This is an equivalence of feasible finishes for one actual source state;
earlier-arrival dominance can then merge sources at the common key. -/
theorem event_low_return_iff (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (o : ℕ)
    (cut : IsCutoff (fun u => (C.chain (!s.side) u).release)
      (C.size (!s.side)) (C.chain s.side s.i).release o)
    (low : s.j < o) (served : (C.chain s.side s.i).release ≤ s.t)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C ⟨!s.side, s.j, s.i+1,
      max (s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position)
        (C.chain (!s.side) s.j).release⟩ goals goal finish ↔
    EventSuffix C ⟨!s.side, o-1, s.i+1,
      s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
        C.dist (C.chain (!s.side) s.j).position (C.chain (!s.side) (o-1)).position⟩
      goals goal finish := by
  have hj := cut.2.1 s.j low
  have d₁ := C.nonneg (eventPos C s) (C.chain (!s.side) s.j).position
  have arrived : (C.chain (!s.side) s.j).release ≤
      s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position := by linarith
  rw [max_eq_left arrived]
  let crossed : EventState := ⟨!s.side, s.j, s.i+1,
    s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position⟩
  have hk : o-1 < C.size (!s.side) := by have := cut.1; omega
  have ready : ∀ u, crossed.i < u → u ≤ o-1 →
      (C.chain crossed.side u).release ≤
        crossed.t + C.dist (eventPos C crossed) (C.chain crossed.side u).position := by
    intro u _ hu
    have hrel := cut.2.1 u (by omega)
    have d₂ := C.nonneg (C.chain (!s.side) s.j).position (C.chain (!s.side) u).position
    have d₁' := d₁
    dsimp only [eventPos] at d₁'
    dsimp only [crossed, eventPos]
    linarith
  exact event_ready_run R L hR hL C hd geometry crossed (o-1) (by dsimp [crossed]; omega)
    hk ready goals goal finish

/-- Exact two-way branching at a blocked state, with the low switch
consolidated to the cutoff. -/
theorem event_compressed_choices (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (hn : s.i+1 < C.size s.side) (hj : s.j < C.size (!s.side))
    (served : (C.chain s.side s.i).release ≤ s.t)
    (blocked : s.t + C.dist (eventPos C s) (C.chain s.side (s.i+1)).position <
      (C.chain s.side (s.i+1)).release)
    (o : ℕ) (cut : IsCutoff (fun u => (C.chain (!s.side) u).release)
      (C.size (!s.side)) (C.chain s.side s.i).release o)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
    EventSuffix C ⟨s.side, s.i+1, s.j, (C.chain s.side (s.i+1)).release⟩ goals goal finish ∨
    (if s.j < o then
      EventSuffix C ⟨!s.side, o-1, s.i+1,
        s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
          C.dist (C.chain (!s.side) s.j).position (C.chain (!s.side) (o-1)).position⟩
        goals goal finish
    else
      EventSuffix C ⟨!s.side, s.j, s.i+1,
        max (s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position)
          (C.chain (!s.side) s.j).release⟩ goals goal finish) := by
  have base := event_blocked_choices R L hR hL C hd geometry s hn hj blocked goals goal finish
  by_cases low : s.j < o
  · rw [ite_eq_left low]
    exact base.trans (or_congr Iff.rfl
      (event_low_return_iff R L hR hL C hd geometry s o cut low served goals goal finish))
  · simpa only [ite_eq_right low] using base

theorem pending_exhausted {Req : Type} (left right : ℕ → Req)
    (a b i j : ℕ) (ha : a ≤ i) (hj : j ≤ b) :
    pending left right a b i j = {q | q ∈ chainSegment right j (b-j)} := by
  ext q
  simp only [pending, Set.mem_ofPred_eq]
  rw [chainSegment_mem]
  constructor
  · rintro (⟨k, hik, hka, _⟩ | ⟨k, hjk, hkb, heq⟩)
    · omega
    · exact ⟨k, hjk, by omega, heq⟩
  · rintro ⟨k, hjk, hkb, heq⟩
    exact Or.inr ⟨k, hjk, by omega, heq⟩

/-- Delaying the final visit preserves all already served requests. -/
theorem timedRoute_delay_finish {Pos : Type} (d : Pos → Pos → ℝ)
    (vs : List (Pos × ℝ)) (goal : Pos) (finish later : ℝ) (hle : finish ≤ later) :
    ∀ x t, timedRoute d x t (vs ++ [(goal, finish)]) →
      timedRoute d x t (vs ++ [(goal, later)]) := by
  induction vs with
  | nil =>
    intro x t h
    exact ⟨le_trans h.1 hle, trivial⟩
  | cons v rest ih =>
    intro x t h
    exact ⟨h.1, ih v.1 v.2 h.2⟩

theorem feasible_delay_finish {Pos : Type} (d : Pos → Pos → ℝ)
    (x : Pos) (t : ℝ) (remaining : Set (Request Pos)) (goals : Set Pos)
    (vs : List (Pos × ℝ)) (goal : Pos) (finish later : ℝ) (hle : finish ≤ later)
    (h : feasible d x t remaining goals ⟨vs, goal, finish⟩) :
    feasible d x t remaining goals ⟨vs, goal, later⟩ := by
  refine ⟨timedRoute_delay_finish d vs goal finish later hle x t h.1, ?_, h.2.2⟩
  intro q hq
  obtain ⟨v, hv, hp, hr⟩ := h.2.1 q hq
  rcases List.mem_append.mp hv with hv | hv
  · exact ⟨v, List.mem_append_left _ hv, hp, hr⟩
  · have heq : v = (goal, finish) := by simpa using hv
    subst v
    exact ⟨(goal, later), by simp, hp, le_trans hr hle⟩

theorem event_completion_right (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (i j : ℕ) (hi : i < C.size false) (hlast : C.size false ≤ i+1)
    (hj : j < C.size true) (t : ℝ)
    (ready : ∀ k, j ≤ k → k < C.size true →
      (C.chain true k).release - R (C.chain true k).position ≤ t - R (C.chain false i).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C ⟨false,i,j,t⟩ goals goal finish ↔
      goal ∈ goals ∧ t + C.dist (C.chain false i).position (C.chain true j).position +
        C.dist (C.chain true j).position goal ≤ finish := by
  let todo := chainSegment (C.chain true) j (C.size true-j)
  have hpending := pending_exhausted (C.chain false) (C.chain true)
    (C.size false) (C.size true) (i+1) j hlast (Nat.le_of_lt hj)
  have hpos : ∀ q ∈ todo, (C.chain false i).position ≤ q.position ∧
      q.position ≤ (C.chain true j).position := by
    intro q hq
    obtain ⟨k, hjk, hkb, heq⟩ := (chainSegment_mem _ _ j q).mp hq
    have hk : k < C.size true := by omega
    subst q
    exact ⟨geometry.separated i k hi hk, geometry.right j k hjk hk⟩
  have hoff : ∀ q ∈ todo, q.release - R q.position ≤ t - R (C.chain false i).position := by
    intro q hq
    obtain ⟨k, hjk, hkb, heq⟩ := (chainSegment_mem _ _ j q).mp hq
    subst q
    exact ready k hjk (by omega)
  have hm : ∃ q ∈ todo, q.position = (C.chain true j).position := by
    refine ⟨C.chain true j, ?_, rfl⟩
    exact (chainSegment_mem _ _ j _).mpr ⟨j, le_rfl, by omega, rfl⟩
  change (∃ vs, feasible C.dist (C.chain false i).position t
    (pending (C.chain false) (C.chain true) (C.size false) (C.size true) (i+1) j)
    goals ⟨vs,goal,finish⟩) ↔ _
  rw [hpending, hd]
  constructor
  · rintro ⟨vs,h⟩
    refine ⟨h.2.2, ?_⟩
    exact (right_completion_optimal R L hR hL _ _ goal t goals h.2.2
      (geometry.separated i j hi hj) todo hpos hoff hm).2 vs finish h
  · rintro ⟨hg,hf⟩
    obtain ⟨vs,h⟩ := (right_completion_optimal R L hR hL _ _ goal t goals hg
      (geometry.separated i j hi hj) todo hpos hoff hm).1
    exact ⟨vs, feasible_delay_finish _ _ _ _ _ _ _ _ _ hf h⟩

theorem event_completion_left (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (i j : ℕ) (hi : i < C.size true) (hlast : C.size true ≤ i+1)
    (hj : j < C.size false) (t : ℝ)
    (ready : ∀ k, j ≤ k → k < C.size false →
      (C.chain false k).release + L (C.chain false k).position ≤ t + L (C.chain true i).position)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C ⟨true,i,j,t⟩ goals goal finish ↔
      goal ∈ goals ∧ t + C.dist (C.chain true i).position (C.chain false j).position +
        C.dist (C.chain false j).position goal ≤ finish := by
  let todo := chainSegment (C.chain false) j (C.size false-j)
  have hpending := pending_exhausted (C.chain true) (C.chain false)
    (C.size true) (C.size false) (i+1) j hlast (Nat.le_of_lt hj)
  have hpos : ∀ q ∈ todo, (C.chain false j).position ≤ q.position ∧
      q.position ≤ (C.chain true i).position := by
    intro q hq
    obtain ⟨k, hjk, hkb, heq⟩ := (chainSegment_mem _ _ j q).mp hq
    have hk : k < C.size false := by omega
    subst q
    exact ⟨geometry.left j k hjk hk, geometry.separated k i hk hi⟩
  have hoff : ∀ q ∈ todo, q.release + L q.position ≤ t + L (C.chain true i).position := by
    intro q hq
    obtain ⟨k, hjk, hkb, heq⟩ := (chainSegment_mem _ _ j q).mp hq
    subst q
    exact ready k hjk (by omega)
  have hm : ∃ q ∈ todo, q.position = (C.chain false j).position := by
    refine ⟨C.chain false j, ?_, rfl⟩
    exact (chainSegment_mem _ _ j _).mpr ⟨j, le_rfl, by omega, rfl⟩
  change (∃ vs, feasible C.dist (C.chain true i).position t
    (pending (C.chain true) (C.chain false) (C.size true) (C.size false) (i+1) j)
    goals ⟨vs,goal,finish⟩) ↔ _
  rw [hpending, hd]
  constructor
  · rintro ⟨vs,h⟩
    refine ⟨h.2.2, ?_⟩
    exact (left_completion_optimal R L hR hL _ _ goal t goals h.2.2
      (geometry.separated j i hj hi) todo hpos hoff hm).2 vs finish h
  · rintro ⟨hg,hf⟩
    obtain ⟨vs,h⟩ := (left_completion_optimal R L hR hL _ _ goal t goals hg
      (geometry.separated j i hj hi) todo hpos hoff hm).1
    exact ⟨vs, feasible_delay_finish _ _ _ _ _ _ _ _ _ hf h⟩

def FinishBy (C : EventData) (goals : Set ℕ) (s : EventState) (bound : ℝ) : Prop :=
  ∃ goal finish, finish ≤ bound ∧ EventSuffix C s goals goal finish

theorem event_suffix_time_lower (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (s : EventState)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ)
    (h : EventSuffix C s goals goal finish) : s.t ≤ finish := by
  obtain ⟨vs,h⟩ := h
  have hr := timedRoute_visit_lower_bound (pathDist R L)
    (pathDist_triangle R L hR hL) _ goal finish (eventPos C s) s.t
    (by simpa only [hd] using h.1) (by simp)
  have hn := pathDist_nonneg R L hR hL (eventPos C s) goal
  linarith

theorem finishBy_time_lower (R L : ℕ → ℝ) (hR : Monotone R) (hL : Monotone L)
    (C : EventData) (hd : C.dist = pathDist R L) (s : EventState)
    (goals : Set ℕ) (bound : ℝ) (h : FinishBy C goals s bound) : s.t ≤ bound := by
  obtain ⟨goal,finish,hb,h⟩ := h
  exact le_trans (event_suffix_time_lower R L hR hL C hd s goals goal finish h) hb

theorem event_suffix_dominance (C : EventData) (side : Bool) (i j k : ℕ)
    (early late : ℝ) (ht : early ≤ late) (hj : j ≤ k)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ)
    (h : EventSuffix C ⟨side,i,j,late⟩ goals goal finish) :
    EventSuffix C ⟨side,i,k,early⟩ goals goal finish := by
  obtain ⟨vs,h⟩ := h
  exact ⟨vs, continuation_dominance C.dist _ ht
    (pending_antitone _ _ _ _ _ hj) goals _ h⟩

def EventInterior (C : EventData) (s : EventState) : Prop :=
  s.i < C.size s.side ∧ s.j < C.size (!s.side)

def eventRank (s : EventState) : ℕ := s.i + s.j

noncomputable def eventBinaryCut (C : EventData) (R L : ℕ → ℝ) (s : EventState) : ℕ :=
  (upperBound (eventOffset C R L s.side) (eventThreshold R L s C)
    s.i (C.size s.side - s.i)).1

noncomputable def eventBinaryState (C : EventData) (R L : ℕ → ℝ) (s : EventState) : EventState :=
  ⟨s.side, eventBinaryCut C R L s - 1, s.j,
    s.t + C.dist (eventPos C s) (C.chain s.side (eventBinaryCut C R L s - 1)).position⟩

theorem event_chain_distance_add (R L : ℕ → ℝ) (C : EventData)
    (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (side : Bool) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hk : k < C.size side) :
    C.dist (C.chain side i).position (C.chain side k).position =
      C.dist (C.chain side i).position (C.chain side j).position +
      C.dist (C.chain side j).position (C.chain side k).position := by
  rw [hd]
  cases side with
  | false =>
    exact pathDist_right_add R L (geometry.left i j hij (by omega))
      (geometry.left j k hjk hk)
  | true =>
    exact pathDist_left_add R L (geometry.right i j hij (by omega))
      (geometry.right j k hjk hk)

theorem event_binary_partition (R L : ℕ → ℝ) (C : EventData)
    (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (hi : s.i < C.size s.side)
    (mono : ∀ u v, s.i ≤ u → u ≤ v → v < C.size s.side →
      eventOffset C R L s.side u ≤ eventOffset C R L s.side v)
    (served : (C.chain s.side s.i).release ≤ s.t) :
    let k := eventBinaryCut C R L s
    s.i < k ∧ k ≤ C.size s.side ∧
      (∀ u, s.i ≤ u → u < k →
        (C.chain s.side u).release ≤ s.t + C.dist (eventPos C s) (C.chain s.side u).position) ∧
      (∀ u, k ≤ u → u < C.size s.side →
        s.t + C.dist (eventPos C s) (C.chain s.side u).position < (C.chain s.side u).release) := by
  have range : s.i + (C.size s.side - s.i) = C.size s.side := by omega
  have part :
      s.i ≤ eventBinaryCut C R L s ∧ eventBinaryCut C R L s ≤ C.size s.side ∧
      (∀ u, s.i ≤ u → u < eventBinaryCut C R L s →
        (C.chain s.side u).release ≤ s.t + C.dist (eventPos C s) (C.chain s.side u).position) ∧
      (∀ u, eventBinaryCut C R L s ≤ u → u < C.size s.side →
        s.t + C.dist (eventPos C s) (C.chain s.side u).position < (C.chain s.side u).release) := by
    cases hs : s.side with
    | false =>
      have range' : s.i + (C.size false - s.i) = C.size false := by simpa [hs] using range
      have base := right_binary_blocker R L (C.chain false) (C.chain false s.i).position
        s.i (C.size false - s.i) s.t
        (fun u hu hub => geometry.left s.i u hu (by omega))
        (by simpa only [eventOffset, hs, Bool.false_eq_true, ↓reduceIte, range'] using mono)
      have offset : eventOffset C R L false =
          (fun k => (C.chain false k).release - R (C.chain false k).position) := by
        funext k
        rfl
      simpa only [eventBinaryCut, hs, offset, eventThreshold, eventPos, hs,
        Bool.false_eq_true, ↓reduceIte, range', hd] using base
    | true =>
      have range' : s.i + (C.size true - s.i) = C.size true := by simpa [hs] using range
      have base := left_binary_blocker R L (C.chain true) (C.chain true s.i).position
        s.i (C.size true - s.i) s.t
        (fun u hu hub => geometry.right s.i u hu (by omega))
        (by simpa only [eventOffset, hs, ↓reduceIte, range'] using mono)
      have offset : eventOffset C R L true =
          (fun k => (C.chain true k).release + L (C.chain true k).position) := by
        funext k
        rfl
      simpa only [eventBinaryCut, hs, offset, eventThreshold, eventPos, hs,
        ↓reduceIte, range', hd] using base
  refine ⟨?_,part.2⟩
  by_contra h
  have bad := part.2.2.2 s.i (by omega) hi
  simp only [eventPos, hd, pathDist_self, add_zero] at bad
  linarith

theorem event_binary_state_guards (R L : ℕ → ℝ) (C : EventData)
    (hd : C.dist = pathDist R L) (geometry : EventGeometry C)
    (s : EventState) (inside : EventInterior C s)
    (mono : ∀ u v, s.i ≤ u → u ≤ v → v < C.size s.side →
      eventOffset C R L s.side u ≤ eventOffset C R L s.side v)
    (served : (C.chain s.side s.i).release ≤ s.t) :
    let u := eventBinaryState C R L s
    EventInterior C u ∧ eventRank s ≤ eventRank u ∧ s.t ≤ u.t ∧
      (C.chain u.side u.i).release ≤ u.t ∧
      (u.i+1 < C.size u.side →
        u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
          (C.chain u.side (u.i+1)).release) := by
  obtain ⟨hk,hbound,ready,blocked⟩ :=
    event_binary_partition R L C hd geometry s inside.1 mono served
  have hik : s.i ≤ eventBinaryCut C R L s - 1 := by omega
  have last : eventBinaryCut C R L s - 1 < C.size s.side := by omega
  have readyLast := ready _ hik (by omega)
  refine ⟨⟨last,inside.2⟩,?_,?_,readyLast,?_⟩
  · dsimp [eventRank,eventBinaryState]; omega
  · exact le_add_of_nonneg_right (C.nonneg _ _)
  · intro hn
    change eventBinaryCut C R L s - 1 + 1 < C.size s.side at hn
    have next : eventBinaryCut C R L s - 1 + 1 = eventBinaryCut C R L s := by omega
    have h := blocked _ (le_refl _) (by omega)
    have add := event_chain_distance_add R L C hd geometry s.side s.i
      (eventBinaryCut C R L s - 1) (eventBinaryCut C R L s) hik (by omega) (by omega)
    dsimp [eventBinaryState,eventPos]
    rw [next]
    dsimp [eventPos] at h
    rw [add] at h
    linarith

end ReleasePath
