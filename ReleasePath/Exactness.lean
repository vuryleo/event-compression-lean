import ReleasePath.Routes

/-!
# Local exactness of the compressed transitions

Builds on `Routes` (the route lemmas).
`ChainHyp` collects the facts about the two record chains used by the queue
proof; the lemmas below package the exact local recurrences (completion,
binary skip, two-way branching) in the `FinishBy` form consumed by
`Invariant.lean`.
-/

namespace ReleasePath

open Classical

noncomputable section

/-! ## Chain hypotheses and goal costs -/

/-- The offset of a request seen from a given chain: `A = r - R(v)` for the
left chain (`false`), `B = r + L(v)` for the right chain (`true`). -/
def reqOffset (R L : ℕ → ℝ) (side : Bool) (q : Request ℕ) : ℝ :=
  if side then q.release + L q.position else q.release - R q.position

/-- Everything the queue proof needs to know about the two record chains. -/
structure ChainHyp (R L : ℕ → ℝ) (C : EventData) : Prop where
  hR : StrictMono R
  hL : StrictMono L
  dist : C.dist = pathDist R L
  posL : ∀ i j, i < j → j < C.size false →
    (C.chain false i).position < (C.chain false j).position
  posR : ∀ i j, i < j → j < C.size true →
    (C.chain true j).position < (C.chain true i).position
  sep : ∀ i j, i < C.size false → j < C.size true →
    (C.chain false i).position ≤ (C.chain true j).position
  offset : ∀ side u v, u < v → v < C.size side →
    eventOffset C R L side u < eventOffset C R L side v
  nonempty : ∀ side, 0 < C.size side
  top : ∀ side k, k < C.size (!side) →
    reqOffset R L side (C.chain (!side) k) ≤ eventOffset C R L side (C.size side - 1)

/-- `D v` is the distance from `v` to the nearest allowed terminal. -/
def GoalCost (R L : ℕ → ℝ) (goals : Set ℕ) (D : ℕ → ℝ) : Prop :=
  ∀ v, (∀ g ∈ goals, D v ≤ pathDist R L v g) ∧ ∃ g ∈ goals, pathDist R L v g = D v

variable {R L : ℕ → ℝ} {C : EventData}

namespace ChainHyp

theorem monoR (H : ChainHyp R L C) : Monotone R := H.hR.monotone
theorem monoL (H : ChainHyp R L C) : Monotone L := H.hL.monotone

theorem geometry (H : ChainHyp R L C) : EventGeometry C where
  left u v huv hv := by
    rcases Nat.lt_or_ge u v with h | h
    · exact le_of_lt (H.posL u v h hv)
    · have : u = v := by omega
      subst this; exact le_rfl
  right u v huv hv := by
    rcases Nat.lt_or_ge u v with h | h
    · exact le_of_lt (H.posR u v h hv)
    · have : u = v := by omega
      subst this; exact le_rfl
  separated := H.sep

theorem offsetMono (H : ChainHyp R L C) (side : Bool) (i : ℕ) :
    ∀ u v, i ≤ u → u ≤ v → v < C.size side →
      eventOffset C R L side u ≤ eventOffset C R L side v := by
  intro u v _ huv hv
  rcases Nat.lt_or_ge u v with h | h
  · exact le_of_lt (H.offset side u v h hv)
  · have : u = v := by omega
    subst this; exact le_rfl

/-- Moving along a chain from `u` to `v > u` takes positive time. -/
theorem chain_dist_eq (H : ChainHyp R L C) (side : Bool) (u v : ℕ) (huv : u ≤ v)
    (hv : v < C.size side) :
    C.dist (C.chain side u).position (C.chain side v).position =
      if side then L (C.chain side u).position - L (C.chain side v).position
      else R (C.chain side v).position - R (C.chain side u).position := by
  rw [H.dist]
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact pathDist_right R L (H.geometry.left u v huv hv)
  | true =>
    simp only [↓reduceIte]
    exact pathDist_left R L (H.geometry.right u v huv hv)

/-- Arriving at a chain node exactly at its release, the next node of the
same chain is strictly blocked (offsets are strict). -/
theorem wait_blocked (H : ChainHyp R L C) (side : Bool) (i : ℕ)
    (hn : i + 1 < C.size side) :
    (C.chain side i).release +
        C.dist (C.chain side i).position (C.chain side (i+1)).position <
      (C.chain side (i+1)).release := by
  have ho := H.offset side i (i+1) (Nat.lt_succ_self i) hn
  rw [H.chain_dist_eq side i (i+1) (Nat.le_succ i) hn]
  cases side with
  | false =>
    simp only [eventOffset, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    linarith
  | true =>
    simp only [eventOffset, ↓reduceIte] at ho ⊢
    linarith

/-- A non-final chain node is strictly separated from every opposite node. -/
theorem cross_pos (H : ChainHyp R L C) (s : EventState) (hn : s.i + 1 < C.size s.side)
    (hj : s.j < C.size (!s.side)) :
    0 < C.dist (eventPos C s) (C.chain (!s.side) s.j).position :=
  pathEvent_cross_positive R L H.hR H.hL C H.dist H.posL H.posR H.sep s hn hj

end ChainHyp

/-! ## Local exactness of the compressed transitions -/

/-- Completion at the last node of a chain. -/
theorem terminal_suffix (H : ChainHyp R L C) (s : EventState)
    (hi : s.i < C.size s.side) (hlast : C.size s.side ≤ s.i + 1)
    (hj : s.j < C.size (!s.side)) (served : (C.chain s.side s.i).release ≤ s.t)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
      goal ∈ goals ∧ s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
        C.dist (C.chain (!s.side) s.j).position goal ≤ finish := by
  rcases s with ⟨side, i, j, t⟩
  have heq : C.size side - 1 = i := by simp only at hi hlast; omega
  cases side with
  | false =>
    apply event_completion_right R L H.monoR H.monoL C H.dist H.geometry i j hi hlast hj t
    intro k _ hk
    have htop := H.top false k hk
    rw [heq] at htop
    simp only [reqOffset, eventOffset, Bool.false_eq_true, Bool.not_false, ↓reduceIte] at htop
    simp only at served
    linarith
  | true =>
    apply event_completion_left R L H.monoR H.monoL C H.dist H.geometry i j hi hlast hj t
    intro k _ hk
    have htop := H.top true k hk
    rw [heq] at htop
    simp only [reqOffset, eventOffset, Bool.not_true, ↓reduceIte] at htop
    simp only at served
    linarith

/-- Completion after a binary search that exhausts the current chain,
evaluated from the state's own position (no explicit skip). -/
theorem exhausted_suffix (H : ChainHyp R L C) (s : EventState)
    (hi : s.i < C.size s.side) (hj : s.j < C.size (!s.side))
    (served : (C.chain s.side s.i).release ≤ s.t)
    (ended : eventBinaryCut C R L s = C.size s.side)
    (goals : Set ℕ) (goal : ℕ) (finish : ℝ) :
    EventSuffix C s goals goal finish ↔
      goal ∈ goals ∧ s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
        C.dist (C.chain (!s.side) s.j).position goal ≤ finish := by
  have jump := (event_binary_jump R L H.monoR H.monoL C H.dist H.geometry s hi
    (H.offsetMono s.side s.i) served goals goal finish).2.2
  have hcut : (upperBound (eventOffset C R L s.side) (eventThreshold R L s C)
      s.i (C.size s.side - s.i)).1 = C.size s.side := ended
  rw [hcut] at jump
  have part := event_binary_partition R L C H.dist H.geometry s hi
    (H.offsetMono s.side s.i) served
  obtain ⟨_, _, ready, _⟩ := part
  rw [ended] at ready
  have hlastlt : C.size s.side - 1 < C.size s.side := by omega
  have hil : s.i ≤ C.size s.side - 1 := by omega
  have readyLast := ready (C.size s.side - 1) hil hlastlt
  let u : EventState := ⟨s.side, C.size s.side - 1, s.j,
    s.t + C.dist (eventPos C s) (C.chain s.side (C.size s.side - 1)).position⟩
  have term := terminal_suffix H u hlastlt (by simp only [u]; omega) hj readyLast goals goal finish
  have hadd : C.dist (eventPos C s) (C.chain s.side (C.size s.side - 1)).position +
      C.dist (C.chain s.side (C.size s.side - 1)).position (C.chain (!s.side) s.j).position =
      C.dist (eventPos C s) (C.chain (!s.side) s.j).position := by
    rw [H.dist]
    unfold eventPos
    cases hs : s.side with
    | false =>
      rw [hs] at hil hlastlt hj
      exact (pathDist_right_add R L (H.geometry.left _ _ hil hlastlt)
        (H.geometry.separated _ _ hlastlt hj)).symm
    | true =>
      rw [hs] at hil hlastlt hj
      exact (pathDist_left_add R L (H.geometry.right _ _ hil hlastlt)
        (H.geometry.separated _ _ hj hlastlt)).symm
  refine jump.trans (term.trans ?_)
  simp only [u, eventPos] at hadd ⊢
  rw [add_assoc s.t, hadd]

/-- The completion value that the algorithm records. -/
def doneCost (C : EventData) (D : ℕ → ℝ) (s : EventState) : ℝ :=
  s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
    D (C.chain (!s.side) s.j).position

/-- Turn an exact completion characterization into the `FinishBy` value. -/
theorem finishBy_of_completion (H : ChainHyp R L C) {goals : Set ℕ} {D : ℕ → ℝ}
    (hD : GoalCost R L goals D) (s : EventState)
    (hcomp : ∀ goal finish, EventSuffix C s goals goal finish ↔
      goal ∈ goals ∧ s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position +
        C.dist (C.chain (!s.side) s.j).position goal ≤ finish)
    (T : ℝ) : FinishBy C goals s T ↔ doneCost C D s ≤ T := by
  constructor
  · rintro ⟨g, f, hfT, h⟩
    obtain ⟨hg, hf⟩ := (hcomp g f).mp h
    have hDg := (hD (C.chain (!s.side) s.j).position).1 g hg
    unfold doneCost
    rw [H.dist] at hf ⊢
    linarith
  · intro hT
    obtain ⟨g, hg, hgd⟩ := (hD (C.chain (!s.side) s.j).position).2
    refine ⟨g, doneCost C D s, hT, (hcomp g _).mpr ⟨hg, ?_⟩⟩
    unfold doneCost
    rw [H.dist, hgd]

/-- Validity of an event state: indices in range, the current node released,
and the opposite prefix released. -/
def Valid (C : EventData) (s : EventState) : Prop :=
  s.i < C.size s.side ∧ s.j < C.size (!s.side) ∧
    (C.chain s.side s.i).release ≤ s.t ∧
    ∀ h, h < s.j → (C.chain (!s.side) h).release ≤ s.t

/-- The three children of a blocked state in the order the implementation
creates them. `crossChild` is the normal switch target. -/
def waitChild (C : EventData) (s : EventState) : EventState :=
  ⟨s.side, s.i+1, s.j, (C.chain s.side (s.i+1)).release⟩

def crossArrival (C : EventData) (s : EventState) : ℝ :=
  s.t + C.dist (eventPos C s) (C.chain (!s.side) s.j).position

def lowChild (C : EventData) (s : EventState) : EventState :=
  ⟨!s.side, eventCutoff C s.side s.i - 1, s.i+1,
    crossArrival C s + C.dist (C.chain (!s.side) s.j).position
      (C.chain (!s.side) (eventCutoff C s.side s.i - 1)).position⟩

def crossChild (C : EventData) (s : EventState) : EventState :=
  ⟨!s.side, s.j, s.i+1, max (crossArrival C s) (C.chain (!s.side) s.j).release⟩

/-- Exact two-way branching at a blocked state, in `FinishBy` form. -/
theorem blocked_finishBy (H : ChainHyp R L C) (goals : Set ℕ) (s : EventState)
    (hv : Valid C s) (hn : s.i + 1 < C.size s.side)
    (blocked : s.t + C.dist (eventPos C s) (C.chain s.side (s.i+1)).position <
      (C.chain s.side (s.i+1)).release) (T : ℝ) :
    FinishBy C goals s T ↔ FinishBy C goals (waitChild C s) T ∨
      (if s.j < eventCutoff C s.side s.i then FinishBy C goals (lowChild C s) T
       else FinishBy C goals (crossChild C s) T) := by
  have ex := fun g f => event_compressed_choices R L H.monoR H.monoL C H.dist H.geometry s hn
    hv.2.1 hv.2.2.1 blocked (eventCutoff C s.side s.i) (eventCutoff_spec C s.side s.i) goals g f
  by_cases low : s.j < eventCutoff C s.side s.i
  · simp only [low, ↓reduceIte] at ex ⊢
    constructor
    · rintro ⟨g, f, hf, h⟩
      rcases (ex g f).mp h with h | h
      · exact Or.inl ⟨g, f, hf, h⟩
      · exact Or.inr ⟨g, f, hf, h⟩
    · rintro (⟨g, f, hf, h⟩ | ⟨g, f, hf, h⟩)
      · exact ⟨g, f, hf, (ex g f).mpr (Or.inl h)⟩
      · exact ⟨g, f, hf, (ex g f).mpr (Or.inr h)⟩
  · simp only [low, ↓reduceIte] at ex ⊢
    constructor
    · rintro ⟨g, f, hf, h⟩
      rcases (ex g f).mp h with h | h
      · exact Or.inl ⟨g, f, hf, h⟩
      · exact Or.inr ⟨g, f, hf, h⟩
    · rintro (⟨g, f, hf, h⟩ | ⟨g, f, hf, h⟩)
      · exact ⟨g, f, hf, (ex g f).mpr (Or.inl h)⟩
      · exact ⟨g, f, hf, (ex g f).mpr (Or.inr h)⟩

/-- The binary skip preserves `FinishBy` exactly. -/
theorem skip_finishBy (H : ChainHyp R L C) (goals : Set ℕ) (s : EventState)
    (hv : Valid C s) (T : ℝ) :
    FinishBy C goals s T ↔ FinishBy C goals (eventBinaryState C R L s) T := by
  have jump := fun g f => (event_binary_jump R L H.monoR H.monoL C H.dist H.geometry s hv.1
    (H.offsetMono s.side s.i) hv.2.2.1 goals g f).2.2
  constructor
  · rintro ⟨g, f, hf, h⟩
    exact ⟨g, f, hf, (jump g f).mp h⟩
  · rintro ⟨g, f, hf, h⟩
    exact ⟨g, f, hf, (jump g f).mpr h⟩

/-- Facts about the state reached by the binary skip. -/
theorem skip_facts (H : ChainHyp R L C) (s : EventState) (hv : Valid C s)
    (notDone : eventBinaryCut C R L s < C.size s.side) :
    let u := eventBinaryState C R L s
    Valid C u ∧ u.side = s.side ∧ u.j = s.j ∧ s.i ≤ u.i ∧ s.t ≤ u.t ∧
      u.i + 1 < C.size u.side ∧
      u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
        (C.chain u.side (u.i+1)).release := by
  have inside : EventInterior C s := ⟨hv.1, hv.2.1⟩
  have guards := event_binary_state_guards R L C H.dist H.geometry s inside
    (H.offsetMono s.side s.i) hv.2.2.1
  have part := event_binary_partition R L C H.dist H.geometry s hv.1
    (H.offsetMono s.side s.i) hv.2.2.1
  obtain ⟨hinside, hrank, ht, hserved, hblock⟩ := guards
  have hn : (eventBinaryState C R L s).i + 1 < C.size (eventBinaryState C R L s).side := by
    simp only [eventBinaryState]; omega
  refine ⟨⟨hinside.1, hinside.2, hserved, ?_⟩, rfl, rfl, ?_, ht, hn, hblock hn⟩
  · intro h hh
    exact le_trans (hv.2.2.2 h hh) ht
  · simp only [eventBinaryState]; omega

/-- Children are dominated by their parent: soundness direction. -/
theorem child_sound (H : ChainHyp R L C) (goals : Set ℕ) (s : EventState)
    (hv : Valid C s) (hn : s.i + 1 < C.size s.side)
    (blocked : s.t + C.dist (eventPos C s) (C.chain s.side (s.i+1)).position <
      (C.chain s.side (s.i+1)).release) (T : ℝ) :
    (FinishBy C goals (waitChild C s) T → FinishBy C goals s T) ∧
    (s.j < eventCutoff C s.side s.i → FinishBy C goals (lowChild C s) T →
      FinishBy C goals s T) ∧
    (¬ s.j < eventCutoff C s.side s.i → FinishBy C goals (crossChild C s) T →
      FinishBy C goals s T) := by
  have hb := blocked_finishBy H goals s hv hn blocked T
  refine ⟨fun h => hb.mpr (Or.inl h), fun low h => hb.mpr (Or.inr ?_),
    fun low h => hb.mpr (Or.inr ?_)⟩
  · simpa only [low, ↓reduceIte] using h
  · simpa only [low, ↓reduceIte] using h

/-- `FinishBy` is antitone in time and in deleted opposite progress. -/
theorem finishBy_dom (C : EventData) (goals : Set ℕ) (side : Bool) (i j k : ℕ)
    (early late : ℝ) (ht : early ≤ late) (hj : j ≤ k) (T : ℝ)
    (h : FinishBy C goals ⟨side, i, j, late⟩ T) : FinishBy C goals ⟨side, i, k, early⟩ T := by
  obtain ⟨g, f, hf, hs⟩ := h
  exact ⟨g, f, hf, event_suffix_dominance C side i j k early late ht hj goals g f hs⟩

end

end ReleasePath
