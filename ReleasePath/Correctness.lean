import ReleasePath.Invariant

/-!
# Initial invariant and correctness at halting

`init_inv` establishes the invariant for the initial queue; `halt_optimal`
shows that whenever the machine has halted (empty queue, or the minimum
queued time is no smaller than the incumbent) under the invariant, the
incumbent is exactly the least feasible finish of the event system.
-/

namespace ReleasePath

open Classical

noncomputable section

variable {R L D : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

theorem mem_waitEntries (e : Entry) :
    e ∈ waitEntries C ↔ ∃ side i, e = Entry.wait side i ∧ i < C.size side := by
  unfold waitEntries
  simp only [List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨false, i, rfl, hi⟩
    · exact ⟨true, i, rfl, hi⟩
  · rintro ⟨side, i, rfl, hi⟩
    cases side
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

theorem mem_initQueue (e : Entry) :
    e ∈ (initCfg C start).queue ↔
      (∃ side, e = Entry.normal side 0 0 (initTime C start side)) ∨
      ∃ side i, e = Entry.wait side i ∧ i < C.size side := by
  simp only [initCfg, List.mem_cons, mem_waitEntries]
  constructor
  · rintro (rfl | rfl | h)
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inl ⟨true, rfl⟩
    · exact Or.inr h
  · rintro (⟨side, rfl⟩ | h)
    · cases side
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h)

theorem entryState_time (c : Cfg) (e : Entry) (s : EventState)
    (h : entryState C c e = some s) : s.t = e.time C := by
  cases e with
  | normal side i j t =>
    simp only [entryState, Option.some.injEq] at h
    subst h; rfl
  | wait side i =>
    simp only [entryState] at h
    cases hst : c.stuck side i with
    | none => rw [hst] at h; simp at h
    | some j =>
      rw [hst] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h; rfl

/-- The two initial states are exactly the event-system optimum. -/
theorem initBy_iff (H : ChainHyp R L C) (T : ℝ) :
    InitBy C goals start T ↔
      FinishBy C goals ⟨false, 0, 0, initTime C start false⟩ T ∨
      FinishBy C goals ⟨true, 0, 0, initTime C start true⟩ T := by
  have base := fun g f => event_initial_choices R L H.monoR H.monoL C H.dist H.geometry
    (H.nonempty false) (H.nonempty true) start goals g f
  constructor
  · rintro ⟨g, f, hf, vs, h⟩
    rcases (base g f).mp ⟨vs, h⟩ with h | h
    · exact Or.inl ⟨g, f, hf, h⟩
    · exact Or.inr ⟨g, f, hf, h⟩
  · rintro (⟨g, f, hf, h⟩ | ⟨g, f, hf, h⟩)
    · obtain ⟨vs, h⟩ := (base g f).mpr (Or.inl h)
      exact ⟨g, f, hf, vs, h⟩
    · obtain ⟨vs, h⟩ := (base g f).mpr (Or.inr h)
      exact ⟨g, f, hf, vs, h⟩

def initClock (C : EventData) : ℝ :=
  min (C.chain false 0).release (C.chain true 0).release

theorem initClock_le (side : Bool) (i : ℕ) (hi : i < C.size side) :
    initClock C ≤ (C.chain side i).release := by
  have h0 : (C.chain side 0).release ≤ (C.chain side i).release :=
    C.release_mono side 0 i (Nat.zero_le i) hi
  cases side
  · exact le_trans (min_le_left _ _) h0
  · exact le_trans (min_le_right _ _) h0

theorem init_inv (H : ChainHyp R L C) : Inv C goals start (initCfg C start) (initClock C) := by
  have hstate : ∀ side, Valid C ⟨side, 0, 0, initTime C start side⟩ := by
    intro side
    refine ⟨H.nonempty side, H.nonempty (!side), le_max_right _ _, ?_⟩
    intro h hh; exact absurd hh (Nat.not_lt_zero h)
  have hsound : ∀ side, Sound C goals start ⟨side, 0, 0, initTime C start side⟩ := by
    intro side T hf
    apply (initBy_iff H T).mpr
    cases side
    · exact Or.inl hf
    · exact Or.inr hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases (mem_initQueue e).mp he with ⟨side, rfl⟩ | ⟨side, i, rfl, hi⟩
    · exact le_trans (initClock_le side 0 (H.nonempty side)) (le_max_right _ _)
    · exact initClock_le side i hi
  · intro side i hi
    exact Or.inl ((mem_initQueue _).mpr (Or.inr ⟨side, i, rfl, hi⟩))
  · intro side i hw
    rcases (mem_initQueue _).mp hw with ⟨_, h⟩ | ⟨side', i', h, hi⟩
    · cases h
    · injection h with h1 h2; subst h1 h2; exact hi
  · intro side i j t hm
    rcases (mem_initQueue _).mp hm with ⟨side', h⟩ | ⟨_, _, h, _⟩
    · injection h with h1 h2 h3 h4; subst h1 h2 h3 h4; exact hstate _
    · cases h
  · intro side i j h; simp [initCfg] at h
  · intro side i j t hm
    rcases (mem_initQueue _).mp hm with ⟨side', h⟩ | ⟨_, _, h, _⟩
    · injection h with h1 h2 h3 h4; subst h1 h2 h3 h4
      exact ⟨_, by simp [initCfg], le_rfl⟩
    · cases h
  · intro side i j t hm
    rcases (mem_initQueue _).mp hm with ⟨side', h⟩ | ⟨_, _, h, _⟩
    · injection h with h1 h2 h3 h4; subst h1 h2 h3 h4; exact hsound _
    · cases h
  · intro side i j h; simp [initCfg] at h
  · intro A h; simp [initCfg] at h
  · intro T hT
    right
    rcases (initBy_iff H T).mp hT with h | h
    · exact ⟨_, (mem_initQueue _).mpr (Or.inl ⟨false, rfl⟩), _, rfl, Nat.zero_le _, h⟩
    · exact ⟨_, (mem_initQueue _).mpr (Or.inl ⟨true, rfl⟩), _, rfl, Nat.zero_le _, h⟩
  · intro side i j b hb T _
    simp only [initCfg] at hb
    split_ifs at hb with h0
    · obtain ⟨rfl, rfl⟩ := h0
      injection hb with hb
      subst hb
      exact Or.inr (Or.inl ((mem_initQueue _).mpr (Or.inl ⟨side, rfl⟩)))
  · intro side i j h; simp [initCfg] at h

/-- The machine has halted: nothing is left, or the minimum is not below the incumbent. -/
def Halted (C : EventData) (c : Cfg) : Prop :=
  c.queue = [] ∨ ∃ e ∈ c.queue, (∀ e' ∈ c.queue, e.time C ≤ e'.time C) ∧ Halts C c e

/-- At halting, the incumbent is a lower bound for every feasible finish. -/
theorem halt_lower (H : ChainHyp R L C) {c : Cfg} {clk : ℝ} (inv : Inv C goals start c clk)
    (hh : Halted C c) (T : ℝ) (hT : InitBy C goals start T) : AnsLe c T := by
  rcases inv.covInit T hT with h | ⟨e', he', s, hs, _, hf⟩
  · exact h
  · have hst := finishBy_time_lower R L H.monoR H.monoL C H.dist s goals T hf
    rw [entryState_time c e' s hs] at hst
    rcases hh with hq | ⟨e, _, hmin, A, hA, hAe⟩
    · rw [hq] at he'; simp at he'
    · exact ⟨A, hA, le_trans hAe (le_trans (hmin e' he') hst)⟩

/-- Some plan always exists: visit every request in list order, waiting as needed. -/
theorem exists_plan (d : ℕ → ℕ → ℝ) (todo : List (Request ℕ)) (goal : ℕ) :
    ∀ x t, ∃ vs finish, timedRoute d x t (vs ++ [(goal, finish)]) ∧
      ∀ q ∈ todo, ∃ v ∈ vs, v.1 = q.position ∧ q.release ≤ v.2 := by
  induction todo with
  | nil =>
    intro x t
    exact ⟨[], t + d x goal, ⟨le_rfl, trivial⟩, by simp⟩
  | cons q rest ih =>
    intro x t
    obtain ⟨vs, finish, hroute, hserve⟩ := ih q.position (max (t + d x q.position) q.release)
    refine ⟨(q.position, max (t + d x q.position) q.release) :: vs, finish,
      ⟨le_max_left _ _, hroute⟩, ?_⟩
    intro q' hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ⟨_, List.mem_cons_self, rfl, le_max_right _ _⟩
    · obtain ⟨v, hv, hp, hr⟩ := hserve q' hq'
      exact ⟨v, List.mem_cons_of_mem _ hv, hp, hr⟩

theorem initBy_exists (hD : GoalCost R L goals D) : ∃ T, InitBy C goals start T := by
  obtain ⟨g, hg, _⟩ := (hD 0).2
  obtain ⟨vs, finish, hroute, hserve⟩ := exists_plan C.dist
    (dualTodo (C.chain false) (C.chain true) (C.size false) (C.size true) 0 0) g start 0
  refine ⟨finish, g, finish, le_rfl, vs, hroute, ?_, hg⟩
  intro q hq
  have hq' : q ∈ {q | q ∈ dualTodo (C.chain false) (C.chain true) (C.size false)
      (C.size true) 0 0} := by
    rw [dualTodo_pending _ _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _)]; exact hq
  obtain ⟨v, hv, hp, hr⟩ := hserve q hq'
  exact ⟨v, List.mem_append_left _ hv, hp, hr⟩

/-- **Correctness at halting.** The incumbent exists and is the least finish
time of the event system. -/
theorem halt_optimal (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) (hh : Halted C c) :
    ∃ A, c.ans = some A ∧ IsLeast {T | InitBy C goals start T} A := by
  obtain ⟨T, hT⟩ := initBy_exists (C := C) (start := start) hD
  obtain ⟨A, hA, _⟩ := halt_lower H inv hh T hT
  refine ⟨A, hA, inv.soundAns A hA, ?_⟩
  intro T' hT'
  obtain ⟨A', hA', hle⟩ := halt_lower H inv hh T' hT'
  rw [hA] at hA'
  injection hA' with h
  subst h
  exact hle

end

end ReleasePath
