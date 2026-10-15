import ReleasePath.Machine

/-!
# Exact effects of the machine operations

Each operation changes at most the queue head, one label, one or two waiting
registers, or the incumbent. These lemmas describe the changes precisely so
that the invariant proof can track every new entry and register value.
-/

namespace ReleasePath

open Classical

noncomputable section

/-! ### push -/

theorem push_queue (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) (e : Entry)
    (h : e ∈ (c.push side i j t).queue) : e ∈ c.queue ∨
      (e = Entry.normal side i j t ∧ (c.push side i j t).best side i j = some t) := by
  unfold Cfg.push at h ⊢
  split_ifs at h ⊢
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr ⟨h, by simp⟩
    · exact Or.inl h
  · exact Or.inl h

theorem push_result (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) :
    (Entry.normal side i j t ∈ (c.push side i j t).queue ∧
      (c.push side i j t).best side i j = some t) ∨
    ∃ b, c.best side i j = some b ∧ b ≤ t := by
  unfold Cfg.push
  split_ifs with himp
  · left; simp
  · right
    cases hb : c.best side i j with
    | none => rw [hb] at himp; exact absurd trivial himp
    | some b =>
      rw [hb] at himp
      exact ⟨b, rfl, le_of_not_gt himp⟩

theorem push_stuck (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) :
    (c.push side i j t).stuck = c.stuck := by
  unfold Cfg.push; split_ifs <;> rfl

theorem push_ans (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) :
    (c.push side i j t).ans = c.ans := by
  unfold Cfg.push; split_ifs <;> rfl

/-- A label changes only by pushing the matching entry. -/
theorem push_best (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) (s : Bool) (a b : ℕ) :
    (c.push side i j t).best s a b = c.best s a b ∨
      ((c.push side i j t).best s a b = some t ∧ s = side ∧ a = i ∧ b = j ∧
        Entry.normal side i j t ∈ (c.push side i j t).queue) := by
  unfold Cfg.push
  split_ifs with himp
  · by_cases hk : s = side ∧ a = i ∧ b = j
    · right
      obtain ⟨rfl, rfl, rfl⟩ := hk
      simp
    · left; simp [hk]
  · left; rfl

/-! ### register -/

theorem register_at (c : Cfg) (side : Bool) (i j : ℕ) :
    (c.register side i j).stuck side i = some (regValue (c.stuck side i) j) := by
  simp [Cfg.register]

theorem register_other (c : Cfg) (side : Bool) (i j : ℕ) (s : Bool) (a : ℕ)
    (h : ¬ (s = side ∧ a = i)) : (c.register side i j).stuck s a = c.stuck s a := by
  simp [Cfg.register, h]

/-- A register value after `register` is either the old value or the new index. -/
theorem register_value (c : Cfg) (side : Bool) (i j : ℕ) (s : Bool) (a k : ℕ)
    (h : (c.register side i j).stuck s a = some k) :
    c.stuck s a = some k ∨ (s = side ∧ a = i ∧ k = j) := by
  by_cases hk : s = side ∧ a = i
  · obtain ⟨rfl, rfl⟩ := hk
    rw [register_at] at h
    simp only [Option.some.injEq] at h
    subst h
    rcases regValue_cases (c.stuck s a) j with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, rfl, h'⟩
  · rw [register_other c side i j s a hk] at h
    exact Or.inl h

/-! ### expand -/

section expand

variable (C : EventData) (c : Cfg) (u : EventState)

/-- Abbreviations for the three expansion branches. -/
def LowBranch : Prop := u.j < eventCutoff C u.side u.i
def CrossWaits : Prop := crossArrival C u ≤ (C.chain (!u.side) u.j).release

theorem expand_low (h : LowBranch C u) :
    expand C c u = (c.register u.side (u.i+1) u.j).push (!u.side)
      (eventCutoff C u.side u.i - 1) (u.i+1) (lowChild C u).t := by
  unfold LowBranch at h; unfold expand; rw [ite_eq_left h]

theorem expand_crossWait (h : ¬ LowBranch C u) (hw : CrossWaits C u) :
    expand C c u = (c.register u.side (u.i+1) u.j).register (!u.side) u.j (u.i+1) := by
  unfold LowBranch at h; unfold CrossWaits at hw; unfold expand; rw [ite_eq_right h, ite_eq_left hw]

theorem expand_crossPush (h : ¬ LowBranch C u) (hw : ¬ CrossWaits C u) :
    expand C c u = (c.register u.side (u.i+1) u.j).push (!u.side) u.j (u.i+1)
      (crossArrival C u) := by
  unfold LowBranch at h; unfold CrossWaits at hw; unfold expand; rw [ite_eq_right h, ite_eq_right hw]

/-- Opposite index and time of the normal entry that the expansion may push. -/
def pushedI : ℕ := if LowBranch C u then eventCutoff C u.side u.i - 1 else u.j

def pushedT : ℝ := if LowBranch C u then (lowChild C u).t else crossArrival C u

def pushedState : EventState := ⟨!u.side, pushedI C u, u.i+1, pushedT C u⟩

theorem expand_queue (e : Entry) (h : e ∈ (expand C c u).queue) :
    e ∈ c.queue ∨ (e = Entry.normal (!u.side) (pushedI C u) (u.i+1) (pushedT C u) ∧
      (LowBranch C u ∨ ¬ CrossWaits C u) ∧
      (expand C c u).best (!u.side) (pushedI C u) (u.i+1) = some (pushedT C u)) := by
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl] at h ⊢
    rcases push_queue _ _ _ _ _ e h with h | h
    · exact Or.inl h
    · right
      unfold pushedI pushedT
      rw [ite_eq_left hl, ite_eq_left hl]
      exact ⟨h.1, Or.inl hl, h.2⟩
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw] at h
      exact Or.inl h
    · rw [expand_crossPush C c u hl hw] at h ⊢
      rcases push_queue _ _ _ _ _ e h with h | h
      · exact Or.inl h
      · right
        unfold pushedI pushedT
        rw [ite_eq_right hl, ite_eq_right hl]
        exact ⟨h.1, Or.inr hw, h.2⟩

theorem expand_ans : (expand C c u).ans = c.ans := by
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl, push_ans]; rfl
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw]; rfl
    · rw [expand_crossPush C c u hl hw, push_ans]; rfl

/-- Register values after expansion. -/
theorem expand_stuck (s : Bool) (a k : ℕ) (h : (expand C c u).stuck s a = some k) :
    c.stuck s a = some k ∨ (s = u.side ∧ a = u.i+1 ∧ k = u.j) ∨
      (¬ LowBranch C u ∧ CrossWaits C u ∧ s = !u.side ∧ a = u.j ∧ k = u.i+1) := by
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl, push_stuck] at h
    rcases register_value c _ _ _ s a k h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw] at h
      rcases register_value _ _ _ _ s a k h with h | h
      · rcases register_value c _ _ _ s a k h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hl, hw, h⟩)
    · rw [expand_crossPush C c u hl hw, push_stuck] at h
      rcases register_value c _ _ _ s a k h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

theorem expand_waitReg : ∃ k, (expand C c u).stuck u.side (u.i+1) = some k ∧ u.j ≤ k := by
  have hg := (register_grows (c.register u.side (u.i+1) u.j) (!u.side) u.j (u.i+1))
  have base : (c.register u.side (u.i+1) u.j).stuck u.side (u.i+1) =
      some (regValue (c.stuck u.side (u.i+1)) u.j) := register_at _ _ _ _
  have hk := regValue_ge_new (c.stuck u.side (u.i+1)) u.j
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl, push_stuck]
    exact ⟨_, base, hk⟩
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw]
      obtain ⟨k, hk', hle⟩ := hg.stuck _ _ _ base
      exact ⟨k, hk', le_trans hk hle⟩
    · rw [expand_crossPush C c u hl hw, push_stuck]
      exact ⟨_, base, hk⟩

theorem expand_crossReg (hl : ¬ LowBranch C u) (hw : CrossWaits C u) :
    ∃ k, (expand C c u).stuck (!u.side) u.j = some k ∧ u.i + 1 ≤ k := by
  rw [expand_crossWait C c u hl hw, register_at]
  exact ⟨_, rfl, regValue_ge_new _ _⟩

/-- The pushed entry is present after expansion, or a label at least as good
was already stored. -/
theorem expand_pushed (hpush : LowBranch C u ∨ ¬ CrossWaits C u) :
    Entry.normal (!u.side) (pushedI C u) (u.i+1) (pushedT C u) ∈ (expand C c u).queue ∨
      ∃ b, c.best (!u.side) (pushedI C u) (u.i+1) = some b ∧ b ≤ pushedT C u := by
  by_cases hl : LowBranch C u
  · unfold pushedI pushedT
    rw [ite_eq_left hl, ite_eq_left hl, expand_low C c u hl]
    rcases push_result (c.register u.side (u.i+1) u.j) _ _ _ _ with h | h
    · exact Or.inl h.1
    · exact Or.inr h
  · have hw : ¬ CrossWaits C u := by tauto
    unfold pushedI pushedT
    rw [ite_eq_right hl, ite_eq_right hl, expand_crossPush C c u hl hw]
    rcases push_result (c.register u.side (u.i+1) u.j) _ _ _ _ with h | h
    · exact Or.inl h.1
    · exact Or.inr h

/-- Labels change only together with a pushed entry. -/
theorem expand_best (s : Bool) (a b : ℕ) :
    (expand C c u).best s a b = c.best s a b ∨
      ∃ t, (expand C c u).best s a b = some t ∧ Entry.normal s a b t ∈ (expand C c u).queue := by
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl]
    rcases push_best (c.register u.side (u.i+1) u.j) (!u.side) (eventCutoff C u.side u.i - 1)
      (u.i+1) (lowChild C u).t s a b with h | ⟨h1, hs, ha, hb, h2⟩
    · exact Or.inl h
    · subst hs ha hb; exact Or.inr ⟨_, h1, h2⟩
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw]; exact Or.inl rfl
    · rw [expand_crossPush C c u hl hw]
      rcases push_best (c.register u.side (u.i+1) u.j) (!u.side) u.j (u.i+1) (crossArrival C u)
        s a b with h | ⟨h1, hs, ha, hb, h2⟩
      · exact Or.inl h
      · subst hs ha hb; exact Or.inr ⟨_, h1, h2⟩

end expand

end

end ReleasePath
