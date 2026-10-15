import ReleasePath.Effects

/-!
# The queue invariant

`Inv C goals start c clk` holds for every configuration reached by the
machine, where `clk` is the time of the last extracted entry. Its soundness
fields say every stored label is realizable from the start; its coverage
fields say every feasible finish of the event system is witnessed either by
the incumbent or by a live entry, with ranks (`i + j`) used to break the
circularity created by lazy deletion of stale labels.
-/

namespace ReleasePath

open Classical

noncomputable section

def Sound (C : EventData) (goals : Set ℕ) (start : ℕ) (s : EventState) : Prop :=
  ∀ T, FinishBy C goals s T → InitBy C goals start T

/-- The state represented by a waiting register. -/
def wState (C : EventData) (side : Bool) (i j : ℕ) : EventState :=
  ⟨side, i, j, (C.chain side i).release⟩

structure Inv (C : EventData) (goals : Set ℕ) (start : ℕ) (c : Cfg) (clk : ℝ) : Prop where
  clock : ∀ e ∈ c.queue, clk ≤ e.time C
  waitLive : ∀ side i, i < C.size side →
    Entry.wait side i ∈ c.queue ∨ (C.chain side i).release ≤ clk
  waitValid : ∀ side i, Entry.wait side i ∈ c.queue → i < C.size side
  normalValid : ∀ side i j t, Entry.normal side i j t ∈ c.queue → Valid C ⟨side, i, j, t⟩
  stuckValid : ∀ side i j, c.stuck side i = some j → Valid C (wState C side i j)
  bestQueue : ∀ side i j t, Entry.normal side i j t ∈ c.queue →
    ∃ b, c.best side i j = some b ∧ b ≤ t
  soundQ : ∀ side i j t, Entry.normal side i j t ∈ c.queue →
    Sound C goals start ⟨side, i, j, t⟩
  soundW : ∀ side i j, c.stuck side i = some j → Sound C goals start (wState C side i j)
  soundAns : ∀ A, c.ans = some A → InitBy C goals start A
  covInit : ∀ T, InitBy C goals start T → AnsLe c T ∨ LiveFin C goals c 0 T
  covKey : ∀ side i j b, c.best side i j = some b → ∀ T,
    FinishBy C goals ⟨side, i, j, b⟩ T →
    AnsLe c T ∨ Entry.normal side i j b ∈ c.queue ∨ LiveFin C goals c (i + j + 1) T
  covWait : ∀ side i j, c.stuck side i = some j → ∀ j', j' ≤ j → ∀ T,
    FinishBy C goals (wState C side i j') T →
    AnsLe c T ∨ Entry.wait side i ∈ c.queue ∨ LiveFin C goals c (i + j' + 1) T

/-- The configuration after removing the extracted entry. -/
def erased (c : Cfg) (e : Entry) : Cfg := { c with queue := c.queue.erase e }

theorem popStep_eq (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (e : Entry) :
    popStep C R L D c e = process C R L D (erased c e) e := rfl

theorem erased_mem {c : Cfg} {e e' : Entry} (h : e' ∈ (erased c e).queue) : e' ∈ c.queue :=
  List.mem_of_mem_erase h

theorem erased_mem_of_ne {c : Cfg} {e e' : Entry} (h : e' ∈ c.queue) (hne : e' ≠ e) :
    e' ∈ (erased c e).queue :=
  (List.mem_erase_of_ne hne).mpr h

@[simp] theorem erased_best (c : Cfg) (e : Entry) : (erased c e).best = c.best := rfl
@[simp] theorem erased_stuck (c : Cfg) (e : Entry) : (erased c e).stuck = c.stuck := rfl
@[simp] theorem erased_ans (c : Cfg) (e : Entry) : (erased c e).ans = c.ans := rfl

/-- Live witnesses of rank above the extracted entry survive its removal. -/
theorem liveFin_erase {C : EventData} {goals : Set ℕ} {c : Cfg} {e : Entry} {ρ : ℕ} {T : ℝ}
    (h : LiveFin C goals c ρ T) (hlow : ∀ s, entryState C c e = some s → eventRank s < ρ) :
    LiveFin C goals (erased c e) ρ T := by
  obtain ⟨e', he', s, hs, hρ, hf⟩ := h
  refine ⟨e', erased_mem_of_ne he' ?_, s, hs, hρ, hf⟩
  rintro rfl
  have := hlow s hs
  omega

section expansion

variable {R L : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

theorem crossArrival_ge (u : EventState) : u.t ≤ crossArrival C u :=
  le_add_of_nonneg_right (C.nonneg _ _)

theorem lowChild_ge (u : EventState) : u.t ≤ (lowChild C u).t :=
  le_trans (crossArrival_ge u) (le_add_of_nonneg_right (C.nonneg _ _))

theorem pushedT_ge (u : EventState) : u.t ≤ pushedT C u := by
  unfold pushedT
  split_ifs
  · exact lowChild_ge u
  · exact crossArrival_ge u

theorem pushedState_low (u : EventState) (hl : LowBranch C u) :
    pushedState C u = lowChild C u := by
  unfold pushedState pushedI pushedT lowChild
  rw [ite_eq_left hl, ite_eq_left hl]

theorem pushedState_cross (u : EventState) (hl : ¬ LowBranch C u) (hw : ¬ CrossWaits C u) :
    pushedState C u = crossChild C u := by
  unfold pushedState pushedI pushedT crossChild
  rw [ite_eq_right hl, ite_eq_right hl]
  unfold CrossWaits at hw
  rw [max_eq_left (le_of_lt (lt_of_not_ge hw))]

theorem crossChild_wait (u : EventState) (hw : CrossWaits C u) :
    crossChild C u = wState C (!u.side) u.j (u.i+1) := by
  unfold crossChild wState
  unfold CrossWaits at hw
  rw [max_eq_right hw]

theorem waitChild_eq (u : EventState) : waitChild C u = wState C u.side (u.i+1) u.j := rfl

/-- Validity of the entry that an expansion may push. -/
theorem pushed_valid (u : EventState) (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hp : LowBranch C u ∨ ¬ CrossWaits C u) : Valid C (pushedState C u) := by
  have hge := pushedT_ge (C := C) u
  have prog : ∀ h, h < u.i + 1 → (C.chain u.side h).release ≤ pushedT C u := by
    intro h hh
    exact le_trans (C.release_mono u.side h u.i (by omega) hu.1) (le_trans hu.2.2.1 hge)
  by_cases hl : LowBranch C u
  · have cut := eventCutoff_spec C u.side u.i
    have hl' : u.j < eventCutoff C u.side u.i := hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [pushedState, pushedI, hl, ↓reduceIte]; have := cut.1; omega
    · simp only [pushedState, Bool.not_not]; exact hn
    · simp only [pushedState, pushedI, hl, ↓reduceIte]
      exact le_trans (cut.2.1 _ (by omega)) (le_trans hu.2.2.1 hge)
    · simpa only [pushedState, Bool.not_not] using prog
  · have hw : ¬ CrossWaits C u := by tauto
    have hw' : ¬ crossArrival C u ≤ (C.chain (!u.side) u.j).release := hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [pushedState, pushedI, hl, ↓reduceIte]; exact hu.2.1
    · simp only [pushedState, Bool.not_not]; exact hn
    · simp only [pushedState, pushedI, pushedT, hl, ↓reduceIte]
      exact le_of_lt (lt_of_not_ge hw')
    · simpa only [pushedState, Bool.not_not] using prog

theorem waitReg_valid (u : EventState) (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release) :
    Valid C (wState C u.side (u.i+1) u.j) := by
  have hlt : u.t < (C.chain u.side (u.i+1)).release := by
    have := C.nonneg (eventPos C u) (C.chain u.side (u.i+1)).position
    linarith
  refine ⟨hn, hu.2.1, le_rfl, ?_⟩
  intro h hh
  exact le_trans (hu.2.2.2 h hh) (le_of_lt hlt)

theorem crossReg_valid (u : EventState) (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hw : CrossWaits C u) : Valid C (wState C (!u.side) u.j (u.i+1)) := by
  unfold CrossWaits at hw
  refine ⟨hu.2.1, by simpa only [wState, Bool.not_not] using hn, le_rfl, ?_⟩
  simp only [wState, Bool.not_not]
  intro h hh
  exact le_trans (C.release_mono u.side h u.i (by omega) hu.1)
    (le_trans hu.2.2.1 (le_trans (crossArrival_ge u) hw))

/-- Everything an expansion adds is valid, sound, and no earlier than the
expanded state. -/
theorem expand_new (H : ChainHyp R L C) (u : EventState) (hu : Valid C u)
    (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release)
    (hs : Sound C goals start u) (c1 : Cfg) :
    (∀ e' ∈ (expand C c1 u).queue, e' ∈ c1.queue ∨
      (e' = Entry.normal (!u.side) (pushedI C u) (u.i+1) (pushedT C u) ∧
        Valid C (pushedState C u) ∧ u.t ≤ pushedT C u ∧
        Sound C goals start (pushedState C u) ∧
        (expand C c1 u).best (!u.side) (pushedI C u) (u.i+1) = some (pushedT C u))) ∧
    (∀ s a k, (expand C c1 u).stuck s a = some k → c1.stuck s a = some k ∨
      (Valid C (wState C s a k) ∧ Sound C goals start (wState C s a k) ∧
        u.t < (C.chain s a).release)) := by
  have csound := fun T => child_sound H goals u hu hn hblk T
  constructor
  · intro e' he'
    rcases expand_queue C c1 u e' he' with h | ⟨heq, hp, hbest⟩
    · exact Or.inl h
    · refine Or.inr ⟨heq, pushed_valid u hu hn hp, pushedT_ge u, ?_, hbest⟩
      intro T hf
      apply hs T
      by_cases hl : LowBranch C u
      · rw [pushedState_low u hl] at hf
        exact (csound T).2.1 hl hf
      · have hw : ¬ CrossWaits C u := by tauto
        rw [pushedState_cross u hl hw] at hf
        exact (csound T).2.2 hl hf
  · intro s a k hk
    rcases expand_stuck C c1 u s a k hk with h | ⟨rfl, rfl, rfl⟩ | ⟨hl, hw, rfl, rfl, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨waitReg_valid u hu hn hblk, ?_, ?_⟩
      · intro T hf
        exact hs T ((csound T).1 (by rw [waitChild_eq]; exact hf))
      · have := C.nonneg (eventPos C u) (C.chain u.side (u.i+1)).position
        linarith
    · refine Or.inr ⟨crossReg_valid u hu hn hw, ?_, ?_⟩
      · intro T hf
        exact hs T ((csound T).2.2 hl (by rw [crossChild_wait u hw]; exact hf))
      · have hpos := H.cross_pos u hn hu.2.1
        unfold CrossWaits crossArrival at hw
        linarith

/-! ### Coverage after an expansion -/

/-- A pushed child (or one already dominated by a stored label) is covered. -/
theorem pushed_cover {c : Cfg} {clk : ℝ} (inv : Inv C goals start c clk) {e : Entry}
    {x : Cfg} (hg : Grows (erased c e) x) (ρ : ℕ)
    (hrank : ∀ s, entryState C c e = some s → eventRank s < ρ)
    (side : Bool) (i j : ℕ) (t : ℝ) (hρ : ρ ≤ i + j)
    (hres : Entry.normal side i j t ∈ x.queue ∨ ∃ b, c.best side i j = some b ∧ b ≤ t)
    (T : ℝ) (hf : FinishBy C goals ⟨side, i, j, t⟩ T) :
    AnsLe x T ∨ LiveFin C goals x ρ T := by
  rcases hres with hmem | ⟨b, hb, hbt⟩
  · exact Or.inr ⟨_, hmem, _, rfl, hρ, hf⟩
  · have hfb := finishBy_dom C goals side i j j b t hbt le_rfl T hf
    rcases inv.covKey side i j b hb T hfb with h | h | h
    · exact Or.inl (hg.ans T h)
    · have hne : Entry.normal side i j b ≠ e := by
        rintro rfl
        have := hrank _ rfl
        simp only [eventRank] at this
        omega
      exact Or.inr ⟨_, hg.queue _ (erased_mem_of_ne h hne), _, rfl, hρ, hfb⟩
    · refine Or.inr (liveFin_grows hg (liveFin_mono (by omega) (liveFin_erase h ?_)))
      intro s hs
      have := hrank s hs
      omega

/-- After expanding a blocked state `u`, every finish available from `u` is
witnessed by the incumbent or by a live entry of strictly larger rank. -/
theorem expand_cover (H : ChainHyp R L C) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue)
    (u : EventState) (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release)
    (htp : e.time C ≤ u.t)
    (hrank : ∀ s, entryState C c e = some s → eventRank s ≤ eventRank u)
    (T : ℝ) (hf : FinishBy C goals u T) :
    AnsLe (expand C (erased c e) u) T ∨
      LiveFin C goals (expand C (erased c e) u) (eventRank u + 1) T := by
  have hg : Grows (erased c e) (expand C (erased c e) u) := expand_grows C _ u
  have hclk : clk ≤ e.time C := inv.clock e he
  have hrank' : ∀ s, entryState C c e = some s → eventRank s < eventRank u + 1 :=
    fun s hs => Nat.lt_succ_of_le (hrank s hs)
  have waitIn : ∀ side i, i < C.size side → e.time C < (C.chain side i).release →
      Entry.wait side i ∈ (expand C (erased c e) u).queue := by
    intro side i hi hlt
    rcases inv.waitLive side i hi with h | h
    · apply hg.queue
      apply erased_mem_of_ne h
      rintro rfl
      simp only [Entry.time] at hlt
      exact lt_irrefl _ hlt
    · exfalso; linarith
  rcases (blocked_finishBy H goals u hu hn hblk T).mp hf with hw | hx
  · have hlt : e.time C < (C.chain u.side (u.i+1)).release := by
      have := C.nonneg (eventPos C u) (C.chain u.side (u.i+1)).position
      linarith
    obtain ⟨k, hk, hjk⟩ := expand_waitReg C (erased c e) u
    right
    refine ⟨_, waitIn u.side (u.i+1) hn hlt, wState C u.side (u.i+1) k, ?_, ?_, ?_⟩
    · simp only [entryState, hk, Option.map_some, wState]
    · simp only [eventRank, wState]; omega
    · rw [waitChild_eq] at hw
      exact finishBy_dom C goals _ _ _ _ _ _ le_rfl hjk T hw
  · by_cases hl : LowBranch C u
    · have hl' : u.j < eventCutoff C u.side u.i := hl
      rw [ite_eq_left hl', ← pushedState_low u hl] at hx
      have hres := expand_pushed C (erased c e) u (Or.inl hl)
      refine pushed_cover inv hg _ hrank' _ _ _ _ ?_ hres T hx
      simp only [eventRank, pushedI, hl, ↓reduceIte]
      omega
    · have hl' : ¬ u.j < eventCutoff C u.side u.i := hl
      rw [ite_eq_right hl'] at hx
      by_cases hw : CrossWaits C u
      · rw [crossChild_wait u hw] at hx
        have hpos := H.cross_pos u hn hu.2.1
        have hw' : crossArrival C u ≤ (C.chain (!u.side) u.j).release := hw
        have hlt : e.time C < (C.chain (!u.side) u.j).release := by
          unfold crossArrival at hw'
          linarith
        obtain ⟨k, hk, hik⟩ := expand_crossReg C (erased c e) u hl hw
        right
        refine ⟨_, waitIn (!u.side) u.j hu.2.1 hlt, wState C (!u.side) u.j k, ?_, ?_, ?_⟩
        · simp only [entryState, hk, Option.map_some, wState]
        · simp only [eventRank, wState]; omega
        · exact finishBy_dom C goals _ _ _ _ _ _ le_rfl hik T hx
      · rw [← pushedState_cross u hl hw] at hx
        have hres := expand_pushed C (erased c e) u (Or.inr hw)
        refine pushed_cover inv hg _ hrank' _ _ _ _ ?_ hres T hx
        simp only [eventRank, pushedI, hl, ↓reduceIte]
        omega

end expansion

/-! ### Coverage of the extracted entry -/

section pop

variable {R L D : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

theorem normal_notDone (H : ChainHyp R L C) (s : EventState) (hv : Valid C s)
    (hcut : ¬ eventBinaryCut C R L s = C.size s.side) :
    eventBinaryCut C R L s < C.size s.side := by
  have part := event_binary_partition R L C H.dist H.geometry s hv.1
    (H.offsetMono s.side s.i) hv.2.2.1
  exact lt_of_le_of_ne part.2.1 hcut

/-- A fresh (non-stale) normal entry is fully replaced by its expansion. -/
theorem normal_cover (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {side : Bool} {i j : ℕ} {t : ℝ}
    (he : Entry.normal side i j t ∈ c.queue) (hfresh : ¬ Stale (c.best side i j) t)
    (T : ℝ) (hf : FinishBy C goals ⟨side, i, j, t⟩ T) :
    AnsLe (popStep C R L D c (.normal side i j t)) T ∨
      LiveFin C goals (popStep C R L D c (.normal side i j t)) (i + j + 1) T := by
  have hv := inv.normalValid side i j t he
  rw [popStep_eq, process_normal, erased_best, ite_eq_right hfresh]
  split_ifs with hcut
  · left
    apply complete_ansLe
    exact (finishBy_of_completion H hD _ (exhausted_suffix H _ hv.1 hv.2.1 hv.2.2.1 hcut goals)
      T).mp hf
  · have notDone := normal_notDone H _ hv hcut
    obtain ⟨hu, hside, hj, hi, ht, hn, hblk⟩ := skip_facts H _ hv notDone
    have hfu := (skip_finishBy H goals _ hv T).mp hf
    have hrank : ∀ s, entryState C c (.normal side i j t) = some s →
        eventRank s ≤ eventRank (eventBinaryState C R L ⟨side, i, j, t⟩) := by
      intro s hs
      simp only [entryState, Option.some.injEq] at hs
      subst hs
      simp only [eventRank] at hi hj ⊢
      omega
    rcases expand_cover H inv he _ hu hn hblk (by simpa [Entry.time] using ht) hrank T hfu with
      h | h
    · exact Or.inl h
    · refine Or.inr (liveFin_mono ?_ h)
      simp only [eventRank] at hi hj ⊢
      omega

/-- A waiting event with a registered index is fully replaced by its expansion. -/
theorem wait_cover (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {side : Bool} {i j : ℕ}
    (he : Entry.wait side i ∈ c.queue) (hst : c.stuck side i = some j)
    (T : ℝ) (hf : FinishBy C goals (wState C side i j) T) :
    AnsLe (popStep C R L D c (.wait side i)) T ∨
      LiveFin C goals (popStep C R L D c (.wait side i)) (i + j + 1) T := by
  have hv := inv.stuckValid side i j hst
  rw [popStep_eq, process_wait_some C R L D (erased c (.wait side i)) side i j hst]
  unfold settle
  split_ifs with hn
  · have hblk := H.wait_blocked side i hn
    exact expand_cover H inv he (wState C side i j) hv hn hblk le_rfl
      (by intro s hs; simp only [entryState, hst, Option.map_some, Option.some.injEq] at hs
          subst hs; exact le_rfl) T hf
  · left
    apply complete_ansLe
    exact (finishBy_of_completion H hD _ (terminal_suffix H _ hv.1 (by simp only [wState] at hn ⊢; omega)
      hv.2.1 hv.2.2.1 goals) T).mp hf

/-- A stale entry is covered by its stored label. -/
theorem stale_cover {c : Cfg} {clk : ℝ} (inv : Inv C goals start c clk) {side : Bool} {i j : ℕ}
    {t : ℝ} (hstale : Stale (c.best side i j) t)
    (T : ℝ) (hf : FinishBy C goals ⟨side, i, j, t⟩ T) :
    AnsLe (popStep C R L D c (.normal side i j t)) T ∨
      LiveFin C goals (popStep C R L D c (.normal side i j t)) (i + j) T := by
  rw [popStep_eq, process_normal, erased_best, ite_eq_left hstale]
  obtain ⟨b, hb, hbt⟩ := hstale
  have hfb := finishBy_dom C goals side i j j b t (le_of_lt hbt) le_rfl T hf
  rcases inv.covKey side i j b hb T hfb with h | h | h
  · exact Or.inl h
  · have hne : Entry.normal side i j b ≠ Entry.normal side i j t := by
      intro heq
      injection heq with _ _ _ h4
      linarith
    exact Or.inr ⟨_, erased_mem_of_ne h hne, _, rfl, le_rfl, hfb⟩
  · refine Or.inr (liveFin_mono (Nat.le_succ _) (liveFin_erase h ?_))
    intro s hs
    simp only [entryState, Option.some.injEq] at hs
    subst hs
    simp only [eventRank]
    omega

/-- The extracted entry's own state is covered after processing. -/
theorem pop_cover (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue)
    (s : EventState) (hs : entryState C c e = some s) (T : ℝ) (hf : FinishBy C goals s T) :
    AnsLe (popStep C R L D c e) T ∨ LiveFin C goals (popStep C R L D c e) (eventRank s) T := by
  cases e with
  | normal side i j t =>
    simp only [entryState, Option.some.injEq] at hs
    subst hs
    by_cases hstale : Stale (c.best side i j) t
    · exact stale_cover inv hstale T hf
    · rcases normal_cover H hD inv he hstale T hf with h | h
      · exact Or.inl h
      · exact Or.inr (liveFin_mono (by simp only [eventRank]; omega) h)
  | wait side i =>
    simp only [entryState] at hs
    cases hst : c.stuck side i with
    | none => rw [hst] at hs; simp at hs
    | some j =>
      rw [hst] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      rcases wait_cover H hD inv he hst T hf with h | h
      · exact Or.inl h
      · exact Or.inr (liveFin_mono (by simp only [eventRank]; omega) h)

/-- Every live witness survives one step, possibly replaced by later entries. -/
theorem liveFin_step (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue) {ρ : ℕ} {T : ℝ}
    (h : LiveFin C goals c ρ T) :
    AnsLe (popStep C R L D c e) T ∨ LiveFin C goals (popStep C R L D c e) ρ T := by
  obtain ⟨e', he', s, hs, hρ, hf⟩ := h
  by_cases hne : e' = e
  · subst hne
    rcases pop_cover H hD inv he' s hs T hf with h | h
    · exact Or.inl h
    · exact Or.inr (liveFin_mono hρ h)
  · right
    rw [popStep_eq]
    exact liveFin_grows (process_grows C R L D _ e)
      ⟨e', erased_mem_of_ne he' hne, s, hs, hρ, hf⟩

end pop

/-! ### Bookkeeping facts about one processing step -/

section step

variable {R L D : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

/-- What one processing step may add: valid sound normal entries no earlier
than the extracted time, valid sound register values strictly later than
it, labels only together with their entries, and realizable incumbents. -/
def PostFacts (C : EventData) (goals : Set ℕ) (start : ℕ) (c : Cfg) (e : Entry)
    (post : Cfg) : Prop :=
  (∀ e' ∈ post.queue, e' ∈ (erased c e).queue ∨ ∃ side i j t, e' = .normal side i j t ∧
    Valid C ⟨side, i, j, t⟩ ∧ e.time C ≤ t ∧ Sound C goals start ⟨side, i, j, t⟩ ∧
    post.best side i j = some t) ∧
  (∀ s a k, post.stuck s a = some k → c.stuck s a = some k ∨
    (Valid C (wState C s a k) ∧ Sound C goals start (wState C s a k) ∧
      e.time C < (C.chain s a).release)) ∧
  (∀ s a b, post.best s a b = c.best s a b ∨
    ∃ t, post.best s a b = some t ∧ Entry.normal s a b t ∈ post.queue) ∧
  (∀ A, post.ans = some A → c.ans = some A ∨ InitBy C goals start A)

theorem postFacts_id (c : Cfg) (e : Entry) : PostFacts C goals start c e (erased c e) :=
  ⟨fun _ h => Or.inl h, fun _ _ _ h => Or.inl h, fun _ _ _ => Or.inl rfl,
    fun _ h => Or.inl h⟩

theorem postFacts_complete (c : Cfg) (e : Entry) (v : ℝ) (hv : InitBy C goals start v) :
    PostFacts C goals start c e ((erased c e).complete v) := by
  refine ⟨fun _ h => Or.inl h, fun _ _ _ h => Or.inl h, fun _ _ _ => Or.inl rfl, ?_⟩
  intro A hA
  simp only [Cfg.complete, erased_ans] at hA
  cases hc : c.ans with
  | none =>
    rw [hc] at hA
    simp only [optMin, Option.some.injEq] at hA
    subst hA
    exact Or.inr hv
  | some x =>
    rw [hc] at hA
    simp only [optMin, Option.some.injEq] at hA
    subst hA
    rcases min_choice x v with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr hv

theorem postFacts_expand (H : ChainHyp R L C) (c : Cfg) (e : Entry) (u : EventState)
    (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release)
    (hs : Sound C goals start u) (htp : e.time C ≤ u.t) :
    PostFacts C goals start c e (expand C (erased c e) u) := by
  obtain ⟨hq, hst⟩ := expand_new H u hu hn hblk hs (erased c e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e' he'
    rcases hq e' he' with h | ⟨heq, hv, ht, hsd, hb⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, _, _, _, heq, hv, le_trans htp ht, hsd, hb⟩
  · intro s a k hk
    rcases hst s a k hk with h | ⟨hv, hsd, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨hv, hsd, lt_of_le_of_lt htp hlt⟩
  · intro s a b
    exact expand_best C (erased c e) u s a b
  · intro A hA
    rw [expand_ans] at hA
    exact Or.inl hA

/-- The processing of any extracted entry satisfies the bookkeeping facts. -/
theorem post_facts (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue) :
    PostFacts C goals start c e (popStep C R L D c e) := by
  rw [popStep_eq]
  cases e with
  | normal side i j t =>
    have hv := inv.normalValid side i j t he
    have hsnd := inv.soundQ side i j t he
    rw [process_normal, erased_best]
    split_ifs with hstale hcut
    · exact postFacts_id c _
    · apply postFacts_complete
      apply hsnd
      exact (finishBy_of_completion H hD _
        (exhausted_suffix H _ hv.1 hv.2.1 hv.2.2.1 hcut goals) _).mpr le_rfl
    · have notDone := normal_notDone H _ hv hcut
      obtain ⟨hu, _, _, _, ht, hn, hblk⟩ := skip_facts H _ hv notDone
      refine postFacts_expand H c _ _ hu hn hblk ?_ (by simpa [Entry.time] using ht)
      intro T hf
      exact hsnd T ((skip_finishBy H goals _ hv T).mpr hf)
  | wait side i =>
    cases hst : c.stuck side i with
    | none =>
      rw [process_wait_none C R L D _ side i (by simpa using hst)]
      exact postFacts_id c _
    | some j =>
      have hv := inv.stuckValid side i j hst
      have hsnd := inv.soundW side i j hst
      rw [process_wait_some C R L D _ side i j (by simpa using hst)]
      unfold settle
      split_ifs with hn
      · exact postFacts_expand H c _ (wState C side i j) hv hn (H.wait_blocked side i hn) hsnd
          le_rfl
      · apply postFacts_complete
        apply hsnd
        exact (finishBy_of_completion H hD _ (terminal_suffix H _ hv.1
          (by simp only [wState] at hn ⊢; omega) hv.2.1 hv.2.2.1 goals) _).mpr le_rfl

/-- **Invariant preservation.** Extracting any minimum-time entry and
processing it preserves the invariant, with the clock advanced to the
extracted time. -/
theorem inv_step (H : ChainHyp R L C) (hD : GoalCost R L goals D) {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) {e : Entry} (he : e ∈ c.queue)
    (hmin : ∀ e' ∈ c.queue, e.time C ≤ e'.time C) :
    Inv C goals start (popStep C R L D c e) (e.time C) := by
  obtain ⟨fq, fs, fb, fa⟩ := post_facts (D := D) H hD inv he
  have hg : Grows (erased c e) (popStep C R L D c e) := by
    rw [popStep_eq]; exact process_grows C R L D _ e
  have hclk : clk ≤ e.time C := inv.clock e he
  -- an entry later than the extracted one is still present
  have later : ∀ e', e' ∈ c.queue → e.time C < e'.time C → e' ∈ (popStep C R L D c e).queue := by
    intro e' he' hlt
    apply hg.queue
    apply erased_mem_of_ne he'
    rintro rfl
    exact lt_irrefl _ hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clock
    intro e' he'
    rcases fq e' he' with h | ⟨side, i, j, t, rfl, _, ht, _, _⟩
    · exact hmin e' (erased_mem h)
    · exact ht
  · -- waitLive
    intro side i hi
    by_cases hw : Entry.wait side i ∈ c.queue
    · by_cases heq : Entry.wait side i = e
      · subst heq; exact Or.inr le_rfl
      · exact Or.inl (hg.queue _ (erased_mem_of_ne hw heq))
    · rcases inv.waitLive side i hi with h | h
      · exact absurd h hw
      · exact Or.inr (le_trans h hclk)
  · -- waitValid
    intro side i hw
    rcases fq _ hw with h | ⟨_, _, _, _, heq, _⟩
    · exact inv.waitValid side i (erased_mem h)
    · cases heq
  · -- normalValid
    intro side i j t hm
    rcases fq _ hm with h | ⟨_, _, _, _, heq, hv, _⟩
    · exact inv.normalValid side i j t (erased_mem h)
    · injection heq with h1 h2 h3 h4; subst h1 h2 h3 h4; exact hv
  · -- stuckValid
    intro side i j hk
    rcases fs side i j hk with h | ⟨hv, _⟩
    · exact inv.stuckValid side i j h
    · exact hv
  · -- bestQueue
    intro side i j t hm
    rcases fq _ hm with h | ⟨_, _, _, _, heq, _, _, _, hb⟩
    · obtain ⟨b, hb, hbt⟩ := inv.bestQueue side i j t (erased_mem h)
      obtain ⟨b', hb', hle⟩ := hg.best side i j b hb
      exact ⟨b', hb', le_trans hle hbt⟩
    · injection heq with h1 h2 h3 h4; subst h1 h2 h3 h4; exact ⟨_, hb, le_rfl⟩
  · -- soundQ
    intro side i j t hm
    rcases fq _ hm with h | ⟨_, _, _, _, heq, _, _, hs, _⟩
    · exact inv.soundQ side i j t (erased_mem h)
    · injection heq with h1 h2 h3 h4; subst h1 h2 h3 h4; exact hs
  · -- soundW
    intro side i j hk
    rcases fs side i j hk with h | ⟨_, hs, _⟩
    · exact inv.soundW side i j h
    · exact hs
  · -- soundAns
    intro A hA
    rcases fa A hA with h | h
    · exact inv.soundAns A h
    · exact h
  · -- covInit
    intro T hT
    rcases inv.covInit T hT with h | h
    · exact Or.inl (hg.ans T h)
    · exact liveFin_step H hD inv he h
  · -- covKey
    intro side i j b hb T hf
    rcases fb side i j with hsame | ⟨t, ht, hm⟩
    · rw [hsame] at hb
      rcases inv.covKey side i j b hb T hf with h | h | h
      · exact Or.inl (hg.ans T h)
      · by_cases heq : Entry.normal side i j b = e
        · subst heq
          have hfresh : ¬ Stale (c.best side i j) b := by
            rintro ⟨x, hx, hxb⟩
            rw [hb] at hx
            injection hx with hx
            subst hx
            exact lt_irrefl _ hxb
          rcases normal_cover H hD inv he hfresh T hf with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl (hg.queue _ (erased_mem_of_ne h heq)))
      · rcases liveFin_step H hD inv he h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · rw [ht] at hb
      injection hb with hb
      subst hb
      exact Or.inr (Or.inl hm)
  · -- covWait
    intro side i j hk j' hj' T hf
    by_cases hold : c.stuck side i = some j
    · rcases inv.covWait side i j hold j' hj' T hf with h | h | h
      · exact Or.inl (hg.ans T h)
      · by_cases heq : Entry.wait side i = e
        · subst heq
          have hfj := finishBy_dom C goals side i j' j _ _ le_rfl hj' T hf
          rcases wait_cover H hD inv he hold T hfj with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (liveFin_mono (by omega) h))
        · exact Or.inr (Or.inl (hg.queue _ (erased_mem_of_ne h heq)))
      · rcases liveFin_step H hD inv he h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · rcases fs side i j hk with h | ⟨hv, _, hlt⟩
      · exact absurd h hold
      · right; left
        rcases inv.waitLive side i hv.1 with hw | hw
        · exact later _ hw (by simpa [Entry.time] using hlt)
        · exfalso; linarith

end step

end

end ReleasePath
