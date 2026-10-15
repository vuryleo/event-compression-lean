import ReleasePath.Correctness

/-!
# Termination with a linear iteration bound

Normal labels can only be stored for *admissible keys*: the two initial keys
and the telescoping switch keys of `switchKeys` (stage 2 of the library).
There are at most `3(a+b)` of them. The potential

  `queue length + waiting entries in queue + 2 * unsettled admissible keys`

drops by at least one in every non-halting step, so the loop halts within
`8(a+b)+2` iterations, where `a`, `b` are the chain lengths.
-/

namespace ReleasePath

open Classical

noncomputable section

/-! ### Shapes of the operations -/

theorem push_shape (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) :
    ((c.push side i j t).queue = c.queue ∧ (c.push side i j t).best = c.best) ∨
    (Improves (c.best side i j) t ∧
      (c.push side i j t).queue = Entry.normal side i j t :: c.queue ∧
      (c.push side i j t).best side i j = some t ∧
      ∀ s a b, ¬ (s = side ∧ a = i ∧ b = j) → (c.push side i j t).best s a b = c.best s a b) := by
  unfold Cfg.push
  split_ifs with himp
  · right
    refine ⟨himp, rfl, by simp, ?_⟩
    intro s a b h
    simp [h]
  · left; exact ⟨rfl, rfl⟩

theorem expand_shape (C : EventData) (c : Cfg) (u : EventState) :
    ((expand C c u).queue = c.queue ∧ (expand C c u).best = c.best) ∨
    (Improves (c.best (!u.side) (pushedI C u) (u.i+1)) (pushedT C u) ∧
      (expand C c u).queue = Entry.normal (!u.side) (pushedI C u) (u.i+1) (pushedT C u) :: c.queue ∧
      (expand C c u).best (!u.side) (pushedI C u) (u.i+1) = some (pushedT C u) ∧
      ∀ s a b, ¬ (s = !u.side ∧ a = pushedI C u ∧ b = u.i+1) →
        (expand C c u).best s a b = c.best s a b) := by
  by_cases hl : LowBranch C u
  · rw [expand_low C c u hl]
    have hI : pushedI C u = eventCutoff C u.side u.i - 1 := ite_eq_left hl
    have hT : pushedT C u = (lowChild C u).t := ite_eq_left hl
    rw [hI, hT]
    exact push_shape _ _ _ _ _
  · by_cases hw : CrossWaits C u
    · rw [expand_crossWait C c u hl hw]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [expand_crossPush C c u hl hw]
      have hI : pushedI C u = u.j := ite_eq_right hl
      have hT : pushedT C u = crossArrival C u := ite_eq_right hl
      rw [hI, hT]
      exact push_shape _ _ _ _ _

/-! ### Admissible keys -/

/-- Cutoffs capped at the last pivot, monotone on all of `ℕ`. -/
def cappedCut (C : EventData) (side : Bool) (i : ℕ) : ℕ :=
  eventCutoff C side (min i (C.size side - 1))

/-- Switch keys landing on chain `side'` (they come from pivots on `!side'`). -/
def sideKeys (C : EventData) (side' : Bool) : Finset (Bool × ℕ × ℕ) :=
  (switchKeys (cappedCut C (!side')) (C.size (!side') - 1)).image (fun p => (side', p.1, p.2))

def KSet (C : EventData) : Finset (Bool × ℕ × ℕ) :=
  {(false, 0, 0), (true, 0, 0)} ∪ sideKeys C false ∪ sideKeys C true

variable {R L D : ℕ → ℝ} {C : EventData} {goals : Set ℕ} {start : ℕ}

theorem sideKeys_card (H : ChainHyp R L C) (side' : Bool) :
    (sideKeys C side').card ≤ C.size side' + 2 * (C.size (!side') - 1) := by
  have hpos := H.nonempty (!side')
  have hmono : Monotone (cappedCut C (!side')) :=
    capped_eventCutoff_mono C (!side') (C.size (!side') - 1) (by omega)
  have hmax : cappedCut C (!side') (C.size (!side') - 1) ≤ C.size side' := by
    have := (eventCutoff_spec C (!side') (min (C.size (!side') - 1) (C.size (!side') - 1))).1
    simpa only [cappedCut, Bool.not_not] using this
  exact le_trans Finset.card_image_le
    (switch_keys_card_le _ hmono (C.size (!side') - 1) (C.size side') hmax)

theorem KSet_card (H : ChainHyp R L C) :
    (KSet C).card ≤ 3 * (C.size false + C.size true) := by
  have h1 := sideKeys_card H false
  have h2 := sideKeys_card H true
  simp only [Bool.not_false, Bool.not_true] at h1 h2
  have h0 : ({(false, 0, 0), (true, 0, 0)} : Finset (Bool × ℕ × ℕ)).card ≤ 2 :=
    Finset.card_le_two
  unfold KSet
  have := Finset.card_union_le ({(false, 0, 0), (true, 0, 0)} ∪ sideKeys C false) (sideKeys C true)
  have := Finset.card_union_le ({(false, 0, 0), (true, 0, 0)} : Finset (Bool × ℕ × ℕ)) (sideKeys C false)
  have := H.nonempty false
  have := H.nonempty true
  omega

/-- The key pushed by the expansion of a valid blocked state is admissible. -/
theorem pushedKey_mem (u : EventState) (hu : Valid C u) (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release) :
    (!u.side, pushedI C u, u.i+1) ∈ KSet C := by
  have hlt : u.t < (C.chain u.side (u.i+1)).release := by
    have := C.nonneg (eventPos C u) (C.chain u.side (u.i+1)).position
    linarith
  have hbound : u.j ≤ eventCutoff C u.side (u.i+1) :=
    blocked_cutoff_bound (fun k => (C.chain (!u.side) k).release) (C.size (!u.side)) u.j
      (eventCutoff C u.side (u.i+1)) u.t _ (le_of_lt hu.2.1) hlt
      (eventCutoff_spec C u.side (u.i+1)) hu.2.2.2
  have hcap : ∀ i, i ≤ C.size u.side - 1 → cappedCut C u.side i = eventCutoff C u.side i := by
    intro i hi
    simp only [cappedCut, Nat.min_eq_left hi]
  have hmem := switch_key_covered (cappedCut C u.side) (C.size u.side - 1) u.i u.j (by omega)
    (by rw [hcap (u.i+1) (by omega)]; exact hbound)
  have hkey : normalSwitchKey (cappedCut C u.side) u.i u.j = (pushedI C u, u.i+1) := by
    unfold normalSwitchKey pushedI LowBranch
    rw [hcap u.i (by omega)]
    split_ifs <;> rfl
  rw [hkey] at hmem
  have hside : (!u.side, pushedI C u, u.i+1) ∈ sideKeys C (!u.side) := by
    unfold sideKeys
    rw [Bool.not_not]
    exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  unfold KSet
  cases hs : u.side
  · rw [hs] at hside
    exact Finset.mem_union_right _ hside
  · rw [hs] at hside
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hside)

/-! ### The shape of one step -/

def PostShape (C : EventData) (c : Cfg) (e : Entry) (post : Cfg) : Prop :=
  (post.queue = c.queue.erase e ∧ post.best = c.best) ∨
  ∃ side i j t, post.queue = Entry.normal side i j t :: c.queue.erase e ∧
    Improves (c.best side i j) t ∧ e.time C ≤ t ∧ (side, i, j) ∈ KSet C ∧
    post.best side i j = some t ∧
    (∀ s a b, ¬ (s = side ∧ a = i ∧ b = j) → post.best s a b = c.best s a b) ∧
    (∀ s a b x, e = Entry.normal s a b x → c.best s a b = some x)

theorem postShape_expand (c : Cfg) (e : Entry) (u : EventState) (hu : Valid C u)
    (hn : u.i + 1 < C.size u.side)
    (hblk : u.t + C.dist (eventPos C u) (C.chain u.side (u.i+1)).position <
      (C.chain u.side (u.i+1)).release)
    (htp : e.time C ≤ u.t)
    (hfresh : ∀ s a b x, e = Entry.normal s a b x → c.best s a b = some x) :
    PostShape C c e (expand C (erased c e) u) := by
  rcases expand_shape C (erased c e) u with ⟨hq, hb⟩ | ⟨himp, hq, hb, hother⟩
  · exact Or.inl ⟨hq, hb⟩
  · exact Or.inr ⟨_, _, _, _, hq, himp, le_trans htp (pushedT_ge u),
      pushedKey_mem u hu hn hblk, hb, hother, hfresh⟩

theorem post_shape (H : ChainHyp R L C) {c : Cfg} {clk : ℝ} (inv : Inv C goals start c clk)
    {e : Entry} (he : e ∈ c.queue) : PostShape C c e (popStep C R L D c e) := by
  rw [popStep_eq]
  cases e with
  | normal side i j t =>
    have hv := inv.normalValid side i j t he
    rw [process_normal, erased_best]
    split_ifs with hstale hcut
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · have notDone := normal_notDone H _ hv hcut
      obtain ⟨hu, _, _, _, ht, hn, hblk⟩ := skip_facts H _ hv notDone
      refine postShape_expand c _ _ hu hn hblk (by simpa [Entry.time] using ht) ?_
      intro s a b x hx
      injection hx with h1 h2 h3 h4
      subst h1 h2 h3 h4
      obtain ⟨y, hy, hyx⟩ := inv.bestQueue _ _ _ _ he
      rcases lt_or_eq_of_le hyx with hlt | heq
      · exact absurd ⟨y, hy, hlt⟩ hstale
      · rw [hy, heq]
  | wait side i =>
    cases hst : c.stuck side i with
    | none =>
      rw [process_wait_none C R L D _ side i (by simpa using hst)]
      exact Or.inl ⟨rfl, rfl⟩
    | some j =>
      have hv := inv.stuckValid side i j hst
      rw [process_wait_some C R L D _ side i j (by simpa using hst)]
      unfold settle
      split_ifs with hn
      · refine postShape_expand c _ (wState C side i j) hv hn (H.wait_blocked side i hn) le_rfl ?_
        intro s a b x hx
        cases hx
      · exact Or.inl ⟨rfl, rfl⟩

/-! ### Counting invariant and potential -/

structure CInv (C : EventData) (c : Cfg) (clk : ℝ) : Prop where
  nodup : c.queue.Nodup
  bestK : ∀ side i j b, c.best side i j = some b → (side, i, j) ∈ KSet C
  settled : ∀ side i j b, c.best side i j = some b → Entry.normal side i j b ∉ c.queue → b ≤ clk

/-- A key is unsettled while its stored label still has a queue entry. -/
def Unsettled (c : Cfg) (k : Bool × ℕ × ℕ) : Prop :=
  ∀ b, c.best k.1 k.2.1 k.2.2 = some b → Entry.normal k.1 k.2.1 k.2.2 b ∈ c.queue

def Entry.isWait : Entry → Bool
  | .wait _ _ => true
  | .normal _ _ _ _ => false

def potential (C : EventData) (c : Cfg) : ℕ :=
  c.queue.length + c.queue.countP Entry.isWait + 2 * ((KSet C).filter (Unsettled c)).card

theorem unsettled_subset {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) (ci : CInv C c clk) {e : Entry} (he : e ∈ c.queue)
    {post : Cfg} (hs : PostShape C c e post) :
    (KSet C).filter (Unsettled post) ⊆ (KSet C).filter (Unsettled c) := by
  intro k hk
  obtain ⟨hkK, hku⟩ := Finset.mem_filter.mp hk
  refine Finset.mem_filter.mpr ⟨hkK, ?_⟩
  obtain ⟨s, a, b⟩ := k
  intro x hx
  have hclk := inv.clock e he
  rcases hs with ⟨hq, hb⟩ | ⟨side, i, j, t, hq, himp, ht, _, hbt, hother, _⟩
  · have := hku x (by simpa [hb] using hx)
    rw [hq] at this
    exact List.mem_of_mem_erase this
  · by_cases hkey : s = side ∧ a = i ∧ b = j
    · obtain ⟨rfl, rfl, rfl⟩ := hkey
      simp only at hx
      rw [hx] at himp
      by_contra hnot
      have := ci.settled s a b x hx hnot
      simp only [Improves] at himp
      linarith
    · have hpost : post.best s a b = some x := by rw [hother s a b hkey]; exact hx
      have hm := hku x hpost
      rw [hq] at hm
      rcases List.mem_cons.mp hm with h | h
      · injection h with h1 h2 h3 _
        exact absurd ⟨h1, h2, h3⟩ hkey
      · exact List.mem_of_mem_erase h

theorem potential_decreases {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) (ci : CInv C c clk) {e : Entry} (he : e ∈ c.queue)
    {post : Cfg} (hs : PostShape C c e post) : potential C post + 1 ≤ potential C c := by
  have hsub := unsettled_subset inv ci he hs
  have hcard := Finset.card_le_card hsub
  have hlen := List.length_erase_of_mem he
  have hpos : 0 < c.queue.length := List.length_pos_of_mem he
  have hcnt := List.countP_erase Entry.isWait c.queue e
  have hcnt_le : (c.queue.erase e).countP Entry.isWait ≤ c.queue.countP Entry.isWait := by
    rw [hcnt]; omega
  unfold potential
  rcases hs with ⟨hq, _⟩ | ⟨side, i, j, t, hq, himp, ht, hK, hbt, hother, hfresh⟩
  · rw [hq]
    omega
  · rw [hq, List.length_cons, List.countP_cons]
    simp only [Entry.isWait, Bool.false_eq_true, ↓reduceIte, add_zero]
    cases e with
    | wait s a =>
      have : (c.queue.erase (Entry.wait s a)).countP Entry.isWait + 1 =
          c.queue.countP Entry.isWait := by
        rw [hcnt]
        simp only [Entry.isWait, he, and_self, ↓reduceIte]
        have : 0 < c.queue.countP Entry.isWait :=
          List.countP_pos_iff.mpr ⟨_, he, by simp [Entry.isWait]⟩
        omega
      omega
    | normal s a b x =>
      have hx := hfresh s a b x rfl
      have hk0 : (s, a, b) ∈ (KSet C).filter (Unsettled c) := by
        refine Finset.mem_filter.mpr ⟨ci.bestK s a b x hx, ?_⟩
        intro y hy
        simp only at hy
        rw [hx] at hy
        injection hy with hy
        subst hy
        exact he
      have hne : ¬ (s = side ∧ a = i ∧ b = j) := by
        rintro ⟨rfl, rfl, rfl⟩
        rw [hx] at himp
        simp only [Improves, Entry.time] at himp ht
        linarith
      have hk0' : (s, a, b) ∉ (KSet C).filter (Unsettled post) := by
        intro hmem
        have hu := (Finset.mem_filter.mp hmem).2
        have hpost : post.best s a b = some x := by rw [hother s a b hne]; exact hx
        have hm := hu x hpost
        rw [hq] at hm
        rcases List.mem_cons.mp hm with h | h
        · injection h with h1 h2 h3 _
          exact hne ⟨h1, h2, h3⟩
        · exact ci.nodup.not_mem_erase h
      have hlt : ((KSet C).filter (Unsettled post)).card <
          ((KSet C).filter (Unsettled c)).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨_, hk0, hk0'⟩)
      omega

theorem cinv_step {c : Cfg} {clk : ℝ}
    (inv : Inv C goals start c clk) (ci : CInv C c clk) {e : Entry} (he : e ∈ c.queue)
    {post : Cfg} (hs : PostShape C c e post) : CInv C post (e.time C) := by
  have hclk := inv.clock e he
  rcases hs with ⟨hq, hb⟩ | ⟨side, i, j, t, hq, himp, ht, hK, hbt, hother, _⟩
  · refine ⟨by rw [hq]; exact ci.nodup.erase e, ?_, ?_⟩
    · intro s a b x hx
      rw [hb] at hx
      exact ci.bestK s a b x hx
    · intro s a b x hx hnot
      rw [hb] at hx
      by_cases hm : Entry.normal s a b x ∈ c.queue
      · by_cases heq : Entry.normal s a b x = e
        · subst heq; exact le_rfl
        · exact absurd (by rw [hq]; exact (List.mem_erase_of_ne heq).mpr hm) hnot
      · exact le_trans (ci.settled s a b x hx hm) hclk
  · refine ⟨?_, ?_, ?_⟩
    · rw [hq]
      refine List.nodup_cons.mpr ⟨?_, ci.nodup.erase e⟩
      intro hm
      obtain ⟨y, hy, hyt⟩ := inv.bestQueue side i j t (List.mem_of_mem_erase hm)
      rw [hy] at himp
      simp only [Improves] at himp
      linarith
    · intro s a b x hx
      by_cases hkey : s = side ∧ a = i ∧ b = j
      · obtain ⟨rfl, rfl, rfl⟩ := hkey; exact hK
      · rw [hother s a b hkey] at hx
        exact ci.bestK s a b x hx
    · intro s a b x hx hnot
      by_cases hkey : s = side ∧ a = i ∧ b = j
      · obtain ⟨rfl, rfl, rfl⟩ := hkey
        rw [hbt] at hx
        injection hx with hx
        subst hx
        exact absurd (by rw [hq]; exact List.mem_cons_self) hnot
      · rw [hother s a b hkey] at hx
        by_cases hm : Entry.normal s a b x ∈ c.queue
        · by_cases heq : Entry.normal s a b x = e
          · subst heq; exact le_rfl
          · have hin : Entry.normal s a b x ∈ post.queue := by
              rw [hq]
              exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne heq).mpr hm)
            exact absurd hin hnot
        · exact le_trans (ci.settled s a b x hx hm) hclk

/-! ### Running the machine -/

theorem step_none_halted (c : Cfg) (h : step C R L D c = none) : Halted C c := by
  unfold step at h
  cases ha : c.queue.argmin (Entry.time C) with
  | none => exact Or.inl (List.argmin_eq_none.mp ha)
  | some e =>
    rw [ha] at h
    simp only at h
    split_ifs at h with hh
    exact Or.inr ⟨e, List.argmin_mem ha, fun e' he' => List.le_of_mem_argmin he' ha, hh⟩

theorem step_some (c c' : Cfg) (h : step C R L D c = some c') :
    ∃ e ∈ c.queue, (∀ e' ∈ c.queue, e.time C ≤ e'.time C) ∧ c' = popStep C R L D c e := by
  unfold step at h
  cases ha : c.queue.argmin (Entry.time C) with
  | none => rw [ha] at h; simp at h
  | some e =>
    rw [ha] at h
    simp only at h
    split_ifs at h with hh
    injection h with h
    exact ⟨e, List.argmin_mem ha, fun e' he' => List.le_of_mem_argmin he' ha, h.symm⟩

theorem run_halts (H : ChainHyp R L C) (hD : GoalCost R L goals D) :
    ∀ n c clk, Inv C goals start c clk → CInv C c clk → potential C c ≤ n →
      Halted C (run C R L D n c) ∧ ∃ clk', Inv C goals start (run C R L D n c) clk' := by
  intro n
  induction n with
  | zero =>
    intro c clk inv _ hp
    unfold potential at hp
    have : c.queue = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨Or.inl this, clk, inv⟩
  | succ n ih =>
    intro c clk inv ci hp
    cases hs : step C R L D c with
    | none =>
      simp only [run, hs]
      exact ⟨step_none_halted c hs, clk, inv⟩
    | some c' =>
      simp only [run, hs]
      obtain ⟨e, he, hmin, rfl⟩ := step_some c c' hs
      have shape := post_shape (D := D) H inv he
      have hdec := potential_decreases inv ci he shape
      exact ih _ _ (inv_step H hD inv he hmin) (cinv_step inv ci he shape) (by omega)

/-! ### Initial potential -/

theorem waitEntries_length : (waitEntries C).length = C.size false + C.size true := by
  simp [waitEntries]

theorem waitEntries_nodup : (waitEntries C).Nodup := by
  unfold waitEntries
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · exact List.Nodup.map (fun a b h => by injection h) List.nodup_range
  · exact List.Nodup.map (fun a b h => by injection h) List.nodup_range
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    intro h; injection h with h; cases h

theorem waitEntries_countP :
    (waitEntries C).countP Entry.isWait = C.size false + C.size true := by
  rw [List.countP_eq_length.mpr, waitEntries_length]
  intro x hx
  obtain ⟨_, _, rfl, _⟩ := (mem_waitEntries x).mp hx
  rfl

theorem init_cinv : CInv C (initCfg C start) (initClock C) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [initCfg]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, waitEntries_nodup⟩⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · injection h with h; cases h
      · obtain ⟨_, _, h, _⟩ := (mem_waitEntries _).mp h; cases h
    · intro h
      obtain ⟨_, _, h, _⟩ := (mem_waitEntries _).mp h; cases h
  · intro side i j b hb
    simp only [initCfg] at hb
    split_ifs at hb with h0
    obtain ⟨rfl, rfl⟩ := h0
    unfold KSet
    apply Finset.mem_union_left; apply Finset.mem_union_left
    cases side <;> simp
  · intro side i j b hb hnot
    simp only [initCfg] at hb
    split_ifs at hb with h0
    obtain ⟨rfl, rfl⟩ := h0
    injection hb with hb
    subst hb
    exact absurd ((mem_initQueue _).mpr (Or.inl ⟨side, rfl⟩)) hnot

/-- The iteration budget: eight times the number of chain nodes, plus two. -/
def eventFuel (C : EventData) : ℕ := 8 * (C.size false + C.size true) + 2

theorem init_potential (H : ChainHyp R L C) :
    potential C (initCfg C start) ≤ eventFuel C := by
  unfold potential eventFuel
  have hk := KSet_card H
  have hf : ((KSet C).filter (Unsettled (initCfg C start))).card ≤ (KSet C).card :=
    Finset.card_filter_le _ _
  have hl : (initCfg C start).queue.length = C.size false + C.size true + 2 := by
    simp only [initCfg, List.length_cons, waitEntries_length]
  have hc : (initCfg C start).queue.countP Entry.isWait = C.size false + C.size true := by
    simp only [initCfg, List.countP_cons, Entry.isWait, Bool.false_eq_true, ↓reduceIte,
      add_zero, waitEntries_countP]
  omega

/-- The event-phase result. -/
def eventSolve (C : EventData) (R L D : ℕ → ℝ) (start : ℕ) : Option ℝ :=
  (run C R L D (eventFuel C) (initCfg C start)).ans

/-- **The event machine halts within `8(a+b)+2` iterations.** -/
theorem event_halts (H : ChainHyp R L C) (hD : GoalCost R L goals D) :
    Halted C (run C R L D (eventFuel C) (initCfg C start)) :=
  (run_halts (goals := goals) H hD _ _ _ (init_inv H) init_cinv (init_potential H)).1

/-- **Event-phase correctness.** The machine returns the least finish time of
the two-chain event system. -/
theorem eventSolve_isLeast (H : ChainHyp R L C) (hD : GoalCost R L goals D) :
    ∃ A, eventSolve C R L D start = some A ∧ IsLeast {T | InitBy C goals start T} A := by
  obtain ⟨hh, clk, inv⟩ :=
    run_halts (goals := goals) H hD _ _ _ (init_inv H) (init_cinv (start := start))
      (init_potential H)
  exact halt_optimal H hD inv hh

end

end ReleasePath
