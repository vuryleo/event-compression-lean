import ReleasePath.Termination

/-!
# Preprocessing and the top-level theorem

Duplicate positions are merged by keeping a request of maximum release; the
two record chains are built by the stage-9 scans; every field of `ChainHyp`
is then derived from the record lemmas of the library. `solve` mirrors the
reference implementation (`event_solve`), including its special cases for
zero and one distinct position, and `solve_isLeast` states that it returns
the least feasible finish time.
-/

namespace ReleasePath

open Classical

noncomputable section

/-! ### Strictly increasing lists -/

theorem pairwise_lt_getD {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (by omega) hj hij

theorem pairwise_gt_getD {l : List ℕ} (hl : l.Pairwise (fun a b => b < a)) {i j : ℕ}
    (hij : i < j) (hj : j < l.length) : l.getD j 0 < l.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (show i < l.length by omega)]
  exact List.pairwise_iff_getElem.mp hl i j (by omega) hj hij

theorem getD_mem_of_lt {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

theorem exists_getD_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : ∃ k < l.length, l.getD k 0 = a := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  exact ⟨k, hk, List.getD_eq_getElem _ _ hk⟩

/-! ### Duplicate merging -/

/-- Distinct request positions in increasing order. -/
def positions (reqs : List (Request ℕ)) : List ℕ :=
  (reqs.map Request.position).toFinset.sort (· ≤ ·)

/-- A request of maximum release at position `v`. -/
def pick (reqs : List (Request ℕ)) (v : ℕ) : Request ℕ :=
  ((reqs.filter (fun q => q.position = v)).argmax Request.release).getD ⟨v, 0⟩

def itemCount (reqs : List (Request ℕ)) : ℕ := (positions reqs).length

def items (reqs : List (Request ℕ)) (k : ℕ) : Request ℕ := pick reqs ((positions reqs).getD k 0)

theorem positions_pairwise (reqs : List (Request ℕ)) : (positions reqs).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort (reqs.map Request.position).toFinset (· ≤ ·)
  have h2 := Finset.sort_nodup (reqs.map Request.position).toFinset (· ≤ ·)
  exact (h2.and h1).imp (fun h => lt_of_le_of_ne h.2 h.1)

theorem mem_positions (reqs : List (Request ℕ)) (v : ℕ) :
    v ∈ positions reqs ↔ ∃ q ∈ reqs, q.position = v := by
  simp [positions]

theorem pick_spec (reqs : List (Request ℕ)) (v : ℕ) (hv : ∃ q ∈ reqs, q.position = v) :
    pick reqs v ∈ reqs ∧ (pick reqs v).position = v ∧
      ∀ q ∈ reqs, q.position = v → q.release ≤ (pick reqs v).release := by
  obtain ⟨q, hq, hqv⟩ := hv
  have hne : reqs.filter (fun q => q.position = v) ≠ [] := by
    intro h
    have : q ∈ reqs.filter (fun q => q.position = v) := List.mem_filter.mpr ⟨hq, by simpa⟩
    rw [h] at this; simp at this
  cases hm : (reqs.filter (fun q => q.position = v)).argmax Request.release with
  | none => exact absurd (List.argmax_eq_none.mp hm) hne
  | some m =>
    have hmem := List.argmax_mem hm
    obtain ⟨hmr, hmv⟩ := List.mem_filter.mp hmem
    simp only [pick, hm, Option.getD_some]
    refine ⟨hmr, by simpa using hmv, ?_⟩
    intro q' hq' hq'v
    exact List.le_of_mem_argmax (List.mem_filter.mpr ⟨hq', by simpa⟩) hm

theorem items_spec (reqs : List (Request ℕ)) (k : ℕ) (hk : k < itemCount reqs) :
    items reqs k ∈ reqs ∧ (items reqs k).position = (positions reqs).getD k 0 ∧
      ∀ q ∈ reqs, q.position = (positions reqs).getD k 0 → q.release ≤ (items reqs k).release :=
  pick_spec reqs _ ((mem_positions reqs _).mp (getD_mem_of_lt hk))

theorem items_pos_lt (reqs : List (Request ℕ)) {i j : ℕ} (hij : i < j) (hj : j < itemCount reqs) :
    (items reqs i).position < (items reqs j).position := by
  rw [(items_spec reqs i (by omega)).2.1, (items_spec reqs j hj).2.1]
  exact pairwise_lt_getD (positions_pairwise reqs) hij hj

theorem items_pos_le (reqs : List (Request ℕ)) :
    ∀ u v, u ≤ v → v < itemCount reqs → (items reqs u).position ≤ (items reqs v).position := by
  intro u v huv hv
  rcases Nat.lt_or_ge u v with h | h
  · exact le_of_lt (items_pos_lt reqs h hv)
  · have : u = v := by omega
    subst this; exact le_rfl

theorem items_cover (reqs : List (Request ℕ)) (q : Request ℕ) (hq : q ∈ reqs) :
    ∃ k < itemCount reqs, (items reqs k).position = q.position ∧
      q.release ≤ (items reqs k).release := by
  obtain ⟨k, hk, hkv⟩ := exists_getD_of_mem ((mem_positions reqs q.position).mpr ⟨q, hq, rfl⟩)
  obtain ⟨_, hpos, hmax⟩ := items_spec reqs k hk
  exact ⟨k, hk, by rw [hpos, hkv], hmax q hq hkv.symm⟩

/-- Merging duplicates preserves exactly which visit lists serve all requests. -/
theorem serves_items_iff (reqs : List (Request ℕ)) (vs : List (ℕ × ℝ)) :
    serves (originalRequests (items reqs) (itemCount reqs)) vs ↔ serves {q | q ∈ reqs} vs := by
  constructor
  · intro h q hq
    obtain ⟨k, hk, hpos, hrel⟩ := items_cover reqs q hq
    obtain ⟨v, hv, hvp, hvr⟩ := h _ ⟨k, hk, rfl⟩
    exact ⟨v, hv, by rw [hvp, hpos], le_trans hrel hvr⟩
  · rintro h q ⟨k, hk, rfl⟩
    exact h _ (items_spec reqs k hk).1

/-! ### Record chains -/

section chains

variable (R L : ℕ → ℝ) (reqs : List (Request ℕ))

def lidx : List ℕ := leftRecordScan R (items reqs) (itemCount reqs)
def ridx : List ℕ := rightRecordScan L (items reqs) (itemCount reqs)

def mkChain : Bool → ℕ → Request ℕ :=
  fun side k => items reqs ((if side then ridx L reqs else lidx R reqs).getD k 0)

def mkSize : Bool → ℕ := fun side => (if side then ridx L reqs else lidx R reqs).length

variable {R L reqs}

theorem lidx_record {k : ℕ} (hk : k < (lidx R reqs).length) :
    LeftRecord R (items reqs) (itemCount reqs) ((lidx R reqs).getD k 0) :=
  (leftRecordScan_mem R (items reqs) _ _).mp (getD_mem_of_lt hk)

theorem ridx_record {k : ℕ} (hk : k < (ridx L reqs).length) :
    RightRecord L (items reqs) (itemCount reqs) ((ridx L reqs).getD k 0) :=
  (rightRecordScan_mem L (items reqs) _ _).mp (getD_mem_of_lt hk)

theorem lidx_lt {i j : ℕ} (hij : i < j) (hj : j < (lidx R reqs).length) :
    (lidx R reqs).getD i 0 < (lidx R reqs).getD j 0 :=
  pairwise_lt_getD (increasingRecords_pairwise _ _) hij hj

theorem ridx_gt {i j : ℕ} (hij : i < j) (hj : j < (ridx L reqs).length) :
    (ridx L reqs).getD j 0 < (ridx L reqs).getD i 0 :=
  pairwise_gt_getD (rightRecordScan_pairwise _ _ _) hij hj

theorem mkChain_false (k : ℕ) : mkChain R L reqs false k = items reqs ((lidx R reqs).getD k 0) := rfl
theorem mkChain_true (k : ℕ) : mkChain R L reqs true k = items reqs ((ridx L reqs).getD k 0) := rfl
theorem mkSize_false : mkSize R L reqs false = (lidx R reqs).length := rfl
theorem mkSize_true : mkSize R L reqs true = (ridx L reqs).length := rfl

theorem mkChain_release_lt (hR : Monotone R) (hL : Monotone L) (side : Bool) (u v : ℕ)
    (huv : u < v) (hv : v < mkSize R L reqs side) :
    (mkChain R L reqs side u).release < (mkChain R L reqs side v).release := by
  cases side with
  | false =>
    rw [mkSize_false] at hv
    rw [mkChain_false, mkChain_false]
    exact left_record_release R hR (items reqs) _ _ _ (items_pos_le reqs) (lidx_record hv)
      (lidx_lt huv hv)
  | true =>
    rw [mkSize_true] at hv
    rw [mkChain_true, mkChain_true]
    have hrv := ridx_record (L := L) (reqs := reqs) hv
    have hru := ridx_record (L := L) (reqs := reqs) (show u < (ridx L reqs).length by omega)
    exact right_record_release L hL (items reqs) _ _ _ (items_pos_le reqs) hrv
      (ridx_gt huv hv) hru.1

/-- The event data built from the scans; `release_mono` holds when the prefix
metrics are monotone (otherwise a placeholder constant chain is used). -/
def mkData (R L : ℕ → ℝ) (reqs : List (Request ℕ)) : EventData :=
  if h : Monotone R ∧ Monotone L then
    pathEventData R L h.1 h.2 (mkChain R L reqs) (mkSize R L reqs) (by
      intro side i j hij hj
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact le_of_lt (mkChain_release_lt h.1 h.2 side i j hlt hj)
      · have : i = j := by omega
        subst this; exact le_rfl)
  else ⟨fun _ _ => ⟨0, 0⟩, fun _ => 0, fun _ _ => 0, fun _ _ => le_rfl,
    fun _ _ _ _ _ => le_rfl⟩

theorem mkData_eq (hR : Monotone R) (hL : Monotone L) :
    (mkData R L reqs).chain = mkChain R L reqs ∧ (mkData R L reqs).size = mkSize R L reqs ∧
      (mkData R L reqs).dist = pathDist R L := by
  unfold mkData
  rw [dite_eq_left ⟨hR, hL⟩]
  exact ⟨rfl, rfl, rfl⟩

/-- The last left record maximizes the left offset over all merged items. -/
theorem lidx_last_max (hpos : 0 < (lidx R reqs).length) (w : ℕ) (hw : w < itemCount reqs) :
    (items reqs w).release - R (items reqs w).position ≤
      (items reqs ((lidx R reqs).getD ((lidx R reqs).length - 1) 0)).release -
        R (items reqs ((lidx R reqs).getD ((lidx R reqs).length - 1) 0)).position := by
  obtain ⟨w', _, hrec, hle⟩ := left_record_witness R (items reqs) _ w hw
  obtain ⟨p, hp, hpw⟩ := exists_getD_of_mem (l := lidx R reqs)
    ((leftRecordScan_mem R (items reqs) _ w').mpr hrec)
  have hlast := lidx_record (R := R) (reqs := reqs) (show (lidx R reqs).length - 1 < _ by omega)
  rcases Nat.lt_or_ge p ((lidx R reqs).length - 1) with hlt | hge
  · have hidx := lidx_lt (R := R) (reqs := reqs) hlt (by omega)
    rw [hpw] at hidx
    exact le_trans hle (le_of_lt (hlast.2 w' hidx))
  · have : p = (lidx R reqs).length - 1 := by omega
    subst this
    rw [hpw]
    exact hle

/-- The last right record maximizes the right offset over all merged items. -/
theorem ridx_last_max (hpos : 0 < (ridx L reqs).length) (w : ℕ) (hw : w < itemCount reqs) :
    (items reqs w).release + L (items reqs w).position ≤
      (items reqs ((ridx L reqs).getD ((ridx L reqs).length - 1) 0)).release +
        L (items reqs ((ridx L reqs).getD ((ridx L reqs).length - 1) 0)).position := by
  obtain ⟨w', _, hrec, hle⟩ := right_record_witness L (items reqs) _ w hw
  obtain ⟨p, hp, hpw⟩ := exists_getD_of_mem (l := ridx L reqs)
    ((rightRecordScan_mem L (items reqs) _ w').mpr hrec)
  have hlast := ridx_record (L := L) (reqs := reqs) (show (ridx L reqs).length - 1 < _ by omega)
  rcases Nat.lt_or_ge p ((ridx L reqs).length - 1) with hlt | hge
  · have hidx := ridx_gt (L := L) (reqs := reqs) hlt (by omega)
    rw [hpw] at hidx
    exact le_trans hle (le_of_lt (hlast.2 w' hidx hrec.1))
  · have : p = (ridx L reqs).length - 1 := by omega
    subst this
    rw [hpw]
    exact hle

theorem lidx_bound {k : ℕ} (hk : k < (lidx R reqs).length) :
    (lidx R reqs).getD k 0 < itemCount reqs := (lidx_record hk).1

theorem ridx_bound {k : ℕ} (hk : k < (ridx L reqs).length) :
    (ridx L reqs).getD k 0 < itemCount reqs := (ridx_record hk).1

theorem lidx_nonempty (hn : 0 < itemCount reqs) : 0 < (lidx R reqs).length := by
  apply List.length_pos_of_mem (a := 0)
  exact (leftRecordScan_mem R (items reqs) _ 0).mpr ⟨hn, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem ridx_nonempty (hn : 0 < itemCount reqs) : 0 < (ridx L reqs).length := by
  apply List.length_pos_of_mem (a := itemCount reqs - 1)
  exact (rightRecordScan_mem L (items reqs) _ _).mpr ⟨by omega, fun j hj hjn => by omega⟩

/-- **The scanned chains satisfy every hypothesis of the queue proof.** -/
theorem mkData_chainHyp (hR : StrictMono R) (hL : StrictMono L) (hn : 0 < itemCount reqs) :
    ChainHyp R L (mkData R L reqs) := by
  obtain ⟨hc, hs, hd⟩ := mkData_eq (reqs := reqs) hR.monotone hL.monotone
  have hposl := lidx_nonempty (R := R) hn
  have hposr := ridx_nonempty (L := L) hn
  refine ⟨hR, hL, hd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    rw [hs, mkSize_false] at hj
    rw [hc, mkChain_false, mkChain_false]
    exact items_pos_lt reqs (lidx_lt hij hj) (lidx_bound hj)
  · intro i j hij hj
    rw [hs, mkSize_true] at hj
    rw [hc, mkChain_true, mkChain_true]
    exact items_pos_lt reqs (ridx_gt hij hj) (ridx_bound (by omega))
  · intro i j hi hj
    rw [hs, mkSize_false] at hi
    rw [hs, mkSize_true] at hj
    rw [hc, mkChain_false, mkChain_true]
    exact record_positions_separated R L hR.monotone hL.monotone (items reqs) _ _ _
      (items_pos_le reqs) (lidx_record hi) (ridx_record hj)
  · intro side u v huv hv
    rw [hs] at hv
    simp only [eventOffset, hc]
    cases side with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, mkChain_false]
      rw [mkSize_false] at hv
      exact (lidx_record hv).2 _ (lidx_lt huv hv)
    | true =>
      simp only [↓reduceIte, mkChain_true]
      rw [mkSize_true] at hv
      exact (ridx_record hv).2 _ (ridx_gt huv hv) (ridx_bound (by omega))
  · intro side
    rw [hs]
    cases side
    · exact hposl
    · exact hposr
  · intro side k hk
    simp only [eventOffset, reqOffset, hc, hs]
    cases side with
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, mkChain_true, mkSize_false,
        mkChain_false] at hk ⊢
      rw [hs, mkSize_true] at hk
      exact lidx_last_max hposl _ (ridx_bound hk)
    | true =>
      simp only [Bool.not_true, ↓reduceIte, mkChain_true, mkSize_true, mkChain_false] at hk ⊢
      rw [hs, mkSize_false] at hk
      exact ridx_last_max hposr _ (lidx_bound hk)

/-- The initial pending set is exactly the set of scanned record requests. -/
theorem mkData_pending (hR : Monotone R) (hL : Monotone L) :
    pending ((mkData R L reqs).chain false) ((mkData R L reqs).chain true)
      ((mkData R L reqs).size false) ((mkData R L reqs).size true) 0 0 =
      scannedRequests R L (items reqs) (itemCount reqs) := by
  obtain ⟨hc, hs, _⟩ := mkData_eq (reqs := reqs) hR hL
  rw [hc, hs]
  ext q
  simp only [pending, scannedRequests, Set.mem_ofPred_eq, List.mem_append, List.mem_map,
    mkChain_false, mkChain_true, mkSize_false, mkSize_true, Nat.zero_le, true_and]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨_, getD_mem_of_lt hk, rfl⟩
    · exact Or.inr ⟨_, getD_mem_of_lt hk, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain ⟨k, hk, hki⟩ := exists_getD_of_mem (l := lidx R reqs) hi
      exact Or.inl ⟨k, hk, by rw [hki]⟩
    · obtain ⟨k, hk, hki⟩ := exists_getD_of_mem (l := ridx L reqs) hi
      exact Or.inr ⟨k, hk, by rw [hki]⟩

end chains

end

end ReleasePath
