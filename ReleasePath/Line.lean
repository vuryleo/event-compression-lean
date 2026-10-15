import ReleasePath.Cost

/-!
# The symmetric line

The setting of the paper: requests at real positions, unit speed in both
directions, and the vehicle may stop anywhere. Plans live on `ℝ` with distance
`|x - y|`. `lineSolve` replaces the start and the request positions by their
ranks, extends the coordinates past the last rank by unit steps, and calls
`solve` with `R = L = coordinate`, `D = 0`.

* `lineSolve_isLeast`: `lineSolve reqs s` is the least finish time over all
  feasible plans on the line.
* `lineSolve_iterations`, `lineSolve_cost`: the iteration and cost bounds, with
  `m` the number of distinct request positions.
-/

namespace ReleasePath

open Classical

noncomputable section

/-- Distance on the line. -/
def lineDist (x y : ℝ) : ℝ := |x - y|

/-- Finish times of feasible plans on the line that start at `s` at time `0`
and may end anywhere. -/
def LineFinishTimes (reqs : List (Request ℝ)) (s : ℝ) : Set ℝ :=
  {T | ∃ p : Plan ℝ, feasible lineDist s 0 {q | q ∈ reqs} Set.univ p ∧ p.finish = T}

variable (reqs : List (Request ℝ)) (s : ℝ)

/-- The start and all request positions. -/
def linePts : Finset ℝ := insert s (reqs.map Request.position).toFinset

theorem linePts_nonempty : (linePts reqs s).Nonempty := ⟨s, Finset.mem_insert_self _ _⟩

/-- Coordinate of rank `i`; ranks past the last point continue by unit steps. -/
def lineCoord (i : ℕ) : ℝ :=
  if h : i < (linePts reqs s).card then (linePts reqs s).orderEmbOfFin rfl ⟨i, h⟩
  else (linePts reqs s).max' (linePts_nonempty reqs s) + (((i - (linePts reqs s).card : ℕ) : ℝ) + 1)

/-- Rank of a point among `linePts`. -/
def lineRank (y : ℝ) : ℕ :=
  if h : y ∈ linePts reqs s then (((linePts reqs s).orderIsoOfFin rfl).symm ⟨y, h⟩ : ℕ) else 0

/-- The instance on ranks. -/
def lineReqs : List (Request ℕ) :=
  reqs.map fun q => ⟨lineRank reqs s q.position, q.release⟩

/-- The algorithm on the line. -/
def lineSolve : ℝ :=
  solve (lineCoord reqs s) (lineCoord reqs s) (lineReqs reqs s) (lineRank reqs s s) (fun _ => 0)

variable {reqs s}

theorem start_mem_linePts : s ∈ linePts reqs s := Finset.mem_insert_self _ _

theorem req_mem_linePts {q : Request ℝ} (hq : q ∈ reqs) : q.position ∈ linePts reqs s :=
  Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map_of_mem hq))

theorem lineCoord_rank {y : ℝ} (hy : y ∈ linePts reqs s) :
    lineCoord reqs s (lineRank reqs s y) = y := by
  set e := (linePts reqs s).orderIsoOfFin rfl
  have hk : ((e.symm ⟨y, hy⟩ : Fin _) : ℕ) < (linePts reqs s).card := (e.symm ⟨y, hy⟩).isLt
  have h1 : lineRank reqs s y = ((e.symm ⟨y, hy⟩ : Fin _) : ℕ) := by
    simp only [lineRank, dite_eq_left hy]; rfl
  rw [h1]
  simp only [lineCoord, dite_eq_left hk]
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp [e]

theorem lineCoord_le_max {i : ℕ} (hi : i < (linePts reqs s).card) :
    lineCoord reqs s i ≤ (linePts reqs s).max' (linePts_nonempty reqs s) := by
  simp only [lineCoord, dite_eq_left hi]
  exact Finset.le_max' _ _ (Finset.orderEmbOfFin_mem _ _ _)

theorem lineCoord_strictMono : StrictMono (lineCoord reqs s) := by
  intro i j hij
  by_cases hj : j < (linePts reqs s).card
  · have hi : i < (linePts reqs s).card := by omega
    simp only [lineCoord, dite_eq_left hi, dite_eq_left hj]
    exact ((linePts reqs s).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
  · have hj' : lineCoord reqs s j = (linePts reqs s).max' (linePts_nonempty reqs s) +
        (((j - (linePts reqs s).card : ℕ) : ℝ) + 1) := by simp only [lineCoord, dite_eq_right hj]
    rw [hj']
    by_cases hi : i < (linePts reqs s).card
    · have := lineCoord_le_max (reqs := reqs) (s := s) hi
      have : (0 : ℝ) ≤ ((j - (linePts reqs s).card : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · simp only [lineCoord, dite_eq_right hi]
      have : ((i - (linePts reqs s).card : ℕ) : ℝ) < ((j - (linePts reqs s).card : ℕ) : ℝ) := by
        exact_mod_cast (by omega : i - (linePts reqs s).card < j - (linePts reqs s).card)
      linarith

theorem lineDist_coord (a b : ℕ) :
    lineDist (lineCoord reqs s a) (lineCoord reqs s b) =
      pathDist (lineCoord reqs s) (lineCoord reqs s) a b := by
  have hm := (lineCoord_strictMono (reqs := reqs) (s := s)).monotone
  unfold lineDist pathDist
  split_ifs with h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm h))]
  · exact abs_of_nonneg (sub_nonneg.mpr (hm (by omega)))

theorem lineDist_rank {x y : ℝ} (hx : x ∈ linePts reqs s) (hy : y ∈ linePts reqs s) :
    pathDist (lineCoord reqs s) (lineCoord reqs s) (lineRank reqs s x) (lineRank reqs s y) =
      lineDist x y := by
  rw [← lineDist_coord, lineCoord_rank hx, lineCoord_rank hy]

/-! ### Transporting routes -/

theorem timedRoute_map {α β : Type} {d : α → α → ℝ} {d' : β → β → ℝ} (e : α → β)
    (P : α → Prop) (he : ∀ a b, P a → P b → d' (e a) (e b) = d a b) :
    ∀ (vs : List (α × ℝ)) (x : α) (t : ℝ), P x → (∀ v ∈ vs, P v.1) →
      timedRoute d x t vs → timedRoute d' (e x) t (vs.map fun v => (e v.1, v.2))
  | [], _, _, _, _, _ => trivial
  | v :: vs, x, t, hx, hP, ⟨h1, h2⟩ => by
    have hv := hP v (List.mem_cons_self ..)
    refine ⟨?_, timedRoute_map e P he vs v.1 v.2 hv
      (fun w hw => hP w (List.mem_cons_of_mem _ hw)) h2⟩
    simpa [he x v.1 hx hv] using h1

theorem lineDist_triangle (x y z : ℝ) : lineDist x z ≤ lineDist x y + lineDist y z := by
  unfold lineDist; exact abs_sub_le x y z

theorem lineDist_nonneg (x y : ℝ) : 0 ≤ lineDist x y := abs_nonneg _

/-- Drop the first visit of a route. -/
theorem timedRoute_skip (x : ℝ) (t : ℝ) (v : ℝ × ℝ) :
    ∀ vs : List (ℝ × ℝ), timedRoute lineDist x t (v :: vs) → timedRoute lineDist x t vs
  | [], _ => trivial
  | w :: ws, ⟨h1, h2, h3⟩ => by
    refine ⟨?_, h3⟩
    have := lineDist_triangle x v.1 w.1
    linarith

/-- Visits at points outside `P` can be dropped; the terminal moves to a
point of `P` if necessary, keeping the finish time. -/
theorem grid_route (P : ℝ → Prop) (g f : ℝ) :
    ∀ (vs : List (ℝ × ℝ)) (x t : ℝ), P x → timedRoute lineDist x t (vs ++ [(g, f)]) →
      ∃ (ws : List (ℝ × ℝ)) (y : ℝ), P y ∧ (∀ w ∈ ws, P w.1) ∧
        (∀ v ∈ vs ++ [(g, f)], P v.1 → v ∈ ws ++ [(y, f)]) ∧
        timedRoute lineDist x t (ws ++ [(y, f)])
  | [], x, t, hx, h => by
    by_cases hg : P g
    · exact ⟨[], g, hg, by simp, by simp, h⟩
    · refine ⟨[], x, hx, by simp, ?_, ?_⟩
      · intro v hv hPv
        simp only [List.nil_append, List.mem_singleton] at hv
        subst hv; exact absurd hPv hg
      · have h1 := h.1
        have := lineDist_nonneg x g
        refine ⟨?_, trivial⟩
        simp only [lineDist, sub_self, abs_zero] at h1 ⊢
        simp only [lineDist] at this
        linarith
  | v :: vs, x, t, hx, h => by
    by_cases hv : P v.1
    · obtain ⟨ws, y, hy, hws, hcov, hr⟩ := grid_route P g f vs v.1 v.2 hv h.2
      refine ⟨v :: ws, y, hy, ?_, ?_, ⟨h.1, hr⟩⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hws w hw
      · intro w hw hPw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hcov w hw hPw)
    · obtain ⟨ws, y, hy, hws, hcov, hr⟩ :=
        grid_route P g f vs x t hx (timedRoute_skip x t v _ h)
      refine ⟨ws, y, hy, hws, ?_, hr⟩
      intro w hw hPw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hPw hv
      · exact hcov w hw hPw

/-! ### The two models have the same finish times -/

theorem lineFinishTimes_eq :
    LineFinishTimes reqs s =
      FinishTimes (lineCoord reqs s) (lineCoord reqs s) (lineReqs reqs s) (lineRank reqs s s)
        Set.univ := by
  ext T
  constructor
  · rintro ⟨p, ⟨hroute, hserve, -⟩, rfl⟩
    obtain ⟨ws, y, hy, hws, hcov, hr⟩ :=
      grid_route (· ∈ linePts reqs s) p.terminal p.finish p.visits s 0 start_mem_linePts hroute
    refine ⟨⟨ws.map (fun w => (lineRank reqs s w.1, w.2)), lineRank reqs s y, p.finish⟩,
      ⟨?_, ?_, Set.mem_univ _⟩, rfl⟩
    · have := timedRoute_map (d := lineDist) (d' := pathDist (lineCoord reqs s) (lineCoord reqs s))
        (lineRank reqs s) (· ∈ linePts reqs s) (fun a b ha hb => lineDist_rank ha hb)
        (ws ++ [(y, p.finish)]) s 0 start_mem_linePts
        (by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hws w hw
          · simp only [List.mem_singleton] at hw; subst hw; exact hy) hr
      simpa using this
    · rintro qn hqn
      simp only [Set.mem_ofPred_eq, lineReqs, List.mem_map] at hqn
      obtain ⟨q, hq, rfl⟩ := hqn
      obtain ⟨v, hv, hvpos, hvrel⟩ := hserve q hq
      have hPv : v.1 ∈ linePts reqs s := hvpos ▸ req_mem_linePts hq
      have hmem := hcov v hv hPv
      refine ⟨(lineRank reqs s v.1, v.2), ?_, by simp [hvpos], hvrel⟩
      rcases List.mem_append.mp hmem with hm | hm
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hm, rfl⟩)
      · simp only [List.mem_singleton] at hm
        subst hm
        simp
  · rintro ⟨p, ⟨hroute, hserve, -⟩, rfl⟩
    refine ⟨⟨p.visits.map (fun v => (lineCoord reqs s v.1, v.2)), lineCoord reqs s p.terminal,
      p.finish⟩, ⟨?_, ?_, Set.mem_univ _⟩, rfl⟩
    · have := timedRoute_map (d := pathDist (lineCoord reqs s) (lineCoord reqs s))
        (d' := lineDist) (lineCoord reqs s) (fun _ => True)
        (fun a b _ _ => lineDist_coord a b)
        (p.visits ++ [(p.terminal, p.finish)]) (lineRank reqs s s) 0 trivial
        (fun _ _ => trivial) hroute
      rw [lineCoord_rank start_mem_linePts] at this
      simpa using this
    · intro q hq
      have hqn : (⟨lineRank reqs s q.position, q.release⟩ : Request ℕ) ∈ lineReqs reqs s :=
        List.mem_map.mpr ⟨q, hq, rfl⟩
      obtain ⟨v, hv, hvpos, hvrel⟩ := hserve _ hqn
      refine ⟨(lineCoord reqs s v.1, v.2), ?_, ?_, hvrel⟩
      · have : (lineCoord reqs s v.1, v.2) ∈
            (p.visits ++ [(p.terminal, p.finish)]).map (fun v => (lineCoord reqs s v.1, v.2)) :=
          List.mem_map.mpr ⟨v, hv, rfl⟩
        simpa using this
      · simp only at hvpos ⊢
        rw [hvpos, lineCoord_rank (req_mem_linePts hq)]

/-! ### Main results on the line -/

/-- **Correctness on the line.** `lineSolve` is the least finish time of a
feasible plan. -/
theorem lineSolve_isLeast (reqs : List (Request ℝ)) (s : ℝ) :
    IsLeast (LineFinishTimes reqs s) (lineSolve reqs s) := by
  rw [lineFinishTimes_eq]
  have hm := (lineCoord_strictMono (reqs := reqs) (s := s))
  exact solve_isLeast hm hm _ _ _ _ (goalCost_univ hm.monotone hm.monotone)

theorem itemCount_lineReqs :
    itemCount (lineReqs reqs s) = (reqs.map Request.position).toFinset.card := by
  have hinj : Set.InjOn (lineRank reqs s) ((reqs.map Request.position).toFinset : Set ℝ) := by
    intro x hx y hy hxy
    have hx' : x ∈ linePts reqs s := Finset.mem_insert_of_mem hx
    have hy' : y ∈ linePts reqs s := Finset.mem_insert_of_mem hy
    rw [← lineCoord_rank hx', ← lineCoord_rank hy', hxy]
  have hset : ((lineReqs reqs s).map Request.position).toFinset =
      (reqs.map Request.position).toFinset.image (lineRank reqs s) := by
    ext k; simp [lineReqs]
  unfold itemCount positions
  rw [Finset.length_sort, hset, Finset.card_image_of_injOn hinj]

/-- **Iterations on the line.** With `m ≥ 1` distinct request positions, the
event loop halts within `8m+10` iterations. -/
theorem lineSolve_iterations (reqs : List (Request ℝ)) (s : ℝ)
    (hn : 0 < (reqs.map Request.position).toFinset.card) :
    let C := mkData (lineCoord reqs s) (lineCoord reqs s) (lineReqs reqs s)
    eventFuel C ≤ 8 * (reqs.map Request.position).toFinset.card + 10 ∧
      Halted C (run C (lineCoord reqs s) (lineCoord reqs s) (fun _ => 0) (eventFuel C)
        (initCfg C (lineRank reqs s s))) := by
  have hm := (lineCoord_strictMono (reqs := reqs) (s := s))
  rw [← itemCount_lineReqs] at hn ⊢
  exact solve_iterations hm hm _ _ Set.univ _ (goalCost_univ hm.monotone hm.monotone) hn

/-- **Cost on the line.** In the cost model of `Cost.lean`, the event phase
costs at most `(8m+10)(1+3⌈log₂(m+4)⌉)`. -/
theorem lineSolve_cost (reqs : List (Request ℝ)) (s : ℝ)
    (hn : 0 < (reqs.map Request.position).toFinset.card) :
    eventCost (mkData (lineCoord reqs s) (lineCoord reqs s) (lineReqs reqs s))
        (lineCoord reqs s) (lineCoord reqs s) (fun _ => 0) (lineRank reqs s s) ≤
      (8 * (reqs.map Request.position).toFinset.card + 10) *
        (1 + 3 * Nat.clog 2 ((reqs.map Request.position).toFinset.card + 4)) := by
  have hm := (lineCoord_strictMono (reqs := reqs) (s := s))
  rw [← itemCount_lineReqs] at hn ⊢
  exact solve_cost hm hm _ _ Set.univ _ (goalCost_univ hm.monotone hm.monotone) hn

end

end ReleasePath
