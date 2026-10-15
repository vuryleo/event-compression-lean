import ReleasePath.Exactness

/-!
# The concrete queue machine

The machine mirrors `event_solve` in the Python reference implementation.
`best` is the earliest-label table, `stuck` the waiting registers `W`, and
`ans` the incumbent (`none` is infinity). The queue is an unordered list and
`step` extracts an entry of minimum time, so every binary-heap implementation,
with any tie-breaking rule, is an instance of the analysed machine.
-/

namespace ReleasePath

open Classical

noncomputable section

inductive Entry where
  | normal (side : Bool) (i j : ℕ) (t : ℝ)
  | wait (side : Bool) (i : ℕ)

instance : DecidableEq Entry := Classical.decEq _

def Entry.time (C : EventData) : Entry → ℝ
  | .normal _ _ _ t => t
  | .wait side i => (C.chain side i).release

structure Cfg where
  queue : List Entry
  best : Bool → ℕ → ℕ → Option ℝ
  stuck : Bool → ℕ → Option ℕ
  ans : Option ℝ

/-- A label strictly improves the stored one (`none` is infinity). -/
def Improves (b : Option ℝ) (t : ℝ) : Prop :=
  match b with
  | none => True
  | some x => t < x

def Cfg.push (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) : Cfg :=
  if Improves (c.best side i j) t then
    { c with
      queue := Entry.normal side i j t :: c.queue
      best := fun s a b => if s = side ∧ a = i ∧ b = j then some t else c.best s a b }
  else c

def regValue (old : Option ℕ) (j : ℕ) : ℕ :=
  match old with
  | none => j
  | some k => max k j

def Cfg.register (c : Cfg) (side : Bool) (i j : ℕ) : Cfg :=
  { c with stuck := fun s a => if s = side ∧ a = i then some (regValue (c.stuck side i) j)
      else c.stuck s a }

def optMin (a : Option ℝ) (v : ℝ) : Option ℝ :=
  match a with
  | none => some v
  | some x => some (min x v)

def Cfg.complete (c : Cfg) (v : ℝ) : Cfg := { c with ans := optMin c.ans v }

/-- Expansion of a blocked state `s` (after any skip): register the waiting
child, then push the consolidated low return, register a cross wait, or push
the cross arrival. -/
def expand (C : EventData) (c : Cfg) (s : EventState) : Cfg :=
  if s.j < eventCutoff C s.side s.i then
    (c.register s.side (s.i+1) s.j).push (!s.side) (eventCutoff C s.side s.i - 1) (s.i+1)
      (lowChild C s).t
  else if crossArrival C s ≤ (C.chain (!s.side) s.j).release then
    (c.register s.side (s.i+1) s.j).register (!s.side) s.j (s.i+1)
  else
    (c.register s.side (s.i+1) s.j).push (!s.side) s.j (s.i+1) (crossArrival C s)

/-- A state at a chain node: complete if the node is last, else expand. -/
def settle (C : EventData) (D : ℕ → ℝ) (c : Cfg) (s : EventState) : Cfg :=
  if s.i + 1 < C.size s.side then expand C c s else c.complete (doneCost C D s)

def Stale (b : Option ℝ) (t : ℝ) : Prop := ∃ x, b = some x ∧ x < t

/-- Processing of an extracted entry (the queue has already lost it). -/
def process (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) : Entry → Cfg
  | .normal side i j t =>
    if Stale (c.best side i j) t then c
    else if eventBinaryCut C R L ⟨side, i, j, t⟩ = C.size side then
      c.complete (doneCost C D ⟨side, i, j, t⟩)
    else expand C c (eventBinaryState C R L ⟨side, i, j, t⟩)
  | .wait side i =>
    match c.stuck side i with
    | none => c
    | some j => settle C D c ⟨side, i, j, (C.chain side i).release⟩

/-- The loop stops once the minimum queued time is no smaller than the incumbent. -/
def Halts (C : EventData) (c : Cfg) (e : Entry) : Prop :=
  ∃ A, c.ans = some A ∧ A ≤ e.time C

def popStep (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (e : Entry) : Cfg :=
  process C R L D { c with queue := c.queue.erase e } e

def step (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) : Option Cfg :=
  match c.queue.argmin (Entry.time C) with
  | none => none
  | some e => if Halts C c e then none else some (popStep C R L D c e)

def run (C : EventData) (R L D : ℕ → ℝ) : ℕ → Cfg → Cfg
  | 0, c => c
  | n+1, c =>
    match step C R L D c with
    | none => c
    | some c' => run C R L D n c'

def waitEntries (C : EventData) : List Entry :=
  (List.range (C.size false)).map (Entry.wait false) ++
    (List.range (C.size true)).map (Entry.wait true)

def initTime (C : EventData) (start : ℕ) (side : Bool) : ℝ :=
  max (C.dist start (C.chain side 0).position) (C.chain side 0).release

def initCfg (C : EventData) (start : ℕ) : Cfg where
  queue := Entry.normal false 0 0 (initTime C start false) ::
    Entry.normal true 0 0 (initTime C start true) :: waitEntries C
  best := fun s i j => if i = 0 ∧ j = 0 then some (initTime C start s) else none
  stuck := fun _ _ => none
  ans := none

/-! ## Semantic predicates -/

/-- The optimum of the event system: some plan from the start serving both
chains finishes by `T`. -/
def InitBy (C : EventData) (goals : Set ℕ) (start : ℕ) (T : ℝ) : Prop :=
  ∃ goal finish, finish ≤ T ∧ ∃ vs, feasible C.dist start 0
    (pending (C.chain false) (C.chain true) (C.size false) (C.size true) 0 0)
    goals ⟨vs, goal, finish⟩

def entryState (C : EventData) (c : Cfg) : Entry → Option EventState
  | .normal side i j t => some ⟨side, i, j, t⟩
  | .wait side i => (c.stuck side i).map (fun j => ⟨side, i, j, (C.chain side i).release⟩)

def AnsLe (c : Cfg) (T : ℝ) : Prop := ∃ A, c.ans = some A ∧ A ≤ T

/-- Some live queue entry of rank at least `ρ` can still finish by `T`. -/
def LiveFin (C : EventData) (goals : Set ℕ) (c : Cfg) (ρ : ℕ) (T : ℝ) : Prop :=
  ∃ e ∈ c.queue, ∃ s, entryState C c e = some s ∧ ρ ≤ eventRank s ∧ FinishBy C goals s T

/-! ## Monotone growth of a configuration during processing -/

structure Grows (c c' : Cfg) : Prop where
  queue : ∀ e ∈ c.queue, e ∈ c'.queue
  stuck : ∀ side i j, c.stuck side i = some j → ∃ k, c'.stuck side i = some k ∧ j ≤ k
  ans : ∀ T, AnsLe c T → AnsLe c' T
  best : ∀ side i j b, c.best side i j = some b → ∃ b', c'.best side i j = some b' ∧ b' ≤ b

theorem Grows.refl (c : Cfg) : Grows c c :=
  ⟨fun _ h => h, fun _ _ j h => ⟨j, h, le_rfl⟩, fun _ h => h, fun _ _ _ b h => ⟨b, h, le_rfl⟩⟩

theorem Grows.trans {c₁ c₂ c₃ : Cfg} (h₁ : Grows c₁ c₂) (h₂ : Grows c₂ c₃) : Grows c₁ c₃ where
  queue e he := h₂.queue e (h₁.queue e he)
  stuck side i j h := by
    obtain ⟨k, hk, hjk⟩ := h₁.stuck side i j h
    obtain ⟨k', hk', hkk⟩ := h₂.stuck side i k hk
    exact ⟨k', hk', le_trans hjk hkk⟩
  ans T h := h₂.ans T (h₁.ans T h)
  best side i j b h := by
    obtain ⟨b', hb', hle⟩ := h₁.best side i j b h
    obtain ⟨b'', hb'', hle'⟩ := h₂.best side i j b' hb'
    exact ⟨b'', hb'', le_trans hle' hle⟩

theorem push_grows (c : Cfg) (side : Bool) (i j : ℕ) (t : ℝ) : Grows c (c.push side i j t) := by
  unfold Cfg.push
  split_ifs with himp
  · refine ⟨fun e he => List.mem_cons_of_mem _ he, fun _ _ j' h => ⟨j', h, le_rfl⟩,
      fun _ h => h, ?_⟩
    intro s a b x hx
    by_cases hk : s = side ∧ a = i ∧ b = j
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      rw [hx] at himp
      exact ⟨t, by simp, le_of_lt himp⟩
    · exact ⟨x, by simp [hk, hx], le_rfl⟩
  · exact Grows.refl c

theorem regValue_ge_old (k j : ℕ) : k ≤ regValue (some k) j := le_max_left k j

theorem regValue_ge_new (old : Option ℕ) (j : ℕ) : j ≤ regValue old j := by
  cases old with
  | none => exact le_rfl
  | some k => exact le_max_right k j

theorem regValue_cases (old : Option ℕ) (j : ℕ) :
    old = some (regValue old j) ∨ regValue old j = j := by
  cases old with
  | none => exact Or.inr rfl
  | some k =>
    simp only [regValue]
    rcases le_total k j with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (by rw [max_eq_left h])

theorem register_grows (c : Cfg) (side : Bool) (i j : ℕ) : Grows c (c.register side i j) := by
  refine ⟨fun e he => he, ?_, fun _ h => h, fun _ _ _ b h => ⟨b, h, le_rfl⟩⟩
  intro s a k hk
  by_cases h : s = side ∧ a = i
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨regValue (c.stuck s a) j, by simp [Cfg.register], ?_⟩
    rw [hk]; exact regValue_ge_old k j
  · exact ⟨k, by simp [Cfg.register, h, hk], le_rfl⟩

theorem optMin_le (a : Option ℝ) (v : ℝ) : ∃ A, optMin a v = some A ∧ A ≤ v := by
  cases a with
  | none => exact ⟨v, rfl, le_rfl⟩
  | some x => exact ⟨min x v, rfl, min_le_right x v⟩

theorem complete_grows (c : Cfg) (v : ℝ) : Grows c (c.complete v) := by
  refine ⟨fun e he => he, fun _ _ j h => ⟨j, h, le_rfl⟩, ?_, fun _ _ _ b h => ⟨b, h, le_rfl⟩⟩
  rintro T ⟨A, hA, hAT⟩
  refine ⟨min A v, ?_, le_trans (min_le_left A v) hAT⟩
  simp [Cfg.complete, optMin, hA]

theorem complete_ansLe (c : Cfg) (v T : ℝ) (h : v ≤ T) : AnsLe (c.complete v) T := by
  obtain ⟨A, hA, hAv⟩ := optMin_le c.ans v
  exact ⟨A, hA, le_trans hAv h⟩

theorem expand_grows (C : EventData) (c : Cfg) (s : EventState) : Grows c (expand C c s) := by
  unfold expand
  have h1 := register_grows c s.side (s.i+1) s.j
  split_ifs
  · exact h1.trans (push_grows _ _ _ _ _)
  · exact h1.trans (register_grows _ _ _ _)
  · exact h1.trans (push_grows _ _ _ _ _)

theorem settle_grows (C : EventData) (D : ℕ → ℝ) (c : Cfg) (s : EventState) :
    Grows c (settle C D c s) := by
  unfold settle
  split_ifs
  · exact expand_grows C c s
  · exact complete_grows c _

theorem process_normal (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (side : Bool) (i j : ℕ)
    (t : ℝ) : process C R L D c (.normal side i j t) =
      if Stale (c.best side i j) t then c
      else if eventBinaryCut C R L ⟨side, i, j, t⟩ = C.size side then
        c.complete (doneCost C D ⟨side, i, j, t⟩)
      else expand C c (eventBinaryState C R L ⟨side, i, j, t⟩) := rfl

theorem process_wait_none (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (side : Bool) (i : ℕ)
    (h : c.stuck side i = none) : process C R L D c (.wait side i) = c := by
  simp only [process, h]

theorem process_wait_some (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (side : Bool) (i j : ℕ)
    (h : c.stuck side i = some j) : process C R L D c (.wait side i) =
      settle C D c ⟨side, i, j, (C.chain side i).release⟩ := by
  simp only [process, h]

theorem process_grows (C : EventData) (R L D : ℕ → ℝ) (c : Cfg) (e : Entry) :
    Grows c (process C R L D c e) := by
  cases e with
  | normal side i j t =>
    rw [process_normal]
    split_ifs
    · exact Grows.refl c
    · exact complete_grows c _
    · exact expand_grows C c _
  | wait side i =>
    cases h : c.stuck side i with
    | none => rw [process_wait_none C R L D c side i h]; exact Grows.refl c
    | some j => rw [process_wait_some C R L D c side i j h]; exact settle_grows C D c _

/-- Live witnesses survive growth (waiting registers only increase). -/
theorem liveFin_grows {C : EventData} {goals : Set ℕ} {c c' : Cfg} (hg : Grows c c')
    {ρ : ℕ} {T : ℝ} (h : LiveFin C goals c ρ T) : LiveFin C goals c' ρ T := by
  obtain ⟨e, he, s, hs, hρ, hf⟩ := h
  refine ⟨e, hg.queue e he, ?_⟩
  cases e with
  | normal side i j t =>
    exact ⟨s, hs, hρ, hf⟩
  | wait side i =>
    simp only [entryState] at hs
    cases hst : c.stuck side i with
    | none => rw [hst] at hs; simp at hs
    | some j =>
      rw [hst] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨k, hk, hjk⟩ := hg.stuck side i j hst
      refine ⟨⟨side, i, k, (C.chain side i).release⟩, by simp [entryState, hk], ?_, ?_⟩
      · simp only [eventRank] at hρ ⊢; omega
      · exact finishBy_dom C goals side i j k _ _ le_rfl hjk T hf

theorem liveFin_mono {C : EventData} {goals : Set ℕ} {c : Cfg} {ρ ρ' : ℕ} {T : ℝ}
    (hρ : ρ' ≤ ρ) (h : LiveFin C goals c ρ T) : LiveFin C goals c ρ' T := by
  obtain ⟨e, he, s, hs, hr, hf⟩ := h
  exact ⟨e, he, s, hs, le_trans hρ hr, hf⟩

end

end ReleasePath
