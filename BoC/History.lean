import BoC.Common

section Definitions

inductive Event where
| Spawn (bid : BId)
| Run (bid : BId)
| Complete (bid : BId)

@[simp]
def is_spawn : Event → Prop
| .Spawn _ => True
| _ => False

@[simp]
def is_run : Event → Prop
| .Run _ => True
| _ => False

@[simp]
def is_complete : Event → Prop
| .Complete _ => True
| _ => False

@[simp]
def Event.fresh (n : Nat) : Event -> Prop
| .Spawn m => m < n
| .Run m => m < n
| .Complete m => m < n

@[simp]
def Event.lt : Event -> Event -> Prop
| .Spawn bid1, e2
| .Run bid1, e2
| .Complete bid1, e2 =>
    match e2 with
    | .Spawn bid2
    | .Run bid2
    | .Complete bid2 => bid1 < bid2

@[simp]
def Event.leq : Event -> Event -> Prop
| .Spawn bid1, e2
| .Run bid1, e2
| .Complete bid1, e2 =>
    match e2 with
    | .Spawn bid2
    | .Run bid2
    | .Complete bid2 => bid1 ≤ bid2

@[simp]
instance EventLT : LT Event where
  lt := Event.lt

@[simp]
instance EventLE : LE Event where
  le := Event.leq

theorem Event.leq_refl (e : Event) : e ≤ e :=
  by
    rcases e <;> simp

theorem Event.lt_neq (e1 e2 : Event) :
    e1 < e2 →
    e1 ≠ e2 :=
  by
    intro h_lt
    rcases e1 <;> rcases e2 <;> simp at h_lt <;> grind

-- TODO: Move to Common.lean
instance BIdDecEq : DecidableEq BId := by
  intros bid1 bid2
  apply Nat.decEq

instance EventDecEq : DecidableEq Event := by
  intros e1 e2
  rcases e1 with bid1 | bid1 | bid1 <;>
  rcases e2 with bid2 | bid2 | bid2 <;>
  simp <;> (try apply BIdDecEq)
       <;> apply isFalse <;> simp

-- A history maps behavior IDs and cowns to the events they have been involved
-- in. An empty event list means the behavior or cown has not been run/used yet.
structure History where
  mk ::
  (behaviors : BId → List Event)
  (cowns : Cown → List Event)

@[reducible]
def History.empty : History :=
  History.mk (fun _ => []) (fun _ => [])

@[simp]
def History.fresh (n : Nat) (h : History) : Prop :=
  (∀bid, ∀e ∈ h.behaviors bid, e.fresh n) ∧
  (∀c, ∀e ∈ h.cowns c, e.fresh n)

@[simp]
def History.add_behavior_event (h : History) (bid : BId) (e : Event) : History :=
  History.mk
    (fun b =>
      if b = bid then
        h.behaviors b ++ [e]
      else
        h.behaviors b)
    h.cowns

@[simp]
def History.add_cown_event (h : History) (cowns : List Cown) (e : Event) : History :=
  History.mk
    h.behaviors
    (fun c' =>
      if c' ∈ cowns then
        h.cowns c' ++ [e]
      else
        h.cowns c')

notation H "[" bid "+=" e "]" => History.add_behavior_event H bid e
notation H "[" cowns "+=" e "]" => History.add_cown_event H cowns e

def wf_behavior_history_tail (bid : BId) : List Event → Prop
| [] => True
| [.Complete bid'] => bid = bid'
| _ => False

def wf_behavior_history (bid : BId) : List Event → Prop
| [] => True
| .Run bid' :: es =>
    bid = bid' ∧
    ∃spawns tail, es = spawns ++ tail ∧
  (∀e, e ∈ spawns → is_spawn e) ∧
      wf_behavior_history_tail bid tail
| _ => False

-- TODO: Could use this instead
-- inductive WfBehaviorHistory (bid : BId) : List Event → Prop where
-- | Empty :
--     WfBehaviorHistory bid []
-- | NonEmpty {spawns tail} :
--     (∀e, e ∈ spawns → is_spawn e) →
--     wf_behavior_history_tail bid tail →
--     WfBehaviorHistory bid (.Run bid :: spawns ++ tail)

def wf_cown_history : List Event → Prop
| [] => True
| [.Run _] => True
| .Run bid :: .Complete bid' :: es =>
    bid = bid' ∧ wf_cown_history es
| _ => False

def unique_spawns (h : BId → List Event) : Prop :=
  ∀bid1 bid2 bid,
    bid1 ≠ bid2 →
    .Spawn bid ∈ h bid1 →
    .Spawn bid ∉ h bid2

def History.events (H : History) : Set Event :=
  {e | ∃bid, e ∈ H.behaviors bid}

def History.timestamp_wf (H : History) (t : Event → Nat) : Prop :=
  -- Time increases along adjacent behavior/cown history events and spawn->run.
  (∀bid e1 e2, [e1, e2] <:+: H.behaviors bid → t e1 < t e2)
  ∧
  (∀c e1 e2, [e1, e2] <:+: H.cowns c → t e1 < t e2)
  ∧
  (∀parent bid,
     .Spawn bid ∈ H.behaviors parent →
     .Run bid ∈ H.behaviors bid →
    t (.Spawn bid) < t (.Run bid))
  ∧
  -- This corresponds to happens-before
  -- TODO: Can we prove preservation of this?
  (∀c bid1 bid2,
    .Complete bid1 ∈ H.cowns c →
    .Run bid2 ∈ H.cowns c →
    t (.Complete bid1) < t (.Run bid2) →
    t (.Spawn bid1) < t (.Spawn bid2))

structure History.wf (t : Event → Nat) (H : History) : Prop where
  -- Behavior histories are well-formed
  behaviorWf : ∀bid, wf_behavior_history bid (H.behaviors bid)
  -- Spawn events are unique across behaviors
  uniqueSpawns : unique_spawns H.behaviors
  -- Cown histories are well-formed
  cownWf : ∀c, wf_cown_history (H.cowns c)
  -- Every cown event corresponds to some behavior event
  cownEvent : ∀c e, e ∈ H.cowns c → ∃bid, e ∈ H.behaviors bid
  -- If a behavior ran on a cown and later completed, the completion appears in that cown's history
  completeOnCown :
    ∀c bid, .Run bid ∈ H.cowns c → .Complete bid ∈ H.behaviors bid → .Complete bid ∈ H.cowns c
  -- There exists a global timestamping that is monotone on history edges.
  spawnOnCown :
    ∀c bid, .Run bid ∈ H.cowns c → ∃bid', .Spawn bid ∈ H.behaviors bid'
  timestampWf : History.timestamp_wf H t
  hasTop : ∃top, ∀e ∈ History.events H, t e < top

notation t "⊢" H => History.wf t H

def History.complete (H : History) : Prop :=
  (∀bid, .Run bid ∈ H.behaviors bid →
         .Complete bid ∈ H.behaviors bid) ∧
  (∀bid1 bid2,
     .Spawn bid2 ∈ H.behaviors bid1 →
     .Run bid2 ∈ H.behaviors bid2)

end Definitions

-- Examples and theorems
private def cyclic_history : History :=
  ⟨fun bid =>
     if bid = 0 then
       [.Run 0, .Spawn 1]
     else if bid = 1 then
       [.Run 1, .Spawn 0]
     else
       [],
   fun _ => []⟩

example (t : Event → Nat) : ¬ (t ⊢ cyclic_history) :=
  by
    intro h_contra
    have h_twf := h_contra.timestampWf
    have h_beh_twf := h_twf.1
    have h_spawn_run_twf := h_twf.2.2.1
    have h_infix01 : [Event.Run 0, Event.Spawn 1] <:+: cyclic_history.behaviors 0 := by
      refine ⟨[], [], ?_⟩
      simp [cyclic_history]
    have h_infix10 : [Event.Run 1, Event.Spawn 0] <:+: cyclic_history.behaviors 1 := by
      refine ⟨[], [], ?_⟩
      simp [cyclic_history]
    have h_r0_s1 : t (Event.Run 0) < t (Event.Spawn 1) := h_beh_twf 0 _ _ h_infix01
    have h_r1_s0 : t (Event.Run 1) < t (Event.Spawn 0) := h_beh_twf 1 _ _ h_infix10
    have h_s1_r1 : t (Event.Spawn 1) < t (Event.Run 1) := by
      apply h_spawn_run_twf 0 1 <;> simp [cyclic_history]
    have h_s0_r0 : t (Event.Spawn 0) < t (Event.Run 0) := by
      apply h_spawn_run_twf 1 0 <;> simp [cyclic_history]
    have h_loop : t (Event.Run 0) < t (Event.Run 0) := by
      exact Nat.lt_trans h_r0_s1 (Nat.lt_trans h_s1_r1 (Nat.lt_trans h_r1_s0 h_s0_r0))
    exact Nat.lt_irrefl _ h_loop

-- TODO: Sort theorems and lemmas
theorem empty_history_wf :
  (t : Event → Nat) → t ⊢ History.empty :=
  by
    intro t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [wf_behavior_history]
    · intro bid1 bid2 bid h_ne h_mem
      simp at h_mem
    · simp [wf_cown_history]
    · simp
    · simp
    · simp
    · simp [History.timestamp_wf]
    · refine ⟨0, ?_⟩
      intro e h_mem
      have h_false : False := by
        simpa [History.events] using h_mem
      exact False.elim h_false

theorem empty_history_complete :
    History.complete History.empty :=
  by
    simp [History.complete]

theorem wf_cown_history_middle_inv {init tail bid1 bid2} :
    wf_cown_history (init ++ .Run bid1 :: .Complete bid2 :: tail) →
    bid1 = bid2 :=
  by
    intro h_wf
    induction init using wf_cown_history.induct with
    | case1 =>
      simp at h_wf
      rcases h_wf with ⟨h_eq, _⟩
      subst h_eq
      simp
    | case2 bid =>
      simp [wf_cown_history] at h_wf
    | case3 bid3 bid4 init' ih =>
      simp at h_wf
      rcases h_wf with ⟨h_eq, h_wf_tail⟩
      subst h_eq
      exact ih h_wf_tail
    | case4 init' not_empty not_just_run not_r_c =>
      cases init' with
      | nil => contradiction
      | cons e init'' =>
        rcases e <;> simp [wf_cown_history] at *
        cases init'' with
        | nil => contradiction
        | cons e' init''' =>
          rcases e' <;> simp [wf_cown_history] at *

theorem wf_cown_history_append_inv {init tail bid} :
    wf_cown_history (init ++ .Run bid :: tail) →
    wf_cown_history (.Run bid :: tail) :=
  by
    intro h_wf
    induction init using wf_cown_history.induct with
    | case1 =>
      simp at h_wf
      exact h_wf
    | case2 bid =>
      simp [wf_cown_history] at h_wf
    | case3 bid3 bid4 init' ih =>
      simp at h_wf
      rcases h_wf with ⟨h_eq, h_wf_tail⟩
      subst h_eq
      exact ih h_wf_tail
    | case4 init' not_empty not_just_run not_r_c =>
      cases init' with
      | nil => contradiction
      | cons e init'' =>
        rcases e <;> simp [wf_cown_history] at *
        cases init'' with
        | nil => contradiction
        | cons e' init''' =>
          rcases e' <;> simp [wf_cown_history] at *

-- Any Complete in a well-formed cown history is immediately preceded by the
-- matching Run:  init = init' ++ [Run bid1].
theorem wf_cown_history_complete_pred {init rest bid1} :
    wf_cown_history (init ++ .Complete bid1 :: rest) →
    ∃ init', init = init' ++ [.Run bid1] :=
  by
    intro h_wf
    induction init using wf_cown_history.induct with
    | case1 =>
      simp [wf_cown_history] at h_wf
    | case2 bid =>
      -- init = [Run bid], list is Run bid :: Complete bid1 :: rest
      simp [wf_cown_history] at h_wf
      exact ⟨[], by simp [h_wf.1]⟩
    | case3 bid3 bid4 init' ih =>
      simp at h_wf
      rcases h_wf with ⟨h_eq, h_wf_tail⟩
      subst h_eq
      cases init' with
      | nil =>
        -- init' = [] means wf_cown_history (Complete bid1 :: rest) which is False
        simp [wf_cown_history] at h_wf_tail
      | cons _ _ =>
        have ⟨init'', h_eq⟩ := ih h_wf_tail
        exact ⟨.Run bid3 :: .Complete bid3 :: init'', by simp [h_eq]⟩
    | case4 cs h_nil h_run h_rc =>
      cases cs with
      | nil => simp at h_nil
      | cons e cs' =>
        cases cs' with
        | nil =>
          rcases e <;> simp [wf_cown_history] at *
        | cons e' cs'' =>
          rcases e <;> rcases e' <;> simp [wf_cown_history] at *

lemma wf_history_tail_no_run_any {bid es} :
    wf_behavior_history_tail bid es →
    ∀e ∈ es, ¬is_run e :=
  by
    introv h_tail h_in
    cases es with
    | nil =>
      simp at h_in
    | cons e es' =>
      cases e with
      | Spawn b =>
        simp [wf_behavior_history_tail] at h_tail
      | Run b =>
        simp [wf_behavior_history_tail] at h_tail
      | Complete b =>
        simp [wf_behavior_history_tail] at h_tail
        rcases es' <;> simp at h_tail
        simp at h_in
        subst h_in
        simp

lemma wf_history_tail_mem_inv {bid es} :
    wf_behavior_history_tail bid es →
    ∀e ∈ es, is_complete e :=
  by
    introv h_tail h_in
    cases es with
    | nil =>
      simp at h_in
    | cons e es' =>
      cases e with
      | Spawn b =>
        simp [wf_behavior_history_tail] at h_tail
      | Run b =>
        simp [wf_behavior_history_tail] at h_tail
      | Complete b =>
        simp [wf_behavior_history_tail] at h_tail
        rcases es' <;> simp at h_tail
        simp at h_in
        subst h_in
        simp

-- TODO: Remove this and prove inline instead (similar for several lemmas below)
theorem wf_history_spawns_no_run {es : List Event} :
    (∀e, e ∈ es → is_spawn e) →
    ∀e ∈ es, ¬is_run e :=
  by
    intro h_spawns e h_in
    have h_is := h_spawns e h_in
    rcases e <;> simp at h_is ⊢

theorem wf_history_spawns_mem_inv {es : List Event} :
    (∀e, e ∈ es → is_spawn e) →
    ∀e ∈ es, is_spawn e :=
  by
    intro h_spawns e h_in
    exact h_spawns e h_in

theorem wf_behavior_history_pair_inv {bid es e1 e2} :
    wf_behavior_history bid es ->
    [e1, e2] <:+: es →
    is_run e1 ∧ is_spawn e2 ∨
    is_run e1 ∧ is_complete e2 ∨
    is_spawn e1 ∧ is_spawn e2 ∨
    is_spawn e1 ∧ is_complete e2 :=
  by
    intro h_wf h_infix
    simp [List.IsInfix] at h_infix
    rcases h_infix with ⟨init, tail, h_eq⟩
    subst h_eq
    simp [wf_behavior_history] at h_wf
    cases init with
    | nil =>
      simp at h_wf
      rcases e1 <;> simp at h_wf
      rcases h_wf with ⟨h_bid, spawns, tail', h_split, h_spawns, h_tail⟩
      cases spawns with
      | nil =>
        simp at h_split
        subst h_split
        simp [wf_behavior_history_tail] at h_tail
        rcases e2 <;> simp at h_tail ⊢
      | cons e spawns' =>
        simp at h_split
        rcases h_split with ⟨h_eq, h_spawns_eq, h_tail_eq⟩
        subst h_eq
        have h_e2_spawn : is_spawn e2 := h_spawns _ (by simp)
        rcases e2 <;> simp at h_e2_spawn ⊢
    | cons e init' =>
      rcases e <;> simp at h_wf
      rcases h_wf with ⟨h_bid, spawns, tail', h_split, h_spawns, h_tail⟩
      have h_no_run : ∀e ∈ spawns ++ tail', ¬is_run e := by
        intro e
        intro h_mem
        rcases List.mem_append.mp h_mem with h_mem_spawns | h_mem_tail
        · have h_is := wf_history_spawns_mem_inv h_spawns e h_mem_spawns
          rcases e <;> simp at h_is ⊢
        · have h_is := wf_history_tail_mem_inv h_tail e h_mem_tail
          rcases e <;> simp at h_is ⊢
      cases e1 with
      | Spawn b1 =>
        cases e2 with
        | Spawn b2
        | Complete b2 => simp
        | Run b2 =>
          have h_mem : .Run b2 ∈ spawns ++ tail' := by
            have : .Run b2 ∈ init' ++ .Spawn b1 :: .Run b2 :: tail := by simp
            simpa [h_split] using this
          exfalso
          apply h_no_run _ h_mem
          simp
      | Run b1 =>
        have h_mem : .Run b1 ∈ spawns ++ tail' := by
          have : .Run b1 ∈ init' ++ .Run b1 :: e2 :: tail := by simp
          simpa [h_split] using this
        exfalso
        apply h_no_run _ h_mem
        simp
      | Complete b1 =>
        have h_mem : .Complete b1 ∈ spawns := by
          cases List.eq_nil_or_concat tail' with
          | inl h_eq =>
            subst h_eq
            have : .Complete b1 ∈ init' ++ .Complete b1 :: e2 :: tail := by simp
            simpa [h_split] using this
          | inr h_ex =>
            rcases h_ex with ⟨tail'', e, h_eq⟩
            subst h_eq
            simp [wf_behavior_history_tail] at h_tail
            rcases tail'' with _ | ⟨e, tail''⟩ <;> simp at h_tail
            have h_eq : spawns ++ [].concat e = spawns.concat e := by simp
            rw [h_eq] at h_split
            cases List.eq_nil_or_concat tail with
            | inl h_eq =>
              subst h_eq
              have h_eq : init' ++ [Event.Complete b1, e2] =
                          (init' ++ [Event.Complete b1]).concat e2 := by simp
              rw [h_eq] at h_split
              have h_eq := List.init_eq_of_concat_eq h_split
              subst h_eq
              simp
            | inr h_ex =>
              rcases h_ex with ⟨spawns', e', h_eq⟩
              rw [h_eq] at h_split
              have h_eq : init' ++ Event.Complete b1 :: e2 :: spawns'.concat e' =
                          (init' ++ Event.Complete b1 :: e2 :: spawns').concat e' := by simp
              rw [h_eq] at h_split
              have h_eq := List.init_eq_of_concat_eq h_split
              subst h_eq
              simp
        exfalso
        have contra := wf_history_spawns_mem_inv h_spawns _ h_mem
        simp at contra

theorem wf_history_spawns_no_dup {es : List Event} :
    (∀e, e ∈ es → is_spawn e) →
    {t : Event → Nat} →
    (∀e1 e2, [e1, e2] <:+: es → t e1 < t e2) →
    List.Pairwise (· ≠ ·) es :=
  by
    intro _ _ h_ts
    exact pairwise_ne_of_pair_ordered h_ts

theorem wf_behavior_history_no_dup {bid es} :
    wf_behavior_history bid es →
    {t : Event → Nat} →
    (∀e1 e2, [e1, e2] <:+: es → t e1 < t e2) →
    List.Pairwise (· ≠ ·) es :=
  by
    intro _ _ h_ts
    exact pairwise_ne_of_pair_ordered h_ts

theorem wf_history_run_mem_inv {bid bid' es} :
    wf_behavior_history bid es →
    .Run bid' ∈ es →
    bid = bid' :=
  by
    intro h_wf h_in
    cases es with
    | nil =>
      simp at h_in
    | cons e es' =>
      cases e with
      | Spawn b
      | Complete b =>
        simp [wf_behavior_history] at h_wf
      | Run b =>
        simp [wf_behavior_history] at h_wf
        rcases h_wf with ⟨h_eq, init, tail, h_eq', h_spawns, h_tail⟩
        subst h_eq
        subst h_eq'
        simp at h_in
        rcases h_in with h_eq | h_in | h_in
        · subst h_eq
          simp
        · have contra := wf_history_spawns_mem_inv h_spawns _ h_in
          simp at contra
        · have contra := wf_history_tail_mem_inv h_tail _ h_in
          simp at contra

theorem wf_history_spawn_mem_inv {bid bid' es} :
    wf_behavior_history bid es →
    .Spawn bid' ∈ es →
    is_spawn (.Spawn bid') :=
  by
    intro _ _
    simp

theorem wf_history_complete_mem_inv {bid bid' es} :
    wf_behavior_history bid es →
    .Complete bid' ∈ es →
    bid = bid' :=
  by
    intro h_wf h_in
    cases es with
    | nil =>
      simp at h_in
    | cons e es' =>
      cases e with
      | Spawn b
      | Complete b =>
        simp [wf_behavior_history] at h_wf
      | Run b =>
        simp [wf_behavior_history] at h_wf
        rcases h_wf with ⟨h_eq, init, tail, h_eq', h_spawns, h_tail⟩
        subst h_eq
        subst h_eq'
        simp at h_in
        rcases h_in with h_in | h_in
        · have contra := wf_history_spawns_mem_inv h_spawns _ h_in
          simp at contra
        · cases tail with
          | nil =>
            simp at h_in
          | cons e tail' =>
            rcases e <;> rcases tail' <;> simp [wf_behavior_history_tail] at h_tail
            grind

lemma wf_history_event_unique {t} {H bid1 bid2 e} :
    (t ⊢ H) →
    e ∈ H.behaviors bid1 →
    e ∈ H.behaviors bid2 →
    bid1 = bid2 :=
  by
    intro h_wf h_mem1 h_mem2
    cases e with
    | Spawn bid =>
      by_cases h_eq : bid1 = bid2
      · exact h_eq
      · exfalso
        have h_not_mem : .Spawn bid ∉ H.behaviors bid2 :=
          h_wf.uniqueSpawns bid1 bid2 bid h_eq h_mem1
        exact h_not_mem h_mem2
    | Run bid =>
      have h1 : bid1 = bid := wf_history_run_mem_inv (h_wf.behaviorWf bid1) h_mem1
      have h2 : bid2 = bid := wf_history_run_mem_inv (h_wf.behaviorWf bid2) h_mem2
      grind
    | Complete bid =>
      have h1 : bid1 = bid := wf_history_complete_mem_inv (h_wf.behaviorWf bid1) h_mem1
      have h2 : bid2 = bid := wf_history_complete_mem_inv (h_wf.behaviorWf bid2) h_mem2
      grind

lemma wf_cown_history_complete_has_run {cs bid} :
    wf_cown_history cs →
    Event.Complete bid ∈ cs →
    Event.Run bid ∈ cs :=
  by
    introv h_wfc h_complete_mem
    induction cs using wf_cown_history.induct with
    | case1 => simp at h_complete_mem
    | case2 _ => simp at h_complete_mem
    | case3 bid1 bid2 cs' ih =>
      simp [wf_cown_history] at h_wfc
      rcases h_wfc with ⟨h_bid_eq, h_wfc'⟩
      subst h_bid_eq
      grind
    | case4 cs' h_nil h_run ih =>
      rcases cs' with _ | ⟨e, cs''⟩ <;> simp at h_complete_mem
      cases cs'' with
      | nil =>
        rcases e <;> simp [wf_cown_history] at h_wfc
        grind
      | cons e' cs''' =>
        rcases e <;> rcases e' <;> simp [wf_cown_history] at h_wfc
        grind
