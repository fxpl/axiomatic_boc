import Mathlib.Logic.Relation

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

def wf_behavior_history_spawns (bid : BId) : List Event → Prop
| [] => True
| .Spawn bid' :: es =>
    bid < bid' ∧
    (∀e ∈ es, (.Spawn bid' < e)) ∧
    wf_behavior_history_spawns bid es
| _ => False

def wf_behavior_history (bid : BId) : List Event → Prop
| [] => True
| .Run bid' :: es =>
    bid = bid' ∧
    ∃spawns tail, es = spawns ++ tail ∧
      wf_behavior_history_spawns bid spawns ∧
      wf_behavior_history_tail bid tail
| _ => False

-- TODO: Could use this instead
inductive WfBehaviorHistory (bid : BId) : List Event → Prop where
| Empty :
    WfBehaviorHistory bid []
| NonEmpty {spawns tail} :
    wf_behavior_history_spawns bid spawns →
    wf_behavior_history_tail bid tail →
    WfBehaviorHistory bid (.Run bid :: spawns ++ tail)

def wf_cown_history : List Event → Prop
| [] => True
| [.Run _] => True
| .Run bid :: .Complete bid' :: es =>
    bid = bid' ∧ wf_cown_history es ∧
    ∀e ∈ es, (.Run bid < e)
| _ => False

def unique_spawns (h : BId → List Event) : Prop :=
  ∀bid1 bid2 bid,
    bid1 ≠ bid2 →
    .Spawn bid ∈ h bid1 →
    .Spawn bid ∉ h bid2

@[simp]
def History.wf (H : History) : Prop :=
  -- Behavior histories are well-formed
  (∀bid, wf_behavior_history bid (H.behaviors bid))
  ∧
  -- Spawn events are unique across behaviors
  unique_spawns H.behaviors
  ∧
  -- Cown histories are well-formed
  (∀c, wf_cown_history (H.cowns c))
  ∧
  -- Every cown event corresponds to some behavior event
  (∀c e, e ∈ H.cowns c → ∃bid, e ∈ H.behaviors bid)

notation "⊢" H => History.wf H

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

example : ¬ (⊢ cyclic_history) :=
  by
    intros h_contra
    rcases h_contra with ⟨h_bid, h_unique, h_cown, h_corr⟩
    rcases h_bid 1 with ⟨_, ⟨spawns, tail, h_eq, h_spawns, h_tail⟩⟩
    cases spawns with
    | nil =>
      simp at h_eq
      subst h_eq
      simp [wf_behavior_history_tail] at h_tail
    | cons e spawns' =>
      simp at h_eq
      rcases h_eq with ⟨h_spawn, h_spawns_eq, h_tail_eq⟩
      subst h_spawn h_spawns_eq
      simp [wf_behavior_history_spawns] at h_spawns

theorem empty_history_wf :
  ⊢ History.empty :=
  by
    simp [History.wf, wf_behavior_history, wf_cown_history, unique_spawns]

theorem empty_history_complete :
    History.complete History.empty :=
  by
    simp [History.complete]

theorem wf_cown_history_no_dup {es} :
    wf_cown_history es →
    List.Pairwise (· ≠ ·) es :=
  by
    intro h_wf
    have ⟨n, h_len⟩ : ∃n : Nat, es.length = n := ⟨es.length, rfl⟩
    induction n using Nat.strongRecOn generalizing es with
    | ind n ih =>
      rcases es with _ | ⟨e, es'⟩ <;> simp
      rcases es' with _ | ⟨e', es''⟩ <;> simp
      cases e with
      | Run bid =>
        cases e' with
        | Complete bid' =>
          rcases h_wf with ⟨h_eq, h_wf_tail, h_lt⟩
          subst h_eq
          simp
          and_intros <;> try grind [Event.lt_neq]
          introv h_in
          have := h_lt a' h_in
          introv contra
          subst contra
          simp at *
        | _ =>
        simp [wf_cown_history] at h_wf
      | _ =>
        simp [wf_cown_history] at h_wf

theorem wf_history_spawn_fresh H {bid fresh : BId} :
    (⊢ H) →
    Event.Run bid ∈ H.behaviors bid →
    History.fresh fresh H →
    ⊢ (H[bid += Event.Spawn fresh]) :=
  by
    introv h_wf h_run h_fresh
    simp [History.wf]
    rcases h_wf with ⟨h_behaviors, h_unique, h_cowns, h_corr⟩
    and_intros <;> try (solve | grind)
    · intros bid'
      by_cases h_eq : bid' = bid
      · simp [h_eq]
        sorry -- Lemma about wf_behavior_history
      · simp [h_eq]
        grind
    · sorry -- Lemma about unique_spawns

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

theorem wf_history_spawns_no_run {bid es} :
    wf_behavior_history_spawns bid es →
    ∀e ∈ es, ¬is_run e :=
  by
    introv h_spawns h_in
    induction es with
    | nil =>
      simp at h_in
    | cons e es' ih =>
      simp at h_in
      cases h_in with
      | inl h_eq =>
        subst h_eq
        rcases e <;> simp [wf_behavior_history_spawns] at h_spawns ⊢
      | inr h_in' =>
        rcases e <;> simp [wf_behavior_history_spawns] at h_spawns ⊢
        rcases h_spawns with ⟨h_lt, h_es_lt, h_spawns'⟩
        apply ih <;> assumption

theorem wf_history_spawns_mem_inv {bid es} :
    wf_behavior_history_spawns bid es →
    ∀e ∈ es, is_spawn e :=
  by
    introv h_spawns h_in
    induction es with
    | nil =>
      simp at h_in
    | cons e es' ih =>
      simp at h_in
      cases h_in with
      | inl h_eq =>
        subst h_eq
        rcases e <;> simp [wf_behavior_history_spawns] at h_spawns ⊢
      | inr h_in' =>
        rcases e <;> simp [wf_behavior_history_spawns] at h_spawns ⊢
        rcases h_spawns with ⟨h_lt, h_es_lt, h_spawns'⟩
        apply ih <;> assumption

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
        rcases e2 <;> simp [wf_behavior_history_spawns] at h_spawns ⊢
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

theorem wf_history_spawns_no_dup {bid es} :
    wf_behavior_history_spawns bid es →
    List.Pairwise (· ≠ ·) es :=
  by
    intro h_wf
    induction es with
    | nil =>
      simp
    | cons e es' ih =>
      rcases e <;> simp [wf_behavior_history_spawns] at h_wf
      rcases h_wf with ⟨h_lt, h_es_lt, h_spawns'⟩
      simp
      and_intros <;> grind

theorem wf_behavior_history_no_dup {bid es} :
    wf_behavior_history bid es →
    List.Pairwise (· ≠ ·) es :=
  by
    intro h_wf
    cases es with
    | nil =>
      simp
    | cons e es' =>
      cases e with
      | Spawn bid'
      | Complete bid' =>
        simp [wf_behavior_history] at h_wf
      | Run bid' =>
        simp [wf_behavior_history] at h_wf
        rcases h_wf with ⟨h_eq, init, tail, h_eq', h_spawns, h_tail⟩
        subst h_eq
        subst h_eq'
        simp
        and_intros
        · introv h_or
          cases h_or with
          | inl h_in =>
            have h_spawn := wf_history_spawns_mem_inv h_spawns _ h_in
            rcases a' <;> simp at h_spawn ⊢
          | inr h_in =>
            have h_tail := wf_history_tail_mem_inv h_tail _ h_in
            rcases a' <;> simp at h_tail ⊢
        · cases tail with
          | nil =>
            simp
            exact wf_history_spawns_no_dup h_spawns
          | cons e tail' =>
            rcases e <;> rcases tail' <;> simp [wf_behavior_history_tail] at h_tail
            subst h_tail
            refine List.pairwise_append.mpr ?_
            and_intros <;> try simp
            · exact wf_history_spawns_no_dup h_spawns
            · introv h_in h_in'
              subst h_in'
              have h_spawn := wf_history_spawns_mem_inv h_spawns _ h_in
              simp at h_spawn

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
