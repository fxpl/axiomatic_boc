import Mathlib.Logic.Relation

import BoC.Common

section Definitions

inductive Event where
| Spawn (bid : BId)
| Run (bid : BId)
| Complete (bid : BId)

def Event.fresh (n : Nat) : Event -> Prop
| .Spawn m => m < n
| .Run m => m < n
| .Complete m => m < n

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

@[simp]
def wf_behavior_history_tail (bid : BId) : List Event → Prop
| [] => True
| [.Complete bid'] => bid = bid'
| .Spawn bid' :: es =>
    bid ≠ bid' ∧ wf_behavior_history_tail bid es
| _ => False

@[simp]
def wf_behavior_history (bid : BId) : List Event → Prop
| [] => True
| .Run bid' :: es =>
    bid = bid' ∧
    wf_behavior_history_tail bid es ∧
    List.Pairwise (· ≠ ·) es
| _ => False

@[simp]
def wf_cown_history : List Event → Prop
| [] => True
| [.Run _] => True
| .Run bid :: .Complete bid' :: es =>
    bid = bid' ∧ wf_cown_history es ∧
    .Run bid ∉ es ∧ .Complete bid' ∉ es
| _ => False

@[simp]
def unique_spawns (h : BId → List Event) : Prop :=
  ∀bid1 bid2 bid,
    bid1 ≠ bid2 →
    .Spawn bid ∈ h bid1 →
    .Spawn bid ∉ h bid2

inductive CausalStep (H : History) : Event → Event → Prop where
| Seq {es1 es2 e1 e2 bid} :
    H.behaviors bid = es1 ++ [e1, e2] ++ es2 →
    CausalStep H e1 e2
| Spawn {bid1 bid2 es} :
    .Spawn bid2 ∈ H.behaviors bid1 →
    H.behaviors bid2 = .Run bid2 :: es →
    CausalStep H (.Spawn bid2) (.Run bid2)

notation H "⊢" e1 "≺" e2 => ((CausalStep H)*) e1 e2

def History.wf (H : History) : Prop :=
  (∀bid, wf_behavior_history bid (H.behaviors bid))
  ∧
  unique_spawns H.behaviors
  ∧
  (∀c, wf_cown_history (H.cowns c))
  ∧
  (∀c, List.Pairwise (H ⊢ · ≺ ·) (H.cowns c))
  ∧
  is_partial_order (H ⊢ · ≺ ·)

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
    rcases h_contra with ⟨h_bid, h_unique, h_cown, h_pairwise, h_po⟩
    have h_01 : cyclic_history ⊢ .Run 0 ≺ .Spawn 1 := by
      apply Relation.ReflTransGen.single
      apply @CausalStep.Seq cyclic_history [] [] (.Run 0) (.Spawn 1) 0
      simp [cyclic_history]
    have h_10 : cyclic_history ⊢ .Spawn 1 ≺ .Run 0 := by
      apply @Relation.ReflTransGen.head Event _ (.Spawn 1) (.Run 1) (.Run 0)
      · apply @CausalStep.Spawn cyclic_history 0 1 [.Spawn 0] <;> simp [cyclic_history]
      · apply @Relation.ReflTransGen.head Event _ (.Run 1) (.Spawn 0) (.Run 0)
        · apply @CausalStep.Seq cyclic_history [] [] (.Run 1) (.Spawn 0) 1
          simp [cyclic_history]
        · apply Relation.ReflTransGen.single
          apply @CausalStep.Spawn cyclic_history 1 0 [.Spawn 1] <;> simp [cyclic_history]
    apply is_partial_order_is_acyclic h_po (.Run 0) (.Spawn 1)
    grind

theorem empty_history_wf :
  ⊢ History.empty :=
  by
    simp [History.wf]
    · apply is_partial_order.mk
      · apply Relation.ReflTransGen.refl
      · intro a b c h_ab h_bc
        apply Relation.ReflTransGen.trans h_ab h_bc
      · intro a b h_ab h_ba
        simp [History.empty] at h_ab
        cases h_ab with
        | refl => rfl
        | tail h_ab h_step =>
          cases h_step <;> simp at *

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
          rcases h_wf with ⟨h_eq, h_wf_tail, h_nin1, h_nin2⟩
          subst h_eq
          simp
          grind
        | _ =>
        simp [wf_cown_history] at h_wf
      | _ =>
        simp [wf_cown_history] at h_wf
