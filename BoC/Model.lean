import Mathlib.Logic.Relation
import BoC.Common
import BoC.History
import Init.Data.List

-- A model is a set of events along with a given program order, coherence order
-- and a disjointness relation on cown sets
structure Model where
  mk ::
  (events : Set Event)
  (po : Event → Event → Prop)
  (co : Cown → Event → Event → Prop)
  -- (disj : Set Cown → Set Cown → Prop)

def wf_po_relation (events : Set Event) (po : Event → Event → Prop) : Prop :=
  -- po only relates known events
  (∀e1 e2, po e1 e2 → e1 ∈ events ∧ e2 ∈ events)
  ∧
  -- po relates run/spawn, run/complete, spawn/spawn, and spawn/complete events
  (∀e1 e2, po e1 e2 → match e1, e2 with
                      | .Run _, .Spawn _
                      | .Run _, .Complete _
                      | .Spawn _, .Spawn _
                      | .Spawn _, .Complete _ => True
                      | _, _ => False)
  ∧
  -- po uniquely determines its predecessors and successors (po is a bijection)
  (∀e1 e2 e3, po e1 e3 → po e2 e3 → e1 = e2) ∧
  (∀e1 e2 e3, po e1 e2 → po e1 e3 → e2 = e3)
  ∧
  -- All events are preceeded by a Run event
  (∀e1 ∈ events, ∃bid, (po*) (.Run bid) e1)
  ∧
  -- A completion event must finish the same behaviour that was started
  (∀bid1 bid2, (po+) (.Run bid1) (.Complete bid2) → bid1 = bid2)

def wf_co_relation (events : Set Event) (co : Cown → Event → Event → Prop) : Prop :=
  -- co only relates known events
  (∀e1 e2 c, co c e1 e2 → e1 ∈ events ∧ e2 ∈ events)
  ∧
  -- co relates complete/run events
  (∀e1 e2 c, co c e1 e2 → match e1, e2 with
                          | .Complete _, .Run _ => True
                          | _, _ => False)
  ∧
  -- co uniquely determines its predecessors and successors (co is a bijection)
  (∀e1 e2 e3 c, co c e1 e3 → co c e2 e3 → e1 = e2) ∧
  (∀e1 e2 e3 c, co c e1 e2 → co c e1 e3 → e2 = e3)

-- From a model, we can derive a run relation which relates a spawn event of a
-- behaviour to the corresponding run event
def derived_run_relation (m : Model) : Event → Event → Prop
| .Spawn bid, .Run bid' =>
    bid = bid' ∧
    .Spawn bid ∈ m.events ∧
    .Run bid ∈ m.events
| _, _ => False

-- From a model we can derive a happens-before relation which relates a
-- completion event with all the run events that happened after it
-- hb = {(Ci,Rj) | Si (po ∪ r ∪ co)+ Sj ∧ cowns(i) ∩ cowns(j) ≠ ∅}
def derived_hb_relation (m : Model) : Event → Event → Prop
| .Complete bid1, .Run bid2 =>
  let r := derived_run_relation m;
  let co' := fun e1 e2 => ∃c, m.co c e1 e2;
  let cowns bid := {c | (∃e, m.co c e (.Run bid)) ∨ (∃e, m.co c (.Complete bid) e)};
  ((m.po ∪ co' ∪ r)+) (.Spawn bid1) (.Spawn bid2) ∧
  (cowns bid1 ∩ cowns bid2 ≠ ∅) ∧
  .Complete bid1 ∈ m.events ∧
  .Run bid2 ∈ m.events
| _, _ => False

-- Well-formedness conditions for a model
def Model.wf : Model → Prop
| m@⟨events, po, co⟩ =>
  wf_po_relation events po ∧
  wf_co_relation events co ∧
  -- Derived relations
  let r := derived_run_relation m;
  let hb := derived_hb_relation m;
  let co' := fun e1 e2 => ∃c, co c e1 e2;
  -- co creates a single causal order path for any given cown
  (∀e1 e2 e3 e4 c,
    e1 ≠ e3 →
    e2 ≠ e4 →
    co c e1 e2 →
    co c e3 e4 →
    ((po ∪ co c)*) e2 e3 ∨ ((po ∪ co c)*) e4 e1) ∧
  -- The transitive closure of po_co_hb is acyclic
  (∀e1 e2, ((po ∪ co' ∪ r ∪ hb)+) e1 e2 → e1 ≠ e2)

def Model.complete : Model → Prop
| ⟨events, po, _⟩ =>
  -- Every run event has a corresponding complete event
  (∀bid, .Run bid ∈ events → (po+) (.Run bid) (.Complete bid))
  ∧
  -- Every spawn event has a corresponding run event
  (∀bid, .Spawn bid ∈ events → .Run bid ∈ events)

def model_from_history (H : History) : Model :=
  ⟨
    -- Events
    {e | ∃bid, e ∈ H.behaviors bid},
    -- Program order
    fun e1 e2 =>
      ∃bid,
        [e1, e2] <:+: H.behaviors bid,
    -- Coherence order
    -- TODO: Rewrite to use [e1, e2] <:+: H.cowns c
    fun c e1 e2 =>
      ∃bid1 bid2 init tail,
        e1 = .Complete bid1 ∧
        e2 = .Run bid2 ∧
        H.cowns c = init ++ .Complete bid1 :: .Run bid2 :: tail
  ⟩

lemma clos_exists_pick {A} {B} {x y : A} {P : A → A → B → Prop} {b : B} :
    ((fun e1 e2 ↦ P e1 e2 b)*) x y →
    ((fun e1 e2 ↦ ∃ b, P e1 e2 b)*) x y :=
  by
    introv h_clos
    induction h_clos with
    | refl => constructor
    | @tail z w h_clos h_infix ih =>
      apply Relation.ReflTransGen.tail ih
      exists b

lemma po_pick_bid {H : History} {e1 e2} {bid} :
    ((fun e1 e2 ↦ [e1, e2] <:+: H.behaviors bid) * ) e1 e2 →
    ((fun e1 e2 ↦ ∃ bid, [e1, e2] <:+: H.behaviors bid) * ) e1 e2 :=
  by
    introv h_clos
    apply clos_exists_pick
    assumption

-- TODO: These names are horrible. Do something about it!
lemma trans_clos_exists_pick {A} {B} {x y : A} {P : A → A → B → Prop} {b : B} :
    ((fun e1 e2 ↦ P e1 e2 b)+) x y →
    ((fun e1 e2 ↦ ∃ b, P e1 e2 b)+) x y :=
  by
    introv h_clos
    induction h_clos with
    | @single a =>
      constructor
      exists b
    | @tail z w h_clos h_infix ih =>
      apply Relation.TransGen.tail ih
      exists b

lemma po_trans_pick_bid {H : History} {e1 e2} {bid} :
    ((fun e1 e2 ↦ [e1, e2] <:+: H.behaviors bid)+) e1 e2 →
    ((fun e1 e2 ↦ ∃ bid, [e1, e2] <:+: H.behaviors bid)+) e1 e2 :=
  by
    introv h_clos
    apply trans_clos_exists_pick
    assumption

lemma po_exists_inv {H : History} {e1 e2} :
    (⊢ H) →
    ((fun e1 e2 ↦ ∃ bid, [e1, e2] <:+: H.behaviors bid)+ ) e1 e2 →
    ∃bid, ((fun e1 e2 ↦ [e1, e2] <:+: H.behaviors bid)+ ) e1 e2 :=
  by
    introv h_wf h_clos
    induction h_clos with
    | single h_ex =>
      rcases h_ex with ⟨bid, h_infix⟩
      exists bid
      exact Relation.TransGen.single h_infix
    | @tail z w h_clos h_infix ih =>
      rcases h_infix with ⟨bid, h_infix⟩
      rcases ih with ⟨bid', h_clos⟩
      exists bid'
      apply Relation.TransGen.tail h_clos
      have h_in : z ∈ H.behaviors bid := by
        rcases h_infix with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_in' : z ∈ H.behaviors bid' := by
        cases h_clos with
        | single h_infix' =>
          rcases h_infix' with ⟨init, tail, h_eq⟩
          simp [← h_eq]
        | tail h_clos' h_infix' =>
          rcases h_infix' with ⟨init, tail, h_eq⟩
          simp [← h_eq]
      have h_eq : bid = bid' := by
        exact wf_history_event_unique h_wf h_in h_in'
      subst h_eq
      assumption

lemma model_from_history_po_events_only {H : History} :
    (⊢ H) →
    ∀ e1 e2,
      (model_from_history H).po e1 e2 →
      e1 ∈ (model_from_history H).events ∧
      e2 ∈ (model_from_history H).events :=
  by
    intro h_wf e1 e2 h_po
    rcases h_po with ⟨bid, init, tail, h_eq⟩
    refine ⟨?_, ?_⟩
    · exact ⟨bid, by rw [← h_eq]; simp⟩
    · exact ⟨bid, by rw [← h_eq]; simp⟩

lemma model_from_history_po_shape {H : History} :
    (⊢ H) →
    ∀ e1 e2,
      (model_from_history H).po e1 e2 →
      match e1, e2 with
      | .Run _, .Spawn _
      | .Run _, .Complete _
      | .Spawn _, .Spawn _
      | .Spawn _, .Complete _ => True
      | _, _ => False :=
  by
    intro h_wf e1 e2 h_po
    rcases h_wf with ⟨h_behaviors, _, _, _, _⟩
    rcases h_po with ⟨bid, h_infix⟩
    rcases (wf_behavior_history_pair_inv (h_behaviors bid) h_infix) <;>
      rcases e1 <;> rcases e2 <;> grind [is_run, is_spawn, is_complete]

lemma model_from_history_po_unique_pred {H : History} :
    (⊢ H) →
    ∀ e1 e2 e3,
      (model_from_history H).po e1 e3 →
      (model_from_history H).po e2 e3 →
      e1 = e2 :=
  by
    intro h_wf e1 e2 e3 h13 h23
    rcases h_wf with ⟨h_behaviors, h_unique, _, _, _⟩
    rcases h13 with ⟨bid1, h_infix1⟩
    rcases h23 with ⟨bid2, h_infix2⟩
    have h_disj : is_spawn e3 ∨ is_complete e3 := by
      have := wf_behavior_history_pair_inv (h_behaviors bid1) h_infix1
      grind
    cases h_disj with
    | inl h_spawn =>
      have h_mem1 : e3 ∈ H.behaviors bid1 := by
        rcases h_infix1 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_mem2 : e3 ∈ H.behaviors bid2 := by
        rcases h_infix2 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_eq : bid1 = bid2 := by
        simp [unique_spawns] at h_unique
        rcases e3 <;> simp at h_spawn
        by_cases (bid1 = bid2) <;> grind
      subst h_eq
      have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid1) := by
        exact wf_behavior_history_no_dup (h_behaviors bid1)
      exact no_dup_pair_eq_l h_no_dup h_infix1 h_infix2
    | inr h_complete =>
      have h_mem1 : e3 ∈ H.behaviors bid1 := by
        rcases h_infix1 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_mem2 : e3 ∈ H.behaviors bid2 := by
        rcases h_infix2 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_eq : bid1 = bid2 := by
        rcases e3 <;> simp at h_complete
        grind [wf_history_complete_mem_inv]
      subst h_eq
      have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid1) := by
        exact wf_behavior_history_no_dup (h_behaviors bid1)
      exact no_dup_pair_eq_l h_no_dup h_infix1 h_infix2

lemma model_from_history_po_unique_succ {H : History} :
    (⊢ H) →
    ∀ e1 e2 e3,
      (model_from_history H).po e1 e2 →
      (model_from_history H).po e1 e3 →
      e2 = e3 :=
  by
    intro h_wf e1 e2 e3 h12 h13
    rcases h_wf with ⟨h_behaviors, h_unique, _, _, _⟩
    rcases h12 with ⟨bid1, h_infix1⟩
    rcases h13 with ⟨bid2, h_infix2⟩
    have h_disj : is_run e1 ∨ is_spawn e1 := by
      have := wf_behavior_history_pair_inv (h_behaviors bid1) h_infix1
      grind
    cases h_disj with
    | inl h_run =>
      have h_mem1 : e1 ∈ H.behaviors bid1 := by
        rcases h_infix1 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_mem2 : e1 ∈ H.behaviors bid2 := by
        rcases h_infix2 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_eq : bid1 = bid2 := by
        rcases e1 <;> simp at h_run
        grind [wf_history_run_mem_inv]
      subst h_eq
      have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid1) := by
        exact wf_behavior_history_no_dup (h_behaviors bid1)
      exact no_dup_pair_eq_r h_no_dup h_infix1 h_infix2
    | inr h_spawn =>
      have h_mem1 : e1 ∈ H.behaviors bid1 := by
        rcases h_infix1 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_mem2 : e1 ∈ H.behaviors bid2 := by
        rcases h_infix2 with ⟨init, tail, h_eq⟩
        rw [← h_eq]
        simp
      have h_eq : bid1 = bid2 := by
        simp [unique_spawns] at h_unique
        rcases e1 <;> simp at h_spawn
        by_cases (bid1 = bid2) <;> grind
      subst h_eq
      have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid1) := by
        exact wf_behavior_history_no_dup (h_behaviors bid1)
      exact no_dup_pair_eq_r h_no_dup h_infix1 h_infix2

lemma model_from_history_po_preceded_by_run {H : History} :
    (⊢ H) →
    ∀ e,
      e ∈ (model_from_history H).events →
      ∃ bid, ((model_from_history H).po*) (.Run bid) e :=
  by
    intro h_wf e h_in
    rcases h_wf with ⟨h_behaviors, _, _, _, _⟩
    rcases h_in with ⟨bid, h_in_bid⟩
    refine ⟨bid, ?_⟩
    apply po_pick_bid (bid := bid)
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup (h_behaviors bid)
    rw [pair_refl_trans_iff h_no_dup]
    have h_bwf : wf_behavior_history bid (H.behaviors bid) := h_behaviors bid
    cases h_beh : H.behaviors bid with
    | nil =>
      simp [h_beh] at h_in_bid
    | cons e' es =>
      cases e' with
      | Spawn bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Complete bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Run bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
        rcases h_bwf with ⟨h_bid_eq, h_rest⟩
        subst h_bid_eq
        simp [h_beh] at h_in_bid
        rcases h_in_bid with h_head | h_tail
        · left
          exact h_head.symm
        · right
          rcases List.mem_iff_append.mp h_tail with ⟨init, tail, h_split⟩
          rw [h_split]
          simp

lemma model_from_history_po_run_complete_same_bid {H : History} :
    (⊢ H) →
    ∀ bid1 bid2,
      ((model_from_history H).po+) (.Run bid1) (.Complete bid2) →
      bid1 = bid2 :=
  by
    intro h_wf bid1 bid2 h_path
    have h_wf' : (⊢ H) := h_wf
    rcases h_wf with ⟨h_behaviors, _, _, _, _⟩
    have ⟨bid, h_trans⟩ := po_exists_inv h_wf' h_path
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup (h_behaviors bid)
    have h_sub := (pair_trans_iff h_no_dup).1 h_trans
    rw [pair_sublist_iff] at h_sub
    rcases h_sub with ⟨init, mid, tail, h_eq⟩
    have h_run_mem : .Run bid1 ∈ H.behaviors bid := by
      rw [h_eq]
      simp
    have h_complete_mem : .Complete bid2 ∈ H.behaviors bid := by
      rw [h_eq]
      simp
    have h_bid_run : bid = bid1 :=
      wf_history_run_mem_inv (h_behaviors bid) h_run_mem
    have h_bid_complete : bid = bid2 :=
      wf_history_complete_mem_inv (h_behaviors bid) h_complete_mem
    grind

lemma model_from_history_trans_po_run_to_complete {H : History} {bid : BId} :
    (⊢ H) →
    .Complete bid ∈ H.behaviors bid →
    ((model_from_history H).po+) (.Run bid) (.Complete bid) :=
  by
    intro h_wf h_complete_mem
    have h_bwf : wf_behavior_history bid (H.behaviors bid) := h_wf.1 bid
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup h_bwf
    apply po_trans_pick_bid (bid := bid)
    rw [pair_trans_iff h_no_dup]
    rw [pair_sublist_iff]
    cases h_beh : H.behaviors bid with
    | nil =>
      simp [h_beh] at h_complete_mem
    | cons e es =>
      cases e with
      | Spawn bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Complete bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Run bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
        rcases h_bwf with ⟨h_bid_eq, h_rest⟩
        subst h_bid_eq
        have h_tail_mem : .Complete bid ∈ es := by
          simpa [h_beh] using h_complete_mem
        rcases List.mem_iff_append.mp h_tail_mem with ⟨mid, tail, h_split⟩
        exists [], mid, tail
        simp [h_split]

lemma model_from_history_po_run_to_complete {H : History} {bid : BId} :
    (⊢ H) →
    .Complete bid ∈ H.behaviors bid →
    ((model_from_history H).po*) (.Run bid) (.Complete bid) :=
  by
    intro h_wf h_complete_mem
    have h_bwf : wf_behavior_history bid (H.behaviors bid) := h_wf.1 bid
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup h_bwf
    apply po_pick_bid (bid := bid)
    rw [pair_refl_trans_iff h_no_dup]
    right
    rw [pair_sublist_iff]
    cases h_beh : H.behaviors bid with
    | nil =>
      simp [h_beh] at h_complete_mem
    | cons e es =>
      cases e with
      | Spawn bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Complete bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
      | Run bid' =>
        simp [wf_behavior_history, h_beh] at h_bwf
        rcases h_bwf with ⟨h_bid_eq, h_rest⟩
        subst h_bid_eq
        have h_tail_mem : .Complete bid ∈ es := by
          simpa [h_beh] using h_complete_mem
        rcases List.mem_iff_append.mp h_tail_mem with ⟨mid, tail, h_split⟩
        exists [], mid, tail
        simp [h_split]

lemma model_from_history_wf_po {H : History} :
    (⊢ H) →
    match model_from_history H with
    | ⟨events, po, _⟩ =>
      wf_po_relation events po :=
  by
    intro h_wf
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact model_from_history_po_events_only h_wf
    · exact model_from_history_po_shape h_wf
    · exact model_from_history_po_unique_pred h_wf
    · exact model_from_history_po_unique_succ h_wf
    · exact model_from_history_po_preceded_by_run h_wf
    · exact model_from_history_po_run_complete_same_bid h_wf

lemma model_from_history_wf_co {H : History} :
    (⊢ H) →
    match model_from_history H with
    | ⟨events, _, co⟩ =>
    wf_co_relation events co :=
  by
    intro h_wf
    rcases h_wf with ⟨h_behaviors, h_unique, h_cowns, h_corr, h_order⟩
    and_intros
    · introv h_co
      rcases h_co with ⟨bid1, bid2, init, tail, h_eq1, h_eq2, h_tail⟩
      have h_in1 : e1 ∈ H.cowns c := by grind
      have h_in2 : e2 ∈ H.cowns c := by grind
      and_intros
      · exact h_corr c e1 h_in1
      · exact h_corr c e2 h_in2
    · introv h_co
      rcases h_co with ⟨bid1, bid2, init, tail, h_eq1, h_eq2, h_tail⟩
      grind
    · introv h_co1 h_co2
      rcases h_co1 with ⟨bid1, bid2, init1, tail1, h_eq11, h_eq12, h_tail1⟩
      rcases h_co2 with ⟨bid3, bid4, init2, tail2, h_eq21, h_eq22, h_tail2⟩
      subst h_eq11 h_eq12 h_eq21
      simp at h_eq22
      subst h_eq22
      have h_no_dup := wf_cown_history_no_dup (h_cowns c)
      rw [h_tail1] at *
      have h_eq : (init1 ++ [Event.Complete bid1]) ++ Event.Run bid2 :: tail1 =
                  (init2 ++ [Event.Complete bid3]) ++ Event.Run bid2 :: tail2 := by
        simpa
      have ⟨h_eq1, h_eq2⟩:= no_dup_middle_inv ?_ h_eq <;> try simpa
      simp at h_eq1
      simpa using h_eq1.2
    · introv h_co1 h_co2
      rcases h_co1 with ⟨bid1, bid2, init1, tail1, h_eq11, h_eq12, h_tail1⟩
      rcases h_co2 with ⟨bid3, bid4, init2, tail2, h_eq21, h_eq22, h_tail2⟩
      subst h_eq11 h_eq12 h_eq22
      simp at h_eq21
      subst h_eq21
      have h_no_dup := wf_cown_history_no_dup (h_cowns c)
      rw [h_tail1] at *
      have ⟨h_eq1, h_eq2⟩:= no_dup_middle_inv ?_ h_tail2 <;> try simpa
      simp at h_eq2
      simpa using h_eq2.1

lemma model_from_history_co_mem {H : History} {c : Cown} {e1 e2 : Event} :
    (model_from_history H).co c e1 e2 →
    e1 ∈ H.cowns c ∧ e2 ∈ H.cowns c :=
  by
    intro h_co
    rcases h_co with ⟨bid1, bid2, init, tail, h_eq1, h_eq2, h_hist⟩
    subst h_eq1 h_eq2
    constructor <;> rw [h_hist] <;> simp

lemma model_from_history_co_run_mem {H : History} {c : Cown} {e : Event} {bid : BId} :
    (model_from_history H).co c e (.Run bid) →
    .Run bid ∈ H.cowns c :=
  by
    intro h_co
    exact (model_from_history_co_mem h_co).2

lemma model_from_history_co_complete_mem {H : History} {c : Cown} {bid : BId} {e : Event} :
    (model_from_history H).co c (.Complete bid) e →
    .Complete bid ∈ H.cowns c :=
  by
    intro h_co
    exact (model_from_history_co_mem h_co).1

lemma model_from_history_complete_event_mem {H : History} {bid : BId} :
    (⊢ H) →
    .Complete bid ∈ (model_from_history H).events →
    .Complete bid ∈ H.behaviors bid :=
  by
    intro h_wf h_in
    rcases h_in with ⟨owner, h_mem⟩
    have h_owner : owner = bid :=
      wf_history_complete_mem_inv (h_wf.1 owner) h_mem
    simpa [h_owner] using h_mem

lemma complete_behavior_event_on_cown {H : History} {c : Cown} {bid : BId} :
    (⊢ H) →
    .Run bid ∈ H.cowns c →
    .Complete bid ∈ H.behaviors bid →
    .Complete bid ∈ H.cowns c :=
  by
    intro h_wf h_run_mem h_complete_mem
    exact h_wf.2.2.2.2.1 c bid h_run_mem h_complete_mem

-- TODO: Move to Common.lean
lemma list_index_lt_inv {A} {x y : A} {l : List A} {i j : Nat} :
  l[i]? = some x →
  l[j]? = some y →
  i < j →
  ∃init mid tail, l = init ++ x :: mid ++ y :: tail :=
  by
    introv h_i h_j h_lt
    induction l generalizing i j with
    | nil => rcases i <;> simp at h_i
    | cons z zs ih =>
      cases h_lt with
      | refl =>
        simp at h_i h_j
        cases i with
        | zero =>
          simp at h_i h_j
          subst h_i
          cases zs with
          | nil => simp at h_j
          | cons z' zs' =>
            simp at h_j
            subst h_j
            exists [], [], zs'
        | succ i' =>
          simp at h_i
          have ⟨init, mid, tail, h_eq⟩ := ih h_i h_j (by simp)
          subst h_eq
          grind
      | @step k h_le =>
        cases i with
        | zero =>
          simp at h_i h_j
          subst h_i
          have h_in : y ∈ zs := by
            grind
          have ⟨init, tail, h_eq⟩ : exists init tail, zs = init ++ y :: tail := by
            rcases List.mem_iff_append.mp h_in with ⟨init, tail, h_eq⟩
            exists init, tail
          subst h_eq
          exists [], init, tail
        | succ i' =>
          simp at h_i h_j
          have h_lt : i' < k := by grind
          have ⟨init, mid, tail, h_eq⟩ := ih h_i h_j h_lt
          grind

lemma list_annoying_inv {A} {a b c d : A} {l init init' tail tail' : List A} :
  a ≠ c →
  a ≠ d →
  b ≠ c →
  l = init' ++ a :: b :: tail' →
  l = init ++ c :: d :: tail →
  (∃init'' mid tail'', l = init'' ++ a :: b :: mid ++ c :: d :: tail'') ∨
  (∃init'' mid tail'', l = init'' ++ c :: d :: mid ++ a :: b :: tail'') :=
  by
    intro h_ac h_ad h_bc h_ab h_cd
    induction init' generalizing l init with
    | nil =>
      simp at h_ab
      rcases init with _ | ⟨x, init'⟩ <;> simp at h_cd; · grind
      rcases init' with _ | ⟨y, init''⟩ <;> simp at h_cd; · grind
      subst h_cd
      simp at h_ab
      rcases h_ab with ⟨h_eq1, h_eq2, h_eq3⟩
      subst h_eq1 h_eq2
      left
      exists [], init'', tail
    | cons x xs ih =>
      simp at h_ab
      cases init with
      | nil =>
        simp at h_cd
        rcases xs with _ | ⟨y, ys⟩ <;> simp at h_ab; · grind
        subst h_cd
        simp at h_ab
        rcases h_ab with ⟨h_eq1, h_eq2, h_eq3⟩
        subst h_eq1 h_eq2 h_eq3
        right
        exists [], ys, tail'
      | cons y ys =>
        simp at h_cd
        subst h_cd
        simp at h_ab
        rcases h_ab with ⟨h_eq1, h_eq2⟩
        subst h_eq1
        rw [←h_eq2] at ih
        cases (ih (l := ys ++ c :: d :: tail) (init := ys) rfl rfl) <;> grind

lemma rel_clos_weaken {A} {R S : A → A → Prop} {x y : A} :
  (∀x y, R x y → S x y) →
  (R*) x y →
  (S*) x y :=
  by
    introv h_subset h_clos
    induction h_clos with
    | refl => constructor
    | @tail z w h_clos h_infix ih =>
      apply Relation.ReflTransGen.tail ih
      apply h_subset
      assumption

lemma rel_trans_clos_weaken {A} {R S : A → A → Prop} {x y : A} :
  (∀x y, R x y → S x y) →
  (R+) x y →
  (S+) x y :=
  by
    introv h_subset h_clos
    induction h_clos with
    | single h_infix =>
      constructor
      apply h_subset
      assumption
    | @tail z w h_clos h_infix ih =>
      apply Relation.TransGen.tail ih
      apply h_subset
      assumption

-- TODO: Check if we can't just derive the new premise from wf_history
lemma wf_cown_history_connected {H} {bid1 bid2} {mid tail} :
    let adjacent_c_r := fun ch e1 e2 =>
      ∃bid1, e1 = Event.Complete bid1 ∧
      ∃bid2, e2 = Event.Run bid2 ∧
      ∃init tail, ch = init ++ e1 :: e2 :: tail
    (⊢ H) →
    (∀e, e ∈ Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail →
      ∃bid, e ∈ H.behaviors bid) →
    wf_cown_history (Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail) →
    (((model_from_history H).po ∪ adjacent_c_r
        (Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail)) * ) (.Run bid1) (.Complete bid2) :=
  by
    introv adj h_wf h_corr h_wf_c
    generalize h_len : mid.length = n
    induction n using Nat.strongRecOn generalizing mid bid1 with
    | ind n ih =>
      cases mid with
      | nil =>
        clear ih
        simp [wf_cown_history] at h_wf_c
        rw [←h_wf_c.1]
        have h_clos : ((model_from_history H).po*) (.Run bid1) (.Complete bid1) := by
          have h_mem_ex := h_corr (.Complete bid1) (by simp [h_wf_c.1])
          rcases h_mem_ex with ⟨bid', h_mem⟩
          have h_eq : bid' = bid1 :=
            wf_history_complete_mem_inv (h_wf.1 bid') h_mem
          subst h_eq
          exact model_from_history_po_run_to_complete h_wf h_mem
        apply rel_clos_weaken ?_ h_clos
        · introv h_po
          left
          assumption
      | cons e mid' =>
        rcases e with _ | _ | bid1' <;> simp [wf_cown_history] at h_wf_c
        rcases h_wf_c with ⟨h_bid_eq, h_wf_c', _⟩
        subst h_bid_eq
        cases mid' with
        | nil => simp [wf_cown_history] at h_wf_c'
        | cons e' mid'' =>
          rcases e' with _ | bid | bid <;> simp [wf_cown_history] at h_wf_c'
          have h_len' : mid''.length < n := by grind
          have h_corr' :
              ∀e, e ∈ Event.Run bid :: mid'' ++ Event.Complete bid2 :: tail →
                ∃bid', e ∈ H.behaviors bid' := by
            intro e h_mem
            have h_mem_big :
                e ∈ [Event.Run bid1, Event.Complete bid1] ++
                  (Event.Run bid :: mid'' ++ Event.Complete bid2 :: tail) := by
              apply List.mem_append.mpr
              right
              simpa using h_mem
            apply h_corr e
            simpa [List.append_assoc] using h_mem_big
          have h_clos := ih (mid''.length) h_len' h_corr' h_wf_c' rfl
          have h_clos_po : ((model_from_history H).po*) (.Run bid1) (.Complete bid1) := by
            have h_mem_ex := h_corr (.Complete bid1) (by simp)
            rcases h_mem_ex with ⟨bid', h_mem⟩
            have h_eq : bid' = bid1 :=
              wf_history_complete_mem_inv (h_wf.1 bid') h_mem
            subst h_eq
            exact model_from_history_po_run_to_complete h_wf h_mem

          -- cheat takes .Run bid1 to .Complete bid1
          -- a single step of adj takes .Complete bid1 to .Run bid
          -- h_clos takes .Run bid to .Complete bid2
          -- TODO: Have a look at what Copilot did below and clean up
          let ch_small := Event.Run bid :: mid'' ++ Event.Complete bid2 :: tail
          let ch_big :=
            Event.Run bid1 ::
            Event.Complete bid1 ::
            Event.Run bid ::
            (mid'' ++ Event.Complete bid2 :: tail)
          have h_lift :
              ∀ {u v},
                (((model_from_history H).po ∪ adj ch_small) * ) u v →
                (((model_from_history H).po ∪ adj ch_big) * ) u v := by
            intro u v h_rel
            induction h_rel with
            | refl =>
              exact Relation.ReflTransGen.refl
            | @tail z w h_prev h_step ih =>
              have h_step' : ((model_from_history H).po ∪ adj ch_big) z w := by
                cases h_step with
                | inl h_po =>
                  exact Or.inl h_po
                | inr h_adj =>
                  rcases h_adj with ⟨bid1', h_eq1, bid2', h_eq2, init, tail', h_eq⟩
                  refine Or.inr ?_
                  refine ⟨
                    bid1', h_eq1,
                    bid2', h_eq2,
                    Event.Run bid1 :: Event.Complete bid1 :: init,
                    tail',
                    ?_
                  ⟩
                  simpa [ch_small, ch_big, List.append_assoc] using h_eq
              exact Relation.ReflTransGen.tail ih h_step'
          have h_clos' :
              (((model_from_history H).po ∪ adj ch_big) * ) (.Run bid) (.Complete bid2) := by
            exact h_lift (by simpa [ch_small] using h_clos)
          have h_adj_step : adj ch_big (.Complete bid1) (.Run bid) := by
            refine ⟨
              bid1, rfl,
              bid, rfl,
              [Event.Run bid1],
              mid'' ++ (Event.Complete bid2 :: tail),
              ?_
            ⟩
            simp [ch_big]
          have h_run_to_run :
              (((model_from_history H).po ∪ adj ch_big) * ) (.Run bid1) (.Run bid) := by
            refine Relation.ReflTransGen.tail ?_ (Or.inr h_adj_step)
            exact rel_clos_weaken (fun _ _ h_po => Or.inl h_po) h_clos_po
          exact Relation.ReflTransGen.trans h_run_to_run h_clos'

lemma wf_cown_history_connected_middle {H : History} {c : Cown} {bid1 bid2 : BId}
                                       {init mid tail : List Event} :
    (⊢ H) →
    wf_cown_history (H.cowns c) →
    H.cowns c = init ++ .Run bid1 :: mid ++ .Complete bid2 :: tail →
    (((model_from_history H).po ∪ (model_from_history H).co c) * ) (.Run bid1) (.Complete bid2) :=
  by
    intro h_wf h_wf_c h_eq
    have h_wf_c' : wf_cown_history (.Run bid1 :: mid ++ .Complete bid2 :: tail) := by
      rw [h_eq] at h_wf_c
      apply wf_cown_history_append_inv (init := init)
      simpa using h_wf_c
    -- TODO: Check for shorter proof
    have h_corr' :
        ∀e, e ∈ Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail →
          ∃bid, e ∈ H.behaviors bid := by
      intro e h_mem
      have h_mem_cown : e ∈ H.cowns c := by
        rw [h_eq]
        have h_suffix :
            e ∈ init ++ (Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail) := by
          apply List.mem_append.mpr
          right
          exact h_mem
        simpa [List.append_assoc] using h_suffix
      exact h_wf.2.2.2.1 c e h_mem_cown
    have h_clos := wf_cown_history_connected h_wf h_corr' h_wf_c'
    apply rel_clos_weaken ?_ h_clos
    · intros x y h_clos
      cases h_clos with
      | inl h_po =>
        left
        assumption
      | inr h_adj =>
        right
        rcases h_adj with ⟨bid1', h_eq1, bid2', h_eq2, init', tail', h_eq⟩
        subst h_eq1 h_eq2
        simp [model_from_history]
        grind

lemma wf_cown_history_connected_cr {H} {bid1 bid2} {mid tail} :
    let adjacent_c_r := fun ch e1 e2 =>
      ∃bid1, e1 = Event.Complete bid1 ∧
      ∃bid2, e2 = Event.Run bid2 ∧
      ∃init tail, ch = init ++ e1 :: e2 :: tail
    (⊢ H) →
    (∀e, e ∈ .Run bid1 :: .Complete bid1 :: mid ++ .Run bid2 :: tail →
      ∃bid, e ∈ H.behaviors bid) →
    wf_cown_history (.Run bid1 :: .Complete bid1 :: mid ++ .Run bid2 :: tail) →
    (((model_from_history H).po ∪ adjacent_c_r
        (.Run bid1 :: .Complete bid1 :: mid ++ .Run bid2 :: tail))+) (.Complete bid1) (.Run bid2) :=
  by
    introv adj h_wf h_corr h_wf_c
    induction mid using wf_cown_history.induct generalizing bid1 with
    | case1 =>
      simp
      apply Relation.TransGen.single
      right
      simp [adj]
      exists [Event.Run bid1], tail
    | case2 bid => simp [wf_cown_history]at h_wf_c
    | case3 bid1' bid2' mid' ih =>
      have h_eq : bid1' = bid2' := by
        simp [wf_cown_history] at h_wf_c
        grind
      subst h_eq

      have h_corr' : (∀e, e ∈ Event.Run bid1' :: Event.Complete bid1' :: mid' ++
                              Event.Run bid2 :: tail →
                        ∃bid, e ∈ H.behaviors bid) := by
        grind

      have h_wf_c' : wf_cown_history (Event.Run bid1' :: Event.Complete bid1' :: mid' ++
                                      Event.Run bid2 :: tail) := by
        grind [wf_cown_history]

      have h_clos := ih h_corr' h_wf_c'
      have h_clos' : (((model_from_history H).po ∪
                        adj (Event.Run bid1 :: Event.Complete bid1 ::
                             Event.Run bid1' :: Event.Complete bid1' :: mid' ++
                             Event.Run bid2 :: tail))+)
             (Event.Complete bid1') (Event.Run bid2) := by
        apply rel_trans_clos_weaken ?_ h_clos
        simp
        introv h_rel
        cases h_rel with
        | inl h_po =>
          left
          assumption
        | inr h_adj =>
          right
          rcases h_adj with ⟨bid1'', h_eq1, bid2'', h_eq2, init, tail, h_eq⟩
          grind

      have h_clos_po : ((model_from_history H).po+) (.Run bid1') (.Complete bid1') := by
        have h_mem : .Complete bid1' ∈ H.behaviors bid1' := by
          have h_mem_ex := h_corr (.Complete bid1') (by simp)
          rcases h_mem_ex with ⟨owner, h_mem_owner⟩
          have h_owner : owner = bid1' :=
            wf_history_complete_mem_inv (h_wf.1 owner) h_mem_owner
          simpa [h_owner] using h_mem_owner
        exact model_from_history_trans_po_run_to_complete h_wf h_mem

      have h_adj_step : adj (.Run bid1 :: .Complete bid1 :: .Run bid1' :: .Complete bid1' ::mid' ++
                             Event.Run bid2 :: tail) (.Complete bid1) (.Run bid1') := by
        simp [adj]
        exists [.Run bid1], (.Complete bid1'::mid' ++ .Run bid2 :: tail)

      apply Relation.TransGen.trans ?_ h_clos'
      apply Relation.TransGen.trans (b := .Run bid1') ?_ ?_
      · apply Relation.TransGen.single
        right
        grind
      · apply rel_trans_clos_weaken ?_ h_clos_po
        introv h_po
        left
        assumption
    | case4 es h_empty h_single ih =>
      rcases es with _ | ⟨e, es'⟩ <;> simp at h_empty
      cases es' with
      | nil =>
        rcases e <;> simp [wf_cown_history] at h_wf_c
      | cons e' cs''' =>
        rcases e <;> rcases e' <;> simp [wf_cown_history] at h_wf_c
        grind

lemma wf_cown_history_connected_middle_cr {H : History} {c : Cown} {bid1 bid2 : BId}
                                          {init mid tail : List Event} :
    (⊢ H) →
    wf_cown_history (H.cowns c) →
    H.cowns c = init ++ .Complete bid1 :: mid ++ .Run bid2 :: tail →
    (((model_from_history H).po ∪ (model_from_history H).co c) + ) (.Complete bid1) (.Run bid2) :=
  by
    intro h_wf h_wf_c h_eq
    -- Extract that init ends with Run bid1 (Complete is always preceded by its Run).
    have h_wf_full : wf_cown_history (init ++ .Complete bid1 :: (mid ++ .Run bid2 :: tail)) := by
      grind

    have ⟨init', h_init_eq⟩ := wf_cown_history_complete_pred h_wf_full
    subst h_init_eq
    simp at h_wf_full
    have h_wf_c' := wf_cown_history_append_inv h_wf_full
    -- TODO: Check for shorter proof
    have h_corr' :
        ∀e, e ∈ .Run bid1 :: .Complete bid1 :: mid ++ .Run bid2 :: tail →
          ∃bid, e ∈ H.behaviors bid := by
      intro e h_mem
      have h_mem_cown : e ∈ H.cowns c := by
        rw [h_eq]
        have h_suffix :
            e ∈ init' ++ (.Run bid1 :: .Complete bid1 :: mid ++ .Run bid2 :: tail) := by
          apply List.mem_append.mpr
          right
          exact h_mem
        simpa [List.append_assoc] using h_suffix
      exact h_wf.2.2.2.1 c e h_mem_cown
    have h_clos := wf_cown_history_connected_cr h_wf h_corr' h_wf_c'
    apply rel_trans_clos_weaken ?_ h_clos
    · intros x y h_clos
      cases h_clos with
      | inl h_po =>
        left
        assumption
      | inr h_adj =>
        right
        rcases h_adj with ⟨bid1', h_eq1, bid2', h_eq2, init', tail', h_eq⟩
        subst h_eq1 h_eq2
        simp [model_from_history]
        grind

lemma model_from_history_single_causal_path {H : History} :
    (⊢ H) →
    match model_from_history H with
    | ⟨_, po, co⟩ =>
    (∀e1 e2 e3 e4 c,
    e1 ≠ e3 →
    e2 ≠ e4 →
    co c e1 e2 →
    co c e3 e4 →
    ((po ∪ co c)*) e2 e3 ∨ ((po ∪ co c)*) e4 e1) :=
  by
    intro h_wf
    simp
    intro e1 e2 e3 e4 c h_neq1 h_neq2 h_21 h_34
    simp [model_from_history] at h_21 h_34
    rcases h_21 with ⟨bid1, h_eq1, bid2, h_eq2, init, tail, h_mid⟩
    rcases h_34 with ⟨bid3, h_eq3, bid4, h_eq4, init', tail', h_mid'⟩
    subst h_eq1 h_eq2 h_eq3 h_eq4
    have h_wf_c : wf_cown_history (H.cowns c) := h_wf.2.2.1 c
    cases (list_annoying_inv (by grind) (by grind) (by grind) h_mid h_mid') with
    | inl h_ex =>
      left
      rcases h_ex with ⟨init, ⟨mid, ⟨tail, h_eq⟩⟩⟩
      have h_eq' : (init ++ Event.Complete bid1 :: Event.Run bid2 :: mid) =
                   ((init ++ [Event.Complete bid1]) ++ Event.Run bid2 :: mid) := by
        simp
      rw [h_eq'] at h_eq
      exact wf_cown_history_connected_middle h_wf h_wf_c h_eq
    | inr h_ex =>
      right
      rcases h_ex with ⟨init, ⟨mid, ⟨tail, h_eq⟩⟩⟩
      have h_eq' : (init ++ Event.Complete bid3 :: Event.Run bid4 :: mid) =
                   ((init ++ [Event.Complete bid3]) ++ Event.Run bid4 :: mid) := by
        simp
      rw [h_eq'] at h_eq
      exact wf_cown_history_connected_middle h_wf h_wf_c h_eq

------------------------------------------

def model_co_any (m : Model) : Event → Event → Prop :=
  fun e1 e2 => ∃c, m.co c e1 e2

def model_base_rel (m : Model) : Event → Event → Prop :=
  m.po ∪ model_co_any m ∪ derived_run_relation m

def model_full_rel (m : Model) : Event → Event → Prop :=
  model_base_rel m ∪ derived_hb_relation m

lemma history_wf_has_timestamp {H : History} :
    (⊢ H) →
    ∃t top, History.timestamp_wf H t ∧ ∀e ∈ History.events H, t e ≤ top :=
  by
    intro h_wf
    exact h_wf.2.2.2.2.2

lemma model_from_history_po_lt_timestamp {H : History} {t : Event → Nat} :
    History.timestamp_wf H t →
    ∀e1 e2,
      (model_from_history H).po e1 e2 →
      t e1 < t e2 :=
  by
    intro h_twf e1 e2 h_po
    rcases h_po with ⟨bid, h_infix⟩
    exact h_twf.1 bid e1 e2 h_infix

lemma model_from_history_co_lt_timestamp {H : History} {t : Event → Nat} :
    History.timestamp_wf H t →
    ∀c e1 e2,
      (model_from_history H).co c e1 e2 →
      t e1 < t e2 :=
  by
    intro h_twf c e1 e2 h_co
    rcases h_co with ⟨bid1, bid2, init, tail, h_eq1, h_eq2, h_mid⟩
    subst h_eq1 h_eq2
    exact h_twf.2.1 c _ _ ⟨init, tail, by simpa using h_mid.symm⟩

lemma model_from_history_run_lt_timestamp {H : History} {t : Event → Nat} :
    (⊢ H) →
    History.timestamp_wf H t →
    ∀e1 e2,
      (derived_run_relation (model_from_history H)) e1 e2 →
      t e1 < t e2 :=
  by
    intro h_wf h_twf e1 e2 h_run
    -- TODO: This seems overly complicated
    have h_twf_flat :
        (∀bid e1 e2, [e1, e2] <:+: H.behaviors bid → t e1 < t e2)
        ∧ (∀c e1 e2, [e1, e2] <:+: H.cowns c → t e1 < t e2)
        ∧ (∀parent bid,
            .Spawn bid ∈ H.behaviors parent →
            .Run bid ∈ H.behaviors bid →
            t (.Spawn bid) < t (.Run bid))
        ∧ (∀c bid1 bid2,
            t (.Spawn bid1) < t (.Spawn bid2) →
            .Complete bid1 ∈ H.cowns c →
            .Run bid2 ∈ H.cowns c →
            t (.Complete bid1) < t (.Run bid2)) := by
      simpa [History.timestamp_wf, and_assoc] using h_twf
    rcases h_twf_flat with ⟨_, _, h_twf_spawn_run, _⟩
    rcases e1 with bid | _ | _ <;>
      rcases e2 with _ | bid' | _ <;>
      simp [derived_run_relation] at h_run
    rcases h_run with ⟨h_eq, h_spawn_in, h_run_in⟩
    subst h_eq
    rcases h_spawn_in with ⟨parent, h_spawn_mem⟩
    rcases h_run_in with ⟨owner, h_run_mem⟩
    have h_owner : owner = bid := by
      exact wf_history_run_mem_inv (h_wf.1 owner) h_run_mem
    have h_lt_owner : t (Event.Spawn owner) < t (Event.Run owner) :=
      h_twf_spawn_run parent owner
        (by simpa [h_owner] using h_spawn_mem)
        (by simpa [h_owner] using h_run_mem)
    simpa [h_owner] using h_lt_owner

lemma model_from_history_base_rel_lt_timestamp {H : History} {t : Event → Nat} :
    (⊢ H) →
    History.timestamp_wf H t →
    ∀e1 e2,
      model_base_rel (model_from_history H) e1 e2 →
      t e1 < t e2 :=
  by
    intro h_wf h_twf e1 e2 h_rel
    rcases h_rel with h_left | h_run
    · rcases h_left with h_po | h_co
      · exact model_from_history_po_lt_timestamp h_twf e1 e2 h_po
      · rcases h_co with ⟨c, h_co⟩
        exact model_from_history_co_lt_timestamp h_twf c e1 e2 h_co
    · exact model_from_history_run_lt_timestamp h_wf h_twf e1 e2 h_run

lemma model_from_history_base_closure_lt_timestamp {H : History} {t : Event → Nat} :
    (⊢ H) →
    History.timestamp_wf H t →
    ∀e1 e2,
      (model_base_rel (model_from_history H)+) e1 e2 →
      t e1 < t e2 :=
  by
    intro h_wf h_twf e1 e2 h_clos
    induction h_clos with
    | single h_step =>
      exact model_from_history_base_rel_lt_timestamp h_wf h_twf _ _ h_step
    | @tail z w h_prev h_step ih =>
      have h_lt1 : t e1 < t z := ih
      have h_lt2 : t z < t w := model_from_history_base_rel_lt_timestamp h_wf h_twf _ _ h_step
      exact Nat.lt_trans h_lt1 h_lt2

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
      rcases h_wfc with ⟨h_bid_eq, h_wfc', _⟩
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

-- TODO: Look at this proof and clean it up
lemma list_order_lt_inv {A} {l : List A} {a b : A} {ord : A → ℕ} :
    ord a < ord b →
    a ∈ l →
    b ∈ l →
    (∀e1 e2, [e1, e2] <:+: l → ord e1 < ord e2) →
    ∃ init mid tail, l = init ++ a :: mid ++ b :: tail :=
  by
    have head_lt_of_mem_ordered :
        ∀ {x : A} {xs : List A} {y : A},
          y ∈ xs →
          (∀e1 e2, [e1, e2] <:+: (x :: xs) → ord e1 < ord e2) →
          ord x < ord y := by
      intro x xs y h_mem h_ord
      rcases List.mem_iff_append.mp h_mem with ⟨mid, tail, h_split⟩
      have h_path : ((fun e1 e2 ↦ [e1, e2] <:+: (x :: xs))+) x y := by
        rw [h_split]
        simpa [List.append_assoc] using
          (pair_infix_trans_clos_middle (x := x) (y := y) (mid := mid) (tail := tail))
      have h_ord_path : ((fun e1 e2 ↦ ord e1 < ord e2)+) x y := by
        exact rel_trans_clos_weaken (fun _ _ h_infix => h_ord _ _ h_infix) h_path
      have close_lt :
          ∀ {u v : A}, ((fun e1 e2 ↦ ord e1 < ord e2)+) u v → ord u < ord v := by
        intro u v h_clos
        induction h_clos with
        | single h_step => exact h_step
        | tail h_prev h_step ih => exact Nat.lt_trans ih h_step
      have h_xy : ord x < ord y := close_lt h_ord_path
      exact h_xy

    induction l with
    | nil =>
      intro h_lt h_a_mem
      cases h_a_mem
    | cons x xs ih =>
      intro h_lt h_a_mem h_b_mem h_ord
      simp at h_a_mem h_b_mem
      cases h_a_mem with
      | inl h_ax =>
        subst h_ax
        cases h_b_mem with
        | inl h_bx =>
          subst h_bx
          exact False.elim (Nat.lt_irrefl _ h_lt)
        | inr h_b_tail =>
          rcases List.mem_iff_append.mp h_b_tail with ⟨mid, tail, h_split⟩
          exact ⟨[], mid, tail, by simp [h_split]⟩
      | inr h_a_tail =>
        cases h_b_mem with
        | inl h_bx =>
          subst h_bx
          have h_ba : ord b < ord a := head_lt_of_mem_ordered h_a_tail h_ord
          exact False.elim (Nat.lt_asymm h_lt h_ba)
        | inr h_b_tail =>
          have h_ord_tail :
              ∀e1 e2, [e1, e2] <:+: xs → ord e1 < ord e2 := by
            intro e1 e2 h_infix
            apply h_ord
            rcases h_infix with ⟨init, tail, h_eq⟩
            exact ⟨x :: init, tail, by simp [h_eq]⟩
          rcases ih h_lt h_a_tail h_b_tail h_ord_tail with ⟨init, mid, tail, h_eq⟩
          exact ⟨x :: init, mid, tail, by simp [h_eq, List.append_assoc]⟩

lemma model_from_history_hb_subset_base_closure {H : History} :
    (⊢ H) →
    ∀e1 e2,
      (derived_hb_relation (model_from_history H)) e1 e2 →
      ∃c, (((model_from_history H).po ∪ (model_from_history H).co c)+) e1 e2 :=
  by
    introv h_wf h_hb
    simp [derived_hb_relation] at h_hb
    rcases e1 with _ | _ | bid1 <;>
      rcases e2 with _ | bid2 | _ <;>
      simp at h_hb
    rcases h_hb with ⟨h_po_co_r, h_overlap, h_c, h_r⟩

    rcases history_wf_has_timestamp h_wf with ⟨t, _, h_twf, _⟩
    have h_twf_flat :
      (∀bid e1 e2, [e1, e2] <:+: H.behaviors bid → t e1 < t e2)
      ∧ (∀c e1 e2, [e1, e2] <:+: H.cowns c → t e1 < t e2)
      ∧ (∀parent bid,
        .Spawn bid ∈ H.behaviors parent →
        .Run bid ∈ H.behaviors bid →
        t (.Spawn bid) < t (.Run bid))
      ∧ (∀c bid1 bid2,
        t (.Spawn bid1) < t (.Spawn bid2) →
        .Complete bid1 ∈ H.cowns c →
        .Run bid2 ∈ H.cowns c →
        t (.Complete bid1) < t (.Run bid2)) := by
      simpa [History.timestamp_wf, and_assoc] using h_twf
    rcases h_twf_flat with ⟨_, h_twf_co, _, h_twf_spawn_order⟩
    have h_lt : t (.Spawn bid1) < t (.Spawn bid2) :=
        model_from_history_base_closure_lt_timestamp h_wf h_twf (Event.Spawn bid1)
          (Event.Spawn bid2) h_po_co_r

    have ⟨c, h_mem1, h_mem2⟩ : ∃c, .Complete bid1 ∈ H.cowns c ∧ .Run bid2 ∈ H.cowns c := by
      let A : Set Cown :=
        {c | (∃e, (model_from_history H).co c e (Event.Run bid1))
                  ∨ (∃e, (model_from_history H).co c (Event.Complete bid1) e)}
      let B : Set Cown :=
        {c | (∃e, (model_from_history H).co c e (Event.Run bid2))
                  ∨ (∃e, (model_from_history H).co c (Event.Complete bid2) e)}
      have ⟨c, h_mem⟩ : ∃c, c ∈ (A ∩ B) := by
        by_cases h_ex : ∃c, c ∈ (A ∩ B)
        · exact h_ex
        · exfalso
          apply h_overlap
          funext c
          apply propext
          constructor
          · intro h_mem
            exfalso
            exact h_ex ⟨c, h_mem⟩
          · intro h_mem
            exact False.elim h_mem
      exists c
      rcases h_mem with ⟨h_mem1, h_mem2⟩
      subst A B
      and_intros
      · cases h_mem1 with
        | inl h_run1 =>
          rcases h_run1 with ⟨e, h_co1⟩
          have h_run1_mem : .Run bid1 ∈ H.cowns c := model_from_history_co_run_mem h_co1
          have h_complete1_beh : .Complete bid1 ∈ H.behaviors bid1 :=
            model_from_history_complete_event_mem h_wf h_c
          exact complete_behavior_event_on_cown h_wf h_run1_mem h_complete1_beh
        | inr h_complete1 =>
          rcases h_complete1 with ⟨e, h_co1⟩
          simp [model_from_history] at h_co1
          grind
      · cases h_mem2 with
        | inl h_run2 =>
          rcases h_run2 with ⟨e, h_co2⟩
          simp [model_from_history] at h_co2
          grind
        | inr h_complete2 =>
          rcases h_complete2 with ⟨e, h_co2⟩
          have h_complete2_cown : .Complete bid2 ∈ H.cowns c := by
            simp [model_from_history] at h_co2; grind
          exact wf_cown_history_complete_has_run (h_wf.2.2.1 c) h_complete2_cown

    clear h_overlap

    -- This is where we use the timestamp ordering
    have h_lt' : t (.Complete bid1) < t (.Run bid2) := by
      exact h_twf_spawn_order c bid1 bid2 h_lt h_mem1 h_mem2

    have h_wf_c : wf_cown_history (H.cowns c) := h_wf.2.2.1 c
    have ⟨init, mid, tail, h_c_eq⟩ : ∃init mid tail,
        H.cowns c = init ++ .Complete bid1 :: mid ++ .Run bid2 :: tail := by
      exact list_order_lt_inv h_lt' h_mem1 h_mem2 (h_twf_co c)
    have h_clos := wf_cown_history_connected_middle_cr h_wf h_wf_c h_c_eq
    exists c

lemma model_from_history_full_step_in_base_closure {H : History} :
    (⊢ H) →
    ∀e1 e2,
      model_full_rel (model_from_history H) e1 e2 →
      (model_base_rel (model_from_history H)+) e1 e2 :=
  by
    intro h_wf e1 e2 h_step
    rcases h_step with h_base | h_hb
    · exact Relation.TransGen.single h_base
    · have ⟨c, h_clos⟩ := model_from_history_hb_subset_base_closure h_wf e1 e2 h_hb
      apply rel_trans_clos_weaken ?_ h_clos
      intro e1 e2 h_step
      cases h_step with
      | inl h_po =>
        left
        left
        assumption
      | inr h_co =>
        left
        right
        exists c

lemma model_from_history_full_closure_in_base_closure {H : History} :
    (⊢ H) →
    ∀e1 e2,
      (model_full_rel (model_from_history H)+) e1 e2 →
      (model_base_rel (model_from_history H)+) e1 e2 :=
  by
    intro h_wf e1 e2 h_clos
    induction h_clos with
    | single h_step =>
      exact model_from_history_full_step_in_base_closure h_wf _ _ h_step
    | @tail z w h_prev h_step ih =>
      exact Relation.TransGen.trans ih
        (model_from_history_full_step_in_base_closure h_wf _ _ h_step)

lemma timestamp_lt_event_neq {t : Event → Nat} {e1 e2 : Event} :
    t e1 < t e2 →
    e1 ≠ e2 :=
  by
    intro h_lt h_eq
    subst h_eq
    simp at h_lt

lemma model_from_history_base_closure_acyclic {H : History} :
    (⊢ H) →
    ∀e1 e2,
      (model_base_rel (model_from_history H)+) e1 e2 →
      e1 ≠ e2 :=
  by
    intro h_wf e1 e2 h_clos
    rcases history_wf_has_timestamp h_wf with ⟨t, _, h_twf, _⟩
    have h_lt : t e1 < t e2 :=
      model_from_history_base_closure_lt_timestamp (H := H) (t := t) h_wf h_twf e1 e2 h_clos
    exact timestamp_lt_event_neq h_lt

lemma model_from_history_wf_acyclic_po_r_co_hb {H : History} :
    (⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let hb := derived_hb_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ∀e1 e2, ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 → e1 ≠ e2 :=
  by
    intro h_wf m r hb co' e1 e2 h_clos
    have h_base : (model_base_rel (model_from_history H)+) e1 e2 := by
      have h_clos' : (model_full_rel (model_from_history H)+) e1 e2 := by
        simpa [model_full_rel, model_base_rel, model_co_any] using h_clos
      exact model_from_history_full_closure_in_base_closure h_wf e1 e2 h_clos'
    exact model_from_history_base_closure_acyclic h_wf e1 e2 h_base

theorem model_from_history_wf {H : History} :
    (⊢ H) →
    Model.wf (model_from_history H) :=
  by
    intro h_wf
    simp [Model.wf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact model_from_history_wf_po h_wf
    · exact model_from_history_wf_co h_wf
    · exact model_from_history_single_causal_path h_wf
    · exact model_from_history_wf_acyclic_po_r_co_hb h_wf

theorem model_from_history_complete {H : History} :
    (⊢ H) →
    History.complete H →
    Model.complete (model_from_history H) :=
  by
    introv h_wf h_complete
    and_intros
    · introv h_run_in
      rcases h_run_in with ⟨bid', h_in⟩

      apply po_trans_pick_bid (bid := bid)
      have h_wf_b : wf_behavior_history bid' (H.behaviors bid') := by
        simp at h_wf
        grind
      have h_eq : bid' = bid := wf_history_run_mem_inv h_wf_b h_in
      subst h_eq
      have h_no_dup := wf_behavior_history_no_dup h_wf_b
      rw [pair_trans_iff h_no_dup]
      simp [History.complete] at h_complete
      have h_in' := h_complete.1 bid' h_in
      rw [pair_sublist_iff]
      cases h_beh : H.behaviors bid' with
      | nil =>
        simp [h_beh] at h_in
      | cons e es =>
        cases e with
        | Spawn b =>
          simp [wf_behavior_history, h_beh] at h_wf_b
        | Complete b =>
          simp [wf_behavior_history, h_beh] at h_wf_b
        | Run b =>
          simp [wf_behavior_history, h_beh] at h_wf_b
          rcases h_wf_b with ⟨h_bid_eq, spawns, tail, h_es_eq, h_spawns, h_tail⟩
          subst h_bid_eq
          have h_in_tail : Event.Complete bid' ∈ spawns ++ tail := by
            rw [h_beh] at h_in'
            rw [h_es_eq] at h_in'
            simp at h_in'
            exact List.mem_append.mpr h_in'
          rcases List.mem_iff_append.mp h_in_tail with ⟨mid, tail', h_split⟩
          exists [], mid, tail'
          grind
    · introv h_spawn_in
      rcases h_spawn_in with ⟨bid', h_in⟩
      exists bid
      simp [History.complete] at h_complete
      grind
