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
    rcases h_wf with ⟨h_behaviors, h_unique, h_cowns, h_corr⟩
    simp
    introv h_neq1 h_neq2 h_21 h_34
    simp [model_from_history] at h_21 h_34
    rcases h_21 with ⟨bid1, h_eq1, bid2, h_eq2, init, tail, h_mid⟩
    rcases h_34 with ⟨bid3, h_eq3, bid4, h_eq4, init', tail', h_mid'⟩
    subst h_eq1 h_eq2 h_eq3 h_eq4
    have h_wf_c : wf_cown_history (H.cowns c) := h_cowns c
    cases (list_annoying_inv (by grind) (by grind) (by grind) h_mid h_mid') with
    | inl h_ex =>
      left
      rcases h_ex with ⟨init, ⟨mid, ⟨tail, h_eq⟩⟩⟩
      have h_eq' : (init ++ Event.Complete bid1 :: Event.Run bid2 :: mid) =
                   ((init ++ [Event.Complete bid1]) ++ Event.Run bid2 :: mid) := by
        simp
      rw [h_eq'] at h_eq
      apply wf_cown_history_connected_middle (by and_intros <;> grind) h_wf_c h_eq
    | inr h_ex =>
      right
      rcases h_ex with ⟨init, ⟨mid, ⟨tail, h_eq⟩⟩⟩
      have h_eq' : (init ++ Event.Complete bid3 :: Event.Run bid4 :: mid) =
                   ((init ++ [Event.Complete bid3]) ++ Event.Run bid4 :: mid) := by
        simp
      rw [h_eq'] at h_eq
      apply wf_cown_history_connected_middle (by and_intros <;> grind) h_wf_c h_eq

------------------------------------------

structure EventCoord where
  parent : BId
  index : Nat

@[simp]
def EventCoord.lt (ec1 ec2 : EventCoord) :=
  ec1.parent < ec2.parent ∨
  (ec1.parent = ec2.parent ∧ ec1.index < ec2.index)

@[simp]
instance EventCoordLT : LT EventCoord where
  lt := EventCoord.lt

lemma event_coord_lt_trans {c1 c2 c3 : EventCoord} :
  c1 < c2 →
  c2 < c3 →
  c1 < c3 :=
  by
    intro h12 h23
    simp [EventCoord.lt] at h12 h23
    cases h12 with
    | inl h12_parent_lt =>
      cases h23 with
      | inl h23_parent_lt =>
        left
        grind
      | inr h23_eq_and_lt =>
        left
        grind
    | inr h12_eq_and_lt =>
      cases h23 with
      | inl h23_parent_lt =>
        left
        grind
      | inr h23_eq_and_lt =>
        right
        grind

def has_coord (H : History) (e : Event) (c : EventCoord) : Prop :=
  (H.behaviors c.parent)[c.index]? = e

lemma mem_has_coord {H : History} {e : Event} {bid : BId} :
  e ∈ H.behaviors bid →
  ∃c, has_coord H e c /\ c.parent = bid :=
  by
    introv h_in
    simp [has_coord]
    rcases (List.mem_iff_getElem?).1 h_in with ⟨idx, h_get⟩
    exists ⟨bid, idx⟩

lemma event_coord_lt_different_events {H : History} {e1 e2 : Event} {c1 c2 : EventCoord} :
  (⊢ H) →
  has_coord H e1 c1 →
  has_coord H e2 c2 →
  c1 < c2 →
  e1 ≠ e2 :=
  by
    introv h_wf h_coord1 h_coord2 h_lt
    simp [has_coord] at h_coord1 h_coord2
    have h_in1 : e1 ∈ H.behaviors c1.parent := by grind
    have h_in2 : e2 ∈ H.behaviors c2.parent := by grind
    simp at h_lt
    cases h_lt with
    | inl h_parent_lt =>
      have h_neq : c1.parent ≠ c2.parent := by grind
      rcases e1 <;> rcases e2 <;> try simp
      · have := h_wf.2.1 _ _ _ h_neq h_in1
        grind
      · have h_wf1 := h_wf.1 c1.parent
        have h_wf2 := h_wf.1 c2.parent
        have := wf_history_run_mem_inv h_wf1 h_in1
        have := wf_history_run_mem_inv h_wf2 h_in2
        grind
      · have h_wf1 := h_wf.1 c1.parent
        have h_wf2 := h_wf.1 c2.parent
        have := wf_history_complete_mem_inv h_wf1 h_in1
        have := wf_history_complete_mem_inv h_wf2 h_in2
        grind
    | inr h_and =>
      rw [h_and.1] at h_coord1 h_in1
      have h_neq : c1.index ≠ c2.index := by grind
      clear h_and h_in1 h_in2
      have h_wf_b : wf_behavior_history c2.parent (H.behaviors c2.parent) := h_wf.1 c2.parent
      have h_no_dup := wf_behavior_history_no_dup h_wf_b
      generalize h_eq : H.behaviors c2.parent = es
      apply no_dup_lookup_disjoint <;> assumption

lemma has_coord_same_event {H : History} {e : Event} {c1 c2 : EventCoord} :
    (⊢ H) →
    has_coord H e c1 →
    has_coord H e c2 →
    c1 = c2 :=
  by
    introv h_wf h_coord1 h_coord2
    cases c1 with
    | mk p1 i1 =>
      cases c2 with
      | mk p2 i2 =>
        simp [has_coord] at h_coord1 h_coord2
        have h_in1 : e ∈ H.behaviors p1 :=
          (List.mem_iff_getElem?).2 ⟨i1, h_coord1⟩
        have h_in2 : e ∈ H.behaviors p2 :=
          (List.mem_iff_getElem?).2 ⟨i2, h_coord2⟩
        have h_parent : p1 = p2 := wf_history_event_unique h_wf h_in1 h_in2
        subst h_parent
        by_cases h_idx : i1 = i2
        · subst h_idx
          simp
        · have h_wf_b : wf_behavior_history p1 (H.behaviors p1) := h_wf.1 p1
          have h_no_dup := wf_behavior_history_no_dup h_wf_b
          have h_neq : e ≠ e :=
            no_dup_lookup_disjoint h_no_dup h_coord1 h_coord2 h_idx
          contradiction
/-
structure EventTuple where
  parent : BId
  event : Event


@[simp]
def event_tuple_partial_order (et1 et2 : EventTuple) :=
  match et1, et2 with
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 ≤ parent2 ∧ bid1 < bid2
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2 ∧ bid1 ≤ bid2
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 ≤ parent2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 ≤ parent2 ∧ bid1 < bid2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2 ∧ bid1 < bid2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 ≤ parent2 ∧ bid1 ≤ bid2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 < parent2 ∧ bid1 < bid2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2 ∧ bid1 < bid2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 < parent2 ∧ bid1 < bid2

@[simp]
def event_tuple_lexical_order (et1 et2 : EventTuple) :=
  match et1, et2 with
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 < parent2 ∨ parent1 = parent2 ∧ bid1 < bid2
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2
  | ⟨parent1, .Spawn bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 ≤ parent2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 ≤ parent2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2
  | ⟨parent1, .Run bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 ≤ parent2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Spawn bid2⟩ => parent1 < parent2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Run bid2⟩ => parent1 < parent2
  | ⟨parent1, .Complete bid1⟩, ⟨parent2, .Complete bid2⟩ => parent1 < parent2

lemma event_tuple_lexical_order_trans {et1 et2 et3 : EventTuple} :
  event_tuple_lexical_order et1 et2 →
  event_tuple_lexical_order et2 et3 →
  event_tuple_lexical_order et1 et3 :=
  by
    cases et1 with
    | mk parent1 e1 =>
      cases et2 with
      | mk parent2 e2 =>
        cases et3 with
        | mk parent3 e3 =>
          simp [event_tuple_lexical_order]
          intro h12 h23
          cases e1 <;> cases e2 <;> cases e3 <;> simp at h12 h23 ⊢ <;> grind

-- TODO: Maybe they don't have to be transitive. All we need is to ensure that
-- the events are different
lemma event_tuple_partial_order_trans {et1 et2 et3 : EventTuple} :
  event_tuple_partial_order et1 et2 →
  event_tuple_partial_order et2 et3 →
  event_tuple_partial_order et1 et3 :=
  by
    cases et1 with
    | mk parent1 e1 =>
      cases et2 with
      | mk parent2 e2 =>
        cases et3 with
        | mk parent3 e3 =>
          simp [event_tuple_partial_order]
          intro h12 h23
          cases e1 <;> cases e2 <;> cases e3 <;> simp at h12 h23 ⊢ <;> try grind
          · and_intros <;> try grind
            sorry
          · sorry
          · sorry
          · sorry

lemma event_tuple_partial_order_different_events {et1 et2 : EventTuple} :
  event_tuple_partial_order et1 et2 →
  et1.event ≠ et2.event :=
  by
    cases et1 with
    | mk parent1 e1 =>
      cases et2 with
      | mk parent2 e2 =>
        intro h_po
        cases e1 <;> cases e2 <;> simp [event_tuple_partial_order] at h_po <;> grind

def has_event_tuple (H : History) (e : Event) (et : EventTuple) : Prop :=
  match et with
  | ⟨parent, .Spawn bid⟩ => e = .Spawn bid ∧ e ∈ H.behaviors parent
  | ⟨parent, .Run bid⟩ => e = .Run bid ∧ e ∈ H.behaviors parent
  | ⟨parent, .Complete bid⟩ => e = .Complete bid ∧ e ∈ H.behaviors parent

lemma event_tuple_lexical_order_different_events {e1 e2} {H} {et1 et2} :
  (⊢ H) →
  has_event_tuple H e1 et1 →
  has_event_tuple H e2 et2 →
  event_tuple_lexical_order et1 et2 →
  et1.event ≠ et2.event :=
  by
    introv h_wf h_et1 h_et2 h_lo
    cases et1 with
    | mk parent1 e1 =>
      cases et2 with
      | mk parent2 e2 =>
        cases e1 <;> cases e2 <;> simp [event_tuple_lexical_order] at h_lo <;> try grind
        · rcases h_lo <;> try grind
          sorry
        · sorry
        · sorry

lemma has_event_tuple_inv {H : History} {e : Event} {et : EventTuple} :
  has_event_tuple H e et →
  et.event = e ∧ e ∈ H.behaviors et.parent :=
  by
    intro h_has
    cases et with
    | mk parent e' =>
      rcases e' <;> grind [has_event_tuple]
-/

lemma event_coord_lt_po {e1 e2 : Event} {H : History} :
    (⊢ H) →
    (model_from_history H).po e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf h_po
    simp [model_from_history] at h_po
    rcases h_po with ⟨bid, init, tail, h_eq⟩
    exists {parent := bid, index := init.length},
      {parent := bid, index := init.length + 1}
    and_intros
    · simp [has_coord]
      rw [← h_eq]
      simp
    · simp [has_coord]
      rw [← h_eq]
      simp
    · right
      constructor
      · rfl
      · exact Nat.lt_succ_self init.length

lemma wf_cown_history_middle_lt {bid1 bid2} {init tail} :
    wf_cown_history (init ++ Event.Complete bid1 :: Event.Run bid2 :: tail) →
    bid1 < bid2 :=
  by
    intro h_wf
    induction init using wf_cown_history.induct with
    | case1 =>
      simp [wf_cown_history] at h_wf
    | case2 bid =>
      simp [wf_cown_history] at h_wf
      grind
    | case3 bid bid' init' ih =>
      simp [wf_cown_history] at h_wf
      grind
    | case4 init' h_contra1 h_contra2 h_contra3 =>
      cases init' with
      | nil => contradiction
      | cons e init'' =>
        rcases e <;> simp [wf_cown_history] at h_wf
        cases init'' with
        | nil =>
          simp [wf_cown_history] at h_wf
          grind
        | cons e' init''' =>
          rcases e' <;> simp [wf_cown_history] at h_wf
          grind

lemma event_coord_lt_co {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    co' e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf h_m h_co' h_co
    subst h_m h_co'
    simp [model_from_history] at h_co
    rcases h_co with ⟨c, bid1, h_eq1, bid2, h_eq2, init, tail, h_eq⟩
    subst h_eq1 h_eq2
    have h_wf_c : wf_cown_history (H.cowns c) := by
      apply h_wf.2.2.1
    rw [h_eq] at h_wf_c
    have h_lt := wf_cown_history_middle_lt h_wf_c
    have h_in1 : .Complete bid1 ∈ H.cowns c := by grind
    have h_in2 : .Run bid2 ∈ H.cowns c := by grind
    have ⟨bid, h_in1⟩ := h_wf.2.2.2.1 c (.Complete bid1) h_in1
    have ⟨bid, h_in2⟩ := h_wf.2.2.2.1 c (.Run bid2) h_in2
    have ⟨c1, h_coord1, h_eq1⟩ := mem_has_coord h_in1
    have ⟨c2, h_coord2, h_eq2⟩ := mem_has_coord h_in2
    subst h_eq1 h_eq2
    have h_eq1 := wf_history_complete_mem_inv (h_wf.1 c1.parent) h_in1
    have h_eq2 := wf_history_run_mem_inv (h_wf.1 c2.parent) h_in2
    subst h_eq1 h_eq2
    exists c1, c2
    and_intros
    · simp [has_coord]
      simpa
    · simp [has_coord]
      simpa
    · left
      simpa

lemma event_coord_lt_r {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    r e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf h_m h_r_def h_r
    subst h_m h_r_def
    simp [model_from_history, derived_run_relation] at h_r
    rcases e1 <;> rcases e2 <;> simp at h_r
    rcases h_r with ⟨h_eq, h_in1, h_in2⟩
    subst h_eq
    rcases h_in1 with ⟨bid, h_in1⟩
    have h_lt := wf_history_spawn_mem_inv (h_wf.1 bid) h_in1
    rcases h_in2 with ⟨bid, h_in2⟩
    have h_eq := wf_history_run_mem_inv (h_wf.1 bid) h_in2
    subst h_eq
    have ⟨c1, h_coord1, h_eq1⟩ := mem_has_coord h_in1
    have ⟨c2, h_coord2, h_eq2⟩ := mem_has_coord h_in2
    subst h_eq1 h_eq2
    exists c1, c2
    and_intros
    · simpa
    · simpa
    · left
      simpa

lemma event_coord_lt_po_co_r {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    (m.po ∪ co' ∪ r) e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf _ _ _ h_union
    rcases h_union with ((h_po | h_co) | h_r)
    · exact event_coord_lt_po h_wf h_po
    · exact event_coord_lt_co h_wf h_co
    · exact event_coord_lt_r h_wf h_r

/-
def derived_hb_relation (m : Model) : Event → Event → Prop
| .Complete bid1, .Run bid2 =>
  let r := derived_run_relation m;
  let co' := fun e1 e2 => ∃c, m.co c e1 e2;
  let cowns bid := {c | (∃e, m.co c e (.Run bid)) ∨ (∃e, m.co c (.Complete bid) e)};
  ((m.po ∪ co' ∪ r)+) (.Spawn bid1) (.Spawn bid2) ∧
  (cowns bid1 ∩ cowns bid2 ≠ ∅)
| _, _ => False
-/
lemma event_coord_lt_po_co_r_clos {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ((m.po ∪ co' ∪ r)+) e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf _ _ _ h_clos
    induction h_clos with
    | single h_rel =>
      exact event_coord_lt_po_co_r h_wf h_rel
    | @tail e1' e2' h_clos h_step ih =>
      have ⟨c1, c2, h_coord1, h_coord2, h_lt⟩ := event_coord_lt_po_co_r h_wf h_step
      rcases ih with ⟨c2', c3, h_coord2', h_coord3, h_lt'⟩
      exists c2', c2
      have h_eq : c1 = c3 := has_coord_same_event h_wf h_coord1 h_coord3
      subst h_eq
      have := event_coord_lt_trans h_lt' h_lt
      and_intros <;> assumption

lemma spawn_run_lt_po_co_r_clos {H : History} {bid1 bid2 : BId} :
    (⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let co' := fun e1 e2 ↦ ∃ c, m.co c e1 e2;
    ((m.po ∪ co' ∪ r) + ) (Event.Spawn bid1) (Event.Run bid2) →
    bid1 ≤ bid2 :=
  by
    introv h_wf m_def r_def co_def h_clos
    generalize h_eq1 : (Event.Spawn bid1) = e1
    generalize h_eq2 : (Event.Run bid2) = e2
    rw [h_eq1, h_eq2] at h_clos
    induction h_clos generalizing bid2 with
    | single h_rel =>
      cases h_rel with
      | inl h_po_co =>
        cases h_po_co  with
        | inl h_po =>
          rw [← h_eq1, ← h_eq2] at h_po
          simp [m_def, model_from_history] at h_po
          sorry -- Contradiction
        | inr h_co =>
          rw [← h_eq1, ← h_eq2] at h_co
          simp [co_def, m_def, model_from_history] at h_co
      | inr h_r =>
        rw [← h_eq1, ← h_eq2] at h_r
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        simp [h_r.1]
    | @tail e1' e2' h_clos h_step ih =>
      rw [← h_eq1] at h_clos
      rw [← h_eq2] at h_step
      cases h_step with
      | inl h_po_co =>
        cases h_po_co  with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          sorry -- Contradiction
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          sorry -- Follows from wf_cown_history
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1' with ⟨bid1'⟩ <;> simp at h_r
        rcases h_r with ⟨h_eq, h_in1, h_in2⟩
        subst h_eq
        sorry -- Circular dependency on the next lemma

lemma spawn_lt_po_co_r_clos {H : History} {bid1 bid2 : BId} :
    (⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let co' := fun e1 e2 ↦ ∃ c, m.co c e1 e2;
    ((m.po ∪ co' ∪ r) + ) (Event.Spawn bid1) (Event.Spawn bid2) →
    bid1 < bid2 :=
  by
    introv h_wf m_def r_def co_def h_clos
    generalize h_eq1 : (Event.Spawn bid1) = e1
    generalize h_eq2 : (Event.Spawn bid2) = e2
    rw [h_eq1, h_eq2] at h_clos
    induction h_clos generalizing bid2 with
    | single h_rel =>
      cases h_rel with
      | inl h_po_co =>
        cases h_po_co  with
        | inl h_po =>
          rw [← h_eq1, ← h_eq2] at h_po
          simp [m_def, model_from_history] at h_po
          sorry -- Follows from wf_behavior_history
        | inr h_co =>
          rw [← h_eq1, ← h_eq2] at h_co
          simp [co_def, m_def, model_from_history] at h_co
      | inr h_r =>
        rw [← h_eq1, ← h_eq2] at h_r
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
    | @tail e1' e2' h_clos h_step ih =>
      rw [← h_eq1] at h_clos
      rw [← h_eq2] at h_step
      cases h_step with
      | inl h_po_co =>
        cases h_po_co  with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          cases e1' with
          | Spawn bid1' =>
            have h_lt := ih rfl
            sorry -- Follows from wf_behavior_history
          | Run bid1' =>
            have h_lt := spawn_run_lt_po_co_r_clos h_wf h_clos
            sorry -- Follows from wf_behavior_history (but the above lemma is currently cheated)
          | Complete bid1' =>
            sorry -- Contradiction
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r

lemma spawn_lt_po_co_r_clos' {H : History} {e1 e2 : Event} :
    (⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let co' := fun e1 e2 ↦ ∃ c, m.co c e1 e2;
    ((m.po ∪ co' ∪ r) + ) e1 e2 →
    match e1, e2 with
    | Event.Spawn bid1, Event.Spawn bid2 =>
      bid1 < bid2
    | Event.Spawn bid1, Event.Run bid2 =>
      bid1 ≤ bid2
    | Event.Spawn bid1, Event.Complete bid2 =>
      ∀bid, .Spawn bid1 ∈ H.behaviors bid → bid ≤ bid2
    | Event.Run bid1, Event.Spawn bid2 =>
      bid1 < bid2
    | Event.Run bid1, Event.Run bid2 =>
      bid1 < bid2
    | Event.Run bid1, Event.Complete bid2 =>
      bid1 ≤ bid2
    | Event.Complete bid1, Event.Spawn bid2 =>
      bid1 < bid2
    | Event.Complete bid1, Event.Run bid2 =>
      bid1 < bid2
    | Event.Complete bid1, Event.Complete bid2 =>
      bid1 < bid2
 :=
  by
    introv h_wf m_def r_def co_def h_clos
    induction h_clos with
    | @single e1' h_rel =>
      cases h_rel with
      | inl h_po_co =>
        cases h_po_co with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          sorry -- Cases on e1' and e2' should follow from wf_behavior_history
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          sorry -- Cases on e1' and e2' should follow from wf_cown_history
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1' with _ | bid1' | _ <;> try simp at h_r
        rcases e1 with _ | bid1 | _ <;> try simp at h_r
        simp [h_r.1]
    | @tail e1' e2' h_clos h_step ih =>
      cases h_step with
      | inl h_po_co =>
        cases h_po_co  with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          cases e1' with
          | Spawn bid1' =>
            sorry -- Follows from wf_behavior_history
          | Run bid1' =>
            sorry -- Follows from wf_behavior_history
          | Complete bid1' =>
            sorry
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          rcases h_co with ⟨c, bid1', h_eq1, bid2, h_eq2, init, tail, h_eq⟩
          subst h_eq1 h_eq2
          simp at *
          cases e1 with
          | Spawn bid1 =>
            have h_co_lt : bid1' < bid2 := by
              have h_wf_c : wf_cown_history (H.cowns c) := h_wf.2.2.1 c
              rw [h_eq] at h_wf_c
              exact wf_cown_history_middle_lt h_wf_c
            have h_src : ∀ bid, Event.Spawn bid1 ∈ H.behaviors bid → bid ≤ bid1' := ih
            sorry

          | Run bid1 =>
            sorry
          | Complete bid1 =>
            sorry
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1' <;> rcases e2' <;> simp at h_r ⊢
        grind

inductive bounded_causality (H : History) : Nat → Event → Event → Prop
| refl : ∀n e,
    (match e with
     | .Spawn bid => n < bid
     | _ => True) → -- TODO: Could add "n < bid" for all spawns after a Run,
    bounded_causality H n e e
| po_run : ∀n bid e1 e2,
    bounded_causality H n e1 e2 →
    (model_from_history H).po (.Run bid) e1 →
    bounded_causality H n (.Run bid) e2
| po_spawn : ∀n bid e1 e2,
    bounded_causality H bid e1 e2 →
    n < bid →
    (model_from_history H).po (.Spawn bid) e1 →
    bounded_causality H n (.Spawn bid) e2
| co : ∀n c e1 e2 e3,
    bounded_causality H n e2 e3 →
    (model_from_history H).co c e1 e2 →
    bounded_causality H n e1 e3
| r : ∀n bid e1 e2,
    bounded_causality H bid e1 e2 →
    n < bid →
    (derived_run_relation (model_from_history H)) (.Spawn bid) e1 →
    bounded_causality H n (.Spawn bid) e2

-- Right-extending variant of bounded_causality
-- This follows the same shape as Relation.TransGen.tail: accumulate steps on the right
inductive bounded_causality' (H : History) : Nat → Event → Event → Prop
| refl : ∀n e,
    (match e with
     | .Spawn bid => n = bid
     | .Run bid => bid ≤ n
     | .Complete bid => bid ≤ n
     ) →
    bounded_causality' H n e e
| snoc_po_spawn : ∀n bid e1 e2,
    bounded_causality' H n e1 e2 →
    (model_from_history H).po e2 (.Spawn bid) →
    n < bid →
    bounded_causality' H bid e1 (.Spawn bid)
| snoc_po_complete : ∀n e1 e2 bid,
    bounded_causality' H n e1 e2 →
    (model_from_history H).po e2 (.Complete bid) →
    bounded_causality' H n e1 (.Complete bid)
| snoc_co : ∀n c e1 e2 e3,
    bounded_causality' H n e1 e2 →
    (model_from_history H).co c e2 e3 →
    bounded_causality' H n e1 e3
| snoc_r : ∀n e1 e2,
    bounded_causality' H n e1 e2 →
    (derived_run_relation (model_from_history H)) e2 (.Run n) →
    bounded_causality' H n e1 (.Run n)

lemma bounded_causality_spawn_tail {H : History} {n : Nat} {e : Event} {bid : BId} :
    bounded_causality H n e (.Spawn bid) →
    n < bid :=
  by
    intro h_bc
    generalize h_eq : (Event.Spawn bid) = e2
    rw [h_eq] at h_bc
    induction h_bc generalizing bid <;> grind

lemma bounded_causality_spawn_tail' {H : History} {n : Nat} {e : Event} {bid : BId} :
    bounded_causality' H n e (.Spawn bid) →
    n = bid :=
  by
    intro h_bc
    generalize h_eq : (Event.Spawn bid) = e2
    rw [h_eq] at h_bc
    induction h_bc generalizing bid <;> try grind
    subst h_eq -- TODO: Clean this up
    simp [model_from_history] at *

lemma bounded_causality_spawn_head {H : History} {n : Nat} {e : Event} {bid : BId} :
    bounded_causality' H n (.Spawn bid) e →
    bid ≤ n :=
  by
    intro h_bc
    generalize h_eq : (Event.Spawn bid) = e1
    rw [h_eq] at h_bc
    induction h_bc with
    | refl _ _ h_match =>
      grind
    | snoc_po_spawn n' bid' e1 e2 h_bc h_lt h_po ih =>
      subst h_eq
      simp at ih
      grind
    | snoc_po_complete n' e1 e2 bid' h_bc h_po ih =>
      subst h_eq
      simp at ih
      assumption
    | snoc_co n' c e1 e2 e3 h_bc h_co ih =>
      simp [model_from_history] at h_co
      subst h_eq
      simp at ih
      assumption
    | snoc_r n' e1 e2 h_bc h_r ih =>
      simp [model_from_history, derived_run_relation] at h_r
      subst h_eq
      simp at ih
      assumption

lemma bounded_causality_spawn_lt' {H : History} {n : Nat} {bid1 bid2 : BId} :
    bounded_causality' H n (.Spawn bid1) (.Spawn bid2) →
    bid1 ≠ bid2 →
    bid1 < bid2 :=
  by
    intro h_bc n_neq
    generalize h_eq1 : (Event.Spawn bid1) = e1
    generalize h_eq2 : (Event.Spawn bid2) = e2
    rw [h_eq1, h_eq2] at h_bc
    induction h_bc generalizing bid2 with
    | refl =>
      subst h_eq1
      simp at h_eq2
      subst h_eq2
      contradiction
    | snoc_po_spawn n' bid e1' e2' h_bc h_po h_lt ih =>
      simp [model_from_history] at h_po
      subst h_eq1
      simp at h_eq2
      subst h_eq2
      have h_le := bounded_causality_spawn_head h_bc
      grind
    | snoc_po_complete n' e1' e2' bid h_bc h_po ih =>
      simp [model_from_history] at h_po
      subst h_eq1
      simp at h_eq2
    | snoc_co n' c e1' e2' e3' h_bc h_co ih =>
      simp [model_from_history] at h_co
      subst h_eq1 h_eq2
      simp at h_co
    | snoc_r n' e1' e2' h_bc h_r ih =>
      simp [model_from_history, derived_run_relation] at h_r
      subst h_eq1
      simp at h_eq2

/-
lemma bounded_causality_spawn_head {H : History} {n : Nat} {e : Event} {bid : BId} :
    bounded_causality H n (.Spawn bid) e →
    n < bid :=
  by
    intro h_bc
    cases h_bc with
    | refl
    | po_spawn
    | r => grind
    | co x1 x2 x3 x4 x5 x6 h_co =>
      simp [model_from_history] at h_co
-/

lemma bounded_causality_spawn_lt {H : History} {n : Nat} {bid1 bid2 : BId} :
    bounded_causality H n (.Spawn bid1) (.Spawn bid2) →
    bid1 ≠ bid2 →
    bid1 < bid2 :=
  by
    intro h_bc h_neq
    cases h_bc with
    | refl =>
      simp at h_neq
    | po_spawn n bid e1 e2 h_bc =>
      exact bounded_causality_spawn_tail h_bc
    | co n c e1 e2 e3 h_bc h_co =>
      simp [model_from_history] at h_co
    | r n bid e1 e2 h_bc =>
      exact bounded_causality_spawn_tail h_bc

lemma po_co_r_clos_bounded_causality' {H : History} {e1 e2 : Event} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ((m.po ∪ co' ∪ r)+) e1 e2 →
    exists n, bounded_causality' H n e1 e2 :=
  by
    introv h_wf m_def r_def co_def h_clos
    induction h_clos with
    | @single e2' h_rel =>
      cases h_rel with
      | inl h_po_co =>
        cases h_po_co with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          rcases h_po with ⟨bid, h_infix⟩
          cases e1 with
          | Spawn bid1 =>
            cases e2' with
            | Spawn bid2 =>
              sorry -- Should follow from wf_history
            | Run bid2 =>
              have h_shape := wf_behavior_history_pair_inv (h_wf.1 bid) h_infix
              simp at h_shape
            | Complete bid2 =>
              exists bid1
              apply bounded_causality'.snoc_po_complete (bid := bid2)
              · exact bounded_causality'.refl bid1 (.Spawn bid1) (by simp)
              · exact ⟨bid, h_infix⟩
          | Run bid1 =>
            cases e2' with
            | Spawn bid2 =>
              have h_mem1 : .Run bid1 ∈ H.behaviors bid := by
                rcases h_infix with ⟨init, tail, h_eq⟩
                rw [← h_eq]
                simp
              have h_mem2 : .Spawn bid2 ∈ H.behaviors bid := by
                rcases h_infix with ⟨init, tail, h_eq⟩
                rw [← h_eq]
                simp
              have h_bid : bid = bid1 := wf_history_run_mem_inv (h_wf.1 bid) h_mem1
              subst bid1
              have h_lt : bid < bid2 := wf_history_spawn_mem_inv (h_wf.1 bid) h_mem2
              exists bid2
              apply bounded_causality'.snoc_po_spawn (n := bid) (e2 := .Run bid)
              · exact bounded_causality'.refl bid (.Run bid) (by simp)
              · exact ⟨bid, h_infix⟩
              · exact h_lt
            | Run bid2 =>
              have h_shape := wf_behavior_history_pair_inv (h_wf.1 bid) h_infix
              simp at h_shape
            | Complete bid2 =>
              have h_mem1 : .Run bid1 ∈ H.behaviors bid := by
                rcases h_infix with ⟨init, tail, h_eq⟩
                rw [← h_eq]
                simp
              have h_bid : bid = bid1 := wf_history_run_mem_inv (h_wf.1 bid) h_mem1
              subst bid1
              exists bid
              apply bounded_causality'.snoc_po_complete (bid := bid2)
              · exact bounded_causality'.refl bid (.Run bid) (by simp)
              · exact ⟨bid, h_infix⟩
          | Complete bid1 =>
            cases e2' <;>
              have h_shape := wf_behavior_history_pair_inv (h_wf.1 bid) h_infix <;>
              simp at h_shape
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          rcases h_co with ⟨c, bid1, h_eq1, bid2, h_eq2, init, tail, h_eq⟩
          subst h_eq1 h_eq2
          exists bid1
          apply bounded_causality'.snoc_co (c := c) (e2 := .Complete bid1)
          · exact bounded_causality'.refl bid1 (.Complete bid1) (by simp)
          · simp [model_from_history]
            exact ⟨init, tail, h_eq⟩
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1 with bid1 | _ | _ <;> rcases e2' with _ | bid2 | _ <;> simp at h_r
        rcases h_r with ⟨h_eq, h_in1, h_in2⟩
        subst h_eq
        exists bid1
        apply bounded_causality'.snoc_r bid1 (.Spawn bid1) (.Spawn bid1)
        · constructor <;> simp
        · simp [model_from_history, derived_run_relation]
          grind
    | @tail e1' e2' h_clos h_step ih =>
      cases h_step with
      | inl h_po_co =>
        cases h_po_co with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          rcases h_po with ⟨bid, h_infix⟩
          cases e2' with
          | Spawn bid2 =>
            cases e1' with
            | Spawn bid1 =>
              sorry -- Should hold
            | Run bid1 =>
              sorry
            | Complete bid1 =>
              have h_shape := wf_behavior_history_pair_inv (h_wf.1 bid) h_infix
              simp at h_shape
          | Run bid2 =>
            have h_shape := wf_behavior_history_pair_inv (h_wf.1 bid) h_infix
            simp at h_shape
          | Complete bid2 =>
            rcases ih with ⟨n, h_bc⟩
            exists n
            apply bounded_causality'.snoc_po_complete (bid := bid2)
            · exact h_bc
            · exact ⟨bid, h_infix⟩
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          rcases h_co with ⟨c, bid1, h_eq1, bid2, h_eq2, init, tail, h_eq⟩
          subst h_eq1 h_eq2
          rcases ih with ⟨n, h_bc⟩
          exists n
          apply bounded_causality'.snoc_co (c := c) (e2 := .Complete bid1)
          · exact h_bc
          · simp [model_from_history]
            exact ⟨init, tail, h_eq⟩
      | inr h_r =>
        -- TODO: Can probably be cleaned up
        cases e1' with
        | Spawn bid1 =>
          cases e2' with
          | Spawn bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
          | Run bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
            rcases h_r with ⟨h_eq, h_in1, h_in2⟩
            rcases ih with ⟨n, h_bc⟩
            have h_n : n = bid1 := bounded_causality_spawn_tail' h_bc
            have h_rn : (derived_run_relation (model_from_history H)) (.Spawn bid1) (.Run n) := by
              simp [derived_run_relation, model_from_history]
              refine ⟨h_n.symm, h_in1, ?_⟩
              simpa [h_n] using h_in2
            have h_bc_run : bounded_causality' H n e1 (.Run n) :=
              bounded_causality'.snoc_r n e1 (.Spawn bid1) h_bc h_rn
            have h_n2 : n = bid2 := Eq.trans h_n h_eq
            exists n
            simpa [h_n2] using h_bc_run
          | Complete bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        | Run bid1 =>
          cases e2' with
          | Spawn bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
          | Run bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
          | Complete bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        | Complete bid1 =>
          cases e2' with
          | Spawn bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
          | Run bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
          | Complete bid2 =>
            simp [r_def, m_def, model_from_history, derived_run_relation] at h_r

-- TODO: Assume that there is an external bound
lemma po_co_r_clos_bounded_causality {H : History} {e1 e2 : Event} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ((m.po ∪ co' ∪ r)+) e1 e2 →
    exists n, bounded_causality H n e1 e2 :=
  by
    introv h_wf m_def r_def co_def h_clos
    induction h_clos with
    | @single e2' h_rel =>
      cases h_rel with
      | inl h_po_co =>
        cases h_po_co with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          sorry -- Should hold
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          rcases h_co with ⟨c, bid1, h_eq1, bid2, h_eq2, init, tail, h_eq⟩
          subst h_eq1 h_eq2
          sorry -- Should hold, but we could make this stronger
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1 with bid1 | _ | _ <;> rcases e2' with _ | bid2 | _ <;> simp at h_r
        rcases h_r with ⟨h_eq, h_in1, h_in2⟩
        subst h_eq
        sorry -- Should, hold
    | @tail e1' e2' h_clos h_step ih =>
      cases h_step with
      | inl h_po_co =>
        cases h_po_co with
        | inl h_po =>
          simp [m_def, model_from_history] at h_po
          sorry -- Proceed by cases on e1' and e2'
        | inr h_co =>
          simp [co_def, m_def, model_from_history] at h_co
          rcases h_co with ⟨c, bid1, h_eq1, bid2, h_eq2, init, tail, h_eq⟩
          subst h_eq1 h_eq2
          sorry -- Hmm, we're sort of going the "wrong way", looking left-to-right in bounded_causality, but right-to-left in the closure
      | inr h_r =>
        simp [r_def, m_def, model_from_history, derived_run_relation] at h_r
        rcases e1' with bid1 | _ | _ <;> rcases e2' with _ | bid2 | _ <;> simp at h_r ⊢
        rcases h_r with ⟨h_eq, h_in1, h_in2⟩
        subst h_eq
        sorry

lemma event_coord_lt_hb {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let hb := derived_hb_relation m
    hb e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf h_m h_hb_def h_hb
    subst h_m h_hb_def
    simp [model_from_history] at h_hb
    rcases e1 <;> rcases e2 <;> simp [derived_hb_relation] at h_hb
    next bid1 bid2 =>
    rcases h_hb with ⟨h_po_co_r, h_disj, ⟨bid1', h_in1⟩, ⟨bid2', h_in2⟩⟩
    have h_wf1 := h_wf.1 bid1'
    have h_wf2 := h_wf.1 bid2'
    have h_eq1 := wf_history_complete_mem_inv h_wf1 h_in1
    have h_eq2 := wf_history_run_mem_inv h_wf2 h_in2
    subst h_eq1 h_eq2
    have h_po_co_r': (let m := model_from_history H
      let r := derived_run_relation m
      let co' := fun e1 e2 => ∃c, m.co c e1 e2
      ((m.po ∪ co' ∪ r)+) (.Spawn bid1') (.Spawn bid2')) := by
      simpa [model_from_history]
    have ⟨n, h_bound⟩ := po_co_r_clos_bounded_causality' h_wf h_po_co_r'
    --have h_lt_bid : bid1' < bid2' := spawn_lt_po_co_r_clos h_wf h_po_co_r' -- TODO: This is currently cheated
    have ⟨c1, c2, h_coord1, h_coord2, h_lt⟩ := event_coord_lt_po_co_r_clos h_wf h_po_co_r'
    have ⟨c1', h_coord1', h_eq1⟩ := mem_has_coord h_in1
    have ⟨c2', h_coord2', h_eq2⟩ := mem_has_coord h_in2
    have h_neq := event_coord_lt_different_events h_wf h_coord1 h_coord2 h_lt
    have h_neq' : bid1' ≠ bid2' := by grind
    have h_lt' : bid1' < bid2' := bounded_causality_spawn_lt' h_bound h_neq'
    subst h_eq1 h_eq2
    exists c1', c2'
    and_intros
    · simpa
    · simpa
    · left
      assumption
    -- · cases h_lt with
    --   | inl h_lt =>
    --     left
    --     simpa
    --   | inr h_eq =>
    --     left -- This could be done manually
    --     simpa

/-
lemma event_tuple_partial_order_po {e1 e2 : Event} {et1 et2 : EventTuple} {H : History} :
    (⊢ H) →
    (model_from_history H).po e1 e2 →
    ∃et1 et2,
      has_event_tuple H e1 et1 ∧
      has_event_tuple H e2 et2 ∧
      event_tuple_partial_order et1 et2 :=
  by
    introv h_wf h_po
    simp [model_from_history] at h_po
    rcases h_po with ⟨bid, init, tail, h_eq⟩
    have h_wf_b := h_wf.1 bid
    rw [←h_eq] at h_wf_b
    simp [wf_behavior_history] at h_wf_b
    have h_in1 : e1 ∈ H.behaviors bid := by grind
    have h_in2 : e2 ∈ H.behaviors bid := by grind
    exists {parent := bid, event := e1}, {parent := bid, event := e2}
    and_intros
    · rcases e1 <;> simpa [has_event_tuple]
    · rcases e2 <;> simpa [has_event_tuple]
    · cases init with
      | nil =>
        rcases e1 <;> simp at h_wf_b
        rcases h_wf_b with ⟨h_bid_eq, spawns, tail', h_eq, h_spawns, h_tail⟩
        subst h_bid_eq
        cases spawns with
        | nil =>
          cases tail' with
          | nil => simp at h_eq
          | cons e tail'' =>
            simp at h_eq
            rcases h_eq with ⟨h_eq1, h_eq2⟩
            subst h_eq1 h_eq2
            rcases e2 <;> rcases tail <;> simp [wf_behavior_history_tail] at h_tail
            subst h_tail
            simp
        | cons e spawns' =>
          simp at h_eq
          rcases h_eq with ⟨h_eq1, h_eq2⟩
          subst h_eq1 h_eq2
          rcases e2 <;> simp [wf_behavior_history_spawns] at h_spawns
          rcases h_spawns with ⟨h_lt, _⟩
          simpa
      | cons e init' =>
        rcases e <;> simp at h_wf_b
        rcases h_wf_b with ⟨h_bid_eq, spawns, tail', h_eq', h_spawns, h_tail⟩
        subst h_bid_eq
        cases tail' with
        | nil =>
          simp at h_eq'
          -- TODO: wf_behavior_history_spawns_append
          sorry
        | cons e tail'' =>
          rcases e <;> rcases tail'' <;> simp [wf_behavior_history_tail] at h_tail
          subst h_tail
          cases list_snoc_cases (l := tail) with
          | inl h_eq'' =>
            subst h_eq''
            simp at h_eq'
            have h_eq'' : init' ++ [e1, e2] = (init' ++ [e1] ++ [e2]) := by
              simp
            rw [h_eq''] at h_eq'
            have ⟨h_eq_spawns, h_eq_e2⟩ := list_snoc_eq_inv h_eq'
            subst h_eq_spawns h_eq_e2
            have h_e1 : is_spawn e1 := by
              apply wf_history_spawns_mem_inv h_spawns
              simp
            rcases e1 <;> simp at h_e1
            simp
          | inr h_snoc =>
            rcases h_snoc with ⟨tail', x, h_eq''⟩
            subst h_eq''
            have h_eq'' : init' ++ e1 :: e2 :: (tail' ++ [x]) =
                          (init' ++ e1 :: e2 :: tail') ++ [x] := by simp
            rw [h_eq''] at h_eq'
            have ⟨h_eq_spawns, _⟩ := list_snoc_eq_inv h_eq'
            subst h_eq_spawns
            -- TODO: wf_behavior_history_spawns_append
            sorry


lemma event_tuple_partial_order_po_r_co_hb {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let hb := derived_hb_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 →
    ∃et1 et2,
      has_event_tuple H e1 et1 ∧
      has_event_tuple H e2 et2 ∧
      event_tuple_partial_order et1 et2 :=
  by
    sorry
-/

lemma event_coord_lt_po_co_r_hb {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let hb := derived_hb_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    (m.po ∪ co' ∪ r ∪ hb) e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf _ _ _ _ h_union
    rcases h_union with (((h_po | h_co) | h_r) | h_hb)
    · exact event_coord_lt_po h_wf h_po
    · exact event_coord_lt_co h_wf h_co
    · exact event_coord_lt_r h_wf h_r
    · exact event_coord_lt_hb h_wf h_hb

lemma event_coord_lt_po_co_r_hb_clos {e1 e2 : Event} {H : History} :
    (⊢ H) →
    let m := model_from_history H
    let r := derived_run_relation m
    let hb := derived_hb_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 →
    ∃c1 c2,
      has_coord H e1 c1 ∧
      has_coord H e2 c2 ∧
      c1 < c2 :=
  by
    introv h_wf _ _ _ _ h_clos
    induction h_clos with
    | single h_rel =>
      exact event_coord_lt_po_co_r_hb h_wf h_rel
    | @tail e1' e2' h_clos h_step ih =>
      have ⟨c1, c2, h_coord1, h_coord2, h_lt⟩ := event_coord_lt_po_co_r_hb h_wf h_step
      rcases ih with ⟨c2', c3, h_coord2', h_coord3, h_lt'⟩
      exists c2', c2
      have h_eq : c1 = c3 := has_coord_same_event h_wf h_coord1 h_coord3
      subst h_eq
      have := event_coord_lt_trans h_lt' h_lt
      and_intros <;> assumption

lemma model_from_history_wf_acyclic_po_r_co_hb {H : History} :
    (⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let hb := derived_hb_relation m
    let co' := fun e1 e2 => ∃c, m.co c e1 e2
    ∀e1 e2, ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 → e1 ≠ e2 :=
  by
    introv h_wf
    simp
    introv h_clos
    have ⟨c1, c2, h_c1, h_c2, h_lt⟩ := event_coord_lt_po_co_r_hb_clos h_wf h_clos
    have h_neq := event_coord_lt_different_events h_wf h_c1 h_c2 h_lt
    exact h_neq

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
