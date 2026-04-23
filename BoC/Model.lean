import BoC.Common
import BoC.History
import Init.Data.List

-- A model is a set of events along with a given program order and cown order
structure Execution where
  mk ::
  (events : Set Event)
  (po : Event → Event → Prop)
  (co : CId → Event → Event → Prop)

structure wf_po_relation (events : Set Event) (po : Event → Event → Prop) : Prop where
  -- po only relates known events
  eventsOnly : ∀e1 e2, po e1 e2 → e1 ∈ events ∧ e2 ∈ events
  -- po relates run/spawn, run/complete, spawn/spawn, and spawn/complete events
  shape :
    ∀e1 e2, po e1 e2 →
      match e1, e2 with
      | .Run _, .Spawn _
      | .Run _, .Complete _
      | .Spawn _, .Spawn _
      | .Spawn _, .Complete _ => True
      | _, _ => False
  -- po uniquely determines its predecessors and successors (po is a bijection)
  uniquePred : ∀e1 e2 e3, po e1 e3 → po e2 e3 → e1 = e2
  uniqueSucc : ∀e1 e2 e3, po e1 e2 → po e1 e3 → e2 = e3
  -- All events are preceeded by a Run event
  precededByRun : ∀e1 ∈ events, ∃bid, (po*) (.Run bid) e1
  -- A completion event must finish the same behaviour that was started
  runCompleteSameBid : ∀bid1 bid2, (po+) (.Run bid1) (.Complete bid2) → bid1 = bid2

structure wf_co_relation (events : Set Event) (co : CId → Event → Event → Prop) : Prop where
  -- co only relates known events
  eventsOnly : ∀e1 e2 c, co c e1 e2 → e1 ∈ events ∧ e2 ∈ events
  -- co relates complete/run events
  shape :
    ∀e1 e2 c, co c e1 e2 →
      match e1, e2 with
      | .Complete _, .Run _ => True
      | _, _ => False
  -- co uniquely determines its predecessors and successors (co is a bijection)
  uniquePred : ∀e1 e2 e3 c, co c e1 e3 → co c e2 e3 → e1 = e2
  uniqueSucc : ∀e1 e2 e3 c, co c e1 e2 → co c e1 e3 → e2 = e3

-- From an execution, we can derive a run relation which relates a spawn event of a
-- behaviour to the corresponding run event
def derived_run_relation (m : Execution) : Event → Event → Prop
| .Spawn bid, .Run bid' =>
    bid = bid' ∧
    .Spawn bid ∈ m.events ∧
    .Run bid ∈ m.events
| _, _ => False


def derived_co_any (m : Execution) : Event → Event → Prop :=
  fun e1 e2 => ∃c, m.co c e1 e2

-- From an execution we can derive a happens-before relation which relates a
-- completion event with all the run events that happened after it
-- hb = {(Ci,Rj) | Si (po ∪ r ∪ co)+ Sj ∧ cowns(i) ∩ cowns(j) ≠ ∅}
def derived_hb_relation (m : Execution) : Event → Event → Prop
| .Complete bid1, .Run bid2 =>
  let r := derived_run_relation m;
  let co' := derived_co_any m;
  let cowns bid := {c | (∃e, m.co c e (.Run bid)) ∨ (∃e, m.co c (.Complete bid) e)};
  ((m.po ∪ co' ∪ r)+) (.Spawn bid1) (.Spawn bid2) ∧
  (cowns bid1 ∩ cowns bid2 ≠ ∅) ∧
  .Complete bid1 ∈ m.events ∧
  .Run bid2 ∈ m.events
| _, _ => False

-- Constraints for a valid execution
structure Execution.valid (m : Execution) : Prop where
  poWf : wf_po_relation m.events m.po
  coWf : wf_co_relation m.events m.co
  -- co creates a single causal order path for any given cown
  singleCausalPath :
    ∀e1 e2 e3 e4 c,
      e1 ≠ e3 →
      e2 ≠ e4 →
      m.co c e1 e2 →
      m.co c e3 e4 →
      ((m.po ∪ m.co c)*) e2 e3 ∨ ((m.po ∪ m.co c)*) e4 e1
  -- The transitive closure of po_co_hb is acyclic
  acyclic :
    let r := derived_run_relation m
    let co' := derived_co_any m
    let hb := derived_hb_relation m
    ∀e1 e2, ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 → e1 ≠ e2

structure Execution.complete (m : Execution) : Prop where
  -- Every run event has a corresponding complete event
  runHasComplete :
    ∀bid, .Run bid ∈ m.events → (m.po+) (.Run bid) (.Complete bid)
  -- Every spawn event has a corresponding run event
  spawnHasRun :
    ∀bid, .Spawn bid ∈ m.events → .Run bid ∈ m.events

def model_from_history (H : History) : Execution :=
  ⟨
    -- Events
    {e | ∃bid, e ∈ H.behaviors bid},
    -- Program order
    fun e1 e2 =>
      ∃bid,
        [e1, e2] <:+: H.behaviors bid,
    -- Coherence order
    fun c e1 e2 =>
      ∃bid1 bid2,
        e1 = .Complete bid1 ∧
        e2 = .Run bid2 ∧
        [e1, e2] <:+: H.cowns c
  ⟩

---------------------------------

lemma po_pick_bid {H : History} {e1 e2} {bid} :
    ((fun e1 e2 ↦ [e1, e2] <:+: H.behaviors bid) * ) e1 e2 →
    ((fun e1 e2 ↦ ∃ bid, [e1, e2] <:+: H.behaviors bid) * ) e1 e2 :=
  by
    introv h_clos
    apply refl_trans_clos_exists_pick
    assumption

lemma po_trans_pick_bid {H : History} {e1 e2} {bid} :
    ((fun e1 e2 ↦ [e1, e2] <:+: H.behaviors bid)+) e1 e2 →
    ((fun e1 e2 ↦ ∃ bid, [e1, e2] <:+: H.behaviors bid)+) e1 e2 :=
  by
    introv h_clos
    apply trans_clos_exists_pick
    assumption

lemma po_exists_inv {H : History} {e1 e2} :
    (t ⊢ H) →
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

lemma model_from_history_po_events_only {t} {H : History} :
    (t ⊢ H) →
    ∀ e1 e2,
      (model_from_history H).po e1 e2 →
      e1 ∈ (model_from_history H).events ∧
      e2 ∈ (model_from_history H).events :=
  by
    intro h_wf e1 e2 h_po
    rcases h_po with ⟨bid, init, tail, h_eq⟩
    constructor
    case left =>
      exact ⟨bid, by rw [← h_eq]; simp⟩
    case right =>
      exact ⟨bid, by rw [← h_eq]; simp⟩

lemma model_from_history_po_shape {t} {H : History} :
    (t ⊢ H) →
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
    have h_behaviors := h_wf.behaviorWf
    rcases h_po with ⟨bid, h_infix⟩
    rcases (wf_behavior_history_pair_inv (h_behaviors bid) h_infix) <;>
      rcases e1 <;> rcases e2 <;> grind [is_run, is_spawn, is_complete]

lemma model_from_history_po_unique_pred {t} {H : History} :
    (t ⊢ H) →
    ∀ e1 e2 e3,
      (model_from_history H).po e1 e3 →
      (model_from_history H).po e2 e3 →
      e1 = e2 :=
  by
    intro h_wf e1 e2 e3 h13 h23
    have h_behaviors := h_wf.behaviorWf
    have h_unique := h_wf.uniqueSpawns
    have h_twf := h_wf.timestampWf
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
        exact wf_behavior_history_no_dup (h_behaviors bid1) (h_twf.behaviorAdj bid1)
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
        exact wf_behavior_history_no_dup (h_behaviors bid1) (h_twf.behaviorAdj bid1)
      exact no_dup_pair_eq_l h_no_dup h_infix1 h_infix2

lemma model_from_history_po_unique_succ {t} {H : History} :
    (t ⊢ H) →
    ∀ e1 e2 e3,
      (model_from_history H).po e1 e2 →
      (model_from_history H).po e1 e3 →
      e2 = e3 :=
  by
    intro h_wf e1 e2 e3 h12 h13
    have h_behaviors := h_wf.behaviorWf
    have h_unique := h_wf.uniqueSpawns
    have h_twf := h_wf.timestampWf
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
        exact wf_behavior_history_no_dup (h_behaviors bid1) (h_twf.behaviorAdj bid1)
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
        exact wf_behavior_history_no_dup (h_behaviors bid1) (h_twf.behaviorAdj bid1)
      exact no_dup_pair_eq_r h_no_dup h_infix1 h_infix2

lemma model_from_history_po_preceded_by_run {t} {H : History} :
    (t ⊢ H) →
    ∀ e,
      e ∈ (model_from_history H).events →
      ∃ bid, ((model_from_history H).po*) (.Run bid) e :=
  by
    intro h_wf e h_in
    have h_behaviors := h_wf.behaviorWf
    have h_twf := h_wf.timestampWf
    rcases h_in with ⟨bid, h_in_bid⟩
    exists bid
    apply po_pick_bid (bid := bid)
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup (h_behaviors bid) (h_twf.behaviorAdj bid)
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

lemma model_from_history_po_run_complete_same_bid {t} {H : History} :
    (t ⊢ H) →
    ∀ bid1 bid2,
      ((model_from_history H).po+) (.Run bid1) (.Complete bid2) →
      bid1 = bid2 :=
  by
    intro h_wf bid1 bid2 h_path
    have h_behaviors := h_wf.behaviorWf
    have h_twf := h_wf.timestampWf
    have ⟨bid, h_trans⟩ := po_exists_inv h_wf h_path
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup (h_behaviors bid) (h_twf.behaviorAdj bid)
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

lemma model_from_history_trans_po_run_to_complete {t} {H : History} {bid : BId} :
    (t ⊢ H) →
    .Complete bid ∈ H.behaviors bid →
    ((model_from_history H).po+) (.Run bid) (.Complete bid) :=
  by
    intro h_wf h_complete_mem
    have h_bwf : wf_behavior_history bid (H.behaviors bid) := h_wf.behaviorWf bid
    have h_twf := h_wf.timestampWf
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup h_bwf (h_twf.behaviorAdj bid)
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

lemma model_from_history_po_run_to_complete {t} {H : History} {bid : BId} :
    (t ⊢ H) →
    .Complete bid ∈ H.behaviors bid →
    ((model_from_history H).po*) (.Run bid) (.Complete bid) :=
  by
    intro h_wf h_complete_mem
    have h_bwf : wf_behavior_history bid (H.behaviors bid) := h_wf.behaviorWf bid
    have h_twf := h_wf.timestampWf
    have h_no_dup : List.Pairwise (· ≠ ·) (H.behaviors bid) := by
      exact wf_behavior_history_no_dup h_bwf (h_twf.behaviorAdj bid)
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

lemma model_from_history_wf_po {t} {H : History} :
    (t ⊢ H) →
    match model_from_history H with
    | ⟨events, po, _⟩ =>
      wf_po_relation events po :=
  by
    intro h_wf
    constructor
    case eventsOnly =>
      exact model_from_history_po_events_only h_wf
    case shape =>
      exact model_from_history_po_shape h_wf
    case uniquePred =>
      exact model_from_history_po_unique_pred h_wf
    case uniqueSucc =>
      exact model_from_history_po_unique_succ h_wf
    case precededByRun =>
      exact model_from_history_po_preceded_by_run h_wf
    case runCompleteSameBid =>
      exact model_from_history_po_run_complete_same_bid h_wf

lemma model_from_history_wf_co {t} {H : History} :
    (t ⊢ H) →
    match model_from_history H with
    | ⟨events, _, co⟩ =>
    wf_co_relation events co :=
  by
    intro h_wf
    have h_corr := h_wf.cownEvent
    have h_ts := h_wf.timestampWf
    constructor
    case eventsOnly =>
      introv h_co
      rcases h_co with ⟨bid1, bid2, h_eq1, h_eq2, h_infix⟩
      have h_in1 : e1 ∈ H.cowns c := (pair_infix_mem h_infix).1
      have h_in2 : e2 ∈ H.cowns c := (pair_infix_mem h_infix).2
      constructor
      case left =>
        exact h_corr c e1 h_in1
      case right =>
        exact h_corr c e2 h_in2
    case shape =>
      introv h_co
      rcases h_co with ⟨bid1, bid2, h_eq1, h_eq2, _⟩
      grind
    case uniquePred =>
      introv h_co1 h_co2
      rcases h_co1 with ⟨bid1, bid2, h_eq11, h_eq12, h_infix1⟩
      rcases h_co2 with ⟨bid3, bid4, h_eq21, h_eq22, h_infix2⟩
      have h_run : Event.Run bid4 = Event.Run bid2 := by
        calc
          Event.Run bid4 = e3 := by simpa using h_eq22.symm
          _ = Event.Run bid2 := by simpa using h_eq12
      have h_infix1' : [Event.Complete bid1, Event.Run bid2] <:+: H.cowns c := by
        simpa [h_eq11, h_eq12] using h_infix1
      have h_infix2' : [Event.Complete bid3, Event.Run bid2] <:+: H.cowns c := by
        simpa [h_eq21, h_eq22, h_run] using h_infix2
      have h_no_dup := pairwise_ne_of_pair_ordered (h_ts.cownAdj c)
      have h_eq := no_dup_pair_eq_l h_no_dup h_infix1' h_infix2'
      simpa [h_eq11, h_eq21] using h_eq
    case uniqueSucc =>
      introv h_co1 h_co2
      rcases h_co1 with ⟨bid1, bid2, h_eq11, h_eq12, h_infix1⟩
      rcases h_co2 with ⟨bid3, bid4, h_eq21, h_eq22, h_infix2⟩
      have h_complete : Event.Complete bid3 = Event.Complete bid1 := by
        calc
          Event.Complete bid3 = e1 := by simpa using h_eq21.symm
          _ = Event.Complete bid1 := by simpa using h_eq11
      have h_infix1' : [Event.Complete bid1, Event.Run bid2] <:+: H.cowns c := by
        simpa [h_eq11, h_eq12] using h_infix1
      have h_infix2' : [Event.Complete bid1, Event.Run bid4] <:+: H.cowns c := by
        simpa [h_eq21, h_eq22, h_complete] using h_infix2
      have h_no_dup := pairwise_ne_of_pair_ordered (h_ts.cownAdj c)
      have h_eq := no_dup_pair_eq_r h_no_dup h_infix1' h_infix2'
      simpa [h_eq12, h_eq22] using h_eq

lemma model_from_history_co_mem {H : History} {c : CId} {e1 e2 : Event} :
    (model_from_history H).co c e1 e2 →
    e1 ∈ H.cowns c ∧ e2 ∈ H.cowns c :=
  by
    intro h_co
    rcases h_co with ⟨_, _, _, _, h_infix⟩
    exact pair_infix_mem h_infix

lemma model_from_history_co_run_mem {H : History} {c : CId} {e : Event} {bid : BId} :
    (model_from_history H).co c e (.Run bid) →
    .Run bid ∈ H.cowns c :=
  by
    intro h_co
    exact (model_from_history_co_mem h_co).2

lemma model_from_history_co_complete_mem {H : History} {c : CId} {bid : BId} {e : Event} :
    (model_from_history H).co c (.Complete bid) e →
    .Complete bid ∈ H.cowns c :=
  by
    intro h_co
    exact (model_from_history_co_mem h_co).1

lemma model_from_history_complete_event_mem {t} {H : History} {bid : BId} :
    (t ⊢ H) →
    .Complete bid ∈ (model_from_history H).events →
    .Complete bid ∈ H.behaviors bid :=
  by
    intro h_wf h_in
    rcases h_in with ⟨owner, h_mem⟩
    have h_owner : owner = bid :=
      wf_history_complete_mem_inv (h_wf.behaviorWf owner) h_mem
    simpa [h_owner] using h_mem

lemma complete_behavior_event_on_cown {t} {H : History} {c : CId} {bid : BId} :
    (t ⊢ H) →
    .Run bid ∈ H.cowns c →
    .Complete bid ∈ H.behaviors bid →
    .Complete bid ∈ H.cowns c :=
  by
    intro h_wf h_run_mem h_complete_mem
    exact h_wf.completeOnCown c bid h_run_mem h_complete_mem

lemma wf_cown_history_connected {t} {H} {bid1 bid2} {mid tail} :
    let adjacent_c_r := fun ch e1 e2 =>
      ∃bid1, e1 = Event.Complete bid1 ∧
      ∃bid2, e2 = Event.Run bid2 ∧
      ∃init tail, ch = init ++ e1 :: e2 :: tail
    (t ⊢ H) →
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
        rcases h_wf_c with ⟨h_bid_eq, h_wf_c'⟩
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

          -- TODO: Try to clean up this part of the proof
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

lemma wf_cown_history_connected_middle {t} {H : History} {c : CId} {bid1 bid2 : BId}
                                       {init mid tail : List Event} :
    (t ⊢ H) →
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
      exact h_wf.cownEvent c e h_mem_cown
    have h_clos := wf_cown_history_connected h_wf h_corr' h_wf_c'
    apply rel_clos_weaken ?_ h_clos
    · intros x y h_clos
      cases h_clos with
      | inl h_po =>
        left
        assumption
      | inr h_adj =>
        right
        rcases h_adj with ⟨bid1', h_eq1, bid2', h_eq2, init2, tail2, h_adj_eq⟩
        subst h_eq1 h_eq2
        change (∃ bidA bidB,
          Event.Complete bid1' = Event.Complete bidA ∧
          Event.Run bid2' = Event.Run bidB ∧
          [Event.Complete bid1', Event.Run bid2'] <:+: H.cowns c)
        refine ⟨bid1', bid2', rfl, rfl, ?_⟩
        have h_pair_infix_ch : [Event.Complete bid1', Event.Run bid2'] <:+:
            (Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail) := by
          refine ⟨init2, tail2, ?_⟩
          simpa [List.append_assoc] using h_adj_eq.symm
        have h_ch_infix_hist :
            (Event.Run bid1 :: mid ++ Event.Complete bid2 :: tail) <:+:
            H.cowns c := by
          refine ⟨init, [], ?_⟩
          simp [h_eq, List.append_assoc]
        exact List.IsInfix.trans h_pair_infix_ch h_ch_infix_hist

lemma wf_cown_history_connected_cr {t} {H} {bid1 bid2} {mid tail} :
    let adjacent_c_r := fun ch e1 e2 =>
      ∃bid1, e1 = Event.Complete bid1 ∧
      ∃bid2, e2 = Event.Run bid2 ∧
      ∃init tail, ch = init ++ e1 :: e2 :: tail
    (t ⊢ H) →
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

lemma wf_cown_history_connected_middle_cr {t} {H : History} {c : CId} {bid1 bid2 : BId}
                                          {init mid tail : List Event} :
    (t ⊢ H) →
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
      exact h_wf.cownEvent c e h_mem_cown
    have h_clos := wf_cown_history_connected_cr h_wf h_corr' h_wf_c'
    apply rel_trans_clos_weaken ?_ h_clos
    · intros x y h_clos
      cases h_clos with
      | inl h_po =>
        left
        assumption
      | inr h_adj =>
        right
        rcases h_adj with ⟨bid1', h_eq1, bid2', h_eq2, init2, tail2, h_adj_eq⟩
        subst h_eq1 h_eq2
        change (∃ bidA bidB,
          Event.Complete bid1' = Event.Complete bidA ∧
          Event.Run bid2' = Event.Run bidB ∧
          [Event.Complete bid1', Event.Run bid2'] <:+: H.cowns c)
        refine ⟨bid1', bid2', rfl, rfl, ?_⟩
        have h_pair_infix_ch : [Event.Complete bid1', Event.Run bid2'] <:+:
            (Event.Run bid1 :: Event.Complete bid1 :: mid ++ Event.Run bid2 :: tail) := by
          refine ⟨init2, tail2, ?_⟩
          simpa [List.append_assoc] using h_adj_eq.symm
        have h_ch_infix_hist :
            (Event.Run bid1 :: Event.Complete bid1 :: mid ++ Event.Run bid2 :: tail) <:+:
            H.cowns c := by
          refine ⟨init', [], ?_⟩
          simp [h_eq, List.append_assoc]
        exact List.IsInfix.trans h_pair_infix_ch h_ch_infix_hist

lemma model_from_history_single_causal_path {t} {H : History} :
    (t ⊢ H) →
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
    rcases h_21 with ⟨h_e1, h_e2, h_infix1⟩
    rcases h_34 with ⟨h_e3, h_e4, h_infix2⟩
    rcases h_e1 with ⟨bid1, h_eq1⟩
    rcases h_e2 with ⟨bid2, h_eq2⟩
    rcases h_e3 with ⟨bid3, h_eq3⟩
    rcases h_e4 with ⟨bid4, h_eq4⟩
    subst h_eq1 h_eq2 h_eq3 h_eq4
    rcases h_infix1 with ⟨init, tail, h_mid⟩
    rcases h_infix2 with ⟨init', tail', h_mid'⟩
    have h_wf_c : wf_cown_history (H.cowns c) := h_wf.cownWf c
    cases (list_two_pairs_inv
      (a := Event.Complete bid1) (b := Event.Run bid2)
      (c := Event.Complete bid3) (d := Event.Run bid4)
      (l := H.cowns c) (init' := init) (tail' := tail)
      (init := init') (tail := tail')
      (by simpa using h_neq1)
      (by intro h; cases h)
      (by intro h; cases h)
      (by simpa [List.append_assoc] using h_mid.symm)
      (by simpa [List.append_assoc] using h_mid'.symm)) with
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

def model_base_rel (m : Execution) : Event → Event → Prop :=
  m.po ∪ derived_co_any m ∪ derived_run_relation m

def model_full_rel (m : Execution) : Event → Event → Prop :=
  model_base_rel m ∪ derived_hb_relation m

lemma model_from_history_po_lt_timestamp {H : History} {t : Event → Nat} :
    History.timestamp_wf H t →
    ∀e1 e2,
      (model_from_history H).po e1 e2 →
      t e1 < t e2 :=
  by
    intro h_twf e1 e2 h_po
    rcases h_po with ⟨bid, h_infix⟩
    exact h_twf.behaviorAdj bid e1 e2 h_infix

lemma model_from_history_co_lt_timestamp {H : History} {t : Event → Nat} :
    History.timestamp_wf H t →
    ∀c e1 e2,
      (model_from_history H).co c e1 e2 →
      t e1 < t e2 :=
  by
    intro h_twf c e1 e2 h_co
    rcases h_co with ⟨bid1, bid2, h_eq1, h_eq2, h_mid⟩
    exact h_twf.cownAdj c _ _ h_mid

lemma model_from_history_run_lt_timestamp {H : History} {t : Event → Nat} :
    (t ⊢ H) →
    History.timestamp_wf H t →
    ∀e1 e2,
      (derived_run_relation (model_from_history H)) e1 e2 →
      t e1 < t e2 :=
  by
    intro h_wf h_twf e1 e2 h_run
    -- TODO: This seems overly complicated
    have h_twf_spawn_run := h_twf.spawnRun
    rcases e1 with bid | _ | _ <;>
      rcases e2 with _ | bid' | _ <;>
      simp [derived_run_relation] at h_run
    rcases h_run with ⟨h_eq, h_spawn_in, h_run_in⟩
    subst h_eq
    rcases h_spawn_in with ⟨parent, h_spawn_mem⟩
    rcases h_run_in with ⟨owner, h_run_mem⟩
    have h_owner : owner = bid := by
      exact wf_history_run_mem_inv (h_wf.behaviorWf owner) h_run_mem
    have h_lt_owner : t (Event.Spawn owner) < t (Event.Run owner) :=
      h_twf_spawn_run parent owner
        (by simpa [h_owner] using h_spawn_mem)
        (by simpa [h_owner] using h_run_mem)
    simpa [h_owner] using h_lt_owner

lemma model_from_history_base_rel_lt_timestamp {H : History} {t : Event → Nat} :
    (t ⊢ H) →
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
    (t ⊢ H) →
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

-- TODO: Go through and see if it can be simplified
lemma wf_cown_history_run_has_complete_of_not_last_by_time
    {cs : List Event} {t : Event → Nat} {bid : BId} {e : Event} :
    wf_cown_history cs →
    Event.Run bid ∈ cs →
    e ∈ cs →
    Event.Run bid ≠ e →
    t (Event.Run bid) ≤ t e →
    (∀ e1 e2, [e1, e2] <:+: cs → t e1 < t e2) →
    Event.Complete bid ∈ cs := by
  intro h_wfc h_run_mem h_e_mem h_ne h_le h_time
  induction cs using wf_cown_history.induct generalizing bid e with
  | case1 =>
    simp at h_run_mem
  | case2 bid0 =>
    simp at h_run_mem
    subst h_run_mem
    simp at h_e_mem
    subst h_e_mem
    exact False.elim (h_ne rfl)
  | case3 bid1 bid2 cs' ih =>
    simp [wf_cown_history] at h_wfc
    rcases h_wfc with ⟨h_bid_eq, h_wfc'⟩
    subst h_bid_eq
    have h_run_cases : bid = bid1 ∨ Event.Run bid ∈ cs' := by
      simpa using h_run_mem
    cases h_run_cases with
    | inl h_bid =>
      subst h_bid
      simp
    | inr h_run_tail =>
      have h_time_tail :
          ∀e1 e2, [e1, e2] <:+: cs' → t e1 < t e2 := by
        intro e1 e2 h_infix
        apply h_time
        rcases h_infix with ⟨init, tail, h_eq⟩
        refine ⟨Event.Run bid1 :: Event.Complete bid1 :: init, tail, ?_⟩
        simp [h_eq]
      have h_e_cases : e = Event.Run bid1 ∨ e = Event.Complete bid1 ∨ e ∈ cs' := by
        simpa using h_e_mem
      cases h_e_cases with
      | inl h_e_run1 =>
        subst h_e_run1
        have h_mem' : Event.Run bid ∈ Event.Complete bid1 :: cs' := by
          simp [h_run_tail]
        have h_lt_run : t (Event.Run bid1) < t (Event.Run bid) :=
          head_lt_of_mem_ordered h_mem' h_time
        exact False.elim (Nat.not_le_of_gt h_lt_run h_le)
      | inr h_rest =>
        cases h_rest with
        | inl h_e_complete1 =>
          subst h_e_complete1
          have h_time_from_complete :
              ∀e1 e2, [e1, e2] <:+: (Event.Complete bid1 :: cs') → t e1 < t e2 := by
            intro e1 e2 h_infix
            apply h_time
            rcases h_infix with ⟨init, tail, h_eq⟩
            refine ⟨Event.Run bid1 :: init, tail, ?_⟩
            simp [h_eq]
          have h_lt_complete_run : t (Event.Complete bid1) < t (Event.Run bid) :=
            head_lt_of_mem_ordered h_run_tail h_time_from_complete
          exact False.elim (Nat.not_le_of_gt h_lt_complete_run h_le)
        | inr h_e_tail =>
          have h_complete_tail : Event.Complete bid ∈ cs' :=
            ih h_wfc' h_run_tail h_e_tail h_ne h_le h_time_tail
          simp [h_complete_tail]
  | case4 cs' h_empty h_single h_rc =>
    rcases cs' with _ | ⟨e0, cs''⟩ <;> simp at h_empty
    cases cs'' with
    | nil =>
      rcases e0 <;> simp [wf_cown_history] at h_wfc
      grind
    | cons e1 cs''' =>
      rcases e0 <;> rcases e1 <;> simp [wf_cown_history] at h_wfc
      grind

lemma model_from_history_hb_subset_base_closure {t} {H : History} :
    (t ⊢ H) →
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

    have h_twf : History.timestamp_wf H t := h_wf.timestampWf
    have h_twf_co := h_twf.cownAdj
    have h_twf_spawn_order := h_twf.happensBefore
    have h_lt : t (.Spawn bid1) < t (.Spawn bid2) :=
        model_from_history_base_closure_lt_timestamp h_wf h_twf (Event.Spawn bid1)
          (Event.Spawn bid2) h_po_co_r

    have ⟨c, h_mem1, h_mem2⟩ : ∃c, .Complete bid1 ∈ H.cowns c ∧ .Run bid2 ∈ H.cowns c := by
      let A : Set CId :=
        {c | (∃e, (model_from_history H).co c e (Event.Run bid1))
                  ∨ (∃e, (model_from_history H).co c (Event.Complete bid1) e)}
      let B : Set CId :=
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
          exact model_from_history_co_complete_mem h_co1
      · cases h_mem2 with
        | inl h_run2 =>
          rcases h_run2 with ⟨e, h_co2⟩
          exact model_from_history_co_run_mem h_co2
        | inr h_complete2 =>
          rcases h_complete2 with ⟨e, h_co2⟩
          have h_complete2_cown : .Complete bid2 ∈ H.cowns c := by
            exact model_from_history_co_complete_mem h_co2
          exact wf_cown_history_complete_has_run (h_wf.cownWf c) h_complete2_cown

    clear h_overlap

    -- This is where we use the timestamp ordering
    -- TODO: This seems complicated
    have h_lt' : t (.Complete bid1) < t (.Run bid2) := by
      by_cases h_cr : t (.Complete bid1) < t (.Run bid2)
      · exact h_cr
      · exfalso
        have h_mem1' : .Complete bid2 ∈ H.cowns c := by
          have h_wfc : wf_cown_history (H.cowns c) := h_wf.cownWf c
          have h_le : t (Event.Run bid2) ≤ t (Event.Complete bid1) := by
            exact Nat.le_of_not_gt (by grind)
          exact wf_cown_history_run_has_complete_of_not_last_by_time
            (cs := H.cowns c) (t := t) (bid := bid2) (e := Event.Complete bid1)
            h_wfc h_mem2 h_mem1 (by simp) h_le (h_twf_co c)
        have h_mem2' : .Run bid1 ∈ H.cowns c := by
          have ⟨init, tail, h_eq⟩ : ∃init tail, H.cowns c = init ++ .Complete bid1 :: tail := by
            exact List.mem_iff_append.mp h_mem1
          have h_wfc : wf_cown_history (init ++ .Complete bid1 :: tail) := by
            simpa [h_eq] using (h_wf.cownWf c)
          have ⟨init', h_eq'⟩ := wf_cown_history_complete_pred h_wfc
          rw [h_eq, h_eq']
          simp
        have h_lt' : t (.Complete bid2) < t (.Run bid1) := by
          have h_bid_ne : bid2 ≠ bid1 := by
            intro h_eq
            subst h_eq
            exact Nat.lt_irrefl _ h_lt
          have h_eq_pair1 :
              ∃ init1 tail1,
                H.cowns c = init1 ++ Event.Run bid1 :: Event.Complete bid1 :: tail1 := by
            have ⟨init, tail, h_eq⟩ :
                ∃ init tail, H.cowns c = init ++ Event.Complete bid1 :: tail := by
              exact List.mem_iff_append.mp h_mem1
            have h_wfc1 : wf_cown_history (init ++ Event.Complete bid1 :: tail) := by
              simpa [h_eq] using (h_wf.cownWf c)
            have ⟨init', h_init⟩ := wf_cown_history_complete_pred h_wfc1
            exists init', tail
            simp [h_eq, h_init, List.append_assoc]
          have h_eq_pair2 :
              ∃ init2 tail2,
                H.cowns c = init2 ++ Event.Run bid2 :: Event.Complete bid2 :: tail2 := by
            have ⟨init, tail, h_eq⟩ :
                ∃ init tail, H.cowns c = init ++ Event.Complete bid2 :: tail := by
              exact List.mem_iff_append.mp h_mem1'
            have h_wfc2 : wf_cown_history (init ++ Event.Complete bid2 :: tail) := by
              simpa [h_eq] using (h_wf.cownWf c)
            have ⟨init', h_init⟩ := wf_cown_history_complete_pred h_wfc2
            exists init', tail
            simp [h_eq, h_init, List.append_assoc]
          rcases h_eq_pair1 with ⟨init1, tail1, h_pair1⟩
          rcases h_eq_pair2 with ⟨init2, tail2, h_pair2⟩
          have h_order :=
            list_two_pairs_inv
              (a := Event.Run bid2) (b := Event.Complete bid2)
              (c := Event.Run bid1) (d := Event.Complete bid1)
              (l := H.cowns c) (init' := init2) (tail' := tail2)
              (init := init1) (tail := tail1)
              (by simp [h_bid_ne])
              (by simp)
              (by simp)
              h_pair2
              h_pair1
          cases h_order with
          | inl h_case =>
            rcases h_case with ⟨init, mid, tail, h_eq_case⟩
            have h_ord_full :
                ∀e1 e2, [e1, e2] <:+: (init ++ Event.Run bid2 :: Event.Complete bid2 ::
                  mid ++ Event.Run bid1 :: Event.Complete bid1 :: tail) → t e1 < t e2 := by
              simpa [h_eq_case] using (h_twf_co c)
            have h_ord_suffix :
                ∀e1 e2, [e1, e2] <:+: (Event.Complete bid2 ::
                  mid ++ Event.Run bid1 :: Event.Complete bid1 :: tail) → t e1 < t e2 := by
              intros e1 e2 h_infix
              apply h_ord_full
              rw [List.append_assoc]
              apply List.infix_append_of_infix_right
              apply List.infix_cons
              exact h_infix
            have h_mem_run1 : Event.Run bid1 ∈
                (mid ++ Event.Run bid1 :: Event.Complete bid1 :: tail) := by
              simp
            exact head_lt_of_mem_ordered
              (ord := t)
              (x := Event.Complete bid2)
              (xs := mid ++ Event.Run bid1 :: Event.Complete bid1 :: tail)
              (y := Event.Run bid1)
              h_mem_run1
              h_ord_suffix
          | inr h_case =>
            rcases h_case with ⟨init, mid, tail, h_eq_case⟩
            have h_ord_full :
                ∀e1 e2, [e1, e2] <:+: (init ++ Event.Run bid1 :: Event.Complete bid1 ::
                  mid ++ Event.Run bid2 :: Event.Complete bid2 :: tail) → t e1 < t e2 := by
              simpa [h_eq_case] using (h_twf_co c)
            have h_ord_suffix :
                ∀e1 e2, [e1, e2] <:+: (Event.Complete bid1 ::
                  mid ++ Event.Run bid2 :: Event.Complete bid2 :: tail) → t e1 < t e2 := by
              intros e1 e2 h_infix
              apply h_ord_full
              rw [List.append_assoc]
              apply List.infix_append_of_infix_right
              apply List.infix_cons
              exact h_infix
            have h_mem_run2 : Event.Run bid2 ∈
                (mid ++ Event.Run bid2 :: Event.Complete bid2 :: tail) := by
              simp
            have h_contra : t (Event.Complete bid1) < t (Event.Run bid2) :=
              head_lt_of_mem_ordered
                (ord := t)
                (x := Event.Complete bid1)
                (xs := mid ++ Event.Run bid2 :: Event.Complete bid2 :: tail)
                (y := Event.Run bid2)
                h_mem_run2
                h_ord_suffix
            exact False.elim (h_cr h_contra)
        have h_lt_rev : t (.Spawn bid2) < t (.Spawn bid1) :=
          h_twf_spawn_order c bid2 bid1 h_mem1' h_mem2' h_lt'
        exact Nat.lt_asymm h_lt h_lt_rev

    have h_wf_c : wf_cown_history (H.cowns c) := h_wf.cownWf c
    have ⟨init, mid, tail, h_c_eq⟩ : ∃init mid tail,
        H.cowns c = init ++ .Complete bid1 :: mid ++ .Run bid2 :: tail := by
      exact list_order_lt_inv h_lt' h_mem1 h_mem2 (h_twf_co c)
    have h_clos := wf_cown_history_connected_middle_cr h_wf h_wf_c h_c_eq
    exists c

lemma model_from_history_full_step_in_base_closure {H : History} :
    (t ⊢ H) →
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
    (t ⊢ H) →
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

lemma model_from_history_base_closure_acyclic {t} {H : History} :
    (t ⊢ H) →
    ∀e1 e2,
      (model_base_rel (model_from_history H)+) e1 e2 →
      e1 ≠ e2 :=
  by
    intro h_wf e1 e2 h_clos
    have h_twf : History.timestamp_wf H t := h_wf.timestampWf
    have h_lt : t e1 < t e2 :=
      model_from_history_base_closure_lt_timestamp (H := H) (t := t) h_wf h_twf e1 e2 h_clos
    exact timestamp_lt_event_neq h_lt

lemma model_from_history_wf_acyclic_po_r_co_hb {H : History} :
    (t ⊢ H) →
    let m := model_from_history H;
    let r := derived_run_relation m;
    let co' := derived_co_any m
    let hb := derived_hb_relation m
    ∀e1 e2, ((m.po ∪ co' ∪ r ∪ hb)+) e1 e2 → e1 ≠ e2 :=
  by
    intro h_wf m r hb co' e1 e2 h_clos
    have h_base : (model_base_rel (model_from_history H)+) e1 e2 := by
      have h_clos' : (model_full_rel (model_from_history H)+) e1 e2 := by
        simpa [model_full_rel, model_base_rel, derived_co_any] using h_clos
      exact model_from_history_full_closure_in_base_closure h_wf e1 e2 h_clos'
    exact model_from_history_base_closure_acyclic h_wf e1 e2 h_base

theorem model_from_history_wf {H : History} :
    (t ⊢ H) →
    Execution.valid (model_from_history H) :=
  by
    intro h_wf
    constructor
    case poWf =>
      exact model_from_history_wf_po h_wf
    case coWf =>
      exact model_from_history_wf_co h_wf
    case singleCausalPath =>
      exact model_from_history_single_causal_path h_wf
    case acyclic =>
      exact model_from_history_wf_acyclic_po_r_co_hb h_wf

theorem model_from_history_complete {H : History} :
    (t ⊢ H) →
    History.complete H →
    Execution.complete (model_from_history H) :=
  by
    introv h_wf h_complete
    constructor
    case runHasComplete =>
      introv h_run_in
      rcases h_run_in with ⟨bid', h_in⟩

      apply po_trans_pick_bid (bid := bid)
      have h_twf := h_wf.timestampWf
      have h_wf_b : wf_behavior_history bid' (H.behaviors bid') := h_wf.behaviorWf bid'
      have h_eq : bid' = bid := wf_history_run_mem_inv h_wf_b h_in
      subst h_eq
      have h_no_dup := wf_behavior_history_no_dup h_wf_b (h_twf.behaviorAdj bid')
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
    case spawnHasRun =>
      introv h_spawn_in
      rcases h_spawn_in with ⟨bid', h_in⟩
      exists bid
      simp [History.complete] at h_complete
      grind
