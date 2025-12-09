import Mathlib.Logic.Relation
import BoC.Common
import BoC.History

-- A model is a set of events along with a given program order, coherence order
-- and a disjointness relation on cown sets
structure Model where
  mk ::
  (events : Set Event)
  (po : Event → Event → Prop)
  (co : Event → Event → Cown → Prop)
  -- (disj : Set Cown → Set Cown → Prop)

def wf_po_relation (events : Set Event) (po : Event → Event → Prop) : Prop :=
  -- po only relates known events
  (∀e1 e2, po e1 e2 → e1 ∈ events ∧ e2 ∈ events)
  ∧
  -- po relates run/spawn, spawn/spawn, and spawn/commit events
  (∀e1 e2, po e1 e2 → match e1, e2 with
                      | .Run _, .Spawn _
                      | .Spawn _, .Spawn _
                      | .Spawn _, .Complete _ => True
                      | _, _ => False)
  ∧
  -- po uniquely determines its predecessors and successors (po is a bijection?)
  (∀e1 e2 e3, po e1 e3 → po e2 e3 → e1 = e2) ∧
  (∀e1 e2 e3, po e1 e2 → po e1 e3 → e2 = e3)
  ∧
  -- All events are preceeded by a Run event
  (∀e1 e2, po e1 e2 → ∃bid, (po*) (.Run bid) e1)
  ∧
  -- A completion event must finish the same behaviour that was started
  (∀bid1 bid2, (po+) (.Run bid1) (.Complete bid2) → bid1 = bid2)

def wf_co_relation (events : Set Event) (co : Event → Event → Cown → Prop) : Prop :=
  -- co only relates known events
  (∀e1 e2 c, co e1 e2 c → e1 ∈ events ∧ e2 ∈ events)
  ∧
  -- co relates commit/run events
  (∀e1 e2 c, co e1 e2 c → match e1, e2 with
                          | .Complete _, .Run _ => True
                          | _, _ => False)
  ∧
  -- co uniquely determines its predecessors and successors (co is a bijection?)
  (∀e1 e2 e3 c, co e1 e3 c → co e2 e3 c → e1 = e2) ∧
  (∀e1 e2 e3 c, co e1 e2 c → co e1 e3 c → e2 = e3)

-- From a model, we can derive a run relation which relates a spawn event of a
-- behaviour to the corresponding run event
def derived_run_relation (m : Model) : Event → Event → Prop
| .Spawn bid, .Run bid' =>
    bid = bid' ∧
    .Spawn bid ∈ m.events ∧
    .Run bid ∈ m.events
| _, _ => False

-- From a model we can derive a happens-before relation which relates a commit
-- with all the runs that happened after it
def derived_hb_relation (m : Model) : Event → Event → Prop
| .Complete bid1, .Run bid2 =>
  let r := derived_run_relation m;
  let co' := fun e1 e2 => ∃c, m.co e1 e2 c;
  let cowns bid := {c | (∃e, m.co e (.Run bid) c) ∨ (∃e, m.co (.Complete bid) e c)};
  let conflict bid1 bid2 := (cowns bid1) ∩ (cowns bid2) ≠ ∅;
  ∃bid_origin bid_spawn,
    (r ∘ (m.po+)) (.Spawn bid_origin) (.Complete bid1) ∧
    ((m.po ∪ co' ∪ r)+) (.Spawn bid_origin) (.Spawn bid_spawn) ∧
    r (.Spawn bid_spawn) (.Run bid2) ∧
    conflict bid1 bid2 ∧
    bid1 ≠ bid2
| _, _ => False

-- Well-formedness conditions for a model
def Model.wf : Model → Prop
| m@⟨events, po, co⟩ =>
  -- Derived relations
  let r := derived_run_relation m;
  let hb := derived_hb_relation m;
  let co_k c := fun e1 e2 => co e1 e2 c;
  let co' := fun e1 e2 => ∃c, co e1 e2 c;
  wf_po_relation events po ∧
  wf_co_relation events co ∧
  -- The transitive closure of po ∪ co ∪ r is acyclic
  (∀e1 e2, ((po ∪ co' ∪ r)+) e1 e2 → e1 ≠ e2) ∧
  -- co creates a single causal order path for any given cown
  (∀e1 e2 e3 e4 c,
    e1 ≠ e3 →
    e2 ≠ e4 →
    co e1 e2 c →
    co e3 e4 c →
    ((po ∪ co_k c)+) e2 e3 ∨ ((po ∪ co_k c)+) e4 e1) ∧
  -- The transitive closure of po_co_hb is acyclic
  (∀e1 e2, ((po ∪ co' ∪ hb)+) e1 e2 → e1 ≠ e2)

def Model.complete : Model → Prop
| ⟨events, po, _⟩ =>
  -- Every run event has a corresponding complete event
  (∀bid, .Run bid ∈ events → (po+) (.Run bid) (.Complete bid))
  ∧
  -- Every spawn event has a corresponding run event
  (∀bid, .Spawn bid ∈ events → .Run bid ∈ events)

-- TODO: def model_from_history
-- TODO: ⊢ H → History.complete H → Model.wf (model_from_history H)
