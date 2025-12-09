import Mathlib.Logic.Relation
import BoC.Common
import BoC.History

-- Program order relation
def po_relation (events : Set Event) : Event → Event → Prop
| .Run bid1, .Spawn bid2 =>
    .Run bid1 ∈ events ∧
    .Spawn bid2 ∈ events
| .Spawn bid1, .Spawn bid2 =>
    .Spawn bid1 ∈ events ∧
    .Spawn bid2 ∈ events
| .Spawn bid1, .Commit bid2 =>
    .Spawn bid1 ∈ events ∧
    .Commit bid2 ∈ events
| _, _ => False

-- Coherence order relation
def co_relation (events : Set Event) : Event → Event → Cown → Prop
| .Commit bid1, .Run bid2, _ =>
    .Commit bid1 ∈ events ∧
    .Run bid2 ∈ events
| _, _, _ => False

-- A model is a set of events along with a given program order, coherence order
-- and a disjointness relation on cown sets
structure Model where
  mk ::
  (events : Set Event)
  (po : Event -> Event -> Prop := po_relation events)
  (co : Event → Event → Cown → Prop := co_relation events)
  -- (disj : Set Cown → Set Cown → Prop)

-- From a model, we can derive a run relation which relates a spawn event of a
-- behaviour to the corresponding run event
def derived_run (m : Model) : Event → Event → Prop
| .Spawn bid, .Run bid' =>
    bid = bid' ∧
    .Spawn bid ∈ m.events ∧
    .Run bid ∈ m.events
| _, _ => False

-- From a model we can derive a happens-before relation which relates a commit
-- with all the runs that happened after it
def derived_hb (m : Model) : Event → Event → Prop
| .Commit bid1, .Run bid2 =>
  let r := derived_run m;
  let co' := fun e1 e2 => ∃c, m.co e1 e2 c;
  let cowns bid := {c | (∃e, m.co e (.Run bid) c) ∨ (∃e, m.co (.Commit bid) e c)};
  let conflict bid1 bid2 := (cowns bid1) ∩ (cowns bid2) ≠ ∅;
  ∃bid_origin bid_spawn,
    (r ∘ (m.po+)) (.Spawn bid_origin) (.Commit bid1) ∧
    ((m.po ∪ co' ∪ r)+) (.Spawn bid_origin) (.Spawn bid_spawn) ∧
    r (.Spawn bid_spawn) (.Run bid2) ∧
    conflict bid1 bid2 ∧
    bid1 ≠ bid2
| _, _ => False

-- TODO: Break out well-formed po and co definitions
-- TODO: Run events are minimal elements in po
-- Well-formedness conditions for a model
def Model.wf : Model → Prop
| m@⟨events, po, co⟩ =>
  let r := derived_run m;
  let hb := derived_hb m;
  let co_k c := fun e1 e2 => co e1 e2 c;
  let co' := fun e1 e2 => ∃c, co e1 e2 c;
  /-1: relations only mention known events -/
  (∀e1 e2, po e1 e2 → e1 ∈ events ∧ e2 ∈ events) ∧
  (∀e1 e2 c, co e1 e2 c → e1 ∈ events ∧ e2 ∈ events) ∧
  /-2: The transitive closure of po_co_r is acyclic -/
  (∀e1 e2, ((po ∪ co' ∪ r)+) e1 e2 → e1 ≠ e2) ∧
  /-3: A commit event must finish the same behaviour that was started -/
  (∀bid1 bid2, (po+) (.Run bid1) (.Commit bid2) → bid1 = bid2) ∧
  /-4: po uniquely determines its predecessors -/
  (∀e1 e2 e3, po e1 e3 → po e2 e3 → e1 = e2) ∧
  /-5: po uniquely determines its successors -/
  (∀e1 e2 e3, po e1 e2 → po e1 e3 → e2 = e3) ∧
  /-6: co uniquely determines its predecessors -/
  (∀e1 e2 e3 c, co e1 e3 c → co e2 e3 c → e1 = e2) ∧
  /-7: co uniquely determines its successors -/
  (∀e1 e2 e3 c, co e1 e2 c → co e1 e3 c → e2 = e3) ∧
  /-8: co creates a single causal order path for any given cown -/
  (∀e1 e2 e3 e4 c,
    e1 ≠ e3 →
    e2 ≠ e4 →
    co e1 e2 c →
    co e3 e4 c →
    ((po ∪ co_k c)+) e2 e3 ∨ ((po ∪ co_k c)+) e4 e1) ∧
  /-9: The transitive closure of po_co_hb is acyclic -/
  (∀e1 e2, ((po ∪ co' ∪ hb)+) e1 e2 → e1 ≠ e2)
  -- TODO: Program order events must start with a Run event
  -- TODO: Coherence order events must start with a Commit event

  -- TODO: Distinguish between partial and complete models


-- TODO: def model_from_history
-- TODO: ⊢ H → History.complete H → Model.wf (model_from_history H)
