import BoC.Common
import BoC.History

section UnderlyingLanguage

inductive Stmt where
| seq (cowns : List Cown) (body cont : Stmt)
| done

notation "when" cowns "{{" s "}}" ";" cont => Stmt.seq cowns s cont
notation "when" cowns "{{" "}}" ";" cont => Stmt.seq cowns Stmt.done cont
notation "when" cowns "{{" s "}}" => Stmt.seq cowns s Stmt.done
notation "when" cowns "{{" "}}" => Stmt.seq cowns Stmt.done Stmt.done

#check when [c1, c2] {{ when [c3] {{ }} }};
       when [] {{ }}

-- TODO: Add version that creates and manages scopes for cowns
-- cowns ⊆ σ
-- ---------------------------------------------------------------------
-- c' ⊢ (Cown c = when cowns { body } ; cont, σ) --> (cont[c ↦ c'], σ ∪ {c'}) | (body, cowns, σ)

set_option quotPrecheck false in
set_option hygiene false in
notation s "~>" s' "|" b => StepBehavior s (s', b)

inductive StepBehavior : Stmt → Stmt × (List Cown × Stmt) → Prop where
| When {cowns body cont} :
    ((Stmt.seq cowns body cont) ~> cont | (cowns, body))

end UnderlyingLanguage

section ConcurrentSemantics
structure Behavior where
  mk ::
  (bid : BId)
  (cowns : List Cown)
  (stmt : Stmt)

structure Cfg where
  mk ::
  (fresh : BId)
  (running : List Behavior)
  (pending : List Behavior)

def CfgFreshness : Cfg -> Prop
| ⟨fresh, running, pending⟩ =>
    (∀b ∈ running, b.bid < fresh) ∧
    (∀b ∈ pending, b.bid < fresh)

inductive StepCfg : Cfg × History → Cfg × History → Prop where
| Spawn {fresh bid : BId} {bs1 bs2 cowns cowns' s s' s'' pending H} :
    (s ~> s' | (cowns', s'')) →
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, s⟩ :: bs2, pending⟩, H)
            (⟨fresh + 1, bs1 ++ ⟨bid, cowns, s'⟩ :: bs2, pending ++ [⟨fresh, cowns', s''⟩]⟩,
              (H[bid += Event.Spawn fresh]))
| Complete {fresh bs1 bs2 bid} {cowns : List Cown} {pending H} :
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2, pending⟩, H)
    (⟨fresh, bs1 ++ bs2, pending⟩, (H[bid += Event.Complete bid][cowns += Event.Complete bid]))
| Run {fresh running bs1 bs2 b H} :
    (∀c, c ∈ b.cowns →  c ∉ running.flatMap Behavior.cowns) →
    (∀c, c ∈ b.cowns →  c ∉ bs1.flatMap Behavior.cowns) →
    StepCfg (⟨fresh, running, bs1 ++ b :: bs2⟩, H)
    (⟨fresh, b :: running, bs1 ++ bs2⟩, (H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]))

notation cfg " ⇒ " cfg' => StepCfg cfg cfg'

theorem step_cfg_freshness {cfg cfg' H H'} :
    ((cfg, H) ⇒ (cfg', H')) →
    CfgFreshness cfg →
    CfgFreshness cfg' :=
  by
    intro h_step h_fresh
    rcases cfg with ⟨fresh, running, pending⟩
    rcases cfg' with ⟨fresh', running', pending'⟩
    rcases h_fresh with ⟨h_running, h_pending⟩
    cases h_step with
    | @Spawn h_step bs1 bs2 bid cowns cowns' s s' s'' pending =>
      constructor <;> try grind
      intro b h_in
      simp at *
      rcases h_in with _ | h_eq | _ <;> try grind
      have h_lt : (Behavior.mk b.bid b.cowns s).bid < fresh :=
      by
        apply h_running
        subst h_eq
        simp
      grind
    | @Complete _ bs1 bs2 bid cowns =>
      constructor <;> grind
    | Run _ _ =>
      constructor <;> grind

def cfg_done : Cfg → Prop
| ⟨_, [], []⟩ => True
| _ => False

theorem step_cfg_progress {cfg H} :
    cfg_done cfg ∨ ∃cfg' H', (cfg, H) ⇒ (cfg', H') :=
  by
    cases cfg with
    | mk fresh running pending =>
      cases running with
      | nil =>
        cases pending with
        | nil =>
          left
          trivial
        | cons b pending' =>
          right
          exists ⟨fresh, b::[], [] ++ pending'⟩,
                  H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]
          rw [← List.nil_append ({ bid := b.bid, cowns := b.cowns, stmt := b.stmt } :: pending')]
          apply StepCfg.Run <;> simp
      | cons b running' =>
        right
        cases b with
        | mk bid cowns stmt =>
          cases stmt with
          | done =>
            exists ⟨fresh, running', pending⟩,
                   H[bid += Event.Complete bid][cowns += Event.Complete bid]
            rw [← List.nil_append ({ bid := bid, cowns := cowns, stmt := Stmt.done } :: running')]
            apply StepCfg.Complete
          | seq cowns' body cont =>
            exists ⟨fresh + 1, ([] ++ ⟨bid, cowns, cont⟩ :: running'),
                    (pending ++ [⟨fresh, cowns', body⟩])⟩, H[bid += Event.Spawn fresh]
            rw [← List.nil_append ({ bid := bid, cowns := cowns,
                                     stmt := Stmt.seq cowns' body cont } :: running')]
            have h_eq2 : (pending ++ [⟨fresh, cowns', body⟩]) =
                         (pending ++ [⟨fresh, cowns', body⟩]) := by rfl
            rw [h_eq2]
            clear h_eq2
            apply StepCfg.Spawn
            apply StepBehavior.When

def HistoryMatchesCfg (H : History) : Cfg → Prop
| ⟨fresh, running, pending⟩ =>
  -- All running behaviors have started but not completed
  (∀b, b ∈ running ↔ (Event.Run b.bid ∈ H.behaviors b.bid ∧
                      Event.Complete b.bid ∉ H.behaviors b.bid)) ∧
  -- All pending behaviors have not started
  (∀b ∈ pending, Event.Run b.bid ∉ H.behaviors b.bid) ∧
  -- Pending behaviors have been spawned
  (∀b ∈ pending, ∃bid', Event.Spawn b.bid ∈ H.behaviors bid') ∧
  -- Spawned behaviors are either pending, running, or completed
  (∀bid1 bid2,
    Event.Spawn bid2 ∈ H.behaviors bid1 →
    (∃b ∈ pending, b.bid = bid2) ∨
    (∃b ∈ running, b.bid = bid2) ∨
    (Event.Complete bid2 ∈ H.behaviors bid2)) ∧
  -- Completed behaviors are not in running or pending
  (∀bid,
    Event.Complete bid ∈ H.behaviors bid →
    (∀b ∈ running, b.bid ≠ bid) ∧
    (∀b ∈ pending, b.bid ≠ bid)) ∧
  -- Currently aquired cowns are held by running behaviors
  (∀b c,
    (b ∈ running ∧ c ∈ b.cowns) ↔
    (Event.Run b.bid ∈ H.cowns c ∧ Event.Complete b.bid ∉ H.cowns c)) ∧
  -- All events in the history are smaller than fresh
  (∀bid e,
    e ∈ H.behaviors bid →
    Event.fresh fresh e) ∧
  (∀c e,
    e ∈ H.cowns c →
    Event.fresh fresh e)

notation H " ⊢ " cfg => HistoryMatchesCfg H cfg

-- Timestamp-indexed variant used to keep the same timestamp witness explicit
-- across configuration/history preservation proofs.
def HistoryMatchesCfgT (H : History) (t : Event → Nat) : Cfg → Prop
| cfg =>
  HistoryMatchesCfg H cfg ∧ History.timestamp_wf H t

-- Pending queue is sorted by increasing spawn timestamp.
def PendingSpawnSortedByTime (t : Event → Nat) (pending : List Behavior) : Prop :=
  List.Pairwise (fun b1 b2 => t (.Spawn b1.bid) < t (.Spawn b2.bid)) pending

-- Stronger timestamp-indexed matching relation that also tracks queue order.
def HistoryMatchesCfgTSorted (H : History) (t : Event → Nat) : Cfg → Prop
| ⟨fresh, running, pending⟩ =>
  HistoryMatchesCfgT H t ⟨fresh, running, pending⟩ ∧ PendingSpawnSortedByTime t pending

lemma history_matches_sorted_to_matches
    {H : History} {t : Event → Nat} {cfg : Cfg} :
    HistoryMatchesCfgTSorted H t cfg → HistoryMatchesCfg H cfg := by
  intro h
  rcases h with ⟨h_mt, _⟩
  exact h_mt.1

lemma history_matches_sorted_to_timestamp
    {H : History} {t : Event → Nat} {cfg : Cfg} :
    HistoryMatchesCfgTSorted H t cfg → History.timestamp_wf H t := by
  intro h
  rcases h with ⟨h_mt, _⟩
  exact h_mt.2

lemma history_wf_has_top
    {H : History} {t : Event → Nat} :
    (t ⊢ H) → ∃ top, ∀e ∈ History.events H, t e ≤ top := by
  intro h_wf
  exact h_wf.2.2.2.2.2.2

/-
lemma step_cfg_preserves_history_wf_spawn
    {fresh bid1 : BId} {bs1 bs2 : List Behavior}
    {cowns cowns' : List Cown} {s s' s'' : Stmt}
    {pending : List Behavior} {H : History} {t : Event → Nat} :
    (s ~> s' | (cowns', s'')) →
    HistoryMatchesCfgTSorted H t ⟨fresh, bs1 ++ ⟨bid1, cowns, s⟩ :: bs2, pending⟩ →
    (t ⊢ H) →
    ∃ t', t' ⊢ (H[bid1 += Event.Spawn fresh]) := by
  intro _h_step h_matches h_wf
  have h_model : HistoryMatchesCfg H ⟨fresh, bs1 ++ ⟨bid1, cowns, s⟩ :: bs2, pending⟩ :=
    history_matches_sorted_to_matches h_matches
  rcases h_model with
    ⟨h_running, _h_pending_not_running, _h_pending_spawned, _h_spawned,
     _h_completed, _h_cowns, h_events_behaviors, h_events_cowns⟩
  have h_run_mem : Event.Run bid1 ∈ H.behaviors bid1 := by
    have h_in_running :
        (⟨bid1, cowns, s⟩ : Behavior) ∈ (bs1 ++ ⟨bid1, cowns, s⟩ :: bs2) := by
      simp
    have h_running_bid := (h_running ⟨bid1, cowns, s⟩).1 h_in_running
    exact h_running_bid.1
  have h_fresh : History.fresh fresh H := by
    constructor
    · intro bid e h_mem
      exact h_events_behaviors bid e h_mem
    · intro c e h_mem
      exact h_events_cowns c e h_mem
  exact wf_history_spawn_fresh (H := H) (t := t) (bid := bid1) (fresh := fresh)
    h_wf h_run_mem h_fresh

lemma step_cfg_preserves_history_wf_complete
    {fresh bid : BId} {bs1 bs2 : List Behavior}
    {cowns : List Cown} {pending : List Behavior}
    {H : History} {t : Event → Nat} :
    HistoryMatchesCfgTSorted H t ⟨fresh, bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2, pending⟩ →
    (t ⊢ H) →
    ∃ t', t' ⊢ (H[bid += Event.Complete bid][cowns += Event.Complete bid]) := by
  intro h_matches h_wf
  have h_model : HistoryMatchesCfg H ⟨fresh, bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2, pending⟩ :=
    history_matches_sorted_to_matches h_matches
  have h_twf : History.timestamp_wf H t :=
    history_matches_sorted_to_timestamp h_matches
  rcases h_model with
    ⟨h_running, _h_pending_not_running, _h_pending_spawned, _h_spawned,
     _h_completed, h_cowns_rel, _h_events_behaviors, _h_events_cowns⟩
  have h_in_running :
      (⟨bid, cowns, Stmt.done⟩ : Behavior) ∈ (bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2) := by
    simp
  have h_running_bid := (h_running ⟨bid, cowns, Stmt.done⟩).1 h_in_running
  have h_run_mem : Event.Run bid ∈ H.behaviors bid := h_running_bid.1
  have h_run_on_cown : ∀ c, c ∈ cowns → Event.Run bid ∈ H.cowns c := by
    intro c h_mem
    have h_rel := (h_cowns_rel ⟨bid, cowns, Stmt.done⟩ c).1
    have h_pair :
      (⟨bid, cowns, Stmt.done⟩ : Behavior) ∈ (bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2)
      ∧ c ∈ cowns :=
      ⟨h_in_running, h_mem⟩
    exact (h_rel h_pair).1
  have ⟨top, h_top⟩ := history_wf_has_top h_wf
  let t' : Event → Nat := fun e => if e = .Complete bid then top + 1 else t e
  have h_t'_run_lt_complete : t' (.Run bid) < t' (.Complete bid) := by
    have h_run_le : t (.Run bid) ≤ top := by
      apply h_top
      · exact ⟨bid, h_run_mem⟩
    have h_lt_succ : t (.Run bid) < top + 1 := Nat.lt_succ_of_le h_run_le
    simp [t', h_lt_succ]
  exact wf_history_complete_fresh h_wf h_run_mem h_running_bid.2 h_run_on_cown
-/

lemma wf_history_spawn_fresh {H : History} {t : Event → Nat} {bid fresh : BId} :
    (t ⊢ H) →
    Event.Run bid ∈ H.behaviors bid →
    History.fresh fresh H →
    ∃t', t' ⊢ (H[bid += Event.Spawn fresh]) :=
  by
    sorry

-- Completing a running behavior preserves History.wf.
-- The new Complete event needs a fresh timestamp: t' e = if e = Complete bid then top+1 else t e.
lemma wf_history_complete_fresh {H : History} {t : Event → Nat}
    {bid : BId} {cowns : List Cown} :
    (t ⊢ H) →
    Event.Run bid ∈ H.behaviors bid →
    Event.Complete bid ∉ H.behaviors bid →
    (∀c, c ∈ cowns → Event.Run bid ∈ H.cowns c) →
    ∃t', t' ⊢ (H[bid += Event.Complete bid][cowns += Event.Complete bid]) := by
  sorry

-- Running a pending behavior preserves History.wf.
-- The new Run event needs a fresh timestamp: t' e = if e = Run bid then top+1 else t e.
-- h_cowns_free: every cown in the list is unoccupied (every Run in its history has a Complete).
lemma wf_history_run_fresh {H : History} {t : Event → Nat}
    {bid : BId} {cowns : List Cown} :
    (t ⊢ H) →
    Event.Run bid ∉ H.behaviors bid →
    (∃ parent, Event.Spawn bid ∈ H.behaviors parent) →
    (∀ c, c ∈ cowns → ∀ bid', Event.Run bid' ∈ H.cowns c → Event.Complete bid' ∈ H.cowns c) →
    ∃t', t' ⊢ (H[bid += Event.Run bid][cowns += Event.Run bid]) := by
  sorry

lemma step_cfg_preserves_history_wf_run
    {fresh : BId} {running bs1 bs2 : List Behavior} {b : Behavior}
    {H : History} {t : Event → Nat} :
    (∀c, c ∈ b.cowns → c ∉ running.flatMap Behavior.cowns) →
    (∀c, c ∈ b.cowns → c ∉ bs1.flatMap Behavior.cowns) →
    HistoryMatchesCfgTSorted H t ⟨fresh, running, bs1 ++ b :: bs2⟩ →
    (t ⊢ H) →
    ∃ t', t' ⊢ (H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]) := by
  intro _h_no_running _h_no_pending h_matches h_wf
  have h_model : HistoryMatchesCfg H ⟨fresh, running, bs1 ++ b :: bs2⟩ :=
    history_matches_sorted_to_matches h_matches
  rcases h_model with
    ⟨_h_running_rel, h_pending_not_running, h_pending_spawned, _h_spawned,
     _h_completed, h_cowns_rel, _h_events_behaviors, _h_events_cowns⟩
  have h_b_in_pending : b ∈ bs1 ++ b :: bs2 := by simp
  have h_run_not_mem : Event.Run b.bid ∉ H.behaviors b.bid :=
    h_pending_not_running b h_b_in_pending
  have h_spawn_mem : ∃ parent, Event.Spawn b.bid ∈ H.behaviors parent :=
    h_pending_spawned b h_b_in_pending
  -- For each c ∈ b.cowns, every Run in H.cowns c already has a matching Complete
  -- (i.e., the cown is unoccupied). Proved by instantiating h_cowns_rel with a fresh
  -- behavior ⟨bid', [], Stmt.done⟩: since c ∈ [] is False, the backward direction of
  -- the iff forces a contradiction whenever Run bid' ∈ H.cowns c ∧ Complete bid' ∉ H.cowns c.
  have h_cowns_free :
      ∀ c, c ∈ b.cowns → ∀ bid', Event.Run bid' ∈ H.cowns c → Event.Complete bid' ∈ H.cowns c := by
    intro c _h_c_in bid' h_run_in
    by_cases (Event.Complete bid' ∈ H.cowns c)
    · assumption
    · have h_back :=
        (h_cowns_rel (⟨bid', [], Stmt.done⟩ : Behavior) c).2 ⟨h_run_in, (by assumption)⟩
      simp at h_back
  exact wf_history_run_fresh h_wf h_run_not_mem h_spawn_mem h_cowns_free

theorem step_cfg_preserves_history_wf {cfg cfg' H H'} {t : Event → Nat} :
    ((cfg, H) ⇒ (cfg', H')) →
    HistoryMatchesCfgTSorted H t cfg →
    (t ⊢ H) →
    ∃t', t' ⊢ H' :=
  by
    intro h_step h_matches h_wf
    have ⟨top, h_top⟩ := history_wf_has_top h_wf
    cases h_step with
    | @Spawn bid1 bid2 bs1 bs2 cs cs' s s' s'' pending h_step =>
      let t' := fun e => if e = .Spawn bid1 then top else t e
      exists t'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · -- TODO: Extract to a lemma
        refine ⟨?_, ?_, ?_, ?_⟩
        · sorry
        · sorry
        · sorry
        · intro c bid1' bid2' h_mem1 h_mem2 h_lt
          sorry
          -- For the -> direction, spawn ID is fresh so we can rely on previous timestamp
          -- For the <- direction, we know that bid1 has no run or completion event
      · exists (top + 1)
        simp [History.events]
        introv h_mem
        sorry
    | @Complete bid1 bs1 bs2 bid cs pending h_step =>
      let t' := fun e => if e = .Complete bid then top else t e
      exists t'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · -- TODO: Extract to a lemma
        refine ⟨?_, ?_, ?_, ?_⟩
        · sorry
        · sorry
        · sorry
        · introv h_mem1 h_mem2
          -- For the <- direction, the new Complete event has the largest timestamp, so inequality should hold vacuously
          sorry
      · exists (top + 1)
        simp [History.events]
        introv h_mem
        sorry
    | @Run bid1 bid2 bs1 bs2 b h_no_running h_no_pending =>
      let t' := fun e => if e = .Run b.bid then top else t e
      exists t'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · -- TODO: Extract to a lemma
        refine ⟨?_, ?_, ?_, ?_⟩
        · sorry
        · sorry
        · sorry
        · introv h_mem1 h_mem2
          -- For the -> direction, the new Run event has the largest timestamp, so inequality should hold trivially
          -- For the <- direction, the new behaviour must have a spawn event happening later than any completed event
          -- Two invariants on configurations:
          --   1) the pending queue is sorted by increasing spawn timestamp
          --   2) for a given cown c, the spawn event of a pending behaviour that
          --      requires c must happen later than the spawn event of any
          --      started behaviour that requires c
          sorry
      · exists (top + 1)
        simp [History.events]
        introv h_mem
        sorry

/-
    -- 1) Pick a post-step timestamp witness.
    have h_t_exists : ∃ t' : Event → Nat, True := by
      -- Missing piece: construct a concrete timestamp witness from the step kind.
      sorry
    rcases h_t_exists with ⟨t', _⟩
    -- 2) Prove each field of History.wf for H' at t' via dedicated lemmas.
    have h_field1 : ∀ bid, wf_behavior_history bid (H'.behaviors bid) := by
      -- Missing piece: behavior-history wf preservation across Spawn/Complete/Run.
      sorry
    have h_field2 : unique_spawns H'.behaviors := by
      -- Missing piece: spawn uniqueness preservation.
      sorry
    have h_field3 : ∀ c, wf_cown_history (H'.cowns c) := by
      -- Missing piece: cown-history wf preservation.
      sorry
    have h_field4 : ∀ c e, e ∈ H'.cowns c → ∃ bid, e ∈ H'.behaviors bid := by
      -- Missing piece: cown-event/behavior-event correspondence preservation.
      sorry
    have h_field5 :
        ∀ c bid, Event.Run bid ∈ H'.cowns c →
          Event.Complete bid ∈ H'.behaviors bid →
          Event.Complete bid ∈ H'.cowns c := by
      -- Missing piece: run->complete-on-cown implication preservation.
      sorry
    have h_field6 : History.timestamp_wf H' t' := by
      -- Missing piece: timestamp-wf preservation for chosen t'.
      sorry
    have h_field7 : ∃ top, ∀ e ∈ History.events H', t' e ≤ top := by
      -- Missing piece: global top bound preservation / reconstruction.
      sorry
    exact ⟨t', ⟨h_field1, h_field2, h_field3, h_field4, h_field5, h_field6, h_field7⟩⟩
-/

theorem step_cfg_preserves_matching_history {cfg cfg' H H'} {t : Event → Nat} :
    HistoryMatchesCfg H cfg →
    ((cfg, H) ⇒ (cfg', H')) →
    (t ⊢ H) →
    HistoryMatchesCfg H' cfg' :=
  by
    intro h_model h_step h_wf
    rcases cfg with ⟨fresh, running, pending⟩
    rcases cfg' with ⟨fresh', running', pending'⟩
    sorry

-----------------------------

theorem cfg_done_history_complete {cfg H} {t : Event → Nat} :
    cfg_done cfg →
    HistoryMatchesCfg H cfg →
    History.wf t H →
    History.complete H :=
  by
    intro h_done h_model h_wf
    rcases cfg with ⟨fresh, running, pending⟩
    rcases h_model with ⟨h_running, h_pending_not_running, h_pending_spawned, h_spawned,
                         h_completed, h_cowns, h_events_behaviors, h_events_cowns⟩
    simp [cfg_done] at h_done
    rcases running with _ | _ <;> try grind
    rcases pending with _ | _ <;> try grind
    simp at *
    and_intros
    · introv h_in
      have aoeu := h_running ⟨bid, [], Stmt.done⟩ h_in
      grind
    · introv h_in
      have h_complete := h_spawned _ _ h_in
      rcases h_wf with ⟨h_wf_bs, _, _, _, _, _, _⟩
      have h_wf_b := h_wf_bs bid2
      let b_hist := H.behaviors bid2
      have h_eq : b_hist = H.behaviors bid2 := by rfl
      rw [← h_eq] at h_complete
      rw [← h_eq] at h_wf_b
      rw [← h_eq]
      rcases (b_hist) with _ | ⟨e, es⟩ <;> try grind
      simp [wf_behavior_history] at h_wf_b
      rcases e <;> try grind

end ConcurrentSemantics
