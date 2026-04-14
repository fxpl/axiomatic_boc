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

def HistoryMatchesCfg (H : History) (t : Event → Nat) : Cfg → Prop
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
    Event.fresh fresh e) ∧
  -- The timestamps of spawns increase in the pending queue
  (List.Pairwise (fun e1 e2 => t e1 < t e2) (pending.map (fun b => Event.Spawn b.bid))) ∧
  -- Everything that has run with a cown spawned before anything pending with that cown
  (∀bid1 b2 c,
    .Run bid1 ∈ H.cowns c →
    b2 ∈ pending →
    c ∈ b2.cowns →
    t (Event.Spawn bid1) < t (Event.Spawn b2.bid))

---------------------------

lemma history_wf_timestamp_wf
    {H : History} {t : Event → Nat} :
    (t ⊢ H) →
    History.timestamp_wf H t :=
  by
    grind [History.wf]

lemma history_wf_has_top
    {H : History} {t : Event → Nat} :
    (t ⊢ H) →
    ∃top, ∀e ∈ History.events H, t e < top :=
  by
    intro h_wf
    exact h_wf.2.2.2.2.2.2

lemma history_matches_cfg_fresh_behavior_history
    {H : History} {t : Event → Nat} {cfg bid e} :
    HistoryMatchesCfg H t cfg →
    e ∈ H.behaviors bid →
    Event.fresh cfg.fresh e :=
  by
    intro h_matches h_in
    exact h_matches.2.2.2.2.2.2.1 bid e h_in

lemma history_matches_cfg_fresh_cown_history
    {H : History} {t : Event → Nat} {cfg c e} :
    HistoryMatchesCfg H t cfg →
    e ∈ H.cowns c →
    Event.fresh cfg.fresh e :=
  by
    intro h_matches h_in
    exact h_matches.2.2.2.2.2.2.2.1 c e h_in

lemma history_matches_cfg_pending_order {H t cfg bid1 b2 c} :
    HistoryMatchesCfg H t cfg →
    .Run bid1 ∈ H.cowns c →
    b2 ∈ cfg.pending →
    c ∈ b2.cowns →
    t (Event.Spawn bid1) < t (Event.Spawn b2.bid) :=
  by
    intro h_matches h_mem1 h_mem2 h_mem3
    exact h_matches.2.2.2.2.2.2.2.2.2 bid1 b2 c h_mem1 h_mem2 h_mem3

@[simp]
lemma history_wf_hb_order {H : History} {t : Event → Nat} {bid1 bid2 c} :
    (t ⊢ H) →
    .Complete bid1 ∈ H.cowns c →
    .Run bid2 ∈ H.cowns c →
    t (.Complete bid1) < t (.Run bid2) →
    t (.Spawn bid1) < t (.Spawn bid2) :=
  by
    intro h_wf h_mem1 h_mem2 h_lt
    have h_wft := history_wf_timestamp_wf h_wf
    grind [History.timestamp_wf]

lemma wf_history_preservation_spawn {t H s top fresh bid bs1 bs2 cs pending} :
  (t ⊢ H) →
  (∀e, e ∈ H.events → t e < top) →
  HistoryMatchesCfg H t
    { fresh,
      running := bs1 ++ {bid, cowns := cs, stmt := s} :: bs2,
      pending } →
  let t' := fun e => if e = Event.Spawn fresh then top else t e;
  (t' ⊢ H[bid+=Event.Spawn fresh]) :=
  by
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · refine ⟨?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · intro c bid1 bid2 h_mem1 h_mem2 h_lt
        have h_wft := history_wf_timestamp_wf h_wf
        simp [t'] at h_lt ⊢
        have h_neq1 : bid1 ≠ fresh := by
          intros contra
          subst contra
          simp at h_mem1
          have h_fresh := history_matches_cfg_fresh_cown_history h_matches h_mem1
          simp [Event.fresh] at h_fresh
        have h_neq2 : bid2 ≠ fresh := by
          intros contra
          subst contra
          simp at h_mem2
          have h_fresh := history_matches_cfg_fresh_cown_history h_matches h_mem2
          simp [Event.fresh] at h_fresh
        split <;> try contradiction
        exact h_wft.2.2.2 c bid1 bid2 h_mem1 h_mem2 h_lt
    · sorry

lemma history_matches_preservation_spawn
    {t H s top fresh bid bs1 bs2 cs cs' s' s'' pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := s } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Spawn fresh then top else t e;
    HistoryMatchesCfg (H[bid += Event.Spawn fresh]) t'
      { fresh := fresh + 1,
        running := bs1 ++ {bid, cowns := cs, stmt := s'} :: bs2,
        pending := pending ++ [{bid := fresh, cowns := cs', stmt := s''}] } :=
  by
    sorry

lemma wf_history_preservation_complete
    {t H top bid1 bs1 bs2 bid cs pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Complete bid then top else t e;
    (t' ⊢ H[bid += Event.Complete bid][cs += Event.Complete bid]) :=
  by
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · refine ⟨?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · intro c bid1 bid2 h_mem1 h_mem2 h_lt
        have h_wft := history_wf_timestamp_wf h_wf
        simp [t'] at h_lt ⊢
        split at h_lt
        · have h_mem2' : .Run bid2 ∈ H.cowns c := by
            simp at h_mem2
            split at h_mem2 <;> grind
          have ⟨bid2', h_mem2''⟩ := h_wf.2.2.2.1 c (.Run bid2) h_mem2'
          have h_wfb : wf_behavior_history bid2' (H.behaviors bid2') := h_wf.1 bid2'
          have h_eq2 : bid2' = bid2 := by
            exact wf_history_run_mem_inv h_wfb h_mem2''
          subst h_eq2
          have h_mem2''' : .Run bid2' ∈ H.events := by
            simp [History.events]
            exists bid2'
          have h_lt' := h_top (.Run bid2') h_mem2'''
          grind
        · have h_mem1' : .Complete bid1 ∈ H.cowns c := by
            simp at h_mem1
            split at h_mem1 <;> grind
          have h_mem2' : .Run bid2 ∈ H.cowns c := by
            simp at h_mem2
            split at h_mem2 <;> grind
          exact h_wft.2.2.2 c bid1 bid2 h_mem1' h_mem2' h_lt
    · sorry

lemma history_matches_preservation_complete
    {t H top bid1 bs1 bs2 bid cs pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Complete bid then top else t e;
    HistoryMatchesCfg (H[bid += Event.Complete bid][cs += Event.Complete bid]) t'
      { fresh := bid1,
        running := bs1 ++ bs2,
        pending } :=
  by
    sorry

lemma wf_history_preservation_run
  {t H top bid1 bs1 bs2 running b} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running,
        pending := bs1 ++ b :: bs2 } →
    let t' := fun e => if e = Event.Run b.bid then top else t e;
    (t' ⊢ H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]) :=
  by
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · refine ⟨?_, ?_, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · intro c bid1 bid2 h_mem1 h_mem2 h_lt
        have h_wft := history_wf_timestamp_wf h_wf
        simp [t'] at h_lt ⊢
        split at h_lt
        · next h_eq =>
          subst h_eq
          have h_wfc : wf_cown_history (H.cowns c) := h_wf.2.2.1 c
          have h_mem1' : .Complete bid1 ∈ H.cowns c := by
            simp at h_mem1
            split at h_mem1 <;> grind
          have h_mem1'' : .Run bid1 ∈ H.cowns c := by
            exact wf_cown_history_complete_has_run h_wfc h_mem1'
          simp at h_mem2
          split at h_mem2
          · next h_cmem =>
            have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
            exact history_matches_cfg_pending_order h_matches h_mem1'' h_pending h_cmem
          · have ⟨bid', h_mem2'⟩ := h_wf.2.2.2.1 c (.Run b.bid) h_mem2
            have h_wfb : wf_behavior_history bid' (H.behaviors bid') := h_wf.1 bid'
            have h_eq2 : bid' = b.bid := by
              exact wf_history_run_mem_inv h_wfb h_mem2'
            subst h_eq2
            have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
            have h_nmem := h_matches.2.1 b h_pending
            contradiction
        · have h_mem1' : .Complete bid1 ∈ H.cowns c := by
            simp at h_mem1
            split at h_mem1 <;> grind
          have h_mem2' : .Run bid2 ∈ H.cowns c := by
            simp at h_mem2
            split at h_mem2 <;> grind
          exact h_wft.2.2.2 c bid1 bid2 h_mem1' h_mem2' h_lt
    · sorry

lemma history_matches_preservation_run
  {t H top bid1 bs1 bs2 running b} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running,
        pending := bs1 ++ b :: bs2 } →
    let t' := fun e => if e = Event.Run b.bid then top else t e;
    HistoryMatchesCfg (H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]) t'
      { fresh := bid1,
        running := b :: running,
        pending := bs1 ++ bs2 } :=
  by
    sorry

theorem wf_preservation {cfg cfg' H H'} {t : Event → Nat} :
    ((cfg, H) ⇒ (cfg', H')) →
    HistoryMatchesCfg H t cfg →
    (t ⊢ H) →
    ∃t', (t' ⊢ H') ∧ HistoryMatchesCfg H' t' cfg' :=
  by
    intro h_step h_matches h_wf
    have ⟨top, h_top⟩ := history_wf_has_top h_wf
    cases h_step with
    | @Spawn fresh bid bs1 bs2 cs cs' s s' s'' pending h_step =>
      let t' := fun e => if e = .Spawn fresh then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_spawn h_wf h_top h_matches
      · exact history_matches_preservation_spawn h_wf h_top h_matches

      -- For the -> direction, spawn ID is fresh so we can rely on previous timestamp
      -- For the <- direction, we know that bid1 has no run or completion event
    | @Complete bid1 bs1 bs2 bid cs pending =>
      let t' := fun e => if e = .Complete bid then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_complete h_wf h_top h_matches
      · exact history_matches_preservation_complete h_wf h_top h_matches
      -- For the <- direction, the new Complete event has the largest timestamp, so inequality should hold vacuously
    | @Run bid1 running bs1 bs2 b h_no_running h_no_pending =>
      let t' := fun e => if e = .Run b.bid then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_run h_wf h_top h_matches
      · exact history_matches_preservation_run h_wf h_top h_matches
      -- For the -> direction, the new Run event has the largest timestamp, so inequality should hold trivially
      -- For the <- direction, the new behaviour must have a spawn event happening later than any completed event

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

-----------------------------

theorem cfg_done_history_complete {cfg H} {t : Event → Nat} :
    cfg_done cfg →
    HistoryMatchesCfg H t cfg →
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
