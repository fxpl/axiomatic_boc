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

-- TODO: This might not be needed if we can derive CfgFreshness from HistoryMatchesCfg
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

structure HistoryMatchesCfg (H : History) (t : Event → Nat) (cfg : Cfg) : Prop where
  -- All running behaviors have started but not completed
  runningNotCompleted :
    ∀b, b ∈ cfg.running ↔ (Event.Run b.bid ∈ H.behaviors b.bid ∧
                           Event.Complete b.bid ∉ H.behaviors b.bid)
  -- All pending behaviors have not started
  pendingNotRunning :
    ∀b ∈ cfg.pending, Event.Run b.bid ∉ H.behaviors b.bid
  -- Pending behaviors have been spawned
  pendingSpawned :
    ∀b ∈ cfg.pending, ∃bid', Event.Spawn b.bid ∈ H.behaviors bid'
  -- Spawned behaviors are either pending, running, or completed
  spawnedDisposition :
    ∀bid1 bid2,
      Event.Spawn bid2 ∈ H.behaviors bid1 →
      (∃b ∈ cfg.pending, b.bid = bid2) ∨
      (∃b ∈ cfg.running, b.bid = bid2) ∨
      (Event.Complete bid2 ∈ H.behaviors bid2)
  -- Completed behaviors are not in running or pending
  completedNotActive :
    ∀bid,
      Event.Complete bid ∈ H.behaviors bid →
      (∀b ∈ cfg.running, b.bid ≠ bid) ∧
      (∀b ∈ cfg.pending, b.bid ≠ bid)
  -- Currently aquired cowns are held by running behaviors
  cownRunning :
    ∀b c,
      (b ∈ cfg.running ∧ c ∈ b.cowns) ↔
      (Event.Run b.bid ∈ H.cowns c ∧ Event.Complete b.bid ∉ H.cowns c)
  -- All events in the history are smaller than fresh
  freshBehaviorHistory :
    ∀bid e,
      e ∈ H.behaviors bid →
      Event.fresh cfg.fresh e
  freshCownHistory :
    ∀c e,
      e ∈ H.cowns c →
      Event.fresh cfg.fresh e
  -- The timestamps of spawns increase in the pending queue
  pendingTimestampOrder :
    List.Pairwise (fun e1 e2 => t e1 < t e2) (cfg.pending.map (fun b => Event.Spawn b.bid))
  -- Everything that has run with a cown spawned before anything pending with that cown
  pendingOrder :
    ∀bid1 b2 c,
      .Run bid1 ∈ H.cowns c →
      b2 ∈ cfg.pending →
      c ∈ b2.cowns →
      t (Event.Spawn bid1) < t (Event.Spawn b2.bid)

---------------------------

lemma history_wf_timestamp_wf
    {H : History} {t : Event → Nat} :
    (t ⊢ H) →
    History.timestamp_wf H t :=
  by
    intro h_wf
    exact h_wf.timestampWf

lemma history_wf_has_top
    {H : History} {t : Event → Nat} :
    (t ⊢ H) →
    ∃top, ∀e ∈ History.events H, t e < top :=
  by
    intro h_wf
    exact h_wf.hasTop

lemma history_matches_cfg_fresh_behavior_history
    {H : History} {t : Event → Nat} {cfg bid e} :
    HistoryMatchesCfg H t cfg →
    e ∈ H.behaviors bid →
    Event.fresh cfg.fresh e :=
  by
    intro h_matches h_in
    exact h_matches.freshBehaviorHistory bid e h_in

lemma history_matches_cfg_fresh_cown_history
    {H : History} {t : Event → Nat} {cfg c e} :
    HistoryMatchesCfg H t cfg →
    e ∈ H.cowns c →
    Event.fresh cfg.fresh e :=
  by
    intro h_matches h_in
    exact h_matches.freshCownHistory c e h_in

lemma history_matches_cfg_pending_order {H t cfg bid1 b2 c} :
    HistoryMatchesCfg H t cfg →
    .Run bid1 ∈ H.cowns c →
    b2 ∈ cfg.pending →
    c ∈ b2.cowns →
    t (Event.Spawn bid1) < t (Event.Spawn b2.bid) :=
  by
    intro h_matches h_mem1 h_mem2 h_mem3
    exact h_matches.pendingOrder bid1 b2 c h_mem1 h_mem2 h_mem3

lemma history_matches_cfg_freshness {H t cfg} :
    HistoryMatchesCfg H t cfg →
    CfgFreshness cfg :=
  by
    intro h_matches
    rcases cfg with ⟨fresh, running, pending⟩
    constructor
    · intro b h_mem
      have h_run_mem := (h_matches.runningNotCompleted b).1 h_mem |>.1
      have h_fresh := h_matches.freshBehaviorHistory b.bid (.Run b.bid) h_run_mem
      simpa [Event.fresh] using h_fresh
    · intro b h_mem
      have ⟨parent, h_spawn_mem⟩ := h_matches.pendingSpawned b h_mem
      have h_fresh := h_matches.freshBehaviorHistory parent (.Spawn b.bid) h_spawn_mem
      simpa [Event.fresh] using h_fresh

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

-- TODO: Move to History.lean
lemma wf_cown_history_mem_no_spawn {es e} :
    wf_cown_history es →
    e ∈ es →
    ¬is_spawn e :=
  by
    intro h_wf h_in
    induction es using wf_cown_history.induct with
    | case1 => trivial
    | case2 bid =>
      simp at h_in
      subst h_in
      simp
    | case3 bid1 bid2 es ih =>
      simp at h_in
      rcases h_in with h_eq | h_eq | h_mem
      · subst h_eq
        simp
      · subst h_eq
        simp
      · simp [wf_cown_history] at h_wf
        grind
    | case4 es h_nempty h_nsingle ih =>
      rcases es with _ | ⟨e', es'⟩ <;> try grind
      simp [wf_cown_history] at h_wf

lemma wf_history_preservation_spawn {t H s top fresh bid bs1 bs2 cs pending} :
  (t ⊢ H) →
  (∀e, e ∈ H.events → t e < top) →
  HistoryMatchesCfg H t
    { fresh,
      running := bs1 ++ {bid, cowns := cs, stmt := s} :: bs2,
      pending } →
  let t' := fun e => if e = Event.Spawn fresh then top else t e
  (t' ⊢ H[bid+=Event.Spawn fresh]) :=
  by
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro bid'
      simp
      split
      · next h_eq =>
        subst h_eq
        have ⟨h_mem, h_nmem⟩ :=
          (h_matches.runningNotCompleted { bid := bid', cowns := cs, stmt := s }).mp (by grind)
        simp at h_mem h_nmem
        have h_wfb := h_wf.behaviorWf bid'
        generalize h_eq : H.behaviors bid' = es
        rw [h_eq] at h_mem h_nmem h_wfb
        cases es with
        | nil => contradiction
        | cons e es' =>
          rcases e <;> simp [wf_behavior_history] at h_wfb
          have ⟨spawns, tail, h_eq, h_spawns, h_tail⟩ := h_wfb.2
          subst h_eq
          by_cases h_nil : tail = []
          · subst h_nil
            simp [wf_behavior_history]
            and_intros <;> try grind
            exists spawns ++ [.Spawn fresh], []
            simp
            and_intros <;> grind [wf_behavior_history_tail]
          · rcases tail with _ | ⟨e', es''⟩ <;>
              simp [wf_behavior_history_tail] at h_tail <;> try contradiction
            rcases e' <;> try simp at h_tail
            rcases es'' <;> simp at h_tail
            subst h_tail
            simp at h_nmem
      · exact h_wf.behaviorWf bid'
    · intro bid1 bid2 bid0 h_ne h_mem1 h_mem2
      by_cases h_eq1 : bid1 = bid
      · have h_eq2 : bid2 ≠ bid := by
          intro h_eq2
          apply h_ne
          rw [h_eq1, h_eq2]
        have h_mem1_cases : .Spawn bid0 ∈ H.behaviors bid1 ∨ bid0 = fresh := by
          simpa [History.add_behavior_event, h_eq1] using h_mem1
        have h_mem2_old : .Spawn bid0 ∈ H.behaviors bid2 := by
          simpa [History.add_behavior_event, h_eq2] using h_mem2
        rcases h_mem1_cases with h_mem1_old | h_bid0
        · have h_mem1_old' : .Spawn bid0 ∈ H.behaviors bid := by
            simpa [h_eq1] using h_mem1_old
          have h_ne' : bid ≠ bid2 := by
            intro h
            exact h_eq2 h.symm
          exact (h_wf.uniqueSpawns bid bid2 bid0 h_ne' h_mem1_old') h_mem2_old
        · subst h_bid0
          simpa [Event.fresh] using h_matches.freshBehaviorHistory bid2 (.Spawn bid0) h_mem2_old
      · have h_mem1_old : .Spawn bid0 ∈ H.behaviors bid1 := by
          simpa [History.add_behavior_event, h_eq1] using h_mem1
        by_cases h_eq2 : bid2 = bid
        · have h_mem2_cases : .Spawn bid0 ∈ H.behaviors bid2 ∨ bid0 = fresh := by
            simpa [History.add_behavior_event, h_eq2] using h_mem2
          rcases h_mem2_cases with h_mem2_old | h_bid0
          · have h_ne' : bid1 ≠ bid2 := by
              intro h_eq
              apply h_ne
              rw [h_eq, h_eq2]
            exact (h_wf.uniqueSpawns bid1 bid2 bid0 h_ne' h_mem1_old) h_mem2_old
          · subst h_bid0
            simpa [Event.fresh] using h_matches.freshBehaviorHistory bid1 (.Spawn bid0) h_mem1_old
        · have h_mem2_old : .Spawn bid0 ∈ H.behaviors bid2 := by
            simpa [History.add_behavior_event, h_eq2] using h_mem2
          exact (h_wf.uniqueSpawns bid1 bid2 bid0 h_ne h_mem1_old) h_mem2_old
    · simp
      exact h_wf.cownWf
    · intro c e h_mem
      simp at h_mem
      have ⟨bid', h_mem'⟩ := h_wf.cownEvent c e h_mem
      exists bid'
      simp
      grind
    · intro c bid1 h_mem1 h_mem2
      simp at h_mem1 h_mem2 ⊢
      split at h_mem2
      · simp at h_mem2
        exact h_wf.completeOnCown c bid1 h_mem1 h_mem2
      · exact h_wf.completeOnCown c bid1 h_mem1 h_mem2
    · have h_wft := history_wf_timestamp_wf h_wf
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [t']
        intros bid' e1 e2 h_infix
        split at h_infix
        · next h_eq =>
          subst h_eq
          simp [List.IsInfix] at h_infix
          rcases h_infix with ⟨init, tail, h_eq⟩
          rcases List.eq_nil_or_concat tail with h_tail_nil | ⟨tail', x, h_tail_eq⟩
          · subst h_tail_nil
            have h_eq' : (init ++ [e1]).concat e2 = (H.behaviors bid').concat (.Spawn fresh) := by
              simpa using h_eq
            have h_init : init ++ [e1] = H.behaviors bid' := List.init_eq_of_concat_eq h_eq'
            have h_e2 : e2 = .Spawn fresh := by
              simpa [h_init] using h_eq'
            subst h_e2
            have h_mem1 : e1 ∈ H.behaviors bid' := by
              rw [← h_init]
              simp
            have h_mem1' : e1 ∈ H.events := by
              simp [History.events]
              exact ⟨bid', h_mem1⟩
            have h_top1 := h_top e1 h_mem1'
            have h_fresh1 := h_matches.freshBehaviorHistory bid' e1 h_mem1
            rcases e1 <;> simp [Event.fresh] at h_fresh1 ⊢ <;> grind
          · subst h_tail_eq
            have h_eq' : (init ++ [e1, e2] ++ tail').concat x =
              (H.behaviors bid').concat (.Spawn fresh) := by
              simpa [List.concat_eq_append, List.append_assoc] using h_eq
            have h_old : init ++ [e1, e2] ++ tail' =
              H.behaviors bid' := List.init_eq_of_concat_eq h_eq'
            have h_infix_old : [e1, e2] <:+: H.behaviors bid' := by
              exact ⟨init, tail', h_old⟩
            have h_lt := h_wft.1 bid' e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_fresh1 := h_matches.freshBehaviorHistory bid' e1 h_mem1
            have h_fresh2 := h_matches.freshBehaviorHistory bid' e2 h_mem2
            rcases e1 <;> rcases e2 <;> simp [Event.fresh] at h_fresh1 h_fresh2 ⊢ <;> grind
        · have h_lt := h_wft.1 bid' e1 e2 h_infix
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix
          have h_fresh1 := h_matches.freshBehaviorHistory bid' e1 h_mem1
          have h_fresh2 := h_matches.freshBehaviorHistory bid' e2 h_mem2
          rcases e1 <;> rcases e2 <;> simp [Event.fresh] at h_fresh1 h_fresh2 ⊢ <;> grind
      · simp [t']
        introv h_infix
        have h_wfc : wf_cown_history (H.cowns c) := h_wf.cownWf c
        have h_lt := h_wft.2.1 c e1 e2 h_infix
        have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix
        have h_nspawn1 : ¬is_spawn e1 := wf_cown_history_mem_no_spawn h_wfc h_mem1
        have h_nspawn2 : ¬is_spawn e2 := wf_cown_history_mem_no_spawn h_wfc h_mem2
        rcases e1 <;> rcases e2 <;> simp at h_nspawn1 h_nspawn2 ⊢ <;> grind
      · intro parent bid1 h_mem1 h_mem2
        by_cases h_eq : bid1 = fresh
        · subst h_eq
          have h_mem2_old : .Run bid1 ∈ H.behaviors bid1 := by
            simp [History.add_behavior_event] at h_mem2
            split at h_mem2
            · rcases List.mem_append.mp h_mem2 with h_old | h_new
              · exact h_old
              · simp at h_new
            · exact h_mem2
          have h_fresh := h_matches.freshBehaviorHistory bid1 (.Run bid1) h_mem2_old
          simp [Event.fresh] at h_fresh
        · have h_mem1_old : .Spawn bid1 ∈ H.behaviors parent := by
            simp [History.add_behavior_event] at h_mem1
            split at h_mem1
            · rcases List.mem_append.mp h_mem1 with h_old | h_new
              · exact h_old
              · have : bid1 = fresh := by
                  simpa using h_new
                contradiction
            · exact h_mem1
          have h_mem2_old : .Run bid1 ∈ H.behaviors bid1 := by
            simp [History.add_behavior_event] at h_mem2
            split at h_mem2
            · rcases List.mem_append.mp h_mem2 with h_old | h_new
              · exact h_old
              · simp at h_new
            · exact h_mem2
          simpa [t', h_eq] using h_wft.2.2.1 parent bid1 h_mem1_old h_mem2_old
      · intro c bid1 bid2 h_mem1 h_mem2 h_lt
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
    · exists top + 1
      intro e h_mem
      simp [History.events] at h_mem
      rcases h_mem with ⟨bid', h_mem⟩
      split at h_mem
      · next h_eq =>
        subst h_eq
        simp at h_mem
        cases h_mem with
        | inl h_mem =>
          by_cases h_eqe : e = .Spawn fresh
          · subst h_eqe
            have h_fresh := h_matches.freshBehaviorHistory bid' (.Spawn fresh) h_mem
            simp [Event.fresh] at h_fresh
          · simp [t', h_eqe]
            have h_mem' : e ∈ H.events := by
              simp [History.events]
              exists bid'
            grind
        | inr h_eq =>
          subst h_eq
          simp [t']
      · simp [t']
        split <;> try simp
        have h_mem' : e ∈ H.events := by
          simp [History.events]
          exists bid'
        have h_lt := h_top e h_mem'
        grind

lemma history_matches_preservation_spawn
    {t H s top fresh bid bs1 bs2 cs cs' s' s'' pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := s } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Spawn fresh then top else t e
    HistoryMatchesCfg (H[bid += Event.Spawn fresh]) t'
      { fresh := fresh + 1,
        running := bs1 ++ {bid, cowns := cs, stmt := s'} :: bs2,
        pending := pending ++ [{bid := fresh, cowns := cs', stmt := s''}] } :=
  by
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · intro bid' e h_mem
      simp [History.add_behavior_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_mem_old | h_mem_new
        · have h_fresh_old : Event.fresh fresh e :=
            h_matches.freshBehaviorHistory bid' e h_mem_old
          rcases e <;> grind [Event.fresh]
        · have h_eq : e = Event.Spawn fresh := by
            simpa using h_mem_new
          subst h_eq
          simp [Event.fresh]
      · have h_fresh_old : Event.fresh fresh e :=
          h_matches.freshBehaviorHistory bid' e h_mem
        rcases e <;> grind [Event.fresh]
    · intro c e h_mem
      have h_mem_old : e ∈ H.cowns c := by
        simpa [History.add_behavior_event] using h_mem
      have h_fresh_old : Event.fresh fresh e :=
        h_matches.freshCownHistory c e h_mem_old
      rcases e <;> grind [Event.fresh]
    · have h_pw := h_matches.pendingTimestampOrder
      rw [List.map_append]
      apply List.pairwise_append.mpr
      and_intros
      · rw [List.pairwise_map]
        simp [t']
        sorry -- Requires freshness
      · simp
      · simp [t']
        introv h_mem
        sorry -- Requires freshness
    · sorry

lemma wf_history_preservation_complete
    {t H top bid1 bs1 bs2 bid cs pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Complete bid then top else t e
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
          have ⟨bid2', h_mem2''⟩ := h_wf.cownEvent c (.Run bid2) h_mem2'
          have h_wfb : wf_behavior_history bid2' (H.behaviors bid2') := h_wf.behaviorWf bid2'
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
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · intro bid' e h_mem
      simp [History.add_cown_event, History.add_behavior_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_mem_old | h_mem_new
        · exact h_matches.freshBehaviorHistory bid' e h_mem_old
        · have h_eq : e = Event.Complete bid := by
            simpa using h_mem_new
          subst h_eq
          have h_running : { bid := bid, cowns := cs, stmt := Stmt.done } ∈
                           bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2 := by
            simp
          have h_run_mem :=
            (h_matches.runningNotCompleted { bid := bid, cowns := cs, stmt := Stmt.done }).1 h_running |>.1
          have h_fresh_run : Event.fresh bid1 (Event.Run bid) :=
            h_matches.freshBehaviorHistory bid (Event.Run bid) h_run_mem
          simpa [Event.fresh] using h_fresh_run
      · exact h_matches.freshBehaviorHistory bid' e h_mem
    · intro c e h_mem
      simp [History.add_cown_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_mem_old | h_mem_new
        · exact h_matches.freshCownHistory c e h_mem_old
        · have h_eq : e = Event.Complete bid := by
            simpa using h_mem_new
          subst h_eq
          have h_running : { bid := bid, cowns := cs, stmt := Stmt.done } ∈
                           bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2 := by
            simp
          have h_run_mem :=
            (h_matches.runningNotCompleted { bid := bid, cowns := cs, stmt := Stmt.done }).1 h_running |>.1
          have h_fresh_run : Event.fresh bid1 (Event.Run bid) :=
            h_matches.freshBehaviorHistory bid (Event.Run bid) h_run_mem
          simpa [Event.fresh]
      · exact h_matches.freshCownHistory c e h_mem
    · simp [t']
      apply List.pairwise_map.mpr
      simp
      have h_pw := h_matches.pendingTimestampOrder
      grind
    · sorry

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
    · intro bid
      simp
      split
      · next h_eq =>
        subst h_eq

        -- We know that there is no complete in a running behaviour
        sorry -- Lemma about fresh runs
      · exact h_wf.behaviorWf bid
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
          have h_wfc : wf_cown_history (H.cowns c) := h_wf.cownWf c
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
          · have ⟨bid', h_mem2'⟩ := h_wf.cownEvent c (.Run b.bid) h_mem2
            have h_wfb : wf_behavior_history bid' (H.behaviors bid') := h_wf.behaviorWf bid'
            have h_eq2 : bid' = b.bid := by
              exact wf_history_run_mem_inv h_wfb h_mem2'
            subst h_eq2
            have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
            have h_nmem := h_matches.pendingNotRunning b h_pending
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
    introv h_wf h_top h_matches t'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · intro bid' e h_mem
      simp [History.add_cown_event, History.add_behavior_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_mem_old | h_mem_new
        · exact h_matches.freshBehaviorHistory bid' e h_mem_old
        · have h_eq : e = Event.Run b.bid := by
            simpa using h_mem_new
          subst h_eq
          have h_pending : b ∈ bs1 ++ b :: bs2 := by
            simp
          have ⟨parent, h_spawn_mem⟩ := h_matches.pendingSpawned b h_pending
          have h_fresh_spawn : Event.fresh bid1 (Event.Spawn b.bid) :=
            h_matches.freshBehaviorHistory parent (Event.Spawn b.bid) h_spawn_mem
          simpa [Event.fresh] using h_fresh_spawn
      · exact h_matches.freshBehaviorHistory bid' e h_mem
    · intro c e h_mem
      simp [History.add_cown_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_mem_old | h_mem_new
        · exact h_matches.freshCownHistory c e h_mem_old
        · have h_eq : e = Event.Run b.bid := by
            simpa using h_mem_new
          subst h_eq
          have h_pending : b ∈ bs1 ++ b :: bs2 := by
            simp
          have ⟨parent, h_spawn_mem⟩ := h_matches.pendingSpawned b h_pending
          have h_fresh_spawn : Event.fresh bid1 (Event.Spawn b.bid) :=
            h_matches.freshBehaviorHistory parent (Event.Spawn b.bid) h_spawn_mem
          simpa [Event.fresh] using h_fresh_spawn
      · exact h_matches.freshCownHistory c e h_mem
    · apply List.pairwise_map.mpr
      simp [t']
      have h_pw := h_matches.pendingTimestampOrder
      grind
    · sorry

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
    have h_running := h_model.runningNotCompleted
    have h_pending_not_running := h_model.pendingNotRunning
    have h_pending_spawned := h_model.pendingSpawned
    have h_spawned := h_model.spawnedDisposition
    have h_completed := h_model.completedNotActive
    have h_cowns := h_model.cownRunning
    have h_events_behaviors := h_model.freshBehaviorHistory
    have h_events_cowns := h_model.freshCownHistory
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
      have h_wf_b := h_wf.behaviorWf bid2
      let b_hist := H.behaviors bid2
      have h_eq : b_hist = H.behaviors bid2 := by rfl
      rw [← h_eq] at h_complete
      rw [← h_eq] at h_wf_b
      rw [← h_eq]
      rcases (b_hist) with _ | ⟨e, es⟩ <;> try grind
      simp [wf_behavior_history] at h_wf_b
      rcases e <;> try grind

end ConcurrentSemantics
