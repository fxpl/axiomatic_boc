import BoC.Common
import BoC.History

section UnderlyingLanguage

inductive Stmt where
| seq (cowns : List CId) (body cont : Stmt)
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

inductive StepBehavior : Stmt → Stmt × (List CId × Stmt) → Prop where
| When {cowns body cont} :
    ((Stmt.seq cowns body cont) ~> cont | (cowns, body))

end UnderlyingLanguage

section ConcurrentSemantics
structure Behavior where
  mk ::
  (bid : BId)
  (cowns : List CId)
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

-- Configuration-only well-formedness facts (independent of history correspondence)
structure CfgWf (cfg : Cfg) : Prop where
  freshness : CfgFreshness cfg
  -- Running behaviors have no duplicate bids
  runningNoDupsByBid :
    (cfg.running.map Behavior.bid).Pairwise (· ≠ ·)

lemma running_unique_by_bid_of_no_dups {running : List Behavior} :
    (running.map Behavior.bid).Pairwise (· ≠ ·) →
    ∀b1 ∈ running, ∀ b2 ∈ running,
      b1.bid = b2.bid →
      b1 = b2 :=
  by
    intro h_nodup
    generalize h_map : running.map Behavior.bid = bids
    rw [h_map] at h_nodup
    induction h_nodup generalizing running with
    | nil =>
      intro b1 hb1
      simp at h_map
      simp [h_map] at hb1
    | @cons bid bids' h_not_mem h_pair ih =>
      cases running with
      | nil =>
        simp at h_map
      | cons br running' =>
        grind

-- Derive uniqueness from no-duplicates property
lemma cfg_wf_running_unique_by_bid {cfg : Cfg} (h : CfgWf cfg) :
    ∀b1 ∈ cfg.running, ∀b2 ∈ cfg.running,
      b1.bid = b2.bid →
      b1 = b2 := by
  exact running_unique_by_bid_of_no_dups h.runningNoDupsByBid

inductive StepCfg : Cfg × History → Cfg × History → Prop where
| Spawn {fresh bid : BId} {bs1 bs2 cowns cowns' s s' s'' pending H} :
    (s ~> s' | (cowns', s'')) →
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, s⟩ :: bs2, pending⟩, H)
            (⟨fresh + 1, bs1 ++ ⟨bid, cowns, s'⟩ :: bs2, pending ++ [⟨fresh, cowns', s''⟩]⟩,
              (H[bid += Event.Spawn fresh]))
| Complete {fresh bs1 bs2 bid} {cowns : List CId} {pending H} :
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2, pending⟩, H)
    (⟨fresh, bs1 ++ bs2, pending⟩, (H[bid += Event.Complete bid][cowns += Event.Complete bid]))
| Run {fresh running bs1 bs2 b H} :
    (∀c, c ∈ b.cowns →  c ∉ running.flatMap Behavior.cowns) →
    (∀c, c ∈ b.cowns →  c ∉ bs1.flatMap Behavior.cowns) →
    StepCfg (⟨fresh, running, bs1 ++ b :: bs2⟩, H)
    (⟨fresh, b :: running, bs1 ++ bs2⟩, (H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]))

notation cfg " ⇒ " cfg' => StepCfg cfg cfg'

lemma cfg_wf_preservation_spawn
    {fresh bid bs1 bs2 cowns cowns' s s' s'' pending} :
    CfgWf
      { fresh,
        running := bs1 ++ { bid := bid, cowns := cowns, stmt := s } :: bs2,
        pending } →
    CfgWf
      { fresh := fresh + 1,
        running := bs1 ++ { bid := bid, cowns := cowns, stmt := s' } :: bs2,
        pending := pending ++ [{ bid := fresh, cowns := cowns', stmt := s'' }] } :=
  by
    intro h_cfgwf
    constructor
    case freshness =>
      rcases h_cfgwf.freshness with ⟨h_run, h_pending⟩
      constructor
      case left =>
        intro b hb_mem
        simp at hb_mem
        rcases hb_mem with hb1 | hbmid | hb2
        · exact Nat.lt_succ_of_lt (h_run b (by simp [hb1]))
        · subst hbmid
          exact Nat.lt_succ_of_lt (h_run { bid := bid, cowns := cowns, stmt := s } (by simp))
        · exact Nat.lt_succ_of_lt (h_run b (by simp [hb2]))
      case right =>
        intro b hb_mem
        rcases List.mem_append.mp hb_mem with h_old | h_new
        · exact Nat.lt_succ_of_lt (h_pending b h_old)
        · have h_eqb : b = { bid := fresh, cowns := cowns', stmt := s'' } := by
            simpa using h_new
          subst h_eqb
          exact Nat.lt_succ_self fresh
    case runningNoDupsByBid =>
      have h_old_nodup := h_cfgwf.runningNoDupsByBid
      simp [List.map_append] at h_old_nodup ⊢
      exact h_old_nodup

lemma cfg_wf_preservation_complete
    {fresh bs1 bs2 bid cowns pending} :
    CfgWf
      { fresh,
        running := bs1 ++ { bid := bid, cowns := cowns, stmt := Stmt.done } :: bs2,
        pending } →
    CfgWf
      { fresh,
        running := bs1 ++ bs2,
        pending } :=
  by
    intro h_cfgwf
    constructor
    case freshness =>
      rcases h_cfgwf.freshness with ⟨h_run, h_pending⟩
      constructor
      · intro b hb_mem
        have h_old_mem : b ∈ bs1 ++ { bid := bid, cowns := cowns, stmt := Stmt.done } :: bs2 := by
          simp at hb_mem
          rcases hb_mem with hb1 | hb2
          · exact by simp [hb1]
          · exact by simp [hb2]
        exact h_run b h_old_mem
      · exact h_pending
    case runningNoDupsByBid =>
      have h_old_nodup := h_cfgwf.runningNoDupsByBid
      have h_pair :
          List.Pairwise (fun x y => x ≠ y)
            (bs1.map Behavior.bid ++ bid :: bs2.map Behavior.bid) := by
        simpa [List.map_append] using h_old_nodup
      have h_pair' :
          List.Pairwise (fun x y => x ≠ y)
            (bs1.map Behavior.bid ++ bs2.map Behavior.bid) := by
        rcases List.pairwise_append.mp h_pair with ⟨h_left, h_right, h_cross⟩
        apply List.pairwise_append.mpr
        and_intros <;> grind
      simpa [List.map_append] using h_pair'

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
    ∀bid,
      (∃b ∈ cfg.running, b.bid = bid) ↔
      (Event.Run bid ∈ H.behaviors bid ∧
       Event.Complete bid ∉ H.behaviors bid)
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
    ∀bid c,
      (∃b ∈ cfg.running, b.bid = bid ∧ c ∈ b.cowns) ↔
      (Event.Run bid ∈ H.cowns c ∧ Event.Complete bid ∉ H.cowns c)
    -- If a behavior ran on a cown, it must have been spawned by some behavior
  spawnOnCown :
    ∀c bid, .Run bid ∈ H.cowns c → ∃bid', .Spawn bid ∈ H.behaviors bid'
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

lemma history_matches_cfg_freshness {H t cfg} :
    HistoryMatchesCfg H t cfg →
    CfgFreshness cfg :=
  by
    intro h_matches
    rcases cfg with ⟨fresh, running, pending⟩
    constructor
    · intro b h_mem
      have h_run_mem :=
        (h_matches.runningNotCompleted b.bid).1 ⟨b, h_mem, rfl⟩ |>.1
      have h_fresh := h_matches.freshBehaviorHistory b.bid (.Run b.bid) h_run_mem
      simpa [Event.fresh] using h_fresh
    · intro b h_mem
      have ⟨parent, h_spawn_mem⟩ := h_matches.pendingSpawned b h_mem
      have h_fresh := h_matches.freshBehaviorHistory parent (.Spawn b.bid) h_spawn_mem
      simpa [Event.fresh] using h_fresh

lemma pairwise_spawn_time_transport_with_top
    {t : Event → Nat} {fresh top : BId} {l : List Behavior} :
    List.Pairwise
      (fun b1 b2 => t (Event.Spawn b1.bid) < t (Event.Spawn b2.bid))
      l →
    (∀ b : Behavior, b ∈ l → b.bid < fresh) →
    List.Pairwise
      (fun a b =>
        (if a.bid = fresh then top else t (Event.Spawn a.bid)) <
        (if b.bid = fresh then top else t (Event.Spawn b.bid)))
      l := by
  intro h_pw
  induction h_pw with
  | nil =>
    intro _
    simp
  | @cons a l h_head h_tail ih =>
    intro h_lt_all
    simp
    constructor
    · intro b h_mem
      have h_lt := h_head b h_mem
      have ha_lt : a.bid < fresh := h_lt_all a (by simp)
      have hb_lt : b.bid < fresh := h_lt_all b (by simp [h_mem])
      have ha_ne : a.bid ≠ fresh := Nat.ne_of_lt ha_lt
      have hb_ne : b.bid ≠ fresh := Nat.ne_of_lt hb_lt
      simpa [ha_ne, hb_ne] using h_lt
    · apply ih
      intro b h_mem
      exact h_lt_all b (by simp [h_mem])

lemma wf_cown_history_append_complete_of_run_not_complete
    {hist : List Event} {bid : BId} :
    wf_cown_history hist →
    Event.Run bid ∈ hist →
    Event.Complete bid ∉ hist →
    wf_cown_history (hist ++ [Event.Complete bid]) := by
  intro h_wfc h_run_mem h_ncomplete
  induction hist using wf_cown_history.induct with
  | case1 =>
    simp at h_run_mem
  | case2 b =>
    simp at h_run_mem
    subst h_run_mem
    simp [wf_cown_history]
  | case3 b1 b2 hist' ih =>
    simp [wf_cown_history] at h_wfc
    rcases h_wfc with ⟨h_eq, h_wfc'⟩
    subst h_eq
    have h_run_tail : Event.Run bid ∈ hist' := by
      simp at h_run_mem
      rcases h_run_mem with h_head | h_tail
      · exfalso
        have h_comp_mem :
            Event.Complete bid ∈ Event.Run b1 :: Event.Complete b1 :: hist' := by
          simp [h_head]
        exact h_ncomplete h_comp_mem
      · exact h_tail
    have h_ncomplete_tail : Event.Complete bid ∉ hist' := by
      intro h_mem
      exact h_ncomplete (by simp [h_mem])
    have h_tail_wf := ih h_wfc' h_run_tail h_ncomplete_tail
    simp [wf_cown_history, h_tail_wf]
  | case4 hist' h_nil h_run h_rc =>
    rcases hist' with _ | ⟨e, hist''⟩
    · simp at h_nil
    · cases hist'' with
      | nil =>
        rcases e <;> simp [wf_cown_history] at h_wfc
        · exfalso
          exact h_run _ rfl
      | cons e' hist''' =>
        rcases e <;> rcases e' <;> simp [wf_cown_history] at h_wfc
        · exfalso
          exact h_rc _ _ _ rfl

-- Combined invariant used across semantic steps:
-- history correspondence + configuration-only well-formedness.
structure CfgHistoryInv (H : History) (t : Event → Nat) (cfg : Cfg) : Prop where
  historyMatches : HistoryMatchesCfg H t cfg
  cfgWf : CfgWf cfg

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
    constructor
    case behaviorWf =>
      intro bid'
      simp
      split
      · next h_eq =>
        subst h_eq
        have h_running_bid :
            ∃b ∈ bs1 ++ { bid := bid', cowns := cs, stmt := s } :: bs2, b.bid = bid' := by
          refine ⟨{ bid := bid', cowns := cs, stmt := s }, ?_, rfl⟩
          simp
        have ⟨h_mem, h_nmem⟩ :=
          (h_matches.runningNotCompleted bid').mp h_running_bid
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
    case uniqueSpawns =>
      intro bid1 bid2 bid0 h_ne h_mem1 h_mem2
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
    case cownWf =>
      simp
      exact h_wf.cownWf
    case cownEvent =>
      intro c e h_mem
      simp at h_mem
      have ⟨bid', h_mem'⟩ := h_wf.cownEvent c e h_mem
      exists bid'
      simp
      grind
    case completeOnCown =>
      intro c bid1 h_mem1 h_mem2
      simp at h_mem1 h_mem2 ⊢
      split at h_mem2
      · simp at h_mem2
        exact h_wf.completeOnCown c bid1 h_mem1 h_mem2
      · exact h_wf.completeOnCown c bid1 h_mem1 h_mem2
    case timestampWf =>
      have h_wft := history_wf_timestamp_wf h_wf
      constructor
      case behaviorAdj =>
        simp [t']
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
            have h_lt := h_wft.behaviorAdj bid' e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_fresh1 := h_matches.freshBehaviorHistory bid' e1 h_mem1
            have h_fresh2 := h_matches.freshBehaviorHistory bid' e2 h_mem2
            rcases e1 <;> rcases e2 <;> simp [Event.fresh] at h_fresh1 h_fresh2 ⊢ <;> grind
        · have h_lt := h_wft.behaviorAdj bid' e1 e2 h_infix
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix
          have h_fresh1 := h_matches.freshBehaviorHistory bid' e1 h_mem1
          have h_fresh2 := h_matches.freshBehaviorHistory bid' e2 h_mem2
          rcases e1 <;> rcases e2 <;> simp [Event.fresh] at h_fresh1 h_fresh2 ⊢ <;> grind
      case cownAdj =>
        simp [t']
        introv h_infix
        have h_wfc : wf_cown_history (H.cowns c) := h_wf.cownWf c
        have h_lt := h_wft.cownAdj c e1 e2 h_infix
        have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix
        have h_nspawn1 : ¬is_spawn e1 := wf_cown_history_mem_no_spawn h_wfc h_mem1
        have h_nspawn2 : ¬is_spawn e2 := wf_cown_history_mem_no_spawn h_wfc h_mem2
        rcases e1 <;> rcases e2 <;> simp at h_nspawn1 h_nspawn2 ⊢ <;> grind
      case spawnRun =>
        intro parent bid1 h_mem1 h_mem2
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
          simpa [t', h_eq] using h_wft.spawnRun parent bid1 h_mem1_old h_mem2_old
      case happensBefore =>
        intro c bid1 bid2 h_mem1 h_mem2 h_lt
        simp [t'] at h_lt ⊢
        have h_neq1 : bid1 ≠ fresh := by
          intros contra
          subst contra
          simp at h_mem1
          have h_fresh := h_matches.freshCownHistory _ _ h_mem1
          simp [Event.fresh] at h_fresh
        have h_neq2 : bid2 ≠ fresh := by
          intros contra
          subst contra
          simp at h_mem2
          have h_fresh := h_matches.freshCownHistory _ _ h_mem2
          simp [Event.fresh] at h_fresh
        split <;> try contradiction
        exact h_wft.happensBefore c bid1 bid2 h_mem1 h_mem2 h_lt
    case hasTop =>
      exists top + 1
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
    constructor
    case runningNotCompleted =>
      intro bid'
      constructor
      · intro h_new_running
        have h_old_running :
            ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := s } :: bs2, b.bid = bid' := by
          rcases h_new_running with ⟨b, hb_mem, hb_bid⟩
          simp at hb_mem
          rcases hb_mem with hb1 | hbmid | hb2
          · exact ⟨b, by simp [hb1], hb_bid⟩
          · subst hbmid
            exact ⟨{ bid := bid, cowns := cs, stmt := s }, by simp, hb_bid⟩
          · exact ⟨b, by simp [hb2], hb_bid⟩
        have h_old := (h_matches.runningNotCompleted bid').1 h_old_running
        constructor
        · by_cases h_eq : bid' = bid
          · subst h_eq
            simpa [History.add_behavior_event]
              using h_old.1
          · simpa [History.add_behavior_event, h_eq]
              using h_old.1
        · by_cases h_eq : bid' = bid
          · subst h_eq
            simpa [History.add_behavior_event]
              using h_old.2
          · simpa [History.add_behavior_event, h_eq]
              using h_old.2
      · intro h_hist
        have h_old_hist :
            Event.Run bid' ∈ H.behaviors bid' ∧
            Event.Complete bid' ∉ H.behaviors bid' := by
          constructor
          · by_cases h_eq : bid' = bid
            · subst h_eq
              simpa [History.add_behavior_event]
                using h_hist.1
            · simpa [History.add_behavior_event, h_eq]
                using h_hist.1
          · by_cases h_eq : bid' = bid
            · subst h_eq
              simpa [History.add_behavior_event]
                using h_hist.2
            · simpa [History.add_behavior_event, h_eq]
                using h_hist.2
        have h_old_running := (h_matches.runningNotCompleted bid').2 h_old_hist
        rcases h_old_running with ⟨b, hb_mem, hb_bid⟩
        simp at hb_mem
        rcases hb_mem with hb1 | hbmid | hb2
        · exact ⟨b, by simp [hb1], hb_bid⟩
        · subst hbmid
          exact ⟨{ bid := bid, cowns := cs, stmt := s' }, by simp, hb_bid⟩
        · exact ⟨b, by simp [hb2], hb_bid⟩
    case pendingNotRunning =>
      intro b hb_mem h_run
      rcases List.mem_append.mp hb_mem with h_old | h_new
      · have h_notrun_old := h_matches.pendingNotRunning b h_old
        by_cases h_eq : b.bid = bid
        · subst h_eq
          simp [History.add_behavior_event] at h_run
          exact h_notrun_old h_run
        · have h_run_old : .Run b.bid ∈ H.behaviors b.bid := by
            simpa [History.add_behavior_event, h_eq] using h_run
          exact h_notrun_old h_run_old
      · have h_eqb : b = { bid := fresh, cowns := cs', stmt := s'' } := by
          simpa using h_new
        subst h_eqb
        by_cases h_eq : fresh = bid
        · subst h_eq
          simp [History.add_behavior_event] at h_run
          have h_fresh_old := h_matches.freshBehaviorHistory fresh (.Run fresh) h_run
          simp [Event.fresh] at h_fresh_old
        · have h_run_old : .Run fresh ∈ H.behaviors fresh := by
            simpa [History.add_behavior_event, h_eq] using h_run
          have h_fresh_old := h_matches.freshBehaviorHistory fresh (.Run fresh) h_run_old
          simp [Event.fresh] at h_fresh_old
    case pendingSpawned =>
      intro b hb_mem
      rcases List.mem_append.mp hb_mem with h_old | h_new
      · rcases h_matches.pendingSpawned b h_old with ⟨parent, h_spawn_mem⟩
        refine ⟨parent, ?_⟩
        by_cases h_parent : parent = bid
        · subst h_parent
          simp [History.add_behavior_event]
          exact Or.inl h_spawn_mem
        · simpa [History.add_behavior_event, h_parent] using h_spawn_mem
      · have h_eq : b = { bid := fresh, cowns := cs', stmt := s'' } := by
          simpa using h_new
        subst h_eq
        refine ⟨bid, ?_⟩
        simp [History.add_behavior_event]
    case spawnedDisposition =>
      intro parent child h_spawn
      have h_running_lift :
        (∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := s } :: bs2, b.bid = child) →
        (∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := s' } :: bs2, b.bid = child) := by
        intro h_old
        rcases h_old with ⟨b, hb_mem, hb_eq⟩
        simp at hb_mem
        rcases hb_mem with hb1 | hbmid | hb2
        · exact ⟨b, by simp [hb1], hb_eq⟩
        · subst hbmid
          refine ⟨{ bid := bid, cowns := cs, stmt := s' }, by simp, ?_⟩
          simpa using hb_eq
        · exact ⟨b, by simp [hb2], hb_eq⟩
      by_cases h_parent : parent = bid
      · have h_spawn_cases : .Spawn child ∈ H.behaviors parent ∨ child = fresh := by
          simpa [History.add_behavior_event, h_parent] using h_spawn
        rcases h_spawn_cases with h_old | h_new
        · rcases h_matches.spawnedDisposition parent child h_old with h_pend | h_run | h_comp
          · left
            rcases h_pend with ⟨b, hb_mem, hb_eq⟩
            exact ⟨b, by exact List.mem_append.mpr (Or.inl hb_mem), hb_eq⟩
          · right
            left
            exact h_running_lift h_run
          · right
            right
            by_cases h_child : child = bid
            · subst h_child
              simp [History.add_behavior_event]
              exact h_comp
            · simpa [History.add_behavior_event, h_child] using h_comp
        · have h_child : child = fresh := by
            simpa using h_new
          left
          refine ⟨{ bid := fresh, cowns := cs', stmt := s'' }, ?_, ?_⟩
          · simp
          · simp [h_child]
      · have h_spawn_old : .Spawn child ∈ H.behaviors parent := by
          simpa [History.add_behavior_event, h_parent] using h_spawn
        rcases h_matches.spawnedDisposition parent child h_spawn_old with h_pend | h_run | h_comp
        · left
          rcases h_pend with ⟨b, hb_mem, hb_eq⟩
          exact ⟨b, by exact List.mem_append.mpr (Or.inl hb_mem), hb_eq⟩
        · right
          left
          exact h_running_lift h_run
        · right
          right
          by_cases h_child : child = bid
          · subst h_child
            simp [History.add_behavior_event]
            exact h_comp
          · simpa [History.add_behavior_event, h_child] using h_comp
    case completedNotActive =>
      intro bidc h_comp
      have h_comp_old : .Complete bidc ∈ H.behaviors bidc := by
        simp [History.add_behavior_event] at h_comp
        split at h_comp
        · rcases List.mem_append.mp h_comp with h_old | h_new
          · exact h_old
          · simp at h_new
        · exact h_comp
      have h_completed_old := h_matches.completedNotActive bidc h_comp_old
      constructor
      · intro b hb_run
        simp at hb_run
        rcases hb_run with hb1 | hbmid | hb2
        · exact h_completed_old.1 b (by simp [hb1])
        · subst hbmid
          exact h_completed_old.1 { bid := bid, cowns := cs, stmt := s } (by simp)
        · exact h_completed_old.1 b (by simp [hb2])
      · intro b hb_pend
        rcases List.mem_append.mp hb_pend with hb_old | hb_new
        · exact h_completed_old.2 b hb_old
        · have h_eq : b = { bid := fresh, cowns := cs', stmt := s'' } := by
            simpa using hb_new
          subst h_eq
          have h_fresh_comp := h_matches.freshBehaviorHistory bidc (.Complete bidc) h_comp_old
          have h_lt : bidc < fresh := by
            simpa [Event.fresh] using h_fresh_comp
          intro h_eq
          subst h_eq
          exact Nat.lt_irrefl fresh h_lt
    case cownRunning =>
      intro bid' c
      constructor
      · intro h_new_running
        have h_old_running :
            ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := s } :: bs2,
              b.bid = bid' ∧ c ∈ b.cowns := by
          rcases h_new_running with ⟨b, hb_mem, hb_props⟩
          simp at hb_mem
          rcases hb_mem with hb1 | hbmid | hb2
          · exact ⟨b, by simp [hb1], hb_props⟩
          · subst hbmid
            exact ⟨{ bid := bid, cowns := cs, stmt := s }, by simp, hb_props⟩
          · exact ⟨b, by simp [hb2], hb_props⟩
        have h_old := (h_matches.cownRunning bid' c).1 h_old_running
        simpa [History.add_behavior_event] using h_old
      · intro h_hist
        have h_old_hist :
            Event.Run bid' ∈ H.cowns c ∧ Event.Complete bid' ∉ H.cowns c := by
          simpa [History.add_behavior_event] using h_hist
        have h_old_running := (h_matches.cownRunning bid' c).2 h_old_hist
        rcases h_old_running with ⟨b, hb_mem, hb_props⟩
        simp at hb_mem
        rcases hb_mem with hb1 | hbmid | hb2
        · exact ⟨b, by simp [hb1], hb_props⟩
        · subst hbmid
          exact ⟨{ bid := bid, cowns := cs, stmt := s' }, by simp, hb_props⟩
        · exact ⟨b, by simp [hb2], hb_props⟩
    case spawnOnCown =>
      intro c bid h_mem1
      simp at h_mem1
      have ⟨bid', h_mem'⟩ := h_matches.spawnOnCown c bid h_mem1
      exists bid'
      simp
      grind
    case freshBehaviorHistory =>
      intro bid' e h_mem
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
    case freshCownHistory =>
      intro c e h_mem
      have h_mem_old : e ∈ H.cowns c := by
          simpa [History.add_behavior_event] using h_mem
      have h_fresh_old : Event.fresh fresh e :=
        h_matches.freshCownHistory c e h_mem_old
      rcases e <;> grind [Event.fresh]
    case pendingTimestampOrder =>
      have h_pw := h_matches.pendingTimestampOrder
      rw [List.map_append]
      apply List.pairwise_append.mpr
      and_intros
      · rw [List.pairwise_map]
        simp [t']
        have h_cfg_fresh := history_matches_cfg_freshness h_matches
        rcases h_cfg_fresh with ⟨_, h_pending_fresh⟩
        have h_pw' : List.Pairwise
            (fun b1 b2 => t (Event.Spawn b1.bid) < t (Event.Spawn b2.bid)) pending := by
          simpa [List.pairwise_map] using h_pw
        apply pairwise_spawn_time_transport_with_top (l := pending) h_pw'
        intro b h_mem
        exact h_pending_fresh b h_mem
      · simp
      · simp [t']
        intro b hb_mem
        have h_cfg_fresh := history_matches_cfg_freshness h_matches
        rcases h_cfg_fresh with ⟨_, h_pending_fresh⟩
        have hb_lt : b.bid < fresh := h_pending_fresh b hb_mem
        have hb_ne : b.bid ≠ fresh := Nat.ne_of_lt hb_lt
        simp [hb_ne]
        have ⟨parent, h_spawn_mem⟩ := h_matches.pendingSpawned b hb_mem
        have h_event_mem : Event.Spawn b.bid ∈ H.events := by
          simp [History.events]
          exact ⟨parent, h_spawn_mem⟩
        exact h_top (Event.Spawn b.bid) h_event_mem
    case pendingOrder =>
      intros bid1 b2 c h_mem1 h_mem2 h_lt
      simp [t'] at h_lt ⊢
      have h_neq1 : bid1 ≠ fresh := by
        intros contra
        subst contra
        simp at h_mem1
        have h_fresh := h_matches.freshCownHistory _ _ h_mem1
        simp [Event.fresh] at h_fresh
      split <;> try contradiction
      split
      · have h_mem : .Spawn bid1 ∈ H.events := by
          simp at h_mem1
          exact h_matches.spawnOnCown c bid1 h_mem1
        exact h_top (Event.Spawn bid1) h_mem
      · simp at h_mem1
        apply h_matches.pendingOrder bid1 b2 c <;> grind

lemma wf_history_preservation_complete
    {t H top bid1 bs1 bs2 bid cs pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    CfgWf
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
    let t' := fun e => if e = Event.Complete bid then top else t e
    (t' ⊢ H[bid += Event.Complete bid][cs += Event.Complete bid]) :=
  by
    introv h_wf h_top h_cfgwf h_matches t'
    constructor
    case behaviorWf =>
      intro bid'
      simp
      split
      · next h_eq =>
        subst h_eq
        have h_running_bid :
            ∃b ∈ bs1 ++ { bid := bid', cowns := cs, stmt := Stmt.done } :: bs2, b.bid = bid' := by
          refine ⟨{ bid := bid', cowns := cs, stmt := Stmt.done }, ?_, rfl⟩
          simp
        have ⟨h_mem, h_nmem⟩ :=
          (h_matches.runningNotCompleted bid').mp h_running_bid
        have h_wfb := h_wf.behaviorWf bid'
        generalize h_eq : H.behaviors bid' = es
        rw [h_eq] at h_mem h_nmem h_wfb
        cases es with
        | nil => contradiction
        | cons e es' =>
          rcases e <;> simp [wf_behavior_history] at h_wfb
          have ⟨spawns, tail, h_eq', h_spawns, h_tail⟩ := h_wfb.2
          subst h_eq'
          by_cases h_nil : tail = []
          · subst h_nil
            constructor
            · exact h_wfb.1
            · refine ⟨spawns, [.Complete bid'], ?_, h_spawns, ?_⟩
              · simp
              · simp [wf_behavior_history_tail]
          · rcases tail with _ | ⟨e', es''⟩ <;>
              simp [wf_behavior_history_tail] at h_tail <;> try contradiction
            rcases e' <;> try simp at h_tail
            rcases es'' <;> simp at h_tail
            subst h_tail
            simp at h_nmem
      · exact h_wf.behaviorWf bid'
    case uniqueSpawns =>
      intro bidx bidy bidz h_ne h_memx h_memy
      by_cases h_eqx : bidx = bid
      · have h_eqy : bidy ≠ bid := by
          intro h_eqy
          apply h_ne
          rw [h_eqx, h_eqy]
        have h_memx_old : .Spawn bidz ∈ H.behaviors bidx := by
          simpa [History.add_behavior_event, h_eqx] using h_memx
        have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
          simpa [History.add_behavior_event, h_eqy] using h_memy
        exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
      · have h_memx_old : .Spawn bidz ∈ H.behaviors bidx := by
          simpa [History.add_behavior_event, h_eqx] using h_memx
        by_cases h_eqy : bidy = bid
        · have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
            simpa [History.add_behavior_event, h_eqy] using h_memy
          exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
        · have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
            simpa [History.add_behavior_event, h_eqy] using h_memy
          exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
    case cownWf =>
      intro c
      by_cases h_c : c ∈ cs
      · simp [History.add_cown_event, h_c]
        have h_running_bid :
            ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
              b.bid = bid ∧ c ∈ b.cowns := by
          refine ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, ?_, rfl, h_c⟩
          simp
        have h_run_ncomplete := (h_matches.cownRunning bid c).1 h_running_bid
        exact wf_cown_history_append_complete_of_run_not_complete
          (h_wf.cownWf c) h_run_ncomplete.1 h_run_ncomplete.2
      · simp [History.add_cown_event, h_c]
        exact h_wf.cownWf c
    case cownEvent =>
      intro c e h_mem
      simp [History.add_cown_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_old | h_new
        · have ⟨parent, h_beh_old⟩ := h_wf.cownEvent c e h_old
          refine ⟨parent, ?_⟩
          by_cases h_parent : parent = bid
          · subst h_parent
            simp [History.add_behavior_event]
            exact Or.inl h_beh_old
          · simpa [History.add_behavior_event, h_parent] using h_beh_old
        · have h_eqe : e = .Complete bid := by
            simpa using h_new
          subst h_eqe
          refine ⟨bid, ?_⟩
          simp [History.add_behavior_event]
      · have ⟨parent, h_beh_old⟩ := h_wf.cownEvent c e h_mem
        refine ⟨parent, ?_⟩
        by_cases h_parent : parent = bid
        · subst h_parent
          simp [History.add_behavior_event]
          exact Or.inl h_beh_old
        · simpa [History.add_behavior_event, h_parent] using h_beh_old
    case completeOnCown =>
      intros c bid2 h_mem1 h_mem2
      have h_run_old : .Run bid2 ∈ H.cowns c := by
        simp [History.add_cown_event] at h_mem1
        split at h_mem1
        · rcases List.mem_append.mp h_mem1 with h_old | h_new
          · exact h_old
          · simp at h_new
        · exact h_mem1
      by_cases h_bid : bid2 = bid
      · subst h_bid
        have h_running_witness :
            ∃b ∈ bs1 ++ { bid := bid2, cowns := cs, stmt := Stmt.done } :: bs2,
              b.bid = bid2 ∧ c ∈ b.cowns := by
          have h_no_complete_beh : .Complete bid2 ∉ H.behaviors bid2 :=
            (h_matches.runningNotCompleted bid2).1
              ⟨{ bid := bid2, cowns := cs, stmt := Stmt.done }, by simp, rfl⟩ |>.2
          have h_run_ncomplete :
              .Run bid2 ∈ H.cowns c ∧ .Complete bid2 ∉ H.cowns c := by
            constructor
            · exact h_run_old
            · intro h_comp_c
              rcases h_wf.cownEvent c (.Complete bid2) h_comp_c with ⟨parent, h_comp_b⟩
              have h_parent_eq : parent = bid2 :=
                wf_history_complete_mem_inv (h_wf.behaviorWf parent) h_comp_b
              subst h_parent_eq
              exact h_no_complete_beh h_comp_b
          exact (h_matches.cownRunning bid2 c).2 h_run_ncomplete
        rcases h_running_witness with ⟨b_run, hb_run_mem, hb_run_bid, hb_run_c⟩
        have h_main_mem : { bid := bid2, cowns := cs, stmt := Stmt.done } ∈
            bs1 ++ { bid := bid2, cowns := cs, stmt := Stmt.done } :: bs2 := by
          simp
        have h_main_eq :=
          cfg_wf_running_unique_by_bid h_cfgwf
            { bid := bid2, cowns := cs, stmt := Stmt.done } h_main_mem
            b_run hb_run_mem (by simp [hb_run_bid])
        have h_cowns_eq := congrArg Behavior.cowns h_main_eq
        have h_cowns_eq' : b_run.cowns = cs := by
          simpa using h_cowns_eq.symm
        have h_c_in_cs : c ∈ cs := by
          simpa [h_cowns_eq'] using hb_run_c
        simp [History.add_cown_event, h_c_in_cs]
      · have h_complete_old : .Complete bid2 ∈ H.behaviors bid2 := by
          simpa [History.add_behavior_event, h_bid] using h_mem2
        have h_complete_c_old : .Complete bid2 ∈ H.cowns c :=
          h_wf.completeOnCown c bid2 h_run_old h_complete_old
        by_cases h_c : c ∈ cs
        · simpa [History.add_cown_event, h_c, h_bid] using h_complete_c_old
        · simpa [History.add_cown_event, h_c] using h_complete_c_old
    case timestampWf =>
      constructor
      case behaviorAdj =>
        intro bid' e1 e2 h_infix_new
        have h_wft := history_wf_timestamp_wf h_wf
        by_cases h_bid : bid' = bid
        · have h_infix : [e1, e2] <:+: H.behaviors bid' ++ [Event.Complete bid'] := by
            simpa [History.add_behavior_event, h_bid] using h_infix_new
          have h_running_bid :
              ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2, b.bid = bid' := by
            refine ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, ?_, ?_⟩
            · simp
            · simp [h_bid]
          have h_not_complete := (h_matches.runningNotCompleted bid').1 h_running_bid |>.2
          simp [List.IsInfix] at h_infix
          rcases h_infix with ⟨init, tail, h_eq⟩
          rcases List.eq_nil_or_concat tail with h_tail_nil | ⟨tail', x, h_tail_eq⟩
          · subst h_tail_nil
            have h_eq' : (init ++ [e1]).concat e2 = (H.behaviors bid').concat (.Complete bid') := by
              simpa using h_eq
            have h_init : init ++ [e1] = H.behaviors bid' := List.init_eq_of_concat_eq h_eq'
            have h_e2 : e2 = .Complete bid' := by
              simpa [h_init] using h_eq'
            subst h_e2
            have h_mem1 : e1 ∈ H.behaviors bid' := by
              rw [← h_init]
              simp
            have h_ne1 : e1 ≠ .Complete bid' := by
              intro h_eq1
              subst h_eq1
              exact h_not_complete h_mem1
            have h_mem1' : e1 ∈ H.events := by
              simp [History.events]
              exact ⟨bid', h_mem1⟩
            have h_lt := h_top e1 h_mem1'
            have h_ne1b : e1 ≠ .Complete bid := by
              simpa [h_bid] using h_ne1
            simpa [t', h_bid, h_ne1b] using h_lt
          · subst h_tail_eq
            have h_eq' : (init ++ [e1, e2] ++ tail').concat x =
              (H.behaviors bid').concat (.Complete bid') := by
              simpa [List.concat_eq_append, List.append_assoc] using h_eq
            have h_old : init ++ [e1, e2] ++ tail' =
              H.behaviors bid' := List.init_eq_of_concat_eq h_eq'
            have h_infix_old : [e1, e2] <:+: H.behaviors bid' := by
              exact ⟨init, tail', h_old⟩
            have h_lt_old := h_wft.behaviorAdj bid' e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_ne1 : e1 ≠ .Complete bid' := by
              intro h_eq1
              subst h_eq1
              exact h_not_complete h_mem1
            have h_ne2 : e2 ≠ .Complete bid' := by
              intro h_eq2
              subst h_eq2
              exact h_not_complete h_mem2
            have h_ne1b : e1 ≠ .Complete bid := by
              simpa [h_bid] using h_ne1
            have h_ne2b : e2 ≠ .Complete bid := by
              simpa [h_bid] using h_ne2
            simpa [t', h_ne1b, h_ne2b] using h_lt_old
        · have h_infix_old : [e1, e2] <:+: H.behaviors bid' := by
            simpa [History.add_behavior_event, h_bid] using h_infix_new
          have h_lt_old := h_wft.behaviorAdj bid' e1 e2 h_infix_old
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
          have h_ne1 : e1 ≠ .Complete bid := by
            intro h_eq1
            subst h_eq1
            have h_bid_eq : bid' = bid :=
              wf_history_complete_mem_inv (h_wf.behaviorWf bid') h_mem1
            exact h_bid h_bid_eq
          have h_ne2 : e2 ≠ .Complete bid := by
            intro h_eq2
            subst h_eq2
            have h_bid_eq : bid' = bid :=
              wf_history_complete_mem_inv (h_wf.behaviorWf bid') h_mem2
            exact h_bid h_bid_eq
          simpa [t', h_ne1, h_ne2] using h_lt_old
      case cownAdj =>
        intro c e1 e2 h_infix_new
        have h_wft := history_wf_timestamp_wf h_wf
        by_cases h_c : c ∈ cs
        · have h_infix : [e1, e2] <:+: H.cowns c ++ [Event.Complete bid] := by
            simpa [History.add_cown_event, h_c] using h_infix_new
          have h_running_bid :
              ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
                b.bid = bid ∧ c ∈ b.cowns := by
            refine ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, ?_, rfl, h_c⟩
            simp
          have h_not_complete := (h_matches.cownRunning bid c).1 h_running_bid |>.2
          simp [List.IsInfix] at h_infix
          rcases h_infix with ⟨init, tail, h_eq⟩
          rcases List.eq_nil_or_concat tail with h_tail_nil | ⟨tail', x, h_tail_eq⟩
          · subst h_tail_nil
            have h_eq' : (init ++ [e1]).concat e2 = (H.cowns c).concat (.Complete bid) := by
              simpa using h_eq
            have h_init : init ++ [e1] = H.cowns c := List.init_eq_of_concat_eq h_eq'
            have h_e2 : e2 = .Complete bid := by
              simpa [h_init] using h_eq'
            subst h_e2
            have h_mem1 : e1 ∈ H.cowns c := by
              rw [← h_init]
              simp
            have h_ne1 : e1 ≠ .Complete bid := by
              intro h_eq1
              subst h_eq1
              exact h_not_complete h_mem1
            have h_mem1' : e1 ∈ H.events := by
              rcases h_wf.cownEvent c e1 h_mem1 with ⟨p, h_ep⟩
              exact ⟨p, h_ep⟩
            have h_lt := h_top e1 h_mem1'
            simpa [t', h_ne1] using h_lt
          · subst h_tail_eq
            have h_eq' : (init ++ [e1, e2] ++ tail').concat x =
              (H.cowns c).concat (.Complete bid) := by
              simpa [List.concat_eq_append, List.append_assoc] using h_eq
            have h_old : init ++ [e1, e2] ++ tail' = H.cowns c :=
              List.init_eq_of_concat_eq h_eq'
            have h_infix_old : [e1, e2] <:+: H.cowns c := by
              exact ⟨init, tail', h_old⟩
            have h_lt_old := h_wft.cownAdj c e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_ne1 : e1 ≠ .Complete bid := by
              intro h_eq1
              subst h_eq1
              exact h_not_complete h_mem1
            have h_ne2 : e2 ≠ .Complete bid := by
              intro h_eq2
              subst h_eq2
              exact h_not_complete h_mem2
            simpa [t', h_ne1, h_ne2] using h_lt_old
        · have h_infix_old : [e1, e2] <:+: H.cowns c := by
            simpa [History.add_cown_event, h_c] using h_infix_new
          have h_lt_old := h_wft.cownAdj c e1 e2 h_infix_old
          have h_running_bid :
              ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2, b.bid = bid := by
            refine ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, ?_, rfl⟩
            simp
          have h_no_complete_beh := (h_matches.runningNotCompleted bid).1 h_running_bid |>.2
          have h_no_complete_c : .Complete bid ∉ H.cowns c := by
            intro h_comp_c
            rcases h_wf.cownEvent c (.Complete bid) h_comp_c with ⟨parent, h_comp_b⟩
            have h_parent_eq : parent = bid :=
              wf_history_complete_mem_inv (h_wf.behaviorWf parent) h_comp_b
            subst h_parent_eq
            exact h_no_complete_beh h_comp_b
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
          have h_ne1 : e1 ≠ .Complete bid := by
            intro h_eq1
            subst h_eq1
            exact h_no_complete_c h_mem1
          have h_ne2 : e2 ≠ .Complete bid := by
            intro h_eq2
            subst h_eq2
            exact h_no_complete_c h_mem2
          simpa [t', h_ne1, h_ne2] using h_lt_old
      case spawnRun =>
        intro parent bid2 h_mem1 h_mem2
        have h_wft := history_wf_timestamp_wf h_wf
        have h_mem1_old : .Spawn bid2 ∈ H.behaviors parent := by
          by_cases h_parent : parent = bid
          · subst h_parent
            simpa [History.add_behavior_event] using h_mem1
          · simpa [History.add_behavior_event, h_parent] using h_mem1
        have h_mem2_old : .Run bid2 ∈ H.behaviors bid2 := by
          by_cases h_eq : bid2 = bid
          · subst h_eq
            simpa [History.add_behavior_event] using h_mem2
          · simpa [History.add_behavior_event, h_eq] using h_mem2
        simpa [t'] using h_wft.spawnRun parent bid2 h_mem1_old h_mem2_old
      case happensBefore =>
        intro c bid1 bid2 h_mem1 h_mem2 h_lt
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
          exact h_wft.happensBefore c bid1 bid2 h_mem1' h_mem2' h_lt
    case hasTop =>
      exists top + 1
      intro e h_mem
      simp [History.events] at h_mem
      rcases h_mem with ⟨bid', h_mem⟩
      split at h_mem
      · next h_eq =>
        subst h_eq
        simp at h_mem
        cases h_mem with
        | inl h_mem =>
          by_cases h_eqe : e = .Complete bid'
          · subst h_eqe
            have h_fresh := h_matches.freshBehaviorHistory bid' (.Complete bid') h_mem
            simp [Event.fresh] at h_fresh
            simp [t']
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

lemma history_matches_preservation_complete
    {t H top bid1 bs1 bs2 bid cs pending} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    CfgWf
      { fresh := bid1,
        running := bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
        pending } →
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
    introv h_wf h_top h_cfgwf h_matches t'
    constructor
    case runningNotCompleted =>
      intro bid'
      constructor
      · intro h_new_running
        rcases h_new_running with ⟨b, hb_mem_new, hb_bid⟩
        have h_old_mem : b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2 := by
          simp at hb_mem_new
          rcases hb_mem_new with hb1 | hb2
          · exact by simp [hb1]
          · exact by simp [hb2]
        have h_old_hist :=
          (h_matches.runningNotCompleted bid').1 ⟨b, h_old_mem, hb_bid⟩
        have h_pair :
            List.Pairwise (fun x y => x ≠ y)
              (bs1.map Behavior.bid ++ ([bid] ++ bs2.map Behavior.bid)) := by
          simpa [List.map_append] using h_cfgwf.runningNoDupsByBid
        have h_left_sep : ∀x ∈ bs1.map Behavior.bid, x ≠ bid := by
          intro x hx
          exact (List.pairwise_append.mp h_pair).2.2 x hx bid (by simp)
        have h_right_sep : ∀x ∈ bs2.map Behavior.bid, x ≠ bid := by
          intro x hx
          have h_mid_pair :
              List.Pairwise (fun u v => u ≠ v) ([bid] ++ bs2.map Behavior.bid) :=
            (List.pairwise_append.mp h_pair).2.1
          have h_bid_ne_x : bid ≠ x :=
            (List.pairwise_append.mp h_mid_pair).2.2 bid (by simp) x hx
          exact fun h => h_bid_ne_x h.symm
        have h_bid'_ne_bid : bid' ≠ bid := by
          intro h_eq
          have h_b_ne : b.bid ≠ bid := by
            simp at hb_mem_new
            rcases hb_mem_new with hb1 | hb2
            · exact h_left_sep b.bid (by exact List.mem_map.mpr ⟨b, hb1, rfl⟩)
            · exact h_right_sep b.bid (by exact List.mem_map.mpr ⟨b, hb2, rfl⟩)
          exact h_b_ne (by simp [hb_bid, h_eq])
        constructor
        · simpa [History.add_behavior_event, History.add_cown_event, h_bid'_ne_bid]
            using h_old_hist.1
        · simpa [History.add_behavior_event, History.add_cown_event, h_bid'_ne_bid]
            using h_old_hist.2
      · intro h_hist
        have h_bid'_ne_bid : bid' ≠ bid := by
          intro h_eq
          have h_comp_new : Event.Complete bid' ∈
              (H[bid += Event.Complete bid][cs += Event.Complete bid]).behaviors bid' := by
            simp [h_eq, History.add_behavior_event, History.add_cown_event]
          exact h_hist.2 h_comp_new
        have h_old_hist :
            Event.Run bid' ∈ H.behaviors bid' ∧ Event.Complete bid' ∉ H.behaviors bid' := by
          constructor
          · simpa [History.add_behavior_event, History.add_cown_event, h_bid'_ne_bid] using h_hist.1
          · simpa [History.add_behavior_event, History.add_cown_event, h_bid'_ne_bid] using h_hist.2
        have h_old_running := (h_matches.runningNotCompleted bid').2 h_old_hist
        rcases h_old_running with ⟨b, hb_mem_old, hb_bid⟩
        simp at hb_mem_old
        rcases hb_mem_old with hb1 | hbmid | hb2
        · exact ⟨b, by simp [hb1], hb_bid⟩
        · subst hbmid
          exfalso
          exact h_bid'_ne_bid hb_bid.symm
        · exact ⟨b, by simp [hb2], hb_bid⟩
    case pendingNotRunning =>
      intro b hb_mem h_run
      have h_notrun_old := h_matches.pendingNotRunning b hb_mem
      by_cases h_eq : b.bid = bid
      · subst h_eq
        simp [History.add_behavior_event] at h_run
        exact h_notrun_old h_run
      · have h_run_old : .Run b.bid ∈ H.behaviors b.bid := by
          simpa [History.add_behavior_event, h_eq] using h_run
        exact h_notrun_old h_run_old
    case pendingSpawned =>
      intro b hb_mem
      rcases h_matches.pendingSpawned b hb_mem with ⟨parent, h_spawn_old⟩
      refine ⟨parent, ?_⟩
      by_cases h_parent : parent = bid
      · subst h_parent
        simpa [History.add_behavior_event] using h_spawn_old
      · simpa [History.add_behavior_event, h_parent] using h_spawn_old
    case spawnedDisposition =>
      intro parent child h_spawn
      have h_spawn_old : Event.Spawn child ∈ H.behaviors parent := by
        by_cases h_parent : parent = bid
        · subst h_parent
          have h_spawn_cases :
              Event.Spawn child ∈ H.behaviors parent ∨
              Event.Spawn child = Event.Complete parent := by
            simpa [History.add_behavior_event] using h_spawn
          rcases h_spawn_cases with h_old | h_new
          · exact h_old
          · simp at h_new
        · simpa [History.add_behavior_event, h_parent] using h_spawn
      rcases h_matches.spawnedDisposition parent child h_spawn_old with h_pend | h_run | h_comp
      · left
        exact h_pend
      · rcases h_run with ⟨b, hb_mem_old, hb_bid⟩
        simp at hb_mem_old
        rcases hb_mem_old with hb1 | hbmid | hb2
        · right
          left
          exact ⟨b, by simp [hb1], hb_bid⟩
        · subst hbmid
          right
          right
          have h_child : child = bid := by
            exact hb_bid.symm
          have h_complete_new :
              Event.Complete child ∈
                (H[bid += Event.Complete bid][cs += Event.Complete bid]).behaviors child := by
            simp [History.add_behavior_event, History.add_cown_event, h_child]
          exact h_complete_new
        · right
          left
          exact ⟨b, by simp [hb2], hb_bid⟩
      · right
        right
        by_cases h_child : child = bid
        · subst h_child
          simp [History.add_behavior_event, History.add_cown_event]
        · simpa [History.add_behavior_event, History.add_cown_event, h_child] using h_comp
    case completedNotActive =>
      simp
      intro bid' h_mem1
      split at h_mem1
      · next h_eq =>
        rw [h_eq] at h_mem1 ⊢
        have h_pair :
            List.Pairwise (fun x y => x ≠ y)
              (bs1.map Behavior.bid ++ ([bid] ++ bs2.map Behavior.bid)) := by
          simpa [List.map_append] using h_cfgwf.runningNoDupsByBid
        have h_left_sep : ∀x ∈ bs1.map Behavior.bid, x ≠ bid := by
          intro x hx
          exact (List.pairwise_append.mp h_pair).2.2 x hx bid (by simp)
        have h_right_sep : ∀x ∈ bs2.map Behavior.bid, x ≠ bid := by
          intro x hx
          have h_mid_pair :
              List.Pairwise (fun u v => u ≠ v) ([bid] ++ bs2.map Behavior.bid) :=
            (List.pairwise_append.mp h_pair).2.1
          have h_bid_ne_x : bid ≠ x :=
            (List.pairwise_append.mp h_mid_pair).2.2 bid (by simp) x hx
          exact fun h => h_bid_ne_x h.symm
        have h_run_bid : Event.Run bid ∈ H.behaviors bid := by
          have h_running :
              { bid := bid, cowns := cs, stmt := Stmt.done } ∈
                bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2 := by
            simp
          exact (h_matches.runningNotCompleted bid).1
            ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, h_running, rfl⟩ |>.1
        constructor
        · intro b hb_mem h_bid
          rcases hb_mem with hb1 | hb2
          · exact h_left_sep b.bid (List.mem_map.mpr ⟨b, hb1, rfl⟩) h_bid
          · exact h_right_sep b.bid (List.mem_map.mpr ⟨b, hb2, rfl⟩) h_bid
        · intro b hb_mem h_bid
          have h_not_run := h_matches.pendingNotRunning b hb_mem
          have h_run_b : Event.Run b.bid ∈ H.behaviors b.bid := by
            rw [h_bid]
            exact h_run_bid
          exact h_not_run h_run_b
      · have := h_matches.completedNotActive bid' h_mem1
        grind
    case cownRunning =>
      intro bid' c
      constructor
      · intro h_new_running
        rcases h_new_running with ⟨b, hb_mem_new, hb_bid, h_c_mem⟩
        have h_old_running :
            ∃b ∈ bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2,
              b.bid = bid' ∧ c ∈ b.cowns := by
          simp at hb_mem_new
          rcases hb_mem_new with hb1 | hb2
          · exact ⟨b, by simp [hb1], hb_bid, h_c_mem⟩
          · exact ⟨b, by simp [hb2], hb_bid, h_c_mem⟩
        have h_old := (h_matches.cownRunning bid' c).1 h_old_running
        have h_pair :
            List.Pairwise (fun x y => x ≠ y)
              (bs1.map Behavior.bid ++ ([bid] ++ bs2.map Behavior.bid)) := by
          simpa [List.map_append] using h_cfgwf.runningNoDupsByBid
        have h_left_sep : ∀x ∈ bs1.map Behavior.bid, x ≠ bid := by
          intro x hx
          exact (List.pairwise_append.mp h_pair).2.2 x hx bid (by simp)
        have h_right_sep : ∀x ∈ bs2.map Behavior.bid, x ≠ bid := by
          intro x hx
          have h_mid_pair :
              List.Pairwise (fun u v => u ≠ v) ([bid] ++ bs2.map Behavior.bid) :=
            (List.pairwise_append.mp h_pair).2.1
          have h_bid_ne_x : bid ≠ x :=
            (List.pairwise_append.mp h_mid_pair).2.2 bid (by simp) x hx
          exact fun h => h_bid_ne_x h.symm
        have h_bid'_ne_bid : bid' ≠ bid := by
          intro h_eq
          have h_b_ne : b.bid ≠ bid := by
            simp at hb_mem_new
            rcases hb_mem_new with hb1 | hb2
            · exact h_left_sep b.bid (List.mem_map.mpr ⟨b, hb1, rfl⟩)
            · exact h_right_sep b.bid (List.mem_map.mpr ⟨b, hb2, rfl⟩)
          exact h_b_ne (by rw [hb_bid, h_eq])
        constructor
        · by_cases h_c_in_cs : c ∈ cs
          · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_old.1
          · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_old.1
        · by_cases h_c_in_cs : c ∈ cs
          · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_old.2
          · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_old.2
      · intro h_hist
        have h_bid'_ne_bid : bid' ≠ bid := by
          intro h_eq
          by_cases h_c_in_cs : c ∈ cs
          · have h_comp_new :
              Event.Complete bid' ∈
                (H[bid += Event.Complete bid][cs += Event.Complete bid]).cowns c := by
              rw [h_eq]
              simp [History.add_cown_event, h_c_in_cs]
            exact h_hist.2 h_comp_new
          · have h_hist_eq := h_hist
            rw [h_eq] at h_hist_eq
            have h_old_hist :
                Event.Run bid ∈ H.cowns c ∧ Event.Complete bid ∉ H.cowns c := by
              constructor
              · simpa [History.add_cown_event, h_c_in_cs] using h_hist_eq.1
              · simpa [History.add_cown_event, h_c_in_cs] using h_hist_eq.2
            have h_old_running := (h_matches.cownRunning bid c).2 h_old_hist
            rcases h_old_running with ⟨b, hb_mem_old, hb_bid, h_c_mem⟩
            have h_main_mem : { bid := bid, cowns := cs, stmt := Stmt.done } ∈
                bs1 ++ { bid := bid, cowns := cs, stmt := Stmt.done } :: bs2 := by
              simp
            have h_main_eq :=
              cfg_wf_running_unique_by_bid h_cfgwf
                { bid := bid, cowns := cs, stmt := Stmt.done } h_main_mem
                b hb_mem_old (by simp [hb_bid])
            have h_cowns_eq := congrArg Behavior.cowns h_main_eq
            have h_cowns_eq' : b.cowns = cs := by
              simpa using h_cowns_eq.symm
            have : c ∈ cs := by
              simpa [h_cowns_eq'] using h_c_mem
            exact h_c_in_cs this
        have h_old_hist :
            Event.Run bid' ∈ H.cowns c ∧ Event.Complete bid' ∉ H.cowns c := by
          constructor
          · by_cases h_c_in_cs : c ∈ cs
            · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_hist.1
            · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_hist.1
          · by_cases h_c_in_cs : c ∈ cs
            · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_hist.2
            · simpa [History.add_cown_event, h_c_in_cs, h_bid'_ne_bid] using h_hist.2
        have h_old_running := (h_matches.cownRunning bid' c).2 h_old_hist
        rcases h_old_running with ⟨b, hb_mem_old, hb_bid, h_c_mem⟩
        simp at hb_mem_old
        rcases hb_mem_old with hb1 | hbmid | hb2
        · exact ⟨b, by simp [hb1], hb_bid, h_c_mem⟩
        · subst hbmid
          exfalso
          exact h_bid'_ne_bid hb_bid.symm
        · exact ⟨b, by simp [hb2], hb_bid, h_c_mem⟩
    case spawnOnCown =>
      intro c bid' h_run
      have h_run_old : .Run bid' ∈ H.cowns c := by
        simp [History.add_cown_event] at h_run
        split at h_run
        · rcases List.mem_append.mp h_run with h_old | h_new
          · exact h_old
          · simp at h_new
        · exact h_run
      rcases h_matches.spawnOnCown c bid' h_run_old with ⟨parent, h_spawn_old⟩
      refine ⟨parent, ?_⟩
      by_cases h_parent : parent = bid
      · subst h_parent
        simpa [History.add_behavior_event] using h_spawn_old
      · simpa [History.add_behavior_event, h_parent] using h_spawn_old
    case freshBehaviorHistory =>
      intro bid' e h_mem
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
            (h_matches.runningNotCompleted bid).1
              ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, h_running, rfl⟩ |>.1
          have h_fresh_run : Event.fresh bid1 (Event.Run bid) :=
            h_matches.freshBehaviorHistory bid (Event.Run bid) h_run_mem
          simpa [Event.fresh] using h_fresh_run
      · exact h_matches.freshBehaviorHistory bid' e h_mem
    case freshCownHistory =>
      intro c e h_mem
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
            (h_matches.runningNotCompleted bid).1
              ⟨{ bid := bid, cowns := cs, stmt := Stmt.done }, h_running, rfl⟩ |>.1
          have h_fresh_run : Event.fresh bid1 (Event.Run bid) :=
            h_matches.freshBehaviorHistory bid (Event.Run bid) h_run_mem
          simpa [Event.fresh]
      · exact h_matches.freshCownHistory c e h_mem
    case pendingTimestampOrder =>
      simp [t']
      apply List.pairwise_map.mpr
      simp
      have h_pw := h_matches.pendingTimestampOrder
      grind
    case pendingOrder =>
      intro bid' b c h_run hb_mem h_c_mem
      have h_run_old : Event.Run bid' ∈ H.cowns c := by
        by_cases h_c_in_cs : c ∈ cs
        · simpa [History.add_cown_event, h_c_in_cs] using h_run
        · simpa [History.add_cown_event, h_c_in_cs] using h_run
      simp [t']
      exact h_matches.pendingOrder bid' b c h_run_old hb_mem h_c_mem

lemma wf_cown_history_append_run_of_closed {t : Event → Nat} {newBid : BId} :
    ∀ hist,
      wf_cown_history hist →
      (∀ bid', Event.Run bid' ∈ hist → Event.Complete bid' ∈ hist) →
      (∀ e1 e2, [e1, e2] <:+: hist → t e1 < t e2) →
      wf_cown_history (hist ++ [Event.Run newBid]) := by
  intro hist h_wfc h_closed h_time
  match hist with
  | [] =>
    simp [wf_cown_history]
  | Event.Run bid' :: [] =>
    exfalso
    have h_complete : Event.Complete bid' ∈ [Event.Run bid'] :=
      h_closed bid' (by simp)
    simp at h_complete
  | Event.Run bid1 :: Event.Complete bid2 :: tail =>
    simp [wf_cown_history] at h_wfc
    rcases h_wfc with ⟨h_eq, h_wfc_tail⟩
    subst h_eq
    have h_time_tail :
        ∀ e1 e2, [e1, e2] <:+: tail → t e1 < t e2 := by
      intro e1 e2 h_infix
      apply h_time
      rcases h_infix with ⟨init, tail', h_eq⟩
      refine ⟨Event.Run bid1 :: Event.Complete bid1 :: init, tail', ?_⟩
      simp [h_eq]
    have h_closed_tail :
        ∀ targetBid, Event.Run targetBid ∈ tail → Event.Complete targetBid ∈ tail := by
      intro targetBid h_run
      have h_complete :
          Event.Complete targetBid ∈ Event.Run bid1 :: Event.Complete bid1 :: tail :=
        h_closed targetBid (by simp [h_run])
      simp at h_complete
      rcases h_complete with h_eq_target | h_tail
      · subst h_eq_target
        exfalso
        have h_run_tail : Event.Run targetBid ∈ tail := by
          simpa using h_run
        have h_time_from_complete :
            ∀ e1 e2, [e1, e2] <:+: (Event.Complete targetBid :: tail) → t e1 < t e2 := by
          intro e1 e2 h_infix
          apply h_time
          rcases h_infix with ⟨init, tail', h_eq⟩
          refine ⟨Event.Run targetBid :: init, tail', ?_⟩
          simp [h_eq]
        have h_lt_run_complete : t (Event.Run targetBid) < t (Event.Complete targetBid) := by
          apply h_time
          exact ⟨[], tail, by simp⟩
        have h_lt_complete_run : t (Event.Complete targetBid) < t (Event.Run targetBid) :=
          head_lt_of_mem_ordered h_run_tail h_time_from_complete
        exact False.elim (Nat.lt_asymm h_lt_run_complete h_lt_complete_run)
      · exact h_tail
    have h_tail_wf :=
      wf_cown_history_append_run_of_closed
        (newBid := newBid) tail h_wfc_tail h_closed_tail h_time_tail
    simpa [List.append_assoc, wf_cown_history] using h_tail_wf
  | Event.Spawn _ :: _ =>
    simp [wf_cown_history] at h_wfc
  | Event.Complete _ :: _ =>
    simp [wf_cown_history] at h_wfc
  | Event.Run _ :: Event.Spawn _ :: _ =>
    simp [wf_cown_history] at h_wfc
  | Event.Run _ :: Event.Run _ :: _ =>
    simp [wf_cown_history] at h_wfc

lemma wf_history_preservation_run
  {t H top bid1 bs1 bs2 running b} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    (∀c, c ∈ b.cowns → c ∉ running.flatMap Behavior.cowns) →
    (∀c, c ∈ b.cowns → c ∉ bs1.flatMap Behavior.cowns) →
    HistoryMatchesCfg H t
      { fresh := bid1,
        running,
        pending := bs1 ++ b :: bs2 } →
    let t' := fun e => if e = Event.Run b.bid then top else t e;
    (t' ⊢ H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]) :=
  by
    introv h_wf h_top h_no_running h_no_pending h_matches t'
    constructor
    case behaviorWf =>
      intro bid
      simp
      split
      · next h_eq =>
        subst h_eq
        have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
        have h_no_run : Event.Run b.bid ∉ H.behaviors b.bid :=
          h_matches.pendingNotRunning b h_pending
        have h_wfb_old := h_wf.behaviorWf b.bid
        have h_empty : H.behaviors b.bid = [] := by
          generalize h_hist : H.behaviors b.bid = es
          rw [h_hist] at h_no_run h_wfb_old
          cases es with
          | nil => rfl
          | cons e rest =>
            cases e with
            | Spawn _ | Complete _ => simp [wf_behavior_history] at h_wfb_old
            | Run bid' =>
              simp only [wf_behavior_history] at h_wfb_old
              have h_bid_eq : b.bid = bid' := h_wfb_old.1
              simp [h_bid_eq] at h_no_run
        rw [h_empty]
        simp [wf_behavior_history, wf_behavior_history_tail]
      · exact h_wf.behaviorWf bid
    case uniqueSpawns =>
      intro bidx bidy bidz h_ne h_memx h_memy
      by_cases h_eqx : bidx = b.bid
      · have h_eqy : bidy ≠ b.bid := by
          intro h_eqy
          apply h_ne
          rw [h_eqx, h_eqy]
        have h_memx_old : .Spawn bidz ∈ H.behaviors bidx := by
          simpa [History.add_behavior_event, h_eqx] using h_memx
        have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
          simpa [History.add_behavior_event, h_eqy] using h_memy
        exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
      · have h_memx_old : .Spawn bidz ∈ H.behaviors bidx := by
          simpa [History.add_behavior_event, h_eqx] using h_memx
        by_cases h_eqy : bidy = b.bid
        · have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
            simpa [History.add_behavior_event, h_eqy] using h_memy
          exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
        · have h_memy_old : .Spawn bidz ∈ H.behaviors bidy := by
            simpa [History.add_behavior_event, h_eqy] using h_memy
          exact (h_wf.uniqueSpawns bidx bidy bidz h_ne h_memx_old) h_memy_old
    case cownWf =>
      intro c
      by_cases h_c : c ∈ b.cowns
      · have h_wft := history_wf_timestamp_wf h_wf
        have h_no_open_run :
            ∀ bid', Event.Run bid' ∈ H.cowns c → Event.Complete bid' ∈ H.cowns c := by
          intro bid' h_run
          by_cases h_complete : Event.Complete bid' ∈ H.cowns c
          · exact h_complete
          · have h_running := (h_matches.cownRunning bid' c).2 ⟨h_run, h_complete⟩
            rcases h_running with ⟨b', hb'_mem, hb'_bid, h_c_mem⟩
            have h_flat : c ∈ running.flatMap Behavior.cowns := by
              exact List.mem_flatMap.mpr ⟨b', hb'_mem, h_c_mem⟩
            exact False.elim ((h_no_running c h_c) h_flat)
        simpa [History.add_cown_event, h_c] using
          wf_cown_history_append_run_of_closed (newBid := b.bid)
            (H.cowns c) (h_wf.cownWf c) h_no_open_run (h_wft.cownAdj c)
      · simpa [History.add_cown_event, h_c] using h_wf.cownWf c
    case cownEvent =>
      intro c e h_mem
      simp [History.add_cown_event] at h_mem
      split at h_mem
      · rcases List.mem_append.mp h_mem with h_old | h_new
        · have ⟨parent, h_beh_old⟩ := h_wf.cownEvent c e h_old
          refine ⟨parent, ?_⟩
          by_cases h_parent : parent = b.bid
          · subst h_parent
            simp [History.add_behavior_event]
            exact Or.inl h_beh_old
          · simpa [History.add_behavior_event, h_parent] using h_beh_old
        · have h_eqe : e = .Run b.bid := by
            simpa using h_new
          subst h_eqe
          refine ⟨b.bid, ?_⟩
          simp [History.add_behavior_event]
      · have ⟨parent, h_beh_old⟩ := h_wf.cownEvent c e h_mem
        refine ⟨parent, ?_⟩
        by_cases h_parent : parent = b.bid
        · subst h_parent
          simp [History.add_behavior_event]
          exact Or.inl h_beh_old
        · simpa [History.add_behavior_event, h_parent] using h_beh_old
    case completeOnCown =>
      intro c bid h_mem1 h_mem2
      by_cases h_bid : bid = b.bid
      · subst h_bid
        have h_complete_old : .Complete b.bid ∈ H.behaviors b.bid := by
          simp [History.add_behavior_event] at h_mem2
          exact h_mem2
        have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
        have h_not_active := h_matches.completedNotActive b.bid h_complete_old
        have h_bid_ne : b.bid ≠ b.bid := h_not_active.2 b h_pending
        exact False.elim (h_bid_ne rfl)
      · have h_run_old : .Run bid ∈ H.cowns c := by
          simp [History.add_cown_event] at h_mem1
          split at h_mem1
          · rcases List.mem_append.mp h_mem1 with h_old | h_new
            · exact h_old
            · have : bid = b.bid := by simpa using h_new
              contradiction
          · exact h_mem1
        have h_complete_old : .Complete bid ∈ H.behaviors bid := by
          simpa [History.add_behavior_event, h_bid] using h_mem2
        have h_complete_c_old := h_wf.completeOnCown c bid h_run_old h_complete_old
        by_cases h_c : c ∈ b.cowns
        · simpa [History.add_cown_event, h_c, h_bid] using h_complete_c_old
        · simpa [History.add_cown_event, h_c] using h_complete_c_old
    case timestampWf =>
      constructor
      case behaviorAdj =>
        intro bid' e1 e2 h_infix_new
        have h_wft := history_wf_timestamp_wf h_wf
        have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
        have h_no_run_b : .Run b.bid ∉ H.behaviors b.bid :=
          h_matches.pendingNotRunning b h_pending
        by_cases h_bid : bid' = b.bid
        · have h_infix : [e1, e2] <:+: H.behaviors bid' ++ [Event.Run b.bid] := by
            simpa [History.add_behavior_event, h_bid] using h_infix_new
          simp [List.IsInfix] at h_infix
          rcases h_infix with ⟨init, tail, h_eq⟩
          rcases List.eq_nil_or_concat tail with h_tail_nil | ⟨tail', x, h_tail_eq⟩
          · subst h_tail_nil
            have h_eq' : (init ++ [e1]).concat e2 = (H.behaviors bid').concat (.Run b.bid) := by
              simpa using h_eq
            have h_init : init ++ [e1] = H.behaviors bid' := List.init_eq_of_concat_eq h_eq'
            have h_e2 : e2 = .Run b.bid := by
              simpa [h_init] using h_eq'
            subst h_e2
            have h_mem1 : e1 ∈ H.behaviors bid' := by
              rw [← h_init]
              simp
            have h_mem1' : e1 ∈ H.events := by
              exact ⟨bid', h_mem1⟩
            have h_lt_top := h_top e1 h_mem1'
            have h_ne1 : e1 ≠ .Run b.bid := by
              intro h_eq1
              subst h_eq1
              have h_run_in : .Run b.bid ∈ H.behaviors b.bid := by
                simpa [h_bid] using h_mem1
              exact h_no_run_b h_run_in
            simpa [t', h_ne1]
              using h_lt_top
          · subst h_tail_eq
            have h_eq' : (init ++ [e1, e2] ++ tail').concat x =
              (H.behaviors bid').concat (.Run b.bid) := by
              simpa [List.concat_eq_append, List.append_assoc] using h_eq
            have h_old : init ++ [e1, e2] ++ tail' = H.behaviors bid' :=
              List.init_eq_of_concat_eq h_eq'
            have h_infix_old : [e1, e2] <:+: H.behaviors bid' := by
              exact ⟨init, tail', h_old⟩
            have h_lt_old := h_wft.behaviorAdj bid' e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_ne1 : e1 ≠ .Run b.bid := by
              intro h_eq1
              subst h_eq1
              have h_run_in : .Run b.bid ∈ H.behaviors b.bid := by
                simpa [h_bid] using h_mem1
              exact h_no_run_b h_run_in
            have h_ne2 : e2 ≠ .Run b.bid := by
              intro h_eq2
              subst h_eq2
              have h_run_in : .Run b.bid ∈ H.behaviors b.bid := by
                simpa [h_bid] using h_mem2
              exact h_no_run_b h_run_in
            simpa [t', h_ne1, h_ne2] using h_lt_old
        · have h_infix_old : [e1, e2] <:+: H.behaviors bid' := by
            simpa [History.add_behavior_event, h_bid] using h_infix_new
          have h_lt_old := h_wft.behaviorAdj bid' e1 e2 h_infix_old
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
          have h_ne1 : e1 ≠ .Run b.bid := by
            intro h_eq1
            subst h_eq1
            have h_bid_eq : bid' = b.bid :=
              wf_history_run_mem_inv (h_wf.behaviorWf bid') h_mem1
            exact h_bid h_bid_eq
          have h_ne2 : e2 ≠ .Run b.bid := by
            intro h_eq2
            subst h_eq2
            have h_bid_eq : bid' = b.bid :=
              wf_history_run_mem_inv (h_wf.behaviorWf bid') h_mem2
            exact h_bid h_bid_eq
          simpa [t', h_ne1, h_ne2] using h_lt_old
      case cownAdj =>
        intro c e1 e2 h_infix_new
        have h_wft := history_wf_timestamp_wf h_wf
        have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
        have h_no_run_b_beh : .Run b.bid ∉ H.behaviors b.bid :=
          h_matches.pendingNotRunning b h_pending
        have h_no_run_b_cown : .Run b.bid ∉ H.cowns c := by
          intro h_run
          have ⟨owner, h_mem_beh⟩ := h_wf.cownEvent c (.Run b.bid) h_run
          have h_owner : owner = b.bid :=
            wf_history_run_mem_inv (h_wf.behaviorWf owner) h_mem_beh
          subst h_owner
          exact h_no_run_b_beh h_mem_beh
        by_cases h_c : c ∈ b.cowns
        · have h_infix : [e1, e2] <:+: H.cowns c ++ [Event.Run b.bid] := by
            simpa [History.add_cown_event, h_c] using h_infix_new
          simp [List.IsInfix] at h_infix
          rcases h_infix with ⟨init, tail, h_eq⟩
          rcases List.eq_nil_or_concat tail with h_tail_nil | ⟨tail', x, h_tail_eq⟩
          · subst h_tail_nil
            have h_eq' : (init ++ [e1]).concat e2 = (H.cowns c).concat (.Run b.bid) := by
              simpa using h_eq
            have h_init : init ++ [e1] = H.cowns c := List.init_eq_of_concat_eq h_eq'
            have h_e2 : e2 = .Run b.bid := by
              simpa [h_init] using h_eq'
            subst h_e2
            have h_mem1 : e1 ∈ H.cowns c := by
              rw [← h_init]
              simp
            have h_mem1' : e1 ∈ H.events := by
              rcases h_wf.cownEvent c e1 h_mem1 with ⟨owner, h_owner_mem⟩
              exact ⟨owner, h_owner_mem⟩
            have h_lt_top := h_top e1 h_mem1'
            have h_ne1 : e1 ≠ .Run b.bid := by
              intro h_eq1
              subst h_eq1
              exact h_no_run_b_cown h_mem1
            simpa [t', h_ne1] using h_lt_top
          · subst h_tail_eq
            have h_eq' : (init ++ [e1, e2] ++ tail').concat x =
              (H.cowns c).concat (.Run b.bid) := by
              simpa [List.concat_eq_append, List.append_assoc] using h_eq
            have h_old : init ++ [e1, e2] ++ tail' = H.cowns c :=
              List.init_eq_of_concat_eq h_eq'
            have h_infix_old : [e1, e2] <:+: H.cowns c := by
              exact ⟨init, tail', h_old⟩
            have h_lt_old := h_wft.cownAdj c e1 e2 h_infix_old
            have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
            have h_ne1 : e1 ≠ .Run b.bid := by
              intro h_eq1
              subst h_eq1
              exact h_no_run_b_cown h_mem1
            have h_ne2 : e2 ≠ .Run b.bid := by
              intro h_eq2
              subst h_eq2
              exact h_no_run_b_cown h_mem2
            simpa [t', h_ne1, h_ne2] using h_lt_old
        · have h_infix_old : [e1, e2] <:+: H.cowns c := by
            simpa [History.add_cown_event, h_c] using h_infix_new
          have h_lt_old := h_wft.cownAdj c e1 e2 h_infix_old
          have ⟨h_mem1, h_mem2⟩ := pair_infix_mem h_infix_old
          have h_ne1 : e1 ≠ .Run b.bid := by
            intro h_eq1
            subst h_eq1
            exact h_no_run_b_cown h_mem1
          have h_ne2 : e2 ≠ .Run b.bid := by
            intro h_eq2
            subst h_eq2
            exact h_no_run_b_cown h_mem2
          simpa [t', h_ne1, h_ne2] using h_lt_old
      case spawnRun =>
        intro parent bid1 h_mem1 h_mem2
        have h_wft := history_wf_timestamp_wf h_wf
        by_cases h_eq : bid1 = b.bid
        · subst h_eq
          have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
          have ⟨owner, h_spawn_mem⟩ := h_matches.pendingSpawned b h_pending
          have h_spawn_event : .Spawn b.bid ∈ H.events := by
            exact ⟨owner, h_spawn_mem⟩
          have h_lt_top := h_top (.Spawn b.bid) h_spawn_event
          simpa [t'] using h_lt_top
        · have h_mem1_old : .Spawn bid1 ∈ H.behaviors parent := by
            by_cases h_parent : parent = b.bid
            · subst h_parent
              simpa [History.add_behavior_event] using h_mem1
            · simpa [History.add_behavior_event, h_parent] using h_mem1
          have h_mem2_old : .Run bid1 ∈ H.behaviors bid1 := by
            simpa [History.add_behavior_event, h_eq] using h_mem2
          have h_lt_old := h_wft.spawnRun parent bid1 h_mem1_old h_mem2_old
          simpa [t', h_eq] using h_lt_old
      case happensBefore =>
        intro c bid1 bid2 h_mem1 h_mem2 h_lt
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
            exact h_matches.pendingOrder bid1 b c h_mem1'' h_pending h_cmem
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
          exact h_wft.happensBefore c bid1 bid2 h_mem1' h_mem2' h_lt
    case hasTop =>
      exists top + 1
      intro e h_mem
      simp [History.events] at h_mem
      rcases h_mem with ⟨bid', h_mem⟩
      split at h_mem
      · next h_eq =>
        subst h_eq
        simp at h_mem
        cases h_mem with
        | inl h_mem =>
          by_cases h_eqe : e = .Run b.bid
          · subst h_eqe
            have h_fresh := h_matches.freshBehaviorHistory b.bid (.Run b.bid) h_mem
            simp [Event.fresh] at h_fresh
            simp [t']
          · simp [t', h_eqe]
            have h_mem' : e ∈ H.events := by
              simp [History.events]
              exists b.bid
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

lemma history_matches_preservation_run
  {t H top bid1 bs1 bs2 running b} :
    (t ⊢ H) →
    (∀e, e ∈ H.events → t e < top) →
    (∀c, c ∈ b.cowns → c ∉ running.flatMap Behavior.cowns) →
    (∀c, c ∈ b.cowns → c ∉ bs1.flatMap Behavior.cowns) →
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
    introv h_wf h_top h_no_running h_no_pending h_matches t'
    constructor
    case runningNotCompleted =>
      intro bid'
      constructor
      · intro h_new_running
        rcases h_new_running with ⟨br, h_mem_new, h_bid⟩
        simp at h_mem_new
        rcases h_mem_new with h_head | h_tail
        · have h_br_eq : br = b := by
            simpa using h_head
          subst h_br_eq
          subst h_bid
          constructor
          · simp [History.add_behavior_event]
          · intro h_comp_new
            have h_comp_old : .Complete br.bid ∈ H.behaviors br.bid := by
              simpa [History.add_behavior_event] using h_comp_new
            have h_pending : br ∈ bs1 ++ br :: bs2 := by simp
            have h_not_active := h_matches.completedNotActive br.bid h_comp_old
            exact (h_not_active.2 br h_pending) rfl
        · have h_old := (h_matches.runningNotCompleted bid').1 ⟨br, h_tail, h_bid⟩
          by_cases h_eq : bid' = b.bid
          · subst h_eq
            exfalso
            have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
            have h_no_run := h_matches.pendingNotRunning b h_pending
            exact h_no_run h_old.1
          · constructor
            · simpa [History.add_behavior_event, h_eq] using h_old.1
            · simpa [History.add_behavior_event, h_eq] using h_old.2
      · intro h_hist
        by_cases h_eq : bid' = b.bid
        · subst h_eq
          exact ⟨b, by simp, rfl⟩
        · have h_old_hist :
              Event.Run bid' ∈ H.behaviors bid' ∧
              Event.Complete bid' ∉ H.behaviors bid' := by
            constructor
            · simpa [History.add_behavior_event, h_eq] using h_hist.1
            · simpa [History.add_behavior_event, h_eq] using h_hist.2
          have h_old_running := (h_matches.runningNotCompleted bid').2 h_old_hist
          rcases h_old_running with ⟨br, h_mem_old, h_bid⟩
          exact ⟨br, by simp [h_mem_old], h_bid⟩
    case pendingNotRunning =>
      intro br hb_mem h_run
      have h_old_mem : br ∈ bs1 ++ b :: bs2 := by
        simp at hb_mem
        rcases hb_mem with hb1 | hb2
        · simp [hb1]
        · simp [hb2]
      have h_notrun_old := h_matches.pendingNotRunning br h_old_mem
      by_cases h_eq : br.bid = b.bid
      · have h_pw := h_matches.pendingTimestampOrder
        have h_pair :
            List.Pairwise (fun e1 e2 => t e1 < t e2)
              (bs1.map (fun b' => Event.Spawn b'.bid) ++
                (Event.Spawn b.bid :: bs2.map (fun b' => Event.Spawn b'.bid))) := by
          simpa [List.map_append] using h_pw
        simp at hb_mem
        rcases hb_mem with hb1 | hb2
        · have h_lt :=
            (List.pairwise_append.mp h_pair).2.2
              (Event.Spawn br.bid)
              (List.mem_map.mpr ⟨br, hb1, rfl⟩)
              (Event.Spawn b.bid)
              (by simp)
          rw [h_eq] at h_lt
          exact False.elim (Nat.lt_irrefl _ h_lt)
        · have h_mid_pair :
            List.Pairwise (fun e1 e2 => t e1 < t e2)
              ([Event.Spawn b.bid] ++ bs2.map (fun b' => Event.Spawn b'.bid)) := by
            simpa using (List.pairwise_append.mp h_pair).2.1
          have h_head_mem : Event.Spawn b.bid ∈ [Event.Spawn b.bid] := by
            simp
          have h_tail_mem : Event.Spawn br.bid ∈ bs2.map (fun b' => Event.Spawn b'.bid) := by
            exact List.mem_map.mpr ⟨br, hb2, rfl⟩
          have h_lt :=
            (List.pairwise_append.mp h_mid_pair).2.2
              (Event.Spawn b.bid)
              h_head_mem
              (Event.Spawn br.bid)
              h_tail_mem
          rw [h_eq] at h_lt
          exact False.elim (Nat.lt_irrefl _ h_lt)
      · have h_run_old : Event.Run br.bid ∈ H.behaviors br.bid := by
          simpa [History.add_behavior_event, h_eq] using h_run
        exact h_notrun_old h_run_old
    case pendingSpawned =>
      intro br hb_mem
      have h_old_mem : br ∈ bs1 ++ b :: bs2 := by
        simp at hb_mem
        rcases hb_mem with hb1 | hb2
        · simp [hb1]
        · simp [hb2]
      rcases h_matches.pendingSpawned br h_old_mem with ⟨parent, h_spawn_old⟩
      refine ⟨parent, ?_⟩
      by_cases h_parent : parent = b.bid
      · subst h_parent
        have h_spawn_new : Event.Spawn br.bid ∈ H.behaviors b.bid ++ [Event.Run b.bid] := by
          exact List.mem_append.mpr (Or.inl h_spawn_old)
        simpa [History.add_behavior_event] using h_spawn_new
      · simpa [History.add_behavior_event, h_parent] using h_spawn_old
    case spawnedDisposition =>
      intro parent child h_spawn
      have h_spawn_old : Event.Spawn child ∈ H.behaviors parent := by
        by_cases h_parent : parent = b.bid
        · subst h_parent
          have h_spawn_new : Event.Spawn child ∈ H.behaviors b.bid ++ [Event.Run b.bid] := by
            simpa [History.add_behavior_event] using h_spawn
          exact (List.mem_append.mp h_spawn_new).elim id (by
            intro h_new
            simp at h_new)
        · simpa [History.add_behavior_event, h_parent] using h_spawn
      rcases h_matches.spawnedDisposition parent child h_spawn_old with h_pend | h_run | h_comp
      · rcases h_pend with ⟨br, hbr_mem, hbr_bid⟩
        simp at hbr_mem
        rcases hbr_mem with hb1 | hbmid | hb2
        · left
          exact ⟨br, by simp [hb1], hbr_bid⟩
        · subst hbmid
          right
          left
          exact ⟨br, by simp, hbr_bid⟩
        · left
          exact ⟨br, by simp [hb2], hbr_bid⟩
      · right
        left
        rcases h_run with ⟨br, hbr_mem, hbr_bid⟩
        exact ⟨br, by simp [hbr_mem], hbr_bid⟩
      · right
        right
        by_cases h_child : child = b.bid
        · subst h_child
          simp [History.add_behavior_event]
          exact h_comp
        · simpa [History.add_behavior_event, h_child] using h_comp
    case completedNotActive =>
      intro bid' h_comp
      have h_comp_old : Event.Complete bid' ∈ H.behaviors bid' := by
        by_cases h_eq : bid' = b.bid
        · subst h_eq
          simpa [History.add_behavior_event] using h_comp
        · simpa [History.add_behavior_event, h_eq] using h_comp
      have h_completed_old := h_matches.completedNotActive bid' h_comp_old
      constructor
      · intro br hbr_mem
        simp at hbr_mem
        rcases hbr_mem with h_head | h_tail
        · subst h_head
          exact h_completed_old.2 br (by simp)
        · exact h_completed_old.1 br h_tail
      · intro br hbr_mem
        have h_old_mem : br ∈ bs1 ++ b :: bs2 := by
          simp at hbr_mem
          rcases hbr_mem with hb1 | hb2
          · simp [hb1]
          · simp [hb2]
        exact h_completed_old.2 br h_old_mem
    case cownRunning =>
      intro bid' c
      constructor
      · intro h_new_running
        rcases h_new_running with ⟨br, hbr_mem, hbr_bid, h_c_mem⟩
        simp at hbr_mem
        rcases hbr_mem with h_head | h_tail
        · subst h_head
          subst hbr_bid
          constructor
          · by_cases h_c_in : c ∈ br.cowns
            · simp [History.add_cown_event, h_c_in]
            · exact False.elim (h_c_in h_c_mem)
          · intro h_comp_new
            have h_comp_old : Event.Complete br.bid ∈ H.cowns c := by
              by_cases h_c_in : c ∈ br.cowns
              · simpa [History.add_cown_event, h_c_in] using h_comp_new
              · exact False.elim (h_c_in h_c_mem)
            have ⟨owner, h_comp_beh⟩ := h_wf.cownEvent c (Event.Complete br.bid) h_comp_old
            have h_owner_eq : owner = br.bid :=
              wf_history_complete_mem_inv (h_wf.behaviorWf owner) h_comp_beh
            subst h_owner_eq
            exact (h_matches.completedNotActive br.bid h_comp_beh).2 br (by simp) rfl
        · have h_old_running :
            ∃ br ∈ running, br.bid = bid' ∧ c ∈ br.cowns := by
            exact ⟨br, h_tail, hbr_bid, h_c_mem⟩
          have h_old := (h_matches.cownRunning bid' c).1 h_old_running
          by_cases h_c_in : c ∈ b.cowns
          · have h_old_mem : c ∈ running.flatMap Behavior.cowns := by
              exact List.mem_flatMap.mpr ⟨br, h_tail, h_c_mem⟩
            exact False.elim ((h_no_running c h_c_in) h_old_mem)
          · simpa [History.add_cown_event, h_c_in] using h_old
      · intro h_hist
        by_cases h_eq : bid' = b.bid
        · subst h_eq
          by_cases h_c_in : c ∈ b.cowns
          · exact ⟨b, by simp, rfl, h_c_in⟩
          · have h_old_hist :
              Event.Run b.bid ∈ H.cowns c ∧ Event.Complete b.bid ∉ H.cowns c := by
              constructor
              · simpa [History.add_cown_event, h_c_in] using h_hist.1
              · simpa [History.add_cown_event, h_c_in] using h_hist.2
            have h_old_running := (h_matches.cownRunning b.bid c).2 h_old_hist
            rcases h_old_running with ⟨br, hbr_mem, hbr_bid, h_c_mem⟩
            have h_run_old : Event.Run b.bid ∈ H.behaviors b.bid :=
              (h_matches.runningNotCompleted b.bid).1 ⟨br, hbr_mem, hbr_bid⟩ |>.1
            exact False.elim ((h_matches.pendingNotRunning b (by simp)) h_run_old)
        · have h_old_hist :
            Event.Run bid' ∈ H.cowns c ∧ Event.Complete bid' ∉ H.cowns c := by
            constructor
            · by_cases h_c_in : c ∈ b.cowns
              · simpa [History.add_cown_event, h_c_in, h_eq] using h_hist.1
              · simpa [History.add_cown_event, h_c_in] using h_hist.1
            · by_cases h_c_in : c ∈ b.cowns
              · simpa [History.add_cown_event, h_c_in, h_eq] using h_hist.2
              · simpa [History.add_cown_event, h_c_in] using h_hist.2
          have h_old_running := (h_matches.cownRunning bid' c).2 h_old_hist
          rcases h_old_running with ⟨br, hbr_mem, hbr_bid, h_c_mem⟩
          exact ⟨br, by simp [hbr_mem], hbr_bid, h_c_mem⟩
    case spawnOnCown =>
      intro c bid h_run
      have h_run_cases : Event.Run bid ∈ H.cowns c ∨ bid = b.bid := by
        by_cases h_c : c ∈ b.cowns
        · have h_mem : Event.Run bid ∈ H.cowns c ++ [Event.Run b.bid] := by
            simpa [History.add_cown_event, h_c] using h_run
          rcases List.mem_append.mp h_mem with h_old | h_new
          · exact Or.inl h_old
          · have h_eq_events : Event.Run bid = Event.Run b.bid := by
              simpa using h_new
            injection h_eq_events with h_eq_bid
            exact Or.inr h_eq_bid
        · have h_old : Event.Run bid ∈ H.cowns c := by
            simpa [History.add_cown_event, h_c] using h_run
          exact Or.inl h_old
      rcases h_run_cases with h_run_old | h_eq_bid
      · rcases h_matches.spawnOnCown c bid h_run_old with ⟨parent, h_spawn_old⟩
        refine ⟨parent, ?_⟩
        by_cases h_parent : parent = b.bid
        · subst h_parent
          have h_spawn_new : Event.Spawn bid ∈ H.behaviors b.bid ++ [Event.Run b.bid] := by
            exact List.mem_append.mpr (Or.inl h_spawn_old)
          simpa [History.add_behavior_event] using h_spawn_new
        · simpa [History.add_behavior_event, h_parent] using h_spawn_old
      · subst h_eq_bid
        have h_pending : b ∈ bs1 ++ b :: bs2 := by simp
        rcases h_matches.pendingSpawned b h_pending with ⟨parent, h_spawn_old⟩
        refine ⟨parent, ?_⟩
        by_cases h_parent : parent = b.bid
        · subst h_parent
          have h_spawn_new : Event.Spawn b.bid ∈ H.behaviors b.bid ++ [Event.Run b.bid] := by
            exact List.mem_append.mpr (Or.inl h_spawn_old)
          simpa [History.add_behavior_event] using h_spawn_new
        · simpa [History.add_behavior_event, h_parent] using h_spawn_old
    case freshBehaviorHistory =>
      intro bid' e h_mem
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
    case freshCownHistory =>
      intro c e h_mem
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
    case pendingTimestampOrder =>
      apply List.pairwise_map.mpr
      simp [t']
      have h_pw := h_matches.pendingTimestampOrder
      grind
    case pendingOrder =>
      intro bid1 b2 c h_run hb_mem h_c_mem
      have h_old_pending : b2 ∈ bs1 ++ b :: bs2 := by
        simp at hb_mem
        rcases hb_mem with hb1 | hb2
        · simp [hb1]
        · simp [hb2]
      simp [t']
      by_cases h_c_in : c ∈ b.cowns
      · have h_run_cases : Event.Run bid1 ∈ H.cowns c ∨ bid1 = b.bid := by
          simpa [History.add_cown_event, h_c_in] using h_run
        rcases h_run_cases with h_run_old | h_eq
        · exact h_matches.pendingOrder bid1 b2 c h_run_old h_old_pending h_c_mem
        · subst h_eq
          simp at hb_mem
          rcases hb_mem with hb1 | hb2
          · have h_bs1_mem : c ∈ bs1.flatMap Behavior.cowns := by
              exact List.mem_flatMap.mpr ⟨b2, hb1, h_c_mem⟩
            exact False.elim ((h_no_pending c h_c_in) h_bs1_mem)
          · have h_pw_old := h_matches.pendingTimestampOrder
            have h_pair :
                List.Pairwise (fun e1 e2 => t e1 < t e2)
                  (bs1.map (fun b' => Event.Spawn b'.bid) ++
                    (Event.Spawn b.bid :: bs2.map (fun b' => Event.Spawn b'.bid))) := by
              simpa [List.map_append] using h_pw_old
            have h_mid_pair :
                List.Pairwise (fun e1 e2 => t e1 < t e2)
                  ([Event.Spawn b.bid] ++ bs2.map (fun b' => Event.Spawn b'.bid)) := by
              simpa using (List.pairwise_append.mp h_pair).2.1
            have h_lt :=
              (List.pairwise_append.mp h_mid_pair).2.2
                (Event.Spawn b.bid)
                (by simp)
                (Event.Spawn b2.bid)
                (List.mem_map.mpr ⟨b2, hb2, rfl⟩)
            simpa using h_lt
      · have h_run_old : Event.Run bid1 ∈ H.cowns c := by
          simpa [History.add_cown_event, h_c_in] using h_run
        exact h_matches.pendingOrder bid1 b2 c h_run_old h_old_pending h_c_mem

lemma cfg_wf_preservation_run
    {H t bid1 running bs1 bs2 b} :
    HistoryMatchesCfg H t
      { fresh := bid1,
        running,
        pending := bs1 ++ b :: bs2 } →
    CfgWf
      { fresh := bid1,
        running,
        pending := bs1 ++ b :: bs2 } →
    CfgWf
      { fresh := bid1,
        running := b :: running,
        pending := bs1 ++ bs2 } :=
  by
    intro h_matches h_cfgwf
    refine ⟨?_, ?_⟩
    · rcases h_cfgwf.freshness with ⟨h_running_fresh, h_pending_fresh⟩
      constructor
      · intro br hbr_mem
        simp at hbr_mem
        rcases hbr_mem with h_head | h_tail
        · subst h_head
          have h_pending : br ∈ bs1 ++ br :: bs2 := by simp
          exact h_pending_fresh br h_pending
        · exact h_running_fresh br h_tail
      · intro br hbr_mem
        have h_old_mem : br ∈ bs1 ++ b :: bs2 := by
          simp at hbr_mem
          rcases hbr_mem with hb1 | hb2
          · simp [hb1]
          · simp [hb2]
        exact h_pending_fresh br h_old_mem
    · have h_old_nodup := h_cfgwf.runningNoDupsByBid
      -- Prove no-dup for b :: running by using matches to show b.bid ∉ running.map bid
      have h_b_not_running : ∀br ∈ running, b.bid ≠ br.bid := by
        intro br hbr_mem
        have h_b_pending : b ∈ bs1 ++ b :: bs2 := by simp
        have h_run_pending := h_matches.pendingNotRunning b h_b_pending
        have h_run_br := (h_matches.runningNotCompleted br.bid).1 ⟨br, hbr_mem, rfl⟩
        intro h_eq
        have h_run_b : Event.Run b.bid ∈ H.behaviors b.bid := by
          simpa [h_eq] using h_run_br.1
        exact h_run_pending h_run_b
      simp only [List.map_cons]
      refine List.Pairwise.cons ?_ h_old_nodup
      intro bid' hbid_mem
      rcases List.mem_map.mp hbid_mem with ⟨br, hbr_mem, h_eq⟩
      subst h_eq
      exact h_b_not_running br hbr_mem

theorem wf_preservation {cfg cfg' H H'} {t : Event → Nat} :
    ((cfg, H) ⇒ (cfg', H')) →
    CfgHistoryInv H t cfg →
    (t ⊢ H) →
    ∃t', (t' ⊢ H') ∧ CfgHistoryInv H' t' cfg' :=
  by
    intro h_step h_inv h_wf
    have ⟨top, h_top⟩ := history_wf_has_top h_wf
    cases h_step with
    | @Spawn fresh bid bs1 bs2 cs cs' s s' s'' pending h_step =>
      have h_matches := h_inv.historyMatches
      have h_cfgwf := h_inv.cfgWf
      let t' := fun e => if e = .Spawn fresh then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_spawn h_wf h_top h_matches
      · have h_matches' : HistoryMatchesCfg (H[bid += Event.Spawn fresh]) t'
            { fresh := fresh + 1,
              running := bs1 ++ { bid := bid, cowns := cs, stmt := s' } :: bs2,
              pending := pending ++ [{ bid := fresh, cowns := cs', stmt := s'' }] } :=
          history_matches_preservation_spawn h_wf h_top h_matches
        have h_cfgwf' : CfgWf
            { fresh := fresh + 1,
              running := bs1 ++ { bid := bid, cowns := cs, stmt := s' } :: bs2,
              pending := pending ++ [{ bid := fresh, cowns := cs', stmt := s'' }] } :=
          cfg_wf_preservation_spawn h_cfgwf
        exact ⟨h_matches', h_cfgwf'⟩
    | @Complete bid1 bs1 bs2 bid cs pending =>
      have h_matches := h_inv.historyMatches
      have h_cfgwf := h_inv.cfgWf
      let t' := fun e => if e = .Complete bid then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_complete h_wf h_top h_cfgwf h_matches
      · have h_matches' := history_matches_preservation_complete h_wf h_top h_cfgwf h_matches
        have h_cfgwf' := cfg_wf_preservation_complete h_cfgwf
        exact ⟨h_matches', h_cfgwf'⟩
    | @Run bid1 running bs1 bs2 b _ h_no_running h_no_pending =>
      have h_matches := h_inv.historyMatches
      have h_cfgwf := h_inv.cfgWf
      let t' := fun e => if e = .Run b.bid then top else t e
      exists t'
      refine ⟨?_, ?_⟩
      · exact wf_history_preservation_run h_wf h_top h_no_running h_no_pending h_matches
      · have h_matches' :=
          history_matches_preservation_run h_wf h_top h_no_running h_no_pending h_matches
        have h_cfgwf' := cfg_wf_preservation_run h_matches h_cfgwf
        exact ⟨h_matches', h_cfgwf'⟩

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
      have := h_running bid h_in
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

theorem starting_cfg_wf {s} :
    let H : History := {behaviors := fun bid => if bid = 0 then [.Run 0] else [],
                        cowns := fun _ => []}
    let t : Event → Nat := (fun _ => 0)
    (t ⊢ H) ∧
    CfgHistoryInv H t
      { fresh := 1,
        running := [{bid := 0, cowns := [], stmt := s}],
        pending := [] } :=
  by
    intros H t
    refine ⟨?_, ?_⟩
    · simp [H, t]
      constructor <;> try simp [wf_behavior_history, unique_spawns, wf_cown_history] <;> try grind
      · intro bid
        by_cases h_eq : bid = 0
        · subst h_eq
          simp [wf_behavior_history_tail]
        · simp [h_eq]
      · constructor <;> try solve | simp
        case behaviorAdj =>
          intro bid e1 e2 h_infix
          by_cases h_eq : bid = 0
          · subst h_eq
            rcases h_infix with ⟨init, tail, h_eq⟩
            cases init <;> cases tail <;> simp at h_eq
          · simp [h_eq] at h_infix
      · exists 1
        simp
    · simp [H, t]
      constructor
      · constructor <;> try simp <;> grind
      · constructor <;> try simp [CfgFreshness]

end ConcurrentSemantics
