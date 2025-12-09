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
inductive StepBehavior : Stmt → Stmt × (List Cown × Stmt) → Prop where
| When {cowns body cont} :
    StepBehavior (Stmt.seq cowns body cont)
                 (cont, (cowns, body))

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
| Spawn {fresh bs1 bs2 bid cowns cowns' s s' s'' pending H} :
    StepBehavior s (s', (cowns', s'')) →
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, s⟩ :: bs2, pending⟩, H)
            (⟨fresh + 1, bs1 ++ ⟨bid, cowns, s'⟩ :: bs2, pending ++ [⟨fresh, cowns', s''⟩]⟩,
              (H[bid += Event.Spawn bid]))
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
                    (pending ++ [⟨fresh, cowns', body⟩])⟩, H[bid += Event.Spawn bid]
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
  -- Pending behaviors have been spComplete
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

theorem step_cfg_preserves_history_wf {cfg cfg' H H'} :
    ((cfg, H) ⇒ (cfg', H')) →
    (H ⊢ cfg) →
    (⊢ H) →
    (⊢ H') :=
  by
    intro h_step h_model h_wf
    rcases cfg with ⟨fresh, running, pending⟩
    rcases cfg' with ⟨fresh', running', pending'⟩
    sorry

theorem step_cfg_preserves_matching_history {cfg cfg' H H'} :
    ((cfg, H) ⇒ (cfg', H')) →
    (H ⊢ cfg) →
    (⊢ H) →
    (H' ⊢ cfg') :=
  by
    intro h_step h_model h_wf
    rcases cfg with ⟨fresh, running, pending⟩
    rcases cfg' with ⟨fresh', running', pending'⟩
    sorry

theorem cfg_done_history_complete {cfg H} :
    cfg_done cfg →
    (H ⊢ cfg) →
    (⊢ H) →
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
      rcases h_wf with ⟨h_wf_bs, _, _, _, _⟩
      have h_wf_b := h_wf_bs bid2
      let b_hist := H.behaviors bid2
      have h_eq : b_hist = H.behaviors bid2 := by rfl
      rw [← h_eq] at h_complete
      rw [← h_eq] at h_wf_b
      rw [← h_eq]
      rcases (b_hist) with _ | ⟨e, es⟩ <;> try grind
      simp at h_wf_b
      rcases e <;> try grind

end ConcurrentSemantics
