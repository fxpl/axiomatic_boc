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

inductive StepBehavior : Stmt → Stmt × (List Cown × Stmt) → Prop where
| When {cowns body cont} :
    StepBehavior (Stmt.seq cowns body cont)
                 (cont, (cowns, body))

notation s "~>" s' "|" res => StepBehavior s (s', res)

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
    (s ~> s' | (cowns', s'')) →
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, s⟩ :: bs2, pending⟩, H)
            (⟨fresh + 1, bs1 ++ (⟨bid, cowns, s'⟩ :: bs2), pending ++ [⟨fresh, cowns', s''⟩]⟩, (H[bid += Event.Spawn bid]))
| Commit {fresh bs1 bs2 bid} {cowns : List Cown} {pending H} :
    StepCfg (⟨fresh, bs1 ++ ⟨bid, cowns, Stmt.done⟩ :: bs2, pending⟩, H)
    (⟨fresh, bs1 ++ bs2, pending⟩, (H[bid += Event.Commit bid][cowns += Event.Commit bid]))
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
    | @Commit _ bs1 bs2 bid cowns =>
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
          exists ⟨fresh, b::[], [] ++ pending'⟩, H[b.bid += Event.Run b.bid][b.cowns += Event.Run b.bid]
          rw [← List.nil_append ({ bid := b.bid, cowns := b.cowns, stmt := b.stmt } :: pending')]
          apply StepCfg.Run <;> simp
      | cons b running' =>
        right
        cases b with
        | mk bid cowns stmt =>
          cases stmt with
          | done =>
            exists ⟨fresh, running', pending⟩, H[bid += Event.Commit bid][cowns += Event.Commit bid]
            rw [← List.nil_append ({ bid := bid, cowns := cowns, stmt := Stmt.done } :: running')]
            apply StepCfg.Commit
          | seq cowns' body cont =>
            exists ⟨fresh + 1, ([] ++ ⟨bid, cowns, cont⟩ :: running'), (pending ++ [⟨fresh, cowns', body⟩])⟩, H[bid += Event.Spawn bid]
            rw [← List.nil_append ({ bid := bid, cowns := cowns, stmt := Stmt.seq cowns' body cont } :: running')]
            have h_eq2 : (pending ++ [⟨fresh, cowns', body⟩]) = (pending ++ [⟨fresh, cowns', body⟩]) := by rfl
            rw [h_eq2]
            clear h_eq2
            apply StepCfg.Spawn
            apply StepBehavior.When

def HistoryMatchesCfg (H : History) : Cfg → Prop
| ⟨fresh, running, pending⟩ =>
  -- All running behaviors have started but not completed
  (∀b, b ∈ running ↔ (Event.Run b.bid ∈ H.behaviors b.bid ∧ Event.Commit b.bid ∉ H.behaviors b.bid)) ∧
  -- All pending behaviors have not started
  (∀b ∈ pending, Event.Run b.bid ∉ H.behaviors b.bid) ∧
  -- Completed behaviors are not in running or pending
  (∀bid,
    Event.Commit bid ∈ H.behaviors bid →
    (∀b ∈ running, b.bid ≠ bid) ∧
    (∀b ∈ pending, b.bid ≠ bid)) ∧
  -- Currently aquired cowns are held by running behaviors
  (∀b c,
    (b ∈ running ∧ c ∈ b.cowns) ↔
    (Event.Run b.bid ∈ H.cowns c ∧ Event.Commit b.bid ∉ H.cowns c)) ∧
  -- All events in the history are smaller than fresh
  (∀bid e,
    e ∈ H.behaviors bid →
    Event.fresh fresh e) ∧
  (∀c e,
    e ∈ H.cowns c →
    Event.fresh fresh e)

notation H " ⊢ " cfg => HistoryMatchesCfg H cfg

inductive ReflTransStepCfg : Cfg × History → Cfg × History → Prop where
| Refl {cfg H} : ReflTransStepCfg (cfg, H) (cfg, H)
| Trans {cfg1 cfg2 cfg3 H1 H2 H3} :
    ((cfg1, H1) ⇒ (cfg2, H2)) →
    ReflTransStepCfg (cfg2, H2) (cfg3, H3) →
    ReflTransStepCfg (cfg1, H1) (cfg3, H3)
notation cfg " ⇒⋆ " cfg' => ReflTransStepCfg cfg cfg'

end ConcurrentSemantics
