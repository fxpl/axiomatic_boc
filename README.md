# An Axiomatic Model for Behaviour-Oriented Concurrency

This repo contains the Lean mechanisation accompanying the paper "When Behaviours Have to Happen: An Axiomatic Model of Causality in Behaviour-Oriented Concurrency" (under submission).
The mechanisation relies on MathLib for relations and sets.
Below is a table containing the mapping from the paper definitions to the corresponding mechanisation.

| In the paper | In the mechanisation |
| ------------ | -------------------- |
| BId ($i$)    | [`def BId`](BoC/Common.lean) |
| CId ($c$)    | [`def Cown`](BoC/Common.lean) |
| Events ($S_i$/$R_i$/$C_i$) | [`inductive Event`](BoC/History.lean) |
| Definition 4 (Structure of BoC executions) | [`structure Execution`](BoC/Model.lean) (A) |
| Definition 5 (Derived relations) | [`def derived_run_relation` and `def derived_co_any`](BoC/Model.lean) (B) |
| Definition 6 (Cowns) | [`let cowns bid := ...`](BoC/Model.lean) |
| Definition 7 (Happens-before) | [`def derived_hb_relation`](BoC/Model.lean) |
| Definition 8 (Valid execution) | [structure Execution.valid](Boc/Model.lean) (C) |
| $H$ (Figure 8) | [`structure History`](BoC/History.lean) |
| $s$ (Figure 8) | [`inductive Stmt`](BoC/Semantics.lean) |
| $b$ (Figure 8) | [`structure Behavior`](BoC/Semantics.lean) |
| $cfg$ (Figure 8) | [`structure Cfg`](BoC/Semantics.lean) |
| Figure 9 | [`inductive StepBehavior` and `inductive StepCfg`](BoC/Semantics.lean) |
| $\vdash_b$ (Figure 10) | [`def wf_behavior_history`](BoC/History.lean) |
| $\vdash_c$ (Figure 10) | [`def wf_cown_history`](BoC/History.lean) |
| Definition 10 (Well-timed history) | [`structure History.timestamp_wf`](BoC/History.lean) |
| Definition 11 (Well-formed history) | [`structure History.wf`](BoC/History.lean) |
| Definition 12 (Translation to axiomatic model) | [`def model_from_history`](BoC/Model.lean) |
| Theorem 13 (Translation soundness) | [`theorem model_from_history_valid`](BoC/Model.lean) |
| Definition 14 (Matching history) | [`structure CfgHistoryInv`](BoC/Semantics.lean) (D) |
| Theorem 15 (Preservation of well-formed and matching histories) | [`theorem wf_preservation`](BoC/Semantics.lean) |

- (A) Items 5 and 6 are defined as part of `wf_po_relation` and `wf_co_relation` respectively, which are included in `Execution.valid`.
- (B) The $\text{co}_c$ relation is expressed as a partial application of $\text{co}$.
- (C) Items 1 (po part), 2, 3, 4 and 5 are defined as part of `wf_po_relation`.
      Items 1 (co part), 6 and 7 are defined as part of `wf_co_relation`
- (D) Item 1 is expressed as pairwise inequality in `cfgWf`. Remaining items are in `historyMatches`

TODO: Complete stuff
TODO: Freshness stuff
