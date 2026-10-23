/-
  ThesePlanetaire/FlowAdmission.lean
  Item 4 (P1) — Bridge DualDAG v2 → WFA framework.

  Connects the coupled_operator (screening mechanism) to the WFA formalism.
  The futureGatedWFA encodes the test-and-keep admission process as a
  weighted automaton, where the admission test uses the iterated
  contextual_fixpoint (not a single Φ step as in clearingToWFA).

  Architectural note:
  DualDAG v2 = SCREENING (binary admit/reject, O(|E|²)).
  The screening output feeds an Eisenberg-Noe CLEARING (continuous payments).
  futureGatedWFA encodes the screening layer as a WFA.

  RCF connection (plan §8.1.3):
  Each letter in the WFA alphabet = an edge (potential transaction).
  The transition test (isAdmissible) = the RCF auxiliary constraint:
  vertex_load demands S e.1 ≤ pool.holdings e.1.
  Agents freely choose which edges to include (opt-in at regexp level).

  Références :
  — Eisenberg-Noe 2001 (Management Science 47(2))
  — Bech & Soramäki 2001 (Bank of Finland DP 9/2001) — validation RTGS
-/

import ThesePlanetaire.DualDAG
import ThesePlanetaire.ClearingWFA
import ThesePlanetaire.welfare_gc_condition

namespace FlowAdmission

open DualDAG Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. coupled_operator as ClearingReduction -/

theorem coupled_clearing_reduction (pool : FuturePool V) (demands : V × V → ℤ) :
    IsClearingReduction (coupled_operator pool demands) :=
  ⟨coupled_operator_contractive pool demands⟩

/-! ### 2. Properties of contextual_fixpoint -/

private lemma descending_chain_le_init (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) (n : ℕ) :
    descending_chain pool demands init n ⊆ init := by
  induction n with
  | zero => exact Subset.refl _
  | succ n ih => exact (descending_chain_antimono pool demands init n).trans ih

theorem contextual_fixpoint_subset (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) :
    contextual_fixpoint pool demands S e ⊆ S ∪ {e} :=
  descending_chain_le_init pool demands (S ∪ {e}) (S ∪ {e}).card

theorem contextual_fixpoint_is_fixed (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) :
    coupled_operator pool demands (contextual_fixpoint pool demands S e) =
    contextual_fixpoint pool demands S e :=
  descending_chain_at_card_fixpoint pool demands (S ∪ {e})

theorem contextual_fixpoint_satisfies_budget (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) :
    ∀ e' ∈ contextual_fixpoint pool demands S e,
      vertex_load demands (contextual_fixpoint pool demands S e) e'.1 ≤
        pool.holdings e'.1 :=
  fixpoint_satisfies_budget pool demands _ (contextual_fixpoint_is_fixed pool demands S e)

/-! ### 3. futureGatedWFA: test-and-keep admission WFA

  The WFA uses isAdmissible (which internally iterates contextual_fixpoint)
  for the admission test, with test-and-keep state tracking: admitted edges
  are never revoked from the current state.

  This differs from clearingToWFA (ClearingWFA.lean:38) which uses a single
  Φ step as transition. The iterated fixpoint is necessary because
  coupled_operator is CONTRACTIVE (not monotone) — a single step may not
  reach the fixed point.

  Note on test-and-keep vs exact clearing:
  The exact clearing semantics (contextual_fixpoint as state) can EVICT
  previously admitted edges. Example on Fin 3, holdings(0)=5, demands 3/4:
  admissionFold [e₁,e₂] = {e₁}, but contextual_fixpoint {e₁} e₂ = ∅.
  Test-and-keep matches the economic model: cleared transactions are final. -/

def futureGatedWFA (pool : FuturePool V) (demands : V × V → ℤ) :
    WeightedAutomaton Bool (V × V) (ActivationState V) where
  init S := decide (S = ∅)
  trans S e T := decide (T = if isAdmissible pool demands S e then S ∪ {e} else S)
  final _ := true

/-! ### 4. Determinism and structural properties -/

theorem futureGatedWFA_deterministic (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) :
    ∃! T, (futureGatedWFA pool demands).trans S e T = true := by
  use if isAdmissible pool demands S e then S ∪ {e} else S
  refine ⟨?_, fun T hT => ?_⟩
  · show decide _ = true
    simp
  · exact decide_eq_true_eq.mp hT

theorem futureGatedWFA_init_unique (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) :
    (futureGatedWFA pool demands).init S = true ↔ S = ∅ := by
  simp [futureGatedWFA]

theorem futureGatedWFA_trans_admitted (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V)
    (h : isAdmissible pool demands S e) :
    (futureGatedWFA pool demands).trans S e (S ∪ {e}) = true := by
  change decide (S ∪ {e} = if isAdmissible pool demands S e then S ∪ {e} else S) = true
  rw [if_pos h]
  exact decide_eq_true_eq.mpr rfl

theorem futureGatedWFA_trans_rejected (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V)
    (h : ¬ isAdmissible pool demands S e) :
    (futureGatedWFA pool demands).trans S e S = true := by
  change decide (S = if isAdmissible pool demands S e then S ∪ {e} else S) = true
  rw [if_neg h]
  exact decide_eq_true_eq.mpr rfl

/-! ### 5. Word-level bridge: admissionFold = unique WFA execution

  The substance of the bridge: starting from ∅, the WFA reaches
  admissionFold w after processing word w. Proven by induction on w,
  composing per-step transitions via trans = true. Combined with
  determinism (futureGatedWFA_deterministic), this means admissionFold
  is THE unique WFA execution.

  The crossing from relational to functional:
  - Relational: WFAReaches builds a chain S₀ →[e₁] S₁ →... →[eₙ] Sₙ
    where each step satisfies trans ... = true
  - Functional: Sₙ = admissionFold pool demands [e₁, ..., eₙ]
  The induction step uses trans_admitted/trans_rejected. -/

theorem admissionFold_step_valid (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) :
    (futureGatedWFA pool demands).trans S e
      (if isAdmissible pool demands S e then S ∪ {e} else S) = true := by
  by_cases h : isAdmissible pool demands S e
  · rw [if_pos h]; exact futureGatedWFA_trans_admitted pool demands S e h
  · rw [if_neg h]; exact futureGatedWFA_trans_rejected pool demands S e h

inductive WFAReaches (wfa : WeightedAutomaton Bool (V × V) (ActivationState V)) :
    ActivationState V → List (V × V) → ActivationState V → Prop where
  | nil (S : ActivationState V) : WFAReaches wfa S [] S
  | step (S : ActivationState V) (e : V × V) (T : ActivationState V)
    (w : List (V × V)) (U : ActivationState V)
    (h_trans : wfa.trans S e T = true) (h_rest : WFAReaches wfa T w U) :
    WFAReaches wfa S (e :: w) U

private theorem wfa_reaches_fold (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (w : List (V × V)) :
    WFAReaches (futureGatedWFA pool demands) S w
      (w.foldl (fun cur e =>
        if isAdmissible pool demands cur e then cur ∪ {e} else cur) S) := by
  induction w generalizing S with
  | nil => exact WFAReaches.nil S
  | cons e es ih =>
    let T := if isAdmissible pool demands S e then S ∪ {e} else S
    exact WFAReaches.step S e T es _
      (admissionFold_step_valid pool demands S e) (ih T)

theorem admissionFold_wfa_terminal (pool : FuturePool V) (demands : V × V → ℤ)
    (w : List (V × V)) :
    (futureGatedWFA pool demands).init ∅ = true ∧
    WFAReaches (futureGatedWFA pool demands) ∅ w (admissionFold pool demands w) :=
  ⟨by simp [futureGatedWFA], wfa_reaches_fold pool demands ∅ w⟩

end FlowAdmission
