/-
  ThesePlanetaire/CommutativeClassification.lean
  Item 2.1 (P1) — Derive Parikh class from dynamics commutativity.

  Layer 1 (general theorems, Status A):
  - IsCommutativeUpdate: update function commutes (≡ RightCommutative)
  - commutative_implies_perm_invariant: commutativity → foldl invariant under permutation
  - noncommutative_implies_order_sensitive: ¬ commutative → ∃ permutation with different results

  Layer 2 (instantiations, Status B — calibration choices):
  - co2_dynamics: additive stock accumulation (commutative → k=0)
  - cocktail_dynamics: toxicity threshold (non-commutative → k≥1)

  The key insight: IsCommutativeUpdate is a property of the dynamics FUNCTION,
  not a label on the planetary boundary. The general theorems are independent
  of parikhClass. The instantiations (which dynamics to assign to which
  boundary) remain calibration choices — honest Status B.

  The parikhClass bridge is deliberately left as calibration, not a Lean
  theorem: parikhClass is a hardcoded match with no link to dynamics
  functions, so any "coherence axiom" would violate the 0-axiom invariant.

  Responds to Challenge E (Parikh = table): the general framework transforms
  a hardcoded match into a derivable property of the dynamics.

  Références :
  — Parikh 1966, J. ACM 13(4) (commutative images of context-free languages are
    semilinear; a fortiori regular ones)
  — Hoffmann 2022 (arXiv:2109.02743, commutative ⇒ poly for constraint languages)
-/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CommutativeClassification

variable {σ α : Type*}

/-! ### Layer 1: General theorems (Status A) -/

/-- A state-transition function commutes: applying actions a then b gives
    the same result as b then a, regardless of the starting state.
    Equivalent to Mathlib's RightCommutative. -/
def IsCommutativeUpdate (f : σ → α → σ) : Prop :=
  ∀ s a b, f (f s a) b = f (f s b) a

/-- Commutative update ⟹ foldl is permutation-invariant.
    Two sequences of actions with the same multiset produce the same final state.
    Delegates to Mathlib's Perm.foldl_eq via the RightCommutative bridge. -/
theorem commutative_implies_perm_invariant {f : σ → α → σ}
    (h : IsCommutativeUpdate f)
    {w₁ w₂ : List α} (hp : w₁.Perm w₂) (s : σ) :
    w₁.foldl f s = w₂.foldl f s := by
  haveI : RightCommutative f := ⟨fun s a b => h s a b⟩
  exact hp.foldl_eq s

/-- Contrapositive: non-commutative ⟹ ∃ two permutations with different results.
    Witnesses: w₁ = [a, b], w₂ = [b, a] from the commutativity failure. -/
theorem noncommutative_implies_order_sensitive {f : σ → α → σ}
    (h : ¬ IsCommutativeUpdate f) :
    ∃ (s : σ) (w₁ w₂ : List α), w₁.Perm w₂ ∧ w₁.foldl f s ≠ w₂.foldl f s := by
  unfold IsCommutativeUpdate at h
  push Not at h
  obtain ⟨s, a, b, hab⟩ := h
  exact ⟨s, [a, b], [b, a], List.Perm.swap b a [], hab⟩

/-! ### Layer 2: Instantiations (Status B — calibration)

  The choice of dynamics model for each planetary boundary is a calibration
  input, not a derived result. The theorems below prove that SPECIFIC models
  are commutative or not — whether those models are the RIGHT ones for each
  boundary is a modeling judgment outside Lean's scope. -/

/-- CO₂ dynamics: additive stock accumulation.
    Each emission adds to the cumulative stock. Order doesn't matter. -/
def co2_dynamics (stock : ℤ) (emission : ℤ) : ℤ := stock + emission

theorem co2_is_commutative : IsCommutativeUpdate co2_dynamics :=
  fun s a b => add_right_comm s a b

/-- Cocktail dynamics (novel entities): toxic interaction threshold.
    Inserting substance into state: if substance 0 is already present
    and we try to add substance 1, the insertion is blocked (toxic
    combination, cf. Persson et al. 2022 cocktail effects). -/
def cocktail_dynamics (state : Finset (Fin 3)) (substance : Fin 3) :
    Finset (Fin 3) :=
  if (0 : Fin 3) ∈ state ∧ substance = (1 : Fin 3) then state
  else insert substance state

private theorem cocktail_witness :
    cocktail_dynamics (cocktail_dynamics ∅ (0 : Fin 3)) 1 ≠
    cocktail_dynamics (cocktail_dynamics ∅ 1) 0 := by decide

theorem cocktail_is_noncommutative : ¬ IsCommutativeUpdate cocktail_dynamics :=
  fun h => cocktail_witness (h ∅ 0 1)

/-! ### Bridge theorems: applying the general framework -/

/-- CO₂ instantiation of the general theorem: any two emission sequences
    with the same multiset of emissions produce the same cumulative stock. -/
theorem co2_order_irrelevant {w₁ w₂ : List ℤ} (hp : w₁.Perm w₂) (s₀ : ℤ) :
    w₁.foldl co2_dynamics s₀ = w₂.foldl co2_dynamics s₀ :=
  commutative_implies_perm_invariant co2_is_commutative hp s₀

/-- Cocktail instantiation of the dual: there exist emission sequences
    where reordering changes the final state (cocktail effects). -/
theorem cocktail_order_matters :
    ∃ (s : Finset (Fin 3)) (w₁ w₂ : List (Fin 3)),
      w₁.Perm w₂ ∧ w₁.foldl cocktail_dynamics s ≠ w₂.foldl cocktail_dynamics s :=
  noncommutative_implies_order_sensitive cocktail_is_noncommutative

end CommutativeClassification
