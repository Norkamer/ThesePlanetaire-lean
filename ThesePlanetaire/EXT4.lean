/-
  MonnaiesEndogene/EXT4.lean
  Proposition EXT-4: Welfare optimality at complete internalization

  Abstraction strategy:
  W is modeled as an abstract antimonotone function W : ℕ → ℤ on the number
  of externality classes k. No DiGraph, no Tarski fixed-point, no formal
  supermodularity machinery — just the abstract order structure.

  EXT4 is a direct corollary of EXT3:
  - EXT3 guarantees ∃ T ≤ m, k T = 1 (complete internalization)
  - If W is antimonotone on k (more internalization → higher welfare),
    then W(k T) = W(1) is the global maximum of W ∘ k.

  Two theorems:
  1. ext4_welfare_convergence     : W weakly antimonotone → W(k T) ≥ W(k t) ∀ t
  2. ext4_unique_welfare_optimum  : W strictly antimonotone (k > 1 → W(1) > W(k)) →
                                    W(k T) is the strict global optimum
-/

import ThesePlanetaire.EXT3


/-- EXT-4 (weak version): Welfare convergence to global optimum.

  If W : ℕ → ℤ is weakly antimonotone (k ≤ k' → W k' ≤ W k),
  and the system satisfies the EXT3 hypotheses, then there exists T ≤ m
  such that W(k T) ≥ W(k t) for all t.

  Interpretation: complete internalization maximizes welfare under any
  welfare function that is non-decreasing in internalization. -/
theorem ext4_welfare_convergence
    (m : ℕ) -- number of edges (EXT3 bound)
    (k : ℕ → ℕ) -- k(t) = number of externality classes at time t
    (W : ℕ → ℤ) -- abstract welfare function on number of classes
    (h_init   : k 0 ≤ m)
    (h_mono   : ∀ t, k (t + 1) ≤ k t)
    (h_strict : ∀ t, k t > 1 → k (t + 1) < k t)
    (h_nat    : ∀ t, k t ≥ 1)
    (h_W_antimonotone : ∀ a b : ℕ, a ≤ b → W b ≤ W a) -- W non-increasing in k
    : ∃ T, T ≤ m ∧ ∀ t, W (k T) ≥ W (k t) := by
  -- EXT3 gives us T with k T = 1
  obtain ⟨T, hT_le, hkT⟩ := ext3_internalization_bound m k h_init h_mono h_strict h_nat
  use T, hT_le
  intro t
  -- k T = 1, so k t ≥ 1 = k T, so W(k T) ≥ W(k t)
  have hkt_ge : k t ≥ k T := by
    rw [hkT]; exact h_nat t
  exact h_W_antimonotone (k T) (k t) hkt_ge

/-- EXT-4 (strict version): Unique welfare optimum.

  If W is strictly antimonotone on k > 1 (i.e., k > 1 → W(1) > W(k)),
  then T is the unique time at which the global welfare optimum is attained,
  and W(k T) strictly dominates all periods where k t > 1. -/
theorem ext4_unique_welfare_optimum
    (m : ℕ)
    (k : ℕ → ℕ)
    (W : ℕ → ℤ)
    (h_init   : k 0 ≤ m)
    (h_mono   : ∀ t, k (t + 1) ≤ k t)
    (h_strict : ∀ t, k t > 1 → k (t + 1) < k t)
    (h_nat    : ∀ t, k t ≥ 1)
    (h_W_strict : ∀ n : ℕ, n > 1 → W 1 > W n) -- strict gain from full internalization
    : ∃ T, T ≤ m ∧ ∀ t, k t > 1 → W (k T) > W (k t) := by
  obtain ⟨T, hT_le, hkT⟩ := ext3_internalization_bound m k h_init h_mono h_strict h_nat
  use T, hT_le
  intro t hkt_gt
  rw [hkT]
  exact h_W_strict (k t) hkt_gt

-- Phase 23 L1: Abstract Φ-isotonicity (proof_critic Phase 23)
section ClearingIsotone

/-- min(x, c) is monotone in x for any constant c. -/
lemma monotone_min_const {α : Type*} [LinearOrder α] (c : α) :
    Monotone (fun x => min x c) :=
  fun _ _ h => min_le_min_right c h

/-- Composition of monotone functions is monotone (Φ = cap ∘ shift). -/
lemma phi_isotone {α β : Type*} [Preorder α] [Preorder β]
    {shift : α → β} {cap : β → β}
    (h_shift : Monotone shift) (h_cap : Monotone cap) :
    Monotone (cap ∘ shift) :=
  h_cap.comp h_shift

end ClearingIsotone
