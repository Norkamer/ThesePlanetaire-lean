/-
  MonnaiesEndogene/EXT3.lean
  Proposition EXT-3: Complete internalization bound (unconditional)

  Statement: In a system satisfying TC-biᵀ with m edges,
  the number of externality classes k(t) decreases monotonically
  and reaches k = 1 (complete internalization) in at most m periods.

  This follows from Moore-Bcirc (GRE26 Thm. B.P8):
  Bcirc is a Lyapunov function on the forest E \ M_p.
  Each R2/R3 fusion strictly reduces k(t).
  Since k(0) ≤ m and k(t) ∈ ℕ, termination in ≤ m steps.
-/

import ThesePlanetaire.Basic

/-- Auxiliary: a sequence bounded by n that strictly decreases when > 1
    and stays at 1 once reached, must reach 1 within n steps. -/
private theorem reach_one_aux
    (n : ℕ) : ∀ (k : ℕ → ℕ),
    k 0 ≤ n →
    (∀ t, k (t + 1) ≤ k t) →
    (∀ t, k t > 1 → k (t + 1) < k t) →
    (∀ t, k t ≥ 1) →
    ∃ T, T ≤ n ∧ k T = 1 := by
  induction n with
  | zero =>
    intro k h_init _ _ h_nat
    have h0 := h_nat 0
    omega
  | succ n ih =>
    intro k h_init h_mono h_strict h_nat
    by_cases hk0 : k 0 = 1
    · exact ⟨0, by omega, hk0⟩
    · have hk0_gt : k 0 > 1 := by have := h_nat 0; omega
      have hk1_lt : k 1 < k 0 := h_strict 0 hk0_gt
      have hk1_le_n : k 1 ≤ n := by omega
      have h_mono' : ∀ t, k (t + 1 + 1) ≤ k (t + 1) := fun t => h_mono (t + 1)
      have h_strict' : ∀ t, k (t + 1) > 1 → k (t + 1 + 1) < k (t + 1) :=
        fun t => h_strict (t + 1)
      have h_nat' : ∀ t, k (t + 1) ≥ 1 := fun t => h_nat (t + 1)
      obtain ⟨T, hT_le, hkT⟩ := ih (fun t => k (t + 1)) hk1_le_n h_mono' h_strict' h_nat'
      exact ⟨T + 1, by omega, hkT⟩

/-- Moore-Bcirc bound: k(t) reaches 1 in at most m steps.

  Hypotheses:
  - h_init: k(0) ≤ m (initial number of components bounded by edge count)
  - h_mono: k is monotonically non-increasing (fusions never split components)
  - h_strict: k strictly decreases when above 1 (each period performs at least one fusion)
  - h_nat: k(t) ≥ 1 (at least one component always exists)
-/
theorem ext3_internalization_bound
    (m : ℕ) -- number of edges
    (k : ℕ → ℕ) -- k(t) = number of components at time t
    (h_init : k 0 ≤ m) -- initial bound
    (h_mono : ∀ t, k (t + 1) ≤ k t) -- monotonically non-increasing
    (h_strict : ∀ t, k t > 1 → k (t + 1) < k t) -- strict decrease when > 1
    (h_nat : ∀ t, k t ≥ 1) -- at least 1 component
    : ∃ T, T ≤ m ∧ k T = 1 :=
  reach_one_aux m k h_init h_mono h_strict h_nat

/-- Once k reaches 1, it stays at 1 (by monotonicity and h_nat). -/
private theorem k_stable_at_one
    (k : ℕ → ℕ)
    (h_mono : ∀ t, k (t + 1) ≤ k t)
    (h_nat : ∀ t, k t ≥ 1)
    (t : ℕ) (hkt : k t = 1)
    : k (t + 1) = 1 := by
  have h1 := h_mono t
  have h2 := h_nat (t + 1)
  omega

/-- Corollary: no externality persists beyond m periods -/
theorem ext3_no_persistent_externality
    (m : ℕ)
    (k : ℕ → ℕ)
    (h_init : k 0 ≤ m)
    (h_mono : ∀ t, k (t + 1) ≤ k t)
    (h_strict : ∀ t, k t > 1 → k (t + 1) < k t)
    (h_nat : ∀ t, k t ≥ 1)
    : ∀ t, t ≥ m → k t = 1 := by
  obtain ⟨T, hT_le, hkT⟩ := ext3_internalization_bound m k h_init h_mono h_strict h_nat
  intro t ht
  -- Show k t = 1 by induction from T to t
  have key : ∀ s, k (T + s) = 1 := by
    intro s
    induction s with
    | zero => simpa using hkT
    | succ s' ihs =>
      rw [Nat.add_succ]
      exact k_stable_at_one k h_mono h_nat _ ihs
  have := key (t - T)
  rwa [Nat.add_sub_cancel' (by omega : T ≤ t)] at this
