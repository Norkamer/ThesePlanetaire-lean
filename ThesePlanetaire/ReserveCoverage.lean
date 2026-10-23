/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/ReserveCoverage.lean
  Phase 10 (2026-10-02), étape 10b : réserve à sources incontrôlables multiples, partition de Ω
  en part couverte et part incontrôlable, condition de couverture par mémoire.

  Développé d'abord en `ReserveCoverage_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase10_2026-10-02/plan_phase10.md` ; analyse :
  `cache/analyse_phase10_garde_repartie_2026-10-02.md` ; amont :
  `cache/analyse_options_1_2_droit_taxe_2026-10-02.md` §2.
-/

import ThesePlanetaire.GuardSupervisor

/-!
# Couverture : ce que la garde peut tenir dépend de ce qui lui échappe

Trois classes de lettres : **ajustables** (`ξ ≠ 0`, la mesure les déplace), **Ω_g** (non
ajustables mais refusables : émetteur couvert par la garde) et **Ω_u** (incontrôlables : nature,
ou émetteur non couvert). La garde ne refuse que les lettres couvertes ; les autres doivent tenir
dans une réserve.

1. ★ `reserveSet_maximal`, `reserveSet_ci_iff` : avec des sources incontrôlables `U` (émission
   `eu u`, chacune au plus une fois par période), le plus grand ensemble contrôlé-invariant est
   contenu dans `X_res = {(L, J) | L + Σ_{u ∉ J} eu u ≤ cap}` ; il est invariant ssi le top le
   restaure (`GuardSupervisor.TopOK` avec `eu := Σ_u eu u`, `m := 1`). `uncSet_reduce` ramène au
   modèle mono-lettre de la Phase 9 : ★ `stockSet_unc_empty`, `regenSet_unc_empty`.
2. ★ `uncMass_cast`, `uncMass_eq_omega_of_xi_zero`, `uncLoad_le_uncMass`, `uncMass_attained` :
   la masse incontrôlable d'un ensemble couvert `A` est `Σ_{i ∉ A} max(a⁺, a⁻)`, soit
   `Σ_{i ∉ A} (Ω_i + |ξ_i|)` ; c'est la part de `Ω` hors de `A` quand `ξ = 0` hors de `A`, et le
   pire cas exact des sections de la boîte.
3. ★ `coverage_stock_iff`, `coverage_regen_iff`, `coverage_flow_iff` : avec
   `M = E_nat + uncMass` (émission naturelle plus agents non couverts), un état viable existe ssi
   `M = 0` (`stock` : couverture totale, pas d'émission naturelle), `M ≤ min r cap` (`regen`),
   `M ≤ cap` (`flow`).
-/

namespace ReserveCoverage

open FeedbackClass (Memory tickOp)
open GuardSupervisor (ControlledInvariant TopOK topOK_stock_iff topOK_flow_iff topOK_regen_iff
  stock_unc_empty regen_unc_empty natInst)
open MeasureFibration (MGInst Ω ξ Box)

/-! ## §1. Réserve à sources multiples -/

section Multi

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Ensemble contrôlé-invariant à sources multiples. État `(L, J)` : charge et sources déjà
tirées dans la période ; une source `u ∉ J` peut toujours survenir ; le top remet `J` à `∅`. -/
def ControlledInvariantSet (tick : ℕ → ℕ) (eu : U → ℕ) (cap : ℕ) (X : ℕ × Finset U → Prop) :
    Prop :=
  (∀ L J, X (L, J) → L ≤ cap) ∧
    (∀ L J u, X (L, J) → u ∉ J → X (L + eu u, insert u J)) ∧
    ∀ L J, X (L, J) → X (tick L, ∅)

/-- La réserve : de quoi absorber les sources restantes de la période. -/
def XresSet (eu : U → ℕ) (cap : ℕ) : ℕ × Finset U → Prop :=
  fun q => q.1 + ∑ u ∈ q.2ᶜ, eu u ≤ cap

/-- La garde avec réserve sur les lettres couvertes (refusables). -/
def reserveGuardSet {α : Type*} (eu : U → ℕ) (cap : ℕ) (e : α → ℕ) (q : ℕ × Finset U) (a : α) :
    Prop :=
  XresSet eu cap (q.1 + e a, q.2)

variable {tick : ℕ → ℕ} {eu : U → ℕ} {cap : ℕ} {X : ℕ × Finset U → Prop}

omit [Fintype U] in
/-- Tirer d'un coup un ensemble de sources encore disponibles. -/
theorem ciSet_draw (hX : ControlledInvariantSet tick eu cap X) {L : ℕ} {J : Finset U}
    (h : X (L, J)) : ∀ K : Finset U, Disjoint K J → X (L + ∑ u ∈ K, eu u, J ∪ K) := by
  intro K
  induction K using Finset.induction_on with
  | empty => intro _; simpa using h
  | insert u K hu ih =>
    intro hd
    have hd' : Disjoint K J := Finset.disjoint_of_subset_left (Finset.subset_insert u K) hd
    have huJ : u ∉ J ∪ K := by
      simp only [Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_left.mp hd (Finset.mem_insert_self u K), hu⟩
    have := hX.2.1 _ _ u (ih hd') huJ
    rw [Finset.sum_insert hu, Finset.union_insert,
      show L + (eu u + ∑ x ∈ K, eu x) = L + ∑ x ∈ K, eu x + eu u by ring]
    exact this

/-- ★ Tout ensemble contrôlé-invariant est contenu dans la réserve : depuis `(L, J)` hors de
`X_res`, tirer les sources restantes dépasse le plafond. -/
theorem reserveSet_maximal (hX : ControlledInvariantSet tick eu cap X) :
    ∀ q, X q → XresSet eu cap q := by
  rintro ⟨L, J⟩ h
  exact hX.1 _ _ (ciSet_draw hX h Jᶜ disjoint_compl_left)

/-- ★ La réserve est contrôlé-invariante ssi le top la restaure, pour la masse totale
`Σ_u eu u` tirée au plus une fois par période. -/
theorem reserveSet_ci_iff :
    ControlledInvariantSet tick eu cap (XresSet eu cap) ↔ TopOK tick (∑ u, eu u) 1 cap := by
  constructor
  · rintro ⟨_, _, htop⟩ L hL
    have := htop L Finset.univ (by simpa [XresSet] using hL)
    simpa [XresSet] using this
  · intro hT
    refine ⟨fun L J h => le_trans (Nat.le_add_right _ _) h, fun L J u h hu => ?_, fun L J h => ?_⟩
    · show L + eu u + ∑ x ∈ (insert u J)ᶜ, eu x ≤ cap
      have hs := Finset.add_sum_erase Jᶜ eu (Finset.mem_compl.mpr hu)
      rw [Finset.compl_insert, add_assoc, hs]
      exact h
    · show tick L + ∑ x ∈ (∅ : Finset U)ᶜ, eu x ≤ cap
      rw [Finset.compl_empty]
      simpa using hT L (le_trans (Nat.le_add_right _ _) h)

/-- La garde avec réserve préserve la réserve ; sous `TopOK`, les sources et le top aussi. -/
theorem reserveGuardSet_preserves {α : Type*} (e : α → ℕ)
    (hT : TopOK tick (∑ u, eu u) 1 cap) {q : ℕ × Finset U} (hq : XresSet eu cap q) :
    (∀ a, reserveGuardSet eu cap e q a → XresSet eu cap (q.1 + e a, q.2)) ∧
      (∀ u, u ∉ q.2 → XresSet eu cap (q.1 + eu u, insert u q.2)) ∧
        XresSet eu cap (tick q.1, ∅) :=
  ⟨fun _ h => h, fun u hu => (reserveSet_ci_iff.mpr hT).2.1 _ _ u hq hu,
    (reserveSet_ci_iff.mpr hT).2.2 _ _ hq⟩

/-- Réduction au modèle mono-lettre de la Phase 9 (`eu := Σ_u eu u`, `m := 1`) : les états
« rien tiré » et « tout tiré ». -/
def reduceSet (X : ℕ × Finset U → Prop) : ℕ × ℕ → Prop :=
  fun q => (q.2 = 0 ∧ X (q.1, ∅)) ∨ (q.2 = 1 ∧ X (q.1, Finset.univ))

/-- Un ensemble contrôlé-invariant à sources multiples induit un ensemble contrôlé-invariant
du modèle mono-lettre, non vide s'il l'est. -/
theorem uncSet_reduce (hX : ControlledInvariantSet tick eu cap X) :
    ControlledInvariant tick (∑ u, eu u) 1 cap (reduceSet X) ∧
      ∀ L J, X (L, J) → reduceSet X (tick L, 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, fun L J h => Or.inl ⟨rfl, hX.2.2 L J h⟩⟩
  · rintro L j (⟨-, h⟩ | ⟨-, h⟩) <;> exact hX.1 _ _ h
  · rintro L j (⟨rfl, h⟩ | ⟨rfl, -⟩) hj
    · refine Or.inr ⟨rfl, ?_⟩
      have := ciSet_draw hX h Finset.univ (Finset.disjoint_empty_right _)
      simpa using this
    · omega
  · rintro L j (⟨-, h⟩ | ⟨-, h⟩) <;> exact Or.inl ⟨rfl, hX.2.2 _ _ h⟩

/-- ★ `stock` : avec des sources incontrôlables effectives, aucun état n'est viable. -/
theorem stockSet_unc_empty (r : ℕ) (h : 0 < ∑ u, eu u)
    (hX : ControlledInvariantSet (tickOp .stock r) eu cap X) : ∀ q, ¬ X q := by
  rintro ⟨L, J⟩ hq
  obtain ⟨hY, hne⟩ := uncSet_reduce hX
  exact stock_unc_empty r (by simpa using h) hY _ (hne L J hq)

/-- ★ `regen` : si les sources d'une période dépassent la régénération, aucun état n'est
viable. -/
theorem regenSet_unc_empty (r : ℕ) (h : r < ∑ u, eu u)
    (hX : ControlledInvariantSet (tickOp .regen r) eu cap X) : ∀ q, ¬ X q := by
  rintro ⟨L, J⟩ hq
  obtain ⟨hY, hne⟩ := uncSet_reduce hX
  exact regen_unc_empty r (by simpa using h) hY _ (hne L J hq)

/-- Viabilité : il existe un ensemble contrôlé-invariant non vide. -/
def Viable (tick : ℕ → ℕ) (eu : U → ℕ) (cap : ℕ) : Prop :=
  ∃ X, ControlledInvariantSet tick eu cap X ∧ ∃ q, X q

theorem sum_le_cap_of_viable (h : Viable tick eu cap) : ∑ u, eu u ≤ cap := by
  obtain ⟨X, hX, ⟨L, J⟩, hq⟩ := h
  have := reserveSet_maximal hX _ (hX.2.2 L J hq)
  simp only [XresSet, Finset.compl_empty] at this
  omega

theorem xresSet_zero (h : ∑ u, eu u ≤ cap) : XresSet eu cap (0, ∅) := by
  simpa [XresSet] using h

theorem viable_stock_iff (r : ℕ) : Viable (tickOp .stock r) eu cap ↔ ∑ u, eu u = 0 := by
  constructor
  · rintro ⟨X, hX, q, hq⟩
    by_contra h
    exact stockSet_unc_empty r (Nat.pos_of_ne_zero h) hX q hq
  · intro h
    exact ⟨_, reserveSet_ci_iff.mpr ((topOK_stock_iff r).mpr (by simpa using h)), _,
      xresSet_zero (by omega)⟩

theorem viable_regen_iff (r : ℕ) :
    Viable (tickOp .regen r) eu cap ↔ ∑ u, eu u ≤ min r cap := by
  constructor
  · intro hv
    refine le_min ?_ (sum_le_cap_of_viable hv)
    obtain ⟨X, hX, q, hq⟩ := hv
    by_contra h
    exact regenSet_unc_empty r (by omega) hX q hq
  · intro h
    exact ⟨_, reserveSet_ci_iff.mpr ((topOK_regen_iff r).mpr (by simpa using h)), _,
      xresSet_zero (le_trans h (min_le_right _ _))⟩

theorem viable_flow_iff (r : ℕ) : Viable (tickOp .flow r) eu cap ↔ ∑ u, eu u ≤ cap :=
  ⟨sum_le_cap_of_viable, fun h =>
    ⟨_, reserveSet_ci_iff.mpr ((topOK_flow_iff r).mpr (by simpa using h)), _, xresSet_zero h⟩⟩

end Multi

/-! ## §2. Partition de Ω : part couverte, part incontrôlable -/

section Partition

variable {ι B : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Part de l'agent `i` dans `Ω` (charge moyenne des deux stratégies). -/
def omegaOf (G : MGInst 𝕜 ι B) (i : ι) (μ : B) : 𝕜 := (G.aP i μ + G.aM i μ) / 2

omit [DecidableEq ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem omega_eq_sum (G : MGInst 𝕜 ι B) (μ : B) : Ω G μ = ∑ i, omegaOf G i μ := rfl

/-- Masse incontrôlable : pire cas des agents hors de l'ensemble couvert `A`. -/
def uncMass (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) : ℕ :=
  ∑ i ∈ Aᶜ, max (aP i μ) (aM i μ)

theorem cast_max_eq (a b : ℕ) :
    ((max a b : ℕ) : 𝕜) = ((a : 𝕜) + b) / 2 + |((a : 𝕜) - b) / 2| := by
  rcases le_total a b with h | h
  · have h' : (a : 𝕜) ≤ b := by exact_mod_cast h
    rw [max_eq_right h, abs_of_nonpos (by linarith)]
    ring
  · have h' : (b : 𝕜) ≤ a := by exact_mod_cast h
    rw [max_eq_left h, abs_of_nonneg (by linarith)]
    ring

/-- ★ La masse incontrôlable est `Σ_{i ∉ A} (Ω_i + |ξ_i|)`. -/
theorem uncMass_cast (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) :
    (uncMass aP aM A μ : 𝕜) =
      ∑ i ∈ Aᶜ, (omegaOf (natInst (𝕜 := 𝕜) aP aM) i μ + |ξ (natInst aP aM) i μ|) := by
  rw [uncMass, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cast_max_eq]
  rfl

/-- ★ Si `ξ = 0` hors de `A` (lettres non ajustables), la masse incontrôlable est la part de
`Ω` hors de `A`. -/
theorem uncMass_eq_omega_of_xi_zero (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B)
    (h : ∀ i ∉ A, ξ (natInst (𝕜 := 𝕜) aP aM) i μ = 0) :
    (uncMass aP aM A μ : 𝕜) = ∑ i ∈ Aᶜ, omegaOf (natInst aP aM) i μ := by
  rw [uncMass_cast]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_compl.mp hi), abs_zero, add_zero]

/-- ★ Pire cas : toute section de la boîte charge les agents non couverts d'au plus la masse
incontrôlable. -/
theorem uncLoad_le_uncMass (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) {m : ι → 𝕜}
    (hm : Box m) :
    ∑ i ∈ Aᶜ, ((1 + m i) / 2 * (aP i μ : 𝕜) + (1 - m i) / 2 * (aM i μ : 𝕜)) ≤
      uncMass aP aM A μ := by
  rw [uncMass, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (aP i μ : 𝕜) ≤ ((max (aP i μ) (aM i μ) : ℕ) : 𝕜) := by exact_mod_cast le_max_left _ _
  have h2 : (aM i μ : 𝕜) ≤ ((max (aP i μ) (aM i μ) : ℕ) : 𝕜) := by exact_mod_cast le_max_right _ _
  obtain ⟨hl, hu⟩ := hm i
  have := mul_le_mul_of_nonneg_left h1 (show (0 : 𝕜) ≤ (1 + m i) / 2 by linarith)
  have := mul_le_mul_of_nonneg_left h2 (show (0 : 𝕜) ≤ (1 - m i) / 2 by linarith)
  nlinarith

/-- ★ … et ce pire cas est atteint par une section pure. -/
theorem uncMass_attained (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) :
    ∃ m : ι → 𝕜, Box m ∧
      ∑ i ∈ Aᶜ, ((1 + m i) / 2 * (aP i μ : 𝕜) + (1 - m i) / 2 * (aM i μ : 𝕜)) =
        uncMass aP aM A μ := by
  refine ⟨fun i => if aM i μ ≤ aP i μ then 1 else -1, fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
  rw [uncMass, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  split_ifs with h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right (le_of_not_ge h)]; ring

end Partition

/-! ## §3. Couverture par mémoire

Sources incontrôlables d'une période : les sources naturelles `Un` (émission `enat`) et les
agents hors de l'ensemble couvert `A`, chacun au pire de ses deux stratégies sur la fibre `μ`.
-/

section Coverage

variable {ι B Un : Type*} [Fintype ι] [DecidableEq ι] [Fintype Un] [DecidableEq Un]

/-- Émission des sources incontrôlables : nature et agents non couverts. -/
def srcEmit (enat : Un → ℕ) (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) : Un ⊕ ι → ℕ
  | .inl n => enat n
  | .inr i => if i ∈ A then 0 else max (aP i μ) (aM i μ)

omit [DecidableEq Un] in
theorem sum_srcEmit (enat : Un → ℕ) (aP aM : ι → B → ℕ) (A : Finset ι) (μ : B) :
    ∑ u, srcEmit enat aP aM A μ u = ∑ n, enat n + uncMass aP aM A μ := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [uncMass, ← Finset.sum_compl_add_sum A]
  simp only [srcEmit]
  rw [Finset.sum_ite_of_true (fun i hi => hi), Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i hi => if_neg (Finset.mem_compl.mp hi)

variable {cap r : ℕ} {enat : Un → ℕ} {aP aM : ι → B → ℕ} {A : Finset ι} {μ : B}

/-- ★ `stock` : un état viable existe ssi la masse incontrôlable totale est nulle — couverture
totale des émetteurs effectifs et pas d'émission naturelle. -/
theorem coverage_stock_iff :
    Viable (tickOp .stock r) (srcEmit enat aP aM A μ) cap ↔
      ∑ n, enat n + uncMass aP aM A μ = 0 := by
  rw [viable_stock_iff, sum_srcEmit]

/-- ★ `regen` : un état viable existe ssi `M ≤ min r cap`. -/
theorem coverage_regen_iff :
    Viable (tickOp .regen r) (srcEmit enat aP aM A μ) cap ↔
      ∑ n, enat n + uncMass aP aM A μ ≤ min r cap := by
  rw [viable_regen_iff, sum_srcEmit]

/-- ★ `flow` : un état viable existe ssi `M ≤ cap`. -/
theorem coverage_flow_iff :
    Viable (tickOp .flow r) (srcEmit enat aP aM A μ) cap ↔
      ∑ n, enat n + uncMass aP aM A μ ≤ cap := by
  rw [viable_flow_iff, sum_srcEmit]

/-- Couverture totale : sans agent non couvert, seule l'émission naturelle reste. -/
theorem uncMass_univ (aP aM : ι → B → ℕ) (μ : B) : uncMass aP aM Finset.univ μ = 0 := by
  simp [uncMass]

end Coverage

end ReserveCoverage

/-!
## Domaine (généralisation D-13, 2026-10-03)

Les déclarations de la section `Partition` (`omegaOf`, `omega_eq_sum`, `cast_max_eq`,
`uncMass_cast`, `uncMass_eq_omega_of_xi_zero`, `uncLoad_le_uncMass`, `uncMass_attained`) sont
énoncées sur un corps ordonné quelconque `𝕜`. Le reste du module est dans `ℕ` : la généralisation
n'y touche pas.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
