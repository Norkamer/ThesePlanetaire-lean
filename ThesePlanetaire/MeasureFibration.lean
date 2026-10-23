/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/MeasureFibration.lean
  Phase 9 (2026-10-02) : la dynamique des mesures sur une base finie — faisabilité par fibre,
  certificat de prix d'état (Farkas), densité d'Arrow–Debreu, bande atteignable, budget `stock`.

  Développé d'abord en `MeasureFibration_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase9_2026-10-02/plan_phase9.md` ; analyse :
  `cache/analyse_phase9_mesures_prix_etat_surete_2026-10-02.md` ; antériorité :
  `cache/recherche_anteriorite_mesures_alpha_c_2026-10-02.md`.
-/

import ThesePlanetaire.FourierMotzkinEconCS
import Mathlib.Tactic.FinCases

/-!
# Fibration finie du jeu de minorité, faisabilité par fibre et prix d'état

**Cadre.** Des agents `ι` et une base finie `B` d'états d'information (les états de la regex
qui lit le grand livre : histoires de longueur `k`, `B := Fin k → Bool`, `card B = 2 ^ k`). Sur
chaque fibre `μ : B`, l'agent `i` dispose de deux stratégies de charge `aP i μ` et `aM i μ` ;
une **section mixte** `m : ι → 𝕜` de la boîte `[-1, 1]^ι` choisit entre elles. La charge
agrégée de la fibre est `load m μ` ; la capacité de la fibre est `L μ`. Le paramètre de contrôle
du jeu de minorité est `α = card B / card ι`.

**Ce que prouve ce module** (`𝕜` corps linéairement ordonné, donc ℚ) :
1. ★ `load_eq` : `load m μ = Ω μ + Σ_i ξ i μ · m i` (décomposition de Challet–Marsili–Zecchina :
   `Ω` = part **non ajustable**, `ξ` = part ajustable) ;
2. ★ `H_eq_zero_iff`, `exists_H_zero_iff` : `H = Σ_μ ρ μ · exc²` est nul ssi chaque fibre est
   exactement à sa capacité ; un minimum nul existe ssi le système égalité est faisable dans la
   boîte. **Connu** : Berg–Marsili–Rustichini–Zecchina 2001, El Farol (Challet–Marsili–Ottino
   2004). Le seuil `α_c` lui-même (méthode des répliques) est hors de portée.
3. ★ `capFeasible_iff_not_cert` : la version **plafond** (`load ≤ L` fibre par fibre) est
   faisable ssi il n'existe pas de **certificat de prix d'état** `y ≥ 0` avec
   `Σ_i |Σ_μ y μ ξ i μ| < Σ_μ y μ (Ω μ − L μ)`. Sens dur par le théorème de l'alternative
   d'EconCSLib (`FourierMotzkinEconCS`). La mathématique (Farkas, FTAP de Ross) est connue ;
   l'objet (plafond d'un commun par fibre, `Ω` non ajustable) est la contribution.
4. ★ `cert_iff_density` : relativement à une mesure de base `ρ > 0` (fréquence de visite des
   états), un certificat est une **densité d'Arrow–Debreu** `q = y / ρ`.
5. ★ `load_band`, `not_capFeasible_of_mean_excess` : **bande atteignable** — une section ne
   déplace la charge de `μ` que de `Σ_i |ξ i μ|` autour de `Ω μ` ; un excès moyen supérieur à la
   masse ajustable est infaisable pour toute mesure (sonde S12).
6. ★ `stock_infeasible_iff`, `stock_measure_cannot` : un budget cumulé (`stock`) sur une suite
   d'états visités est une instance à **une seule fibre** (`stockAggregate`), dont le
   certificat est un scalaire (un prix unique sur l'horizon, lecture de Hotelling,
   `RightsIntertemporal.hotelling_no_ponzi`). Sous la demande minimale atteignable, aucune
   dynamique des mesures — même à sections variables dans le temps — ne tient le budget.
-/

open Finset BigOperators

namespace MeasureFibration

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## §1. Fibration finie -/

/-- Une instance : deux stratégies de charge par agent et par fibre, une capacité par fibre. -/
structure MGInst (𝕜 : Type*) (ι B : Type*) where
  /-- charge de la stratégie « + » de l'agent `i` sur la fibre `μ` -/
  aP : ι → B → 𝕜
  /-- charge de la stratégie « − » -/
  aM : ι → B → 𝕜
  /-- capacité (plafond) de la fibre -/
  L : B → 𝕜

variable {ι B : Type*} [Fintype ι] [Fintype B]

/-- Part non ajustable de la charge de la fibre `μ` : moyenne des deux stratégies, sommée. -/
def Ω (G : MGInst 𝕜 ι B) (μ : B) : 𝕜 := ∑ i, (G.aP i μ + G.aM i μ) / 2

/-- Part ajustable de l'agent `i` sur la fibre `μ`. -/
def ξ (G : MGInst 𝕜 ι B) (i : ι) (μ : B) : 𝕜 := (G.aP i μ - G.aM i μ) / 2

/-- Section mixte dans la boîte `[-1, 1]^ι` (`m i = 1` : stratégie « + » ; `-1` : « − »). -/
def Box (m : ι → 𝕜) : Prop := ∀ i, -1 ≤ m i ∧ m i ≤ 1

/-- Charge agrégée de la fibre `μ` sous la section `m`. -/
def load (G : MGInst 𝕜 ι B) (m : ι → 𝕜) (μ : B) : 𝕜 :=
  ∑ i, ((1 + m i) / 2 * G.aP i μ + (1 - m i) / 2 * G.aM i μ)

omit [Fintype B] in
/-- ★ Décomposition de Challet–Marsili–Zecchina : part non ajustable + part ajustable. -/
theorem load_eq (G : MGInst 𝕜 ι B) (m : ι → 𝕜) (μ : B) :
    load G m μ = Ω G μ + ∑ i, ξ G i μ * m i := by
  simp only [load, Ω, ξ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Excès de la fibre `μ` sur sa capacité. -/
def exc (G : MGInst 𝕜 ι B) (m : ι → 𝕜) (μ : B) : 𝕜 := load G m μ - G.L μ

/-- Hamiltonien du jeu de minorité à capacité : excès quadratique pondéré par la mesure de base
`ρ` (fréquence de visite des états d'information). -/
def H (G : MGInst 𝕜 ι B) (ρ : B → 𝕜) (m : ι → 𝕜) : 𝕜 := ∑ μ, ρ μ * exc G m μ ^ 2

/-! ## §2. Équilibre exact : `H = 0` ⟺ chaque fibre à sa capacité -/

/-- ★ Version support : sous `ρ ≥ 0`, `H = 0` ssi l'excès est nul sur le support de `ρ`. -/
theorem H_eq_zero_iff_support (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 ≤ ρ μ)
    (m : ι → 𝕜) : H G ρ m = 0 ↔ ∀ μ, ρ μ ≠ 0 → exc G m μ = 0 := by
  unfold H
  rw [Finset.sum_eq_zero_iff_of_nonneg fun μ _ => mul_nonneg (hρ μ) (sq_nonneg _)]
  refine ⟨fun h μ hμ => ?_, fun h μ _ => ?_⟩
  · rcases mul_eq_zero.mp (h μ (Finset.mem_univ _)) with h0 | h0
    · exact absurd h0 hμ
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  · by_cases hμ : ρ μ = 0
    · simp [hμ]
    · simp [h μ hμ]

/-- ★ Sous `ρ > 0` : `H = 0` ssi chaque fibre est exactement à sa capacité. -/
theorem H_eq_zero_iff (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 < ρ μ) (m : ι → 𝕜) :
    H G ρ m = 0 ↔ ∀ μ, exc G m μ = 0 := by
  rw [H_eq_zero_iff_support G (fun μ => (hρ μ).le)]
  exact ⟨fun h μ => h μ (hρ μ).ne', fun h μ _ => h μ⟩

/-- Faisabilité du système égalité dans la boîte. -/
def EqFeasible (G : MGInst 𝕜 ι B) : Prop := ∃ m, Box m ∧ ∀ μ, load G m μ = G.L μ

/-- ★ Un minimum nul de `H` existe dans la boîte ssi le système égalité est faisable. -/
theorem exists_H_zero_iff (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 < ρ μ) :
    (∃ m, Box m ∧ H G ρ m = 0) ↔ EqFeasible G := by
  simp only [H_eq_zero_iff G hρ, exc, sub_eq_zero, EqFeasible]

/-! ## §3. Plafond par fibre et certificat de prix d'état -/

/-- Faisabilité du plafond : une section de la boîte tient chaque fibre sous sa capacité. -/
def CapFeasible (G : MGInst 𝕜 ι B) : Prop := ∃ m, Box m ∧ ∀ μ, load G m μ ≤ G.L μ

/-- Certificat de prix d'état : des prix `y ≥ 0` par fibre sous lesquels la valeur de l'excès
non ajustable dépasse ce que toute section peut compenser. -/
def IsStatePriceCert (G : MGInst 𝕜 ι B) (y : B → 𝕜) : Prop :=
  (∀ μ, 0 ≤ y μ) ∧ ∑ i, |∑ μ, y μ * ξ G i μ| < ∑ μ, y μ * (Ω G μ - G.L μ)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Valeur, aux prix `y`, de la part ajustable : `Σ_μ y μ Σ_i ξ i μ m i = Σ_i m i Σ_μ y μ ξ i μ`. -/
theorem price_adjustable (G : MGInst 𝕜 ι B) (y : B → 𝕜) (m : ι → 𝕜) :
    ∑ μ, y μ * ∑ i, ξ G i μ * m i = ∑ i, m i * ∑ μ, y μ * ξ G i μ := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- Dans la boîte, `-(m · c) ≤ |c|`. -/
theorem neg_mul_le_abs_of_box {m c : 𝕜} (hm : -1 ≤ m ∧ m ≤ 1) : -(m * c) ≤ |c| := by
  have h1 : |m| ≤ 1 := abs_le.mpr hm
  calc -(m * c) ≤ |m * c| := neg_le_abs _
    _ = |m| * |c| := abs_mul _ _
    _ ≤ 1 * |c| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |c| := one_mul _

/-- ★ Sens facile (dualité faible) : un certificat de prix d'état interdit le plafond. -/
theorem not_capFeasible_of_cert (G : MGInst 𝕜 ι B) {y : B → 𝕜}
    (hy : IsStatePriceCert G y) : ¬ CapFeasible G := by
  rintro ⟨m, hm, hcap⟩
  obtain ⟨hy0, hlt⟩ := hy
  have h1 : ∑ μ, y μ * (Ω G μ - G.L μ) ≤ ∑ μ, y μ * -(∑ i, ξ G i μ * m i) := by
    refine Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_left ?_ (hy0 μ)
    have := hcap μ
    rw [load_eq] at this
    linarith
  have h2 : ∑ μ, y μ * -(∑ i, ξ G i μ * m i) = ∑ i, -(m i * ∑ μ, y μ * ξ G i μ) := by
    simp only [mul_neg, Finset.sum_neg_distrib, price_adjustable]
  have h3 : ∑ i, -(m i * ∑ μ, y μ * ξ G i μ) ≤ ∑ i, |∑ μ, y μ * ξ G i μ| :=
    Finset.sum_le_sum fun i _ => neg_mul_le_abs_of_box (hm i)
  linarith

/-! ### Sens dur : codage dans le théorème de l'alternative d'EconCSLib

Variables `x : Fin n → 𝕜` (transport `ι ≃ Fin n`), lignes `B ⊕ ι ⊕ ι` :
- `inl μ` : `−Σ_i ξ i μ · m i ≥ Ω μ − L μ` (plafond) ;
- `inr (inl i)` : `m i ≥ −1` ;
- `inr (inr i)` : `−m i ≥ −1`. -/

section Hard

open EconCSLib.LinearAlgebra

/-- Matrice du système, colonnes indexées par `Fin (card ι)`. -/
noncomputable def capMat (G : MGInst 𝕜 ι B) :
    B ⊕ ι ⊕ ι → Fin (Fintype.card ι) → 𝕜 :=
  Sum.elim (fun μ j => -ξ G ((Fintype.equivFin ι).symm j) μ)
    (Sum.elim (fun i j => if Fintype.equivFin ι i = j then 1 else 0)
      (fun i j => if Fintype.equivFin ι i = j then -1 else 0))

/-- Second membre du système. -/
def capRhs (G : MGInst 𝕜 ι B) : B ⊕ ι ⊕ ι → 𝕜 :=
  Sum.elim (fun μ => Ω G μ - G.L μ) (Sum.elim (fun _ => -1) (fun _ => -1))

theorem capFeasible_of_isFeasible (G : MGInst 𝕜 ι B) :
    IsFeasible (capMat G) (capRhs G) → CapFeasible G := by
  rintro ⟨x, hx⟩
  refine ⟨fun i => x (Fintype.equivFin ι i), fun i => ⟨?_, ?_⟩, fun μ => ?_⟩
  · have := hx (Sum.inr (Sum.inl i))
    simpa [rowEval, capMat, capRhs] using this
  · have := hx (Sum.inr (Sum.inr i))
    simp only [rowEval, capMat, capRhs, Sum.elim_inr, ite_mul, neg_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    linarith
  · have := hx (Sum.inl μ)
    simp only [rowEval, capMat, capRhs, Sum.elim_inl, neg_mul, Finset.sum_neg_distrib] at this
    have hre : ∑ j, ξ G ((Fintype.equivFin ι).symm j) μ * x j
        = ∑ i, ξ G i μ * x (Fintype.equivFin ι i) := by
      rw [← (Fintype.equivFin ι).symm.sum_comp]
      simp
    rw [load_eq]
    rw [hre] at this
    linarith

/-- ★ Sens dur : l'infaisabilité du plafond produit un certificat de prix d'état. -/
theorem cert_of_not_capFeasible (G : MGInst 𝕜 ι B) (h : ¬ CapFeasible G) :
    ∃ y, IsStatePriceCert G y := by
  classical
  obtain ⟨u, hu0, hcol, hpos⟩ :=
    (theorem_of_alternative (capMat G) (capRhs G)).mp
      (fun hf => h (capFeasible_of_isFeasible G hf))
  set y : B → 𝕜 := fun μ => u (Sum.inl μ)
  set p : ι → 𝕜 := fun i => u (Sum.inr (Sum.inl i))
  set q : ι → 𝕜 := fun i => u (Sum.inr (Sum.inr i))
  -- colonne `e i` : `p i − q i = Σ_μ y μ ξ i μ`
  have hcol' : ∀ i, p i - q i = ∑ μ, y μ * ξ G i μ := by
    intro i
    have := hcol (Fintype.equivFin ι i)
    simp only [Fintype.sum_sum_type, capMat, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one,
      mul_zero, mul_neg, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib] at this
    simp only [p, q, y]
    linarith
  have hrhs : 0 < ∑ μ, y μ * (Ω G μ - G.L μ) - ∑ i, p i - ∑ i, q i := by
    simp only [Fintype.sum_sum_type, capRhs, Sum.elim_inl, Sum.elim_inr, mul_neg, mul_one,
      Finset.sum_neg_distrib] at hpos
    simp only [p, q, y]
    linarith
  refine ⟨y, fun μ => hu0 _, ?_⟩
  have habs : ∀ i, |∑ μ, y μ * ξ G i μ| ≤ p i + q i := by
    intro i
    rw [← hcol' i]
    have hp : 0 ≤ p i := hu0 _
    have hq : 0 ≤ q i := hu0 _
    rw [abs_le]
    constructor <;> linarith
  calc ∑ i, |∑ μ, y μ * ξ G i μ| ≤ ∑ i, (p i + q i) := Finset.sum_le_sum fun i _ => habs i
    _ = ∑ i, p i + ∑ i, q i := Finset.sum_add_distrib
    _ < ∑ μ, y μ * (Ω G μ - G.L μ) := by linarith

end Hard

/-- ★ Théorème de l'alternative pour le plafond par fibre : faisable ssi aucun certificat de
prix d'état. -/
theorem capFeasible_iff_not_cert (G : MGInst 𝕜 ι B) :
    CapFeasible G ↔ ¬ ∃ y, IsStatePriceCert G y := by
  classical
  refine ⟨fun hf ⟨y, hy⟩ => not_capFeasible_of_cert G hy hf, fun hn => ?_⟩
  by_contra h
  exact hn (cert_of_not_capFeasible G h)

/-! ## §4. Densité d'Arrow–Debreu -/

/-- ★ Un certificat reste un certificat à une échelle `c > 0` près. -/
theorem cert_smul (G : MGInst 𝕜 ι B) {y : B → 𝕜} (hy : IsStatePriceCert G y) {c : 𝕜}
    (hc : 0 < c) : IsStatePriceCert G (fun μ => c * y μ) := by
  obtain ⟨hy0, hlt⟩ := hy
  refine ⟨fun μ => mul_nonneg hc.le (hy0 μ), ?_⟩
  have e1 : ∑ i, |∑ μ, c * y μ * ξ G i μ| = c * ∑ i, |∑ μ, y μ * ξ G i μ| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ μ, c * y μ * ξ G i μ = c * ∑ μ, y μ * ξ G i μ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => mul_assoc _ _ _
    rw [this, abs_mul, abs_of_pos hc]
  have e2 : ∑ μ, c * y μ * (Ω G μ - G.L μ) = c * ∑ μ, y μ * (Ω G μ - G.L μ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => mul_assoc _ _ _
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hlt hc

/-- La masse d'un certificat est strictement positive. -/
theorem cert_sum_pos (G : MGInst 𝕜 ι B) {y : B → 𝕜} (hy : IsStatePriceCert G y) :
    0 < ∑ μ, y μ := by
  obtain ⟨hy0, hlt⟩ := hy
  by_contra h
  have h0 : ∑ μ, y μ = 0 := le_antisymm (not_lt.mp h) (Finset.sum_nonneg fun μ _ => hy0 μ)
  have hz : ∀ μ, y μ = 0 := fun μ =>
    (Finset.sum_eq_zero_iff_of_nonneg fun ν _ => hy0 ν).mp h0 μ (Finset.mem_univ _)
  simp [hz] at hlt

/-- ★ Normalisation : un certificat peut être pris de masse 1, c'est-à-dire comme une loi de
probabilité sur la base (prix d'état normalisés). -/
theorem cert_normalize (G : MGInst 𝕜 ι B) {y : B → 𝕜} (hy : IsStatePriceCert G y) :
    ∃ y', IsStatePriceCert G y' ∧ ∑ μ, y' μ = 1 := by
  have hs := cert_sum_pos G hy
  refine ⟨fun μ => (∑ ν, y ν)⁻¹ * y μ, cert_smul G hy (inv_pos.mpr hs), ?_⟩
  rw [← Finset.mul_sum, inv_mul_cancel₀ hs.ne']

/-- Densité de prix d'état relativement à la mesure de base `ρ` (sur son support). -/
def stateDensity (ρ y : B → 𝕜) (μ : B) : 𝕜 := y μ / ρ μ

/-- Certificat écrit comme densité `q` relativement à `ρ` : les sommes sont des espérances sous
`ρ`. -/
def IsDensityCert (G : MGInst 𝕜 ι B) (ρ q : B → 𝕜) : Prop :=
  (∀ μ, 0 ≤ q μ) ∧
    ∑ i, |∑ μ, ρ μ * (q μ * ξ G i μ)| < ∑ μ, ρ μ * (q μ * (Ω G μ - G.L μ))

/-- ★ Lecture de Radon–Nikodym : sous `ρ > 0`, `y` est un certificat ssi sa densité `y / ρ` en
est un, en espérance sous `ρ`. -/
theorem cert_iff_density (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 < ρ μ) (y : B → 𝕜) :
    IsStatePriceCert G y ↔ IsDensityCert G ρ (stateDensity ρ y) := by
  have hk : ∀ μ (z : 𝕜), ρ μ * (stateDensity ρ y μ * z) = y μ * z := fun μ z => by
    unfold stateDensity
    field_simp [(hρ μ).ne']
  simp only [IsDensityCert, IsStatePriceCert, hk]
  refine and_congr (forall_congr' fun μ => ?_) Iff.rfl
  rw [stateDensity, le_div_iff₀ (hρ μ), zero_mul]

/-- Réciproque : une densité `q ≥ 0` relativement à `ρ > 0` donne les prix `ρ q`. -/
theorem density_iff_cert (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 < ρ μ) (q : B → 𝕜) :
    IsDensityCert G ρ q ↔ IsStatePriceCert G (fun μ => ρ μ * q μ) := by
  simp only [IsDensityCert, IsStatePriceCert, mul_assoc]
  refine and_congr (forall_congr' fun μ => ?_) Iff.rfl
  exact (mul_nonneg_iff_of_pos_left (hρ μ)).symm

/-- ★ Le plafond par fibre est faisable ssi aucune densité de prix d'état relativement à la
mesure de base `ρ > 0` ne l'interdit. Hors du support de `ρ` (états jamais visités, par exemple
sous η = 1 quand l'information se fige), la densité n'est pas définie : c'est le problème
d'équivalence des mesures, et `cert_iff_density` exige `ρ > 0`. -/
theorem capFeasible_iff_no_density (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 < ρ μ) :
    CapFeasible G ↔ ¬ ∃ q, IsDensityCert G ρ q := by
  rw [capFeasible_iff_not_cert]
  refine not_congr ⟨fun ⟨y, hy⟩ => ⟨_, (cert_iff_density G hρ y).mp hy⟩,
    fun ⟨q, hq⟩ => ⟨_, (density_iff_cert G hρ q).mp hq⟩⟩

/-! ## §5. `Ω` = part non ajustable ; bande atteignable ; budget `stock` -/

omit [Fintype ι] [Fintype B] in
/-- La part ajustable de `i` sur `μ` est nulle ssi ses deux stratégies y chargent pareil : ses
lettres y sont **incontrôlables** par la mesure. -/
theorem xi_eq_zero_iff (G : MGInst 𝕜 ι B) (i : ι) (μ : B) :
    ξ G i μ = 0 ↔ G.aP i μ = G.aM i μ := by
  simp [ξ, sub_eq_zero]

omit [Fintype B] in
/-- Si `ξ i μ = 0`, la charge de `μ` ne dépend pas de la section de `i`. -/
theorem load_indep (G : MGInst 𝕜 ι B) {m m' : ι → 𝕜} {μ : B} {i : ι} (hξ : ξ G i μ = 0)
    (hm : ∀ k, k ≠ i → m k = m' k) : load G m μ = load G m' μ := by
  rw [load_eq, load_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    simp [hξ]
  · rw [hm k hk]

omit [Fintype B] in
/-- ★ **Bande atteignable** : dans la boîte, une section ne déplace la charge de `μ` que de la
masse ajustable `Σ_i |ξ i μ|` autour de la part non ajustable `Ω μ`. -/
theorem load_band (G : MGInst 𝕜 ι B) {m : ι → 𝕜} (hm : Box m) (μ : B) :
    |load G m μ - Ω G μ| ≤ ∑ i, |ξ G i μ| := by
  rw [load_eq, add_sub_cancel_left]
  calc |∑ i, ξ G i μ * m i| ≤ ∑ i, |ξ G i μ * m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ξ G i μ| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr (hm i))

/-- Charge minimale atteignable de la fibre `μ`. -/
def minLoad (G : MGInst 𝕜 ι B) (μ : B) : 𝕜 := Ω G μ - ∑ i, |ξ G i μ|

omit [Fintype B] in
theorem minLoad_le_load (G : MGInst 𝕜 ι B) {m : ι → 𝕜} (hm : Box m) (μ : B) :
    minLoad G μ ≤ load G m μ := by
  have := (abs_le.mp (load_band G hm μ)).1
  unfold minLoad
  linarith

/-- ★ Excès moyen (sonde S12) : si, sous une mesure `ρ ≥ 0`, l'excès moyen de la part non
ajustable dépasse ce que les sections peuvent déplacer en moyenne, aucune mesure ne tient le
plafond (`y = ρ` est un certificat). -/
theorem not_capFeasible_of_mean_excess (G : MGInst 𝕜 ι B) {ρ : B → 𝕜} (hρ : ∀ μ, 0 ≤ ρ μ)
    (h : ∑ i, |∑ μ, ρ μ * ξ G i μ| < ∑ μ, ρ μ * (Ω G μ - G.L μ)) : ¬ CapFeasible G :=
  not_capFeasible_of_cert G ⟨hρ, h⟩

/-- Budget `stock` sur la suite d'états visités `s : Fin T → B` : une seule fibre (`Unit`),
des agents `Fin T × ι` (la section peut **changer à chaque pas** : toute dynamique des mesures
est couverte), capacité = le budget cumulé `Bud`. -/
def stockAggregate (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) (Bud : 𝕜) :
    MGInst 𝕜 (Fin T × ι) Unit where
  aP := fun ti _ => G.aP ti.2 (s ti.1)
  aM := fun ti _ => G.aM ti.2 (s ti.1)
  L := fun _ => Bud

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype B] in
/-- La charge de l'agrégat est la charge cumulée le long de la suite d'états visités. -/
theorem stockAggregate_load (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) (Bud : 𝕜)
    (m : Fin T × ι → 𝕜) :
    load (stockAggregate G s Bud) m () = ∑ t, load G (fun i => m (t, i)) (s t) := by
  simp only [load, stockAggregate, Fintype.sum_prod_type]

omit [IsStrictOrderedRing 𝕜] [Fintype B] in
/-- Le plafond de l'agrégat est le budget cumulé, à sections variables dans le temps. -/
theorem stock_capFeasible_iff (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) (Bud : 𝕜) :
    CapFeasible (stockAggregate G s Bud) ↔
      ∃ m : Fin T → ι → 𝕜, (∀ t, Box (m t)) ∧ ∑ t, load G (m t) (s t) ≤ Bud := by
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨fun t i => m (t, i), fun t i => hm (t, i), by
      rw [← stockAggregate_load]; exact h ()⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨fun ti => m ti.1 ti.2, fun ti => hm ti.1 ti.2, fun _ => ?_⟩
    rw [stockAggregate_load]
    exact h

omit [Fintype B] in
/-- ★ Le certificat d'un budget `stock` est un **scalaire** (un prix unique sur tout
l'horizon : lecture de Hotelling, `RightsIntertemporal.hotelling_no_ponzi`) ; il existe ssi le
budget est sous la demande minimale atteignable cumulée. -/
theorem stock_cert_iff (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) (Bud : 𝕜) :
    (∃ y, IsStatePriceCert (stockAggregate G s Bud) y) ↔ Bud < ∑ t, minLoad G (s t) := by
  have hΩ : Ω (stockAggregate G s Bud) () = ∑ t, Ω G (s t) := by
    simp only [Ω, stockAggregate, Fintype.sum_prod_type]
  have hA : ∀ Y : 𝕜, 0 ≤ Y → ∑ ti : Fin T × ι, |Y * ξ (stockAggregate G s Bud) ti ()|
      = Y * ∑ t, ∑ i, |ξ G i (s t)| := by
    intro Y hY
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg hY]
    rfl
  have hm : ∑ t, minLoad G (s t) = ∑ t, Ω G (s t) - ∑ t, ∑ i, |ξ G i (s t)| := by
    simp only [minLoad, Finset.sum_sub_distrib]
  simp only [IsStatePriceCert, Fintype.sum_unique, PUnit.default_eq_unit]
  constructor
  · rintro ⟨y, hy0, hlt⟩
    rw [hA _ (hy0 ()), hΩ] at hlt
    have := lt_of_mul_lt_mul_left hlt (hy0 ())
    rw [hm]
    have hL : (stockAggregate G s Bud).L () = Bud := rfl
    linarith
  · intro h
    refine ⟨fun _ => 1, fun _ => zero_le_one, ?_⟩
    rw [hA _ zero_le_one, hΩ]
    have hL : (stockAggregate G s Bud).L () = Bud := rfl
    rw [hm] at h
    rw [hL]
    linarith

omit [Fintype B] in
/-- ★ Un budget `stock` est infaisable pour toute dynamique des mesures ssi il est sous la
demande minimale atteignable cumulée (sens dur par Farkas, ici élémentaire). -/
theorem stock_infeasible_iff (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) (Bud : 𝕜) :
    ¬ CapFeasible (stockAggregate G s Bud) ↔ Bud < ∑ t, minLoad G (s t) := by
  rw [capFeasible_iff_not_cert, not_not, stock_cert_iff]

omit [Fintype B] in
/-- ★ **La mesure ne peut pas** : sous la demande minimale atteignable cumulée, toute suite de
sections de la boîte dépasse le budget (preuve directe par la bande atteignable). -/
theorem stock_measure_cannot (G : MGInst 𝕜 ι B) {T : ℕ} (s : Fin T → B) {Bud : 𝕜}
    (h : Bud < ∑ t, minLoad G (s t)) (m : Fin T → ι → 𝕜) (hm : ∀ t, Box (m t)) :
    Bud < ∑ t, load G (m t) (s t) :=
  lt_of_lt_of_le h (Finset.sum_le_sum fun t _ => minLoad_le_load G (hm t) (s t))

/-! ## §6. Témoins sur ℚ -/

/-- Témoin de conservation : deux agents, deux fibres ; la stratégie « + » charge la fibre 0,
la stratégie « − » la fibre 1. Toute section charge 2 au total. -/
def consInst (c : ℚ) : MGInst ℚ (Fin 2) (Fin 2) where
  aP := fun _ μ => if μ = 0 then 1 else 0
  aM := fun _ μ => if μ = 0 then 0 else 1
  L := fun _ => c

/-- Prix d'état uniformes `y = (1, 1)` : certificat pour la capacité 1/2 par fibre. -/
theorem consInst_cert : IsStatePriceCert (consInst (1 / 2)) (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, ?_⟩
  simp [consInst, Ω, ξ, Fin.sum_univ_two]
  norm_num

/-- ★ Couplage par la section : chaque fibre seule est tenable sous 1/2… -/
theorem consInst_fiberwise (μ : Fin 2) :
    ∃ m, Box m ∧ load (consInst (1 / 2)) m μ ≤ 1 / 2 := by
  refine ⟨fun _ => if μ = 0 then -1 else 1, fun _ => ?_, ?_⟩
  · split_ifs <;> norm_num
  · fin_cases μ <;> simp [load, consInst]

/-- ★ … mais pas les deux ensemble : la section est commune aux fibres. -/
theorem consInst_infeasible : ¬ CapFeasible (consInst (1 / 2)) :=
  not_capFeasible_of_cert _ consInst_cert

/-- Avec la capacité 1 par fibre, la section neutre `m = 0` tient le plafond. -/
theorem consInst_feasible : CapFeasible (consInst 1) := by
  refine ⟨fun _ => 0, fun _ => by norm_num, fun μ => ?_⟩
  fin_cases μ <;> simp [load, consInst]

/-- Témoin `stock` : une fibre ; l'agent 0 charge 1 quelle que soit sa stratégie (lettres
incontrôlables, `ξ = 0`) ; les agents 1 et 2 choisissent entre 1 et 0. Demande naturelle
(`m = 0`) : 2 par pas ; demande minimale atteignable : 1 par pas. -/
def stockInst : MGInst ℚ (Fin 3) (Fin 1) where
  aP := fun _ _ => 1
  aM := fun i _ => if i = 0 then 1 else 0
  L := fun _ => 0

/-- ★ Sur 4 pas, un budget de 3 (< 4 = demande minimale cumulée) est infaisable pour toute
dynamique des mesures, et le certificat est le prix scalaire `1`. -/
theorem stockInst_infeasible :
    ¬ CapFeasible (stockAggregate stockInst (fun _ : Fin 4 => (0 : Fin 1)) 3) := by
  rw [stock_infeasible_iff]
  simp [minLoad, Ω, ξ, stockInst, Fin.sum_univ_three]
  norm_num

end MeasureFibration
