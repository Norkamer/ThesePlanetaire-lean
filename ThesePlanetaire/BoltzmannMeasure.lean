/-
  MonnaiesEndogene/BoltzmannMeasure.lean
  Mesure de Boltzmann B_p sur M_EXT1 et Cascade Depth Index (CDI).

  B_p(τ) = p^{|τ|} / (1+p)^{|Σ|}  (Th.5.3 Cat A)
  CDI(p) = -p * M'(p)/M(p)        (Th.6.1 Cat B, monoïde libre)
  CDI_EXT1(p) = n*p/(1+p)          (indépendance totale, cas particulier)

  Référence Python : boltzmann.py (BoltzmannMeasure), cdi.py (cascade_depth_index).
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
import ThesePlanetaire.TraceMonoid
import ThesePlanetaire.MobiusPolynomial

open TraceMonoid

namespace BoltzmannMeasure

/-- Mesure de Boltzmann B_p sur M_EXT1 (Th.5.3 Cat A).
    B_p(τ) = p^{|τ|} / (1+p)^{|Σ|}
    Sous EXT1, chaque lettre est incluse indépendamment avec probabilité p/(1+p). -/
structure BoltzmannMeasure where
  alphabetSize : ℕ
  p : NNReal

/-- Probabilité d'inclusion par lettre : q = p/(1+p).
    Si p = 0, retourne 0 (pas de division par zéro). -/
noncomputable def inclusionProb (bm : BoltzmannMeasure) : ℝ :=
  if (bm.p : ℝ) = 0 then 0 else (bm.p : ℝ) / (1 + (bm.p : ℝ))

/-- Fonction de partition EXT1 : Z_M(p) = (1+p)^{|Σ|} = Σ_{S⊆Σ} p^{|S|}. -/
noncomputable def partition (bm : BoltzmannMeasure) : ℝ :=
  ((1 : ℝ) + (bm.p : ℝ)) ^ bm.alphabetSize

theorem partition_pos (bm : BoltzmannMeasure) : 0 < partition bm := by
  unfold partition; positivity

theorem partition_nonneg (bm : BoltzmannMeasure) : 0 ≤ partition bm :=
  le_of_lt (partition_pos bm)

/-- B_p(τ) = p^{|τ|} / (1+p)^{|Σ|} pour |τ| ≤ |Σ|, 0 sinon.
    Th.5.4 (Cat B) : B_p(τ) > 0 ssi τ satisfait EXT1 (|τ| ≤ |Σ|). -/
noncomputable def prob (bm : BoltzmannMeasure) (t : Trace) : ℝ :=
  if Trace.length t > bm.alphabetSize then 0
  else ((bm.p : ℝ) ^ Trace.length t) / partition bm

/-- La garde d'admissibilité EXT1 (branche rejet) : une trace de longueur > |Σ| a
    probabilité 0 — pas plus d'obligations actives que d'instruments. Pendant mesure des
    filtres d'admissibilité du système (physicalCondition per-boundary, budget gates). -/
theorem prob_eq_zero_of_length_gt (bm : BoltzmannMeasure) (t : Trace)
    (h : Trace.length t > bm.alphabetSize) :
    prob bm t = 0 := by
  dsimp [prob]
  rw [if_pos h]

/-- La garde d'admissibilité EXT1 (branche admissible) : pour |τ| ≤ |Σ|,
    B_p(τ) = p^{|τ|} / Z. -/
theorem prob_eq_of_length_le (bm : BoltzmannMeasure) (t : Trace)
    (h : Trace.length t ≤ bm.alphabetSize) :
    prob bm t = (bm.p : ℝ) ^ Trace.length t / partition bm := by
  dsimp [prob]
  rw [if_neg (not_lt_of_ge h)]

/-- La probabilité est toujours ≥ 0 car p ≥ 0 et (1+p)^n > 0. -/
theorem prob_nonneg (bm : BoltzmannMeasure) (t : Trace) : 0 ≤ prob bm t := by
  dsimp [prob, partition]
  by_cases hk : Trace.length t > bm.alphabetSize
  · simp [hk]
  · simp [hk]
    have hp : 0 ≤ (bm.p : ℝ) := NNReal.coe_nonneg _
    apply div_nonneg
    · exact pow_nonneg hp _
    · positivity

/-- La probabilité est ≤ 1 : p^k ≤ (1+p)^k ≤ (1+p)^n. -/
theorem prob_le_one (bm : BoltzmannMeasure) (t : Trace) : prob bm t ≤ 1 := by
  dsimp [prob, partition]
  by_cases hk : Trace.length t > bm.alphabetSize
  · simp [hk]
  · simp [hk]
    have hp : 0 ≤ (bm.p : ℝ) := NNReal.coe_nonneg _
    have hp_bound : (bm.p : ℝ) ≤ (1 : ℝ) + (bm.p : ℝ) := by linarith
    have h_denom : 0 < ((1 : ℝ) + (bm.p : ℝ)) ^ bm.alphabetSize := by positivity
    have hk' : Trace.length t ≤ bm.alphabetSize := by omega
    have h_one_plus_p_ge_one : 1 ≤ (1 : ℝ) + (bm.p : ℝ) := by linarith
    have h1 : (bm.p : ℝ) ^ Trace.length t ≤ ((1 : ℝ) + (bm.p : ℝ)) ^ Trace.length t :=
      pow_le_pow_left₀ hp hp_bound (Trace.length t)
    have h2 : ((1 : ℝ) + (bm.p : ℝ)) ^ Trace.length t ≤ ((1 : ℝ) + (bm.p : ℝ)) ^ bm.alphabetSize :=
      pow_le_pow_right₀ h_one_plus_p_ge_one hk'
    have h_num : (bm.p : ℝ) ^ Trace.length t ≤ ((1 : ℝ) + (bm.p : ℝ)) ^ bm.alphabetSize :=
      le_trans h1 h2
    exact div_le_one_of_le₀ h_num h_denom.le

/-- Espérance de |τ| sous B_p : E[|τ|] = n * p/(1+p).
    Formule close issue de la loi binomiale (chaque lettre incluse indépendamment). -/
noncomputable def expectedLength (bm : BoltzmannMeasure) : ℝ :=
  (bm.alphabetSize : ℝ) * inclusionProb bm

/-- Once-only pour BoltzmannMeasure : si τ1 ∩ τ2 = ∅ et |τ1|+|τ2| ≤ |Σ|,
    alors B_p(τ1 ∪ τ2) = B_p(τ1)·B_p(τ2) / B_p(∅).

    **Once-only unifié (F6)** — 4 formalismes, 1 loi :
    - mesure-théorique (canonique) : `prob_once_only` (ici) ;
    - combinatoire : `Article6.double_count_iff_not_squarefree` (double
      comptage ⟺ non-squarefree) ;
    - instance fusion : `FusedAlphabet.fused_double_count_iff_not_squarefree`
      (levée sur le coproduit Letter ⊕ (V×V)) ;
    - probabiliste : `prob_eq_inclusionProb_product` (F8 — indépendance
      totale, traduction probabiliste de l'once-only). -/
theorem prob_once_only (bm : BoltzmannMeasure) (t1 t2 : Trace)
    (h_disjoint : t1.letters ∩ t2.letters = ∅)
    (h_size : Trace.length t1 + Trace.length t2 ≤ bm.alphabetSize) :
    prob bm (t1.concat t2) = prob bm t1 * prob bm t2 / prob bm (Trace.empty) := by
  have h_len : Trace.length (t1.concat t2) = Trace.length t1 + Trace.length t2 :=
    Trace.length_concat t1 t2 h_disjoint
  have h_le_u : Trace.length (t1.concat t2) ≤ bm.alphabetSize := by rw [h_len]; exact h_size
  have h_le1 : Trace.length t1 ≤ bm.alphabetSize := by omega
  have h_le2 : Trace.length t2 ≤ bm.alphabetSize := by omega
  have h_le0 : Trace.length (Trace.empty) ≤ bm.alphabetSize := by
    simp [Trace.empty, Trace.length]
  rw [prob, if_neg (by omega : ¬(Trace.length (t1.concat t2) > bm.alphabetSize))]
  rw [prob, if_neg (by omega : ¬(Trace.length t1 > bm.alphabetSize))]
  rw [prob, if_neg (by omega : ¬(Trace.length t2 > bm.alphabetSize))]
  rw [prob, if_neg (by omega : ¬(Trace.length (Trace.empty) > bm.alphabetSize))]
  have h_card : (t1.concat t2).letters.card = t1.letters.card + t2.letters.card := by
    simpa [Trace.length] using h_len
  simp [h_card, Trace.empty, Trace.length]
  rw [pow_add]
  dsimp [partition]
  all_goals field_simp

theorem expectedLength_eq (bm : BoltzmannMeasure) :
    expectedLength bm = (bm.alphabetSize : ℝ) * (bm.p : ℝ) / (1 + (bm.p : ℝ)) := by
  dsimp [expectedLength, inclusionProb]
  by_cases hp : (bm.p : ℝ) = 0
  · simp [hp]
  · simp [hp, mul_div_assoc]

/-- Structure produit (F8) : B_p(τ) = q^{|τ|} · (1-q)^{n-|τ|} avec q = p/(1+p).

    Chaque lettre/obligation est active **indépendamment** avec probabilité
    q = p/(1+p) — l'indépendance totale d'EXT1, traduction probabiliste de
    l'once-only (l'activation d'une obligation n'influence pas celle d'une
    autre ; pendant algébrique de l'algèbre squarefree x∪x = x).

    **Once-only unifié (F6)** : 4e formalisme de la loi unique — voir
    `prob_once_only` (mesure-théorique), `Article6.double_count_iff_not_squarefree`
    (combinatoire), `FusedAlphabet.fused_double_count_iff_not_squarefree` (instance). -/
theorem prob_eq_inclusionProb_product (bm : BoltzmannMeasure) (t : Trace)
    (h : Trace.length t ≤ bm.alphabetSize) :
    prob bm t = inclusionProb bm ^ Trace.length t *
      (1 - inclusionProb bm) ^ (bm.alphabetSize - Trace.length t) := by
  rw [prob_eq_of_length_le bm t h]
  dsimp [partition, inclusionProb]
  by_cases hp : (bm.p : ℝ) = 0
  · -- p = 0 : q = 0, 1-q = 1 — 0^0 = 1 vs 0^k = 0 selon |τ|
    by_cases hlen : Trace.length t = 0
    · simp [hp, hlen]
    · simp [hp, hlen]
  · -- p ≠ 0 : q = p/(1+p), 1-q = 1/(1+p)
    have h1p : (1 + (bm.p : ℝ)) ≠ 0 := by positivity
    have h1q : 1 - (bm.p : ℝ) / (1 + (bm.p : ℝ)) = 1 / (1 + (bm.p : ℝ)) := by
      field_simp [h1p]
      ring
    simp [hp]
    rw [div_pow, h1q, div_pow]
    simp only [one_pow]
    rw [div_mul_div_comm]
    simp only [mul_one]
    rw [← pow_add, Nat.add_sub_of_le h]

/-- Espérance de |τ|² sous B_p : formule binomiale n*q*(1-q) + n²*q²
    où q = p/(1+p). -/
noncomputable def expectedSquaredLength (bm : BoltzmannMeasure) : ℝ :=
  let n := (bm.alphabetSize : ℝ)
  let q := inclusionProb bm
  n * q * (1 - q) + (n * q) ^ 2

/-! ### Dérivée du polynôme de Möbius et CDI

  CDI(p) = -p * M'(p)/M(p)  (Th.6.1 Cat B)
  où M'(p) = dM/dp = Σ_{k=1}^n k * c_k * p^{k-1}. -/

/-- Dérivée du polynôme de Möbius : M'(p) = Σ_{k=1}^n k * c_k * p^{k-1}.
    Le terme k=0 est nul (dérivée d'une constante). -/
noncomputable def mobiusDerivative (mp : MobiusPolynomial.MobiusPolynomial) (p : NNReal) : ℝ :=
  let p_val := (p : ℝ)
  Finset.sum (Finset.range (mp.n + 1)) (λ k =>
    if k = 0 then 0
    else (k : ℝ) * (mp.coeff k : ℝ) * (p_val ^ (k - 1)))

/-- CDI(p) = -p * M'(p)/M(p) — formule close de Cartier-Foata (Th.6.1 Cat B).
    Valide pour M(p) > 0 (i.e., p < p*, rayon de convergence).
    Retourne 0 si M(p) = 0 (p = p*, divergence du CDI).

    Sous EXT1 avec indépendance totale, M(p) = (1-p)^n et
    CDI(p) = n*p/(1+p) = E[|τ|] (voir cdi_ext1). -/
noncomputable def cdi (mp : MobiusPolynomial.MobiusPolynomial) (bm : BoltzmannMeasure) : ℝ :=
  let p_val := (bm.p : ℝ)
  let m_p := MobiusPolynomial.evaluate mp bm.p
  let m_prime := mobiusDerivative mp bm.p
  if m_p = 0 then 0
  else -p_val * m_prime / m_p

/-- Sous indépendance totale, CDI(p) = n*p/(1+p) = expectedLength.
    Sous EXT1, M(p) = (1-p)^n → M'(p) = -n*(1-p)^{n-1} → CDI = n*p/(1-p)...
    NON, attention : EXT1 = Z_M(p) = (1+p)^n, pas 1/M.
    Pour le monoïde LIBRE (Cartier-Foata), Z_CF(p) = 1/M(p) et CDI = -p*M'/M.
    Sous indépendance totale du monoïde libre, M(p) = (1-p)^n non plus.
    La relation entre CDI et expectedLength dépend du régime (EXT1 vs Cartier-Foata).

    **Convention placeholder (F11)** : pont externe Ch.8 — doc
    auto-correctif (le commentaire ci-dessus documente le piège de régime).
    `True := by trivial`, JAMAIS cité comme preuve. -/
theorem cdi_ext1_independent (_bm : BoltzmannMeasure) : True := by
  trivial

end BoltzmannMeasure
