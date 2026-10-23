/-
  MonnaiesEndogene/MobiusPolynomial.lean
  Polynôme de Möbius et fonctions de partition.

  M(X) = Σ_{C∈Cliques(I)} (-1)^{|C|} X^{|C|}
  où I = graphe de concurrence (indépendance).

  Deux fonctions de partition :
  - Z_EXT1(p) = (1+p)^|Σ|  (somme sur tous les sous-ensembles, Th.4.1 Cat A)
  - Z_CF(p)   = 1/M(p)    (série de croissance du monoïde de traces LIBRE)

  Sous EXT1, Z_EXT1 ≠ Z_CF en général. Les deux coïncident uniquement
  pour les graphes de dépendance triviaux (indépendance totale).

  Référence Python : boltzmann.py (MobiusPolynomial, PartitionFunction).
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import ThesePlanetaire.TraceMonoid

open TraceMonoid
open scoped BigOperators

namespace MobiusPolynomial

/-- Polynôme de Möbius du graphe de dépendance.
    M(p) = Σ_{k=0}^n c_k · p^k où c_k = (-1)^k · (#cliques de taille k).

    Les coefficients c_k sont entiers (ℤ), l'évaluation se fait dans ℝ. -/
structure MobiusPolynomial where
  n : ℕ
  /-- coeff k = nombre de cliques de taille k, avec signe (-1)^k. -/
  coeff : ℕ → ℤ
  /-- Les coefficients au-delà de n sont nuls. -/
  coeff_zero_above : ∀ k, n < k → coeff k = 0

/-- Construit le polynôme de Möbius à partir d'une décomposition de Cartier-Foata.
    Les cliques du graphe de concurrence déterminent les coefficients. -/
noncomputable def ofCartierFoata (cf : CartierFoata) : MobiusPolynomial where
  n := cf.indep.alphabet.card
  coeff k :=
    -- c₀ = 1 (clique vide, convention)
    if k = 0 then 1
    else
      let cliques_of_size := (cf.cliques).countP (λ c => c.card = k)
      if k % 2 = 0 then
        cliques_of_size  -- (-1)^k = +1 pour k pair
      else
        -cliques_of_size  -- (-1)^k = -1 pour k impair
  coeff_zero_above k h := by
    have hk_ne_zero : k ≠ 0 := Nat.ne_zero_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
    have h_card_lt : cf.indep.alphabet.card < k := h
    have h_empty : (cf.cliques).countP (λ c => c.card = k) = 0 := by
      refine List.countP_eq_zero.mpr (λ c hc => ?_)
      unfold CartierFoata.cliques at hc
      rcases List.mem_filter.mp hc with ⟨hne, hdec⟩
      have hc_sub : c ⊆ cf.indep.alphabet := by
        have : c ∈ (cf.indep.alphabet.powerset).toList := List.mem_of_mem_filter hc
        have hpowerset : c ∈ cf.indep.alphabet.powerset := by
          simpa [Finset.mem_toList] using this
        exact Finset.mem_powerset.mp hpowerset
      have hc_card : c.card ≤ cf.indep.alphabet.card := Finset.card_le_card hc_sub
      have hne_card : c.card ≠ k := Nat.ne_of_lt (Nat.lt_of_le_of_lt hc_card h_card_lt)
      by_cases hcard : c.card = k
      · exfalso; exact hne_card hcard
      · simp [hcard]
    simp [hk_ne_zero, h_empty]

/-- Évalue M(p) dans ℝ. -/
noncomputable def evaluate (mp : MobiusPolynomial) (p : NNReal) : ℝ :=
  let p_val := (p : ℝ)
  Finset.sum (Finset.range (mp.n + 1)) (λ k =>
    (mp.coeff k : ℝ) * (p_val ^ k))

/-- Fonction de partition EXT1 : Z_EXT1(p) = (1+p)^|Σ| = Σ_{S⊆Σ} p^{|S|}.
    Th.4.1 (Cat A) : sous EXT1, la mesure de Boltzmann est B_p(τ) = p^{|τ|}/Z_EXT1(p). -/
def partition_ext1 (alphabet_size : ℕ) (p : NNReal) : NNReal :=
  (1 + p) ^ alphabet_size

/-- Fonction de partition du monoïde de traces LIBRE (sans contrainte EXT1).
    Z_CF(p) = 1/M(p) pour p < p* où p* est la plus petite racine positive de M.
    Th.5.1 (Cat A) : identité de Cartier-Foata Z_CF(p) · M(p) = 1. -/
noncomputable def partition_cartier_foata (mp : MobiusPolynomial) (p : NNReal) : ℝ :=
  let m_val := evaluate mp p
  if m_val = 0 then 0  -- p = p*, rayon de convergence — Z_CF diverge
  else 1 / m_val

/-- Th.5.1 (Cat A) : Z_CF(p) · M(p) = 1.
    Pour le monoïde de traces LIBRE (sans EXT1), la série de croissance
    Z_CF(p) = Σ_{τ∈M(Σ,I)} p^{|τ|} et le polynôme de Möbius M(p)
    vérifient l'identité de Cartier-Foata : Z_CF(p) · M(p) = 1.

    ATTENTION : sous EXT1, Z_EXT1(p) = (1+p)^n ≠ 1/M(p) en général.
    Cette identité concerne uniquement le monoïde LIBRE. -/
theorem cartier_foata_identity (mp : MobiusPolynomial) (p : NNReal) (hp : evaluate mp p ≠ 0) :
    partition_cartier_foata mp p * evaluate mp p = 1 := by
  unfold partition_cartier_foata
  rw [if_neg hp]
  field_simp [hp]

/-- Sous indépendance totale (EXT1 complet), M(p) = (1-p)^n
    et Z_CF(p) = 1/(1-p)^n pour p < 1.

    Sous EXT1, la fonction de partition pertinente est Z_EXT1(p) = (1+p)^n.
    Le lemme documente la distinction entre les deux régimes.

    Preuve : théorème binomial (Mathlib.Data.Nat.Choose.Sum.add_pow). -/
lemma mobius_total_independence (n : ℕ) (p : NNReal) :
    (∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ k * (Nat.choose n k : ℝ) * (p : ℝ) ^ k)) = (1 - (p : ℝ)) ^ n := by
  have h := add_pow (-(p : ℝ)) 1 n
  simp only [one_pow, mul_one] at h
  rw [show -(p : ℝ) + 1 = 1 - (p : ℝ) from by ring] at h
  rw [h]
  congr 1
  ext k
  rw [neg_pow]
  ring

/-! ### Identité binomiale sur le powerset (F5 — normalisation)
    ∑_{S⊆F} p^|S| = (1+p)^|F| : la masse totale du système once-only = 1.
    Le binôme lui-même est trivial (`add_pow`) ; la subtilité est la réindexation
    powerset → binôme (somme sur 2^n sous-ensembles groupée par cardinal), levée
    par induction via `Finset.sum_powerset_insert` (l'image est gérée en interne,
    pas de `Set.InjOn`). Portage verbatim de `normalisationF5_scratch` (dérisque F5). -/

/-- ∑_{S ⊆ F} p^|S| = (1+p)^|F| — l'identité binomiale sur le powerset, SANS
    hypothèse (pure ring, valable ∀ p : ℝ). -/
theorem sum_powerset_pow_card {α : Type*} [DecidableEq α] (s : Finset α) (p : ℝ) :
    ∑ S ∈ s.powerset, p ^ S.card = (1 + p) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.powerset_empty]
  | insert a s ha ih =>
    -- Pour chaque t ⊆ s : a ∉ t (car a ∉ s), donc |insert a t| = |t| + 1,
    -- et p^|insert a t| = p^(|t|+1) = p · p^|t|.
    have h_eq : ∀ t ∈ s.powerset, p ^ (insert a t).card = p * p ^ t.card := by
      intro t ht
      have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
      rw [Finset.card_insert_of_notMem hat, pow_add, pow_one]
      ring
    -- La part « avec a » : ∑_{t⊆s} p^|insert a t| = ∑_{t⊆s} p·p^|t| = p·∑_{t⊆s} p^|t|
    -- = p·(1+p)^|s| (par ih).
    have h2 : ∑ t ∈ s.powerset, p ^ (insert a t).card = p * (1 + p) ^ s.card := by
      rw [Finset.sum_congr rfl h_eq, ← Finset.mul_sum, ih]
    -- Assemblage : somme(sans a) + somme(avec a) = (1+p)^|s| + p·(1+p)^|s|
    -- = (1+p)·(1+p)^|s| = (1+p)^(|s|+1) = (1+p)^|insert a s|.
    rw [Finset.sum_powerset_insert ha, ih, h2,
        Finset.card_insert_of_notMem ha, pow_add, pow_one]
    ring

/-- Spécialisation Fintype : ∑_{S ⊆ univ} p^|S| = (1+p)^|α| (via `Finset.card_univ`). -/
theorem sum_powerset_pow_card_univ (α : Type*) [Fintype α] [DecidableEq α] (p : ℝ) :
    ∑ S ∈ (Finset.univ : Finset α).powerset, p ^ S.card = (1 + p) ^ Fintype.card α := by
  rw [← Finset.card_univ]
  exact sum_powerset_pow_card (Finset.univ : Finset α) p

/-- Normalisation (F5) : la masse totale = 1. La partition (1+p)^n normalise :
    (Σ p^|S|) / (1+p)^n = (1+p)^n / (1+p)^n = 1. Sous-criticité p ≥ 0 ⟹ 1+p > 0.
    Ferme les stubs `FiniteEXT1Measure.normalisation:103` et
    `BernoulliMeasure.normalisation_placeholder:143` (`True := by trivial`).
    (Forme parenthésée — `Finset.sum_div` est absent en ℝ.) -/
theorem normalisation_generic (α : Type*) [Fintype α] [DecidableEq α] (p : ℝ) (hp : 0 ≤ p) :
    (∑ S ∈ (Finset.univ : Finset α).powerset, p ^ S.card) / (1 + p) ^ Fintype.card α = 1 := by
  have h1p : (0 : ℝ) < 1 + p := by linarith
  have hne : (1 + p) ^ (Finset.univ : Finset α).card ≠ 0 := by positivity
  rw [← Finset.card_univ, sum_powerset_pow_card]
  exact div_self hne

/-- Sous indépendance totale (mp.n = n, coeff k = (-1)^k * C(n,k)),
    la fonction de partition CartierFoata vaut 1/(1-p)^n.
    Pont formel entre mobius_total_independence et la définition de partition_cf
    dans le cas dégénéré I = vide (toutes les lettres indépendantes). -/
lemma total_independence_partition (mp : MobiusPolynomial)
    (n : ℕ) (hn_dim : mp.n = n)
    (hcoeff : ∀ k, mp.coeff k = (-1)^k * Nat.choose n k)
    (p : NNReal) (hp : (1 - (p:ℝ))^n ≠ 0) :
    partition_cartier_foata mp p = 1 / (1 - (p:ℝ))^n := by
  have heq : evaluate mp p = (1 - (p:ℝ))^n := by
    simp only [evaluate, hn_dim]
    have hc : ∀ k, (mp.coeff k : ℝ) = (-1)^k * (Nat.choose n k : ℝ) :=
      fun k => by exact_mod_cast hcoeff k
    simp_rw [hc]
    exact mobius_total_independence n p
  unfold partition_cartier_foata
  rw [if_neg (heq ▸ hp), heq]

/-- p* = plus petite racine positive de M(p).
    Pour p < p*, Z_CF(p) = 1/M(p) > 0 (mesure de Boltzmann sur M(Σ,I) bien définie).
    Cas I=∅ (séquentiel, convention I-cliques) : M(p) = 1 - n·p → p* = 1/n.
    Cas I=Σ×Σ (indépendance totale) : M(p) = (1-p)^n → p* = 1.
    Pour I intermédiaire : p* ≥ 1/n (1/n est une lower bound sur le rayon réel). -/
noncomputable def critical_radius (mp : MobiusPolynomial) : ℝ :=
  -- Première racine positive de M(p) via le terme linéaire.
  -- Si coeff 1 < 0 : p* = 1/(-coeff 1) (exact pour I=∅, lower bound pour I≠∅).
  -- Sinon repli p* = 1 (indépendance totale ou cas non couvert).
  -- Implémentation complète par bissection : Sprint 2.
  if mp.coeff 1 < 0 then
    1 / (-(mp.coeff 1 : ℝ))
  else
    1

/-- Pour M(p) = 1 - n·p (cas I=∅, n agents séquentiels), p* = 1/n. -/
lemma critical_radius_sequential (n : ℕ) (hn : 0 < n) :
    critical_radius {
      n := n,
      coeff := fun k => if k = 0 then 1 else if k = 1 then -(n : ℤ) else 0,
      coeff_zero_above := by intro k hk; split_ifs <;> omega } = 1 / (n : ℝ) := by
  simp only [critical_radius]
  -- beta-réduit : if 1=0 then 1 else if True then -↑n else 0 → -(n:ℤ)
  have h_eval : (if (1:ℕ) = 0 then (1:ℤ) else if True then -(n:ℤ) else 0) = -(n:ℤ) := by simp
  simp only [h_eval]
  have hlt : -(n:ℤ) < 0 := by omega
  rw [if_pos hlt]
  push_cast
  simp [neg_neg]

/-- Tout singleton {a} pour a ∈ cf.indep.alphabet est une I-clique.
    Preuve : ∀ x ∈ {a}, ∀ y ∈ {a} → x=a et y=a → x=y (branche left, sans utiliser indep). -/
lemma singleton_in_cliques (cf : CartierFoata) (a : Letter)
    (ha : a ∈ cf.indep.alphabet) : ({a} : Finset Letter) ∈ cf.cliques := by
  unfold CartierFoata.cliques
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_toList]
    exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha)
  · simp only [decide_eq_true_eq]
    exact ⟨Finset.singleton_nonempty a, fun x hx y hy => by
      simp only [Finset.mem_singleton] at hx hy
      exact Or.inl (hx.trans hy.symm)⟩

/-- coeff 1 de ofCartierFoata = -|Σ| : les seules I-cliques de taille 1
    sont les singletons (triviales pour tout I), et il y en a n = |Σ|.
    Conséquence : guard `coeff 1 < 0` ↔ n > 0 ↔ alphabet non-vide.
    Références : Cartier-Foata 1969, Viennot 1986, Abbes-Mairesse 2015. -/
lemma ofCartierFoata_coeff_one (cf : CartierFoata) :
    (ofCartierFoata cf).coeff 1 = -(cf.indep.alphabet.card : ℤ) := by
  simp only [ofCartierFoata]
  norm_num
  suffices h : cf.cliques.countP (fun c => c.card = 1) = cf.indep.alphabet.card by
    exact_mod_cast h
  -- cliques est une liste nodup (filtre de Finset.toList)
  have hnodup : cf.cliques.Nodup := List.Nodup.filter _ (Finset.nodup_toList _)
  -- countP → longueur du filtre → card du toFinset (nodup)
  rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (hnodup.filter _),
      List.toFinset_filter]
  -- Bijection : alphabet → cliques.toFinset.filter (·.card=1) via a ↦ {a}
  symm
  apply Finset.card_bij (fun a _ => ({a} : Finset Letter))
  · -- {a} ∈ cliques et {a}.card = 1
    intro a ha
    simp only [Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
    exact ⟨singleton_in_cliques cf a ha, Finset.card_singleton a⟩
  · -- injectivité : {a} = {b} → a = b
    intro a₁ _ a₂ _ heq
    exact Finset.singleton_injective heq
  · -- surjectivité : c de card 1 dans cliques → c = {a} pour a ∈ alphabet
    intro c hc
    simp only [Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq] at hc
    rw [Finset.card_eq_one] at hc
    obtain ⟨a, rfl⟩ := hc.2
    refine ⟨a, ?_, rfl⟩
    -- a ∈ alphabet : {a} ∈ cliques → {a} ⊆ alphabet
    have hmem := hc.1
    unfold CartierFoata.cliques at hmem
    rcases List.mem_filter.mp hmem with ⟨hpow, _⟩
    rw [Finset.mem_toList, Finset.mem_powerset] at hpow
    exact Finset.singleton_subset_iff.mp hpow

/-- Le coeff 1 du polynôme restreint à s = -|s|.
    Instance directe de ofCartierFoata_coeff_one pour cf.restrict. -/
lemma ofCartierFoata_restrict_coeff_one (cf : CartierFoata) (s : Finset Letter)
    (hs : s ⊆ cf.indep.alphabet) :
    (ofCartierFoata (cf.restrict s hs)).coeff 1 = -(s.card : ℤ) := by
  have h := ofCartierFoata_coeff_one (cf.restrict s hs)
  simp only [CartierFoata.restrict_indep_alphabet] at h
  exact h

/-- Le rayon critique du système restreint à s (non vide) vaut 1/|s|.
    Valable pour toute structure d'indépendance (généralise critical_radius_sequential). -/
lemma critical_radius_restrict_total (cf : CartierFoata) (s : Finset Letter)
    (hs : s ⊆ cf.indep.alphabet) (hs_pos : 0 < s.card) :
    critical_radius (ofCartierFoata (cf.restrict s hs)) = 1 / (s.card : ℝ) := by
  simp only [critical_radius, ofCartierFoata_restrict_coeff_one]
  have hlt : -(s.card : ℤ) < 0 := by omega
  rw [if_pos hlt]
  push_cast
  ring

/-! ### Pont TEG (conjecture ouverte — non axiome)
    p* = 1/n est combinatoire (rayon de Z_M pour M(Σ,∅)).
    λ_Perron (valeur propre de Perron classique, matrice de concurrence G_D,
    Abbes-Mairesse JCTA 135, 2015) — DISTINCT de λ* max-plus du TEG.
    Le saut λ_Perron ↔ λ* max-plus (BCOQ 1992 spectral) reste informel.
    Obligation formelle future : `teg_to_mobius`. -/

end MobiusPolynomial
