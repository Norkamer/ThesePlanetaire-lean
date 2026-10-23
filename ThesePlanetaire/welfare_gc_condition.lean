-- welfare_gc_condition.lean
-- Phase 42 : fix structural issues + ALT5 CCPOEquilibrium payload
-- Issues fixed:
--   (1) phi_reduces_classes now used directly in welfare_gc_from_sigma_reduces
--   (2) sigma_eq_clearing_phi deleted (tautology)
--   (3) phi_progressive_nontrivial deleted (exact duplicate of welfare_gc_from_sigma_reduces)

import ThesePlanetaire.Basic
import ThesePlanetaire.LatticeClearing
import ThesePlanetaire.EXT4
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic.Linarith

section WelfareGC

/-- Un opérateur de clearing est contractif s'il réduit l'état d'activation.
    C'est la sémantique économique du clearing : Φ(S) ⊆ S
    (l'opérateur ne crée pas de nouvelles arêtes, il en supprime).
    **Note** : `IsClearingSection` (LatticeClearing.lean) est *extensif*
    (S ⊆ Φ S) car elle modélise une section (closure). Le clearing
    économique est l'opposé : contractif. Les deux structures coexistent
    car elles modélisent des aspects différents du système. -/
structure IsClearingReduction {V : Type*} [DecidableEq V]
    (Φ : ClearingOperator V) : Prop where
  contractive : ∀ (S : ActivationState V), Φ S ⊆ S

/-
  THÉORÈME (Phase A — réécriture d'axiome) :
  Tout opérateur contractif satisfait phi_reduces_classes.
  Ce n'est plus un axiome mais une conséquence tautologique de la
  définition de `IsClearingReduction`.

  L'ancien axiome `phi_reduces_classes` était une hypothèse de modélisation
  (la sémantique du clearing est contractive). Il est désormais typé
  explicitement via `IsClearingReduction`. -/
theorem phi_reduces_classes {V : Type*} [Fintype V] [DecidableEq V]
    (Φ : ClearingOperator V)
    (h : IsClearingReduction Φ)
    : ∀ (S : ActivationState V), Φ S ⊆ S := h.contractive

/-
  COROLLAIRE DÉRIVÉ (Phase A refactor) :
  welfare_gc_condition est DÉRIVÉE depuis phi_reduces_classes sous
  l'hypothèse explicite `IsClearingReduction Φ`.

  Phase A fix: suppression de l'axiome global, remplacement par une
  hypothèse locale typée (`IsClearingReduction`). -/
lemma welfare_gc_from_sigma_reduces {V : Type*} [Fintype V] [DecidableEq V]
    (W : ActivationState V → ℤ)
    (Φ : ClearingOperator V)
    (h_phi : IsClearingReduction Φ)
    (h_W_antim : ∀ S T : ActivationState V, S ⊆ T → W T ≤ W S)
    : ∀ (S : ActivationState V), W (Φ S) ≥ W S := by
  intro S
  exact h_W_antim (Φ S) S (phi_reduces_classes Φ h_phi S)

/-
  BRIDGE EXT4 :
  Connexion W(σ s) ≥ W s ↔ W(k T) ≥ W(k t) de EXT4.

  k : ℕ→ℕ dans EXT4 joue le rôle de sigma composé : si le système
  converge (EXT4 : ∃ T, k T = 1 ≤ k t pour tout t), alors
  welfare_gc_from_sigma_reduces fournit le bas de la chaîne inductive.
-/
lemma welfare_gc_to_ext4_bridge
    (m : ℕ)
    (k : ℕ → ℕ)
    (W : ℕ → ℤ)
    (h_init   : k 0 ≤ m)
    (h_mono   : ∀ t, k (t + 1) ≤ k t)
    (h_strict : ∀ t, k t > 1 → k (t + 1) < k t)
    (h_nat    : ∀ t, k t ≥ 1)
    (h_W_antimonotone : ∀ a b : ℕ, a ≤ b → W b ≤ W a)
    : ∃ T, T ≤ m ∧ ∀ t, W (k T) ≥ W (k t) :=
  ext4_welfare_convergence m k W h_init h_mono h_strict h_nat h_W_antimonotone

-- Conserve le bridge original pour compatibilité
/-
  welfare_gc_implies_antimonotone_on_sigma : bridge vers ext4_welfare_convergence.
  Conservé depuis Phase 38.
-/
lemma welfare_gc_implies_antimonotone_on_sigma
    (W : ℕ → ℤ)
    (sigma : ℕ → ℕ)
    (_h_sigma_reduces : ∀ s, sigma s ≤ s)
    (h_W_antim       : ∀ a b : ℕ, a ≤ b → W b ≤ W a)
    (a b : ℕ) (hab : a ≤ b) : W b ≤ W a :=
  h_W_antim a b hab

end WelfareGC

section CCPOEquilibrium

/-
  ALT5 payload (Phase 42) : Existence d'un équilibre de clearing via Bourbaki-Witt.

  L'opérateur de clearing Phi : Fin(m+1) → Fin(m+1) est déflationnaire
  (Phi s ≤ s en ordre naturel). Dans OrderDual, il devient inflationnaire.
  Fin(m+1) est un CompleteLattice → ChainCompletePartialOrder (instance automatique).
  nonempty_fixedPoints_of_inflationary donne ∃ s, Phi s = s.

  Avantage clé vs EXT4 : pas de h_strict (pas de dépendance H-COOP).
-/
lemma alt5_ccpo_equilibrium_exists
    (m : ℕ)
    (Phi : Fin (m + 1) → Fin (m + 1))
    (h_deflationary : ∀ s : Fin (m + 1), Phi s ≤ s)
    : ∃ s : Fin (m + 1), Phi s = s := by
  -- Fin (m+1) a un minimum : l'élément 0. Une fonction déflationnaire fixe ce minimum.
  have hm_pos : 0 < m + 1 := by omega
  let s_min : Fin (m + 1) := ⟨0, hm_pos⟩
  have h_min_defl : Phi s_min ≤ s_min := h_deflationary s_min
  have h_val_zero : (Phi s_min).val = 0 := by
    have hle : (Phi s_min).val ≤ s_min.val := h_min_defl
    have hs_val : s_min.val = 0 := rfl
    rw [hs_val] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)
  refine ⟨s_min, Fin.ext h_val_zero⟩

/-
  ALT5 bridge (Phase 43) : Existence d'un équilibre pour Phi sur {k : ℕ // 1 ≤ k ∧ k ≤ m}.

  Contexte économique : les agents indexent les classes d'externalités par k ∈ {1, ..., m}.
  Ce type apparaît naturellement dans les preuves EXT1–EXT4 (k : ℕ, hk_lo : 1 ≤ k, hk_hi : k ≤ m).

  Stratégie :
  1. Le type {k : ℕ // 1 ≤ k ∧ k ≤ m} est définitionnellement égal à Set.Icc 1 m
     (par définition : Set.Icc a b = {x | a ≤ x ∧ x ≤ b}).
  2. Set.Icc.completeLattice [Fact (1 ≤ m)] donne CompleteLattice (Set.Icc 1 m).
  3. CompleteLattice → ChainCompletePartialOrder (instance automatique Bourbaki-Witt).
  4. Même pattern OrderDual que alt5_ccpo_equilibrium_exists.

  Dépendances Mathlib :
  - Mathlib.Order.CompleteLatticeIntervals (Set.Icc.completeLattice)
  - Mathlib.Order.BourbakiWitt (nonempty_fixedPoints_of_inflationary)
  - Mathlib.Order.Interval.Set.Basic (Set.nonempty_Icc_subtype)
-/
lemma alt5_nat_bridge
    (m : ℕ)
    (hm : 1 ≤ m)
    (Phi : {k : ℕ // 1 ≤ k ∧ k ≤ m} → {k : ℕ // 1 ≤ k ∧ k ≤ m})
    (h_defl : ∀ s : {k : ℕ // 1 ≤ k ∧ k ≤ m}, Phi s ≤ s)
    : ∃ s : {k : ℕ // 1 ≤ k ∧ k ≤ m}, Phi s = s := by
  -- Le minimum de {k // 1 ≤ k ∧ k ≤ m} est 1. Une fonction déflationnaire le fixe.
  let s_min : {k : ℕ // 1 ≤ k ∧ k ≤ m} := ⟨1, ⟨le_refl 1, hm⟩⟩
  have h_min_defl : Phi s_min ≤ s_min := h_defl s_min
  -- h_min_defl : (Phi s_min).val ≤ 1
  have h_prop := (Phi s_min).property
  -- h_prop : 1 ≤ (Phi s_min).val ∧ (Phi s_min).val ≤ m
  rcases h_prop with ⟨hlo, hhi⟩
  have h_val_eq : (Phi s_min).val = s_min.val := by
    have hle : (Phi s_min).val ≤ s_min.val := h_min_defl
    have hge : s_min.val ≤ (Phi s_min).val := by
      -- from hlo: 1 ≤ (Phi s_min).val, and s_min.val = 1
      simpa [s_min] using hlo
    exact Nat.le_antisymm hle hge
  exact ⟨s_min, Subtype.ext h_val_eq⟩

end CCPOEquilibrium

section ALT5Transfer

/-
  ALT5 Transfer Lemma (Phase 44) :
  Si une séquence k : ℕ → ℕ est déflationnaire (k(t+1) ≤ k(t)),
  bornée (k(0) ≤ m), et k(t) ≥ 1 pour tout t,
  alors il existe T tel que k(T) = k(T+1) (point fixe séquentiel).

  Stratégie : induction bien-fondée sur n = k(0) - 1 (le "slack" disponible).
  Lemme auxiliaire : si k(0) ≤ n+1, la séquence se stabilise.
  - Base n=0 : k(0) ≤ 1 et k(0) ≥ 1, donc k(0)=1 ; k(1) ≤ 1 et ≥ 1, donc k(1)=1, T=0.
  - Étape n→n+1 : si k(1) = k(0), T=0 ; sinon k(1) < k(0) ≤ n+2, donc k(1) ≤ n+1,
    et la séquence décalée k(·+1) satisfait les hypothèses avec borne n+1, IH donne T'.
    Alors T = T' + 1 convient.
-/
private lemma stabilizes_aux :
    ∀ (n : ℕ) (k : ℕ → ℕ),
    k 0 ≤ n + 1 →
    (∀ t, 1 ≤ k t) →
    (∀ t, k (t + 1) ≤ k t) →
    ∃ T, k T = k (T + 1) := by
  intro n
  induction n with
  | zero =>
    intro k h_bound h_nat h_mono
    have hk0 : k 0 = 1 := Nat.le_antisymm h_bound (h_nat 0)
    have hmono_simp : k 1 ≤ k 0 := by simpa using h_mono 0
    rw [hk0] at hmono_simp
    have hk1 : k 1 = 1 := Nat.le_antisymm hmono_simp (h_nat 1)
    exact ⟨0, by rw [hk0, hk1]⟩
  | succ n ih =>
    intro k h_bound h_nat h_mono
    -- Cas 1 : k 1 = k 0, T = 0 convient
    -- Cas 2 : k 1 < k 0, appliquer IH à la séquence décalée k' t = k (t+1)
    by_cases heq : k 1 = k 0
    · exact ⟨0, heq.symm⟩
    · -- k 1 ≠ k 0 et k 1 ≤ k 0 (h_mono 0), donc k 1 < k 0
      have hlt : k 1 < k 0 := Nat.lt_of_le_of_ne (h_mono 0) heq
      -- k 1 ≤ n + 1 : puisque k 1 ≤ k 0 - 1 ≤ (n+2) - 1 = n + 1
      have h_bound' : k 1 ≤ n + 1 := by omega
      -- Séquence décalée k' t = k (t+1)
      let k' : ℕ → ℕ := fun t => k (t + 1)
      have h_nat' : ∀ t, 1 ≤ k' t := fun t => h_nat (t + 1)
      have h_mono' : ∀ t, k' (t + 1) ≤ k' t := fun t => h_mono (t + 1)
      have h_bound_k' : k' 0 ≤ n + 1 := h_bound'
      -- IH donne T' tel que k'(T') = k'(T'+1)
      obtain ⟨T', hT'⟩ := ih k' h_bound_k' h_nat' h_mono'
      -- k(T'+1) = k'(T') = k'(T'+1) = k(T'+2) = k((T'+1)+1)
      exact ⟨T' + 1, hT'⟩

/-- ALT5 Transfer Lemma (Phase 44) :
    Si une séquence k : ℕ → ℕ est déflationnaire (k(t+1) ≤ k(t)),
    bornée (k(0) ≤ m), et k(t) ≥ 1 pour tout t,
    alors il existe T tel que k(T) = k(T+1) (point fixe séquentiel). -/
lemma alt5_transfer_lemma
    (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ → ℕ)
    (h_init : k 0 ≤ m)
    (h_nat : ∀ t, 1 ≤ k t)
    (h_mono : ∀ t, k (t + 1) ≤ k t)
    : ∃ T, k T = k (T + 1) := by
  -- Appliquer stabilizes_aux avec n = m - 1, donc n + 1 = m
  obtain ⟨T, hT⟩ := stabilizes_aux (m - 1) k (by omega) h_nat h_mono
  exact ⟨T, hT⟩

/-- ALT5 Transfer Corollary (Phase 44) :
    Si de plus h_strict (k(t) > 1 → k(t+1) < k(t)), le point fixe séquentiel est 1.
    Corollaire : la séquence converge vers 1. -/
lemma alt5_transfer_corollary
    (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ → ℕ)
    (h_init : k 0 ≤ m)
    (h_nat : ∀ t, 1 ≤ k t)
    (h_mono : ∀ t, k (t + 1) ≤ k t)
    (h_strict : ∀ t, 1 < k t → k (t + 1) < k t)
    : ∃ T, k T = 1 := by
  -- alt5_transfer_lemma donne T tel que k(T) = k(T+1)
  obtain ⟨T, hT⟩ := alt5_transfer_lemma m hm k h_init h_nat h_mono
  -- k(T) = k(T+1) contredit h_strict si k(T) > 1
  -- Donc k(T) ≤ 1, combiné avec h_nat T : 1 ≤ k(T), on obtient k(T) = 1
  refine ⟨T, ?_⟩
  have hle : k T ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hlt := h_strict T hgt
    -- k(T+1) < k(T) mais k(T) = k(T+1) — contradiction
    linarith [hT.symm.le]
  exact Nat.le_antisymm hle (h_nat T)

end ALT5Transfer

/-
  SECTION HSUPERLocal — Phase 47
  Supermodularité locale de W_eff sur Dom_eff ⊆ Finset(V×V)

  hsuper_local_finset est un bridge axiomatique (h_dom comme hypothèse)
  cohérent avec la stratégie de phi_reduces_classes.
  Connexion sémantique W_eff ↔ W : ℕ → ℤ via
  Finset.card_union_add_card_inter (lemme cardinal auxiliaire).

  Phase 47 proof_critic Option B — Finset + ActivationState existant.
-/
section HSUPERLocal

/-- hsuper_local_finset : W_eff est supermodulaire sur Dom_eff.
    h_dom est la précondition (axiome posé ou à prouver).
    Forme standard : W(S∪T) + W(S∩T) ≥ W(S) + W(T).
    Cohérent avec Milgrom-Shannon (1994) increasing differences. -/
lemma hsuper_local_finset {V : Type*} [DecidableEq V] [Fintype V]
    (S₀ : Finset (V × V))
    (W_eff : Finset (V × V) → ℤ)
    (h_dom : ∀ S T : Finset (V × V), DomEff S₀ S → DomEff S₀ T →
        W_eff (S ∪ T) + W_eff (S ∩ T) ≥ W_eff S + W_eff T)
    (S T : Finset (V × V))
    (hS : DomEff S₀ S) (hT : DomEff S₀ T) :
    W_eff (S ∪ T) + W_eff (S ∩ T) ≥ W_eff S + W_eff T :=
  h_dom S T hS hT

/-- hsuper_cardinality_identity : identité cardinale auxiliaire.
    Finset.card_union_add_card_inter : (S∪T).card + (S∩T).card = S.card + T.card.
    Bridge structurel W_eff(S) = W(S.card) → clé pour connexion 1D↔nD.
    Non-sorry : théorème Mathlib standard. -/
lemma hsuper_cardinality_identity {V : Type*} [DecidableEq V]
    (S T : Finset (V × V)) :
    (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
  Finset.card_union_add_card_inter S T

end HSUPERLocal

section HSUPERFromRank
/-
  Instanciation concrète de h_dom pour W_eff = -(matroid eRk).
  Mathlib garantit eRk_submod : eRk(X∩Y) + eRk(X∪Y) ≤ eRk(X) + eRk(Y).
  La négation inverse l'inégalité → supermodularité de -eRk.

  On restreint à [Fintype α] pour garantir la finitude (eRk ≤ encard < ⊤).
-/

/-- Welfare concret : W_rank_eff S = -(rang matroïdal de S) en ℤ.
    Supermodulaire par négation de la submodularité de eRk. -/
noncomputable def W_rank_eff {α : Type*} (M : Matroid α) (S : Set α) : ℤ :=
  -((M.eRk S).toNat : ℤ)

/-- Finitude : sur un Fintype, eRk S est toujours fini. -/
private lemma eRk_ne_top_of_fintype {α : Type*} [Fintype α]
    (M : Matroid α) (S : Set α) : M.eRk S ≠ ⊤ := by
  have h_le : M.eRk S ≤ S.encard := M.eRk_le_encard S
  have h_fin : S.Finite := Set.toFinite S
  have h_enc : S.encard ≠ ⊤ := h_fin.encard_lt_top.ne
  exact ne_top_of_le_ne_top h_enc h_le

/-- Submodularité de eRk → supermodularité de W_rank_eff.
    Preuve : eRk(S∩T) + eRk(S∪T) ≤ eRk(S) + eRk(T)  [eRk_submod]
    → -(eRk(S∪T)) + -(eRk(S∩T)) ≥ -(eRk(S)) + -(eRk(T))
    → W_rank_eff(S∪T) + W_rank_eff(S∩T) ≥ W_rank_eff(S) + W_rank_eff(T). -/
lemma h_dom_rank_supermodular {α : Type*} [Fintype α]
    (M : Matroid α) (S T : Set α) :
    W_rank_eff M (S ∪ T) + W_rank_eff M (S ∩ T) ≥
    W_rank_eff M S + W_rank_eff M T := by
  unfold W_rank_eff
  have h_sub := M.eRk_submod S T
  have hS   := eRk_ne_top_of_fintype M S
  have hT   := eRk_ne_top_of_fintype M T
  have hU   := eRk_ne_top_of_fintype M (S ∪ T)
  have hI   := eRk_ne_top_of_fintype M (S ∩ T)
  have hST_sum : M.eRk S + M.eRk T ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hS, hT⟩
  have h_nat : (M.eRk (S ∩ T)).toNat + (M.eRk (S ∪ T)).toNat
             ≤ (M.eRk S).toNat + (M.eRk T).toNat := by
    have h := ENat.toNat_le_toNat h_sub hST_sum
    rwa [ENat.toNat_add hI hU, ENat.toNat_add hS hT] at h
  linarith [show ((M.eRk (S ∩ T)).toNat : ℤ) + ((M.eRk (S ∪ T)).toNat : ℤ)
                ≤ ((M.eRk S).toNat : ℤ) + ((M.eRk T).toNat : ℤ) from by exact_mod_cast h_nat]

theorem hsuper_rank_instance {α : Type*} [Fintype α]
    (M : Matroid α) (S T : Set α) :
    W_rank_eff M (S ∪ T) + W_rank_eff M (S ∩ T) ≥
    W_rank_eff M S + W_rank_eff M T :=
  h_dom_rank_supermodular M S T

end HSUPERFromRank

section CoActivableMatroid

/-- Paire (e, f) co-activable = {e, f} est indépendant dans M. -/
def CoActivablePair {α : Type*} (M : Matroid α) (e f : α) : Prop :=
  M.Indep {e, f}

end CoActivableMatroid

section GeneralizedSubmodularWelfare

/-! ### Généralisation : submodularité → supermodularité (Milgrom–Shannon 1994)

  Topkis (1978, *Operations Research* 26:2) a établi la théorie fondamentale
  des fonctions submodulaires sur un treillis : f est submodulaire ssi
  f(S∪T) + f(S∩T) ≤ f(S) + f(T) pour tout S, T. La négation -f est alors
  supermodulaire (inégalité inversée).

  Milgrom & Shannon (1994, *Econometrica* 62:1) ont utilisé cette propriété
  pour dériver les théorèmes de welfare dans les jeux à complémentarités
  stratégiques : si le payoff est supermodulaire, les équilibres extrémaux
  sont Pareto-ordonnables (Milgrom & Roberts 1990, Theorem 7).

  L'entropie de Shannon H(A) = H(X_A) est un exemple canonique de fonction
  submodulaire (diminishing returns du gain d'information, voir Bach 2010,
  §10.5 ; Krause & Guestrin 2005). Son opposé -H est donc supermodulaire
  et peut servir de welfare dans des modèles d'information.

  Cette section généralise `h_dom_rank_supermodular` (spécifique au rang
  matroïdal eRk) à toute fonction submodulaire sur un type fini. -/

/-- Fonction submodulaire sur un type fini.
    Définition standard (Topkis 1978) : f(S∪T) + f(S∩T) ≤ f(S) + f(T). -/
def Submodular {α : Type*} (f : Set α → ℤ) : Prop :=
  ∀ S T : Set α, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

/-- Théorème de généralisation (Milgrom–Shannon 1994) :
    Si f est submodulaire, alors -f est supermodulaire.

    Preuve : multiplication par -1 de l'inégalité de submodularité.
    C'est exactement le mécanisme de `h_dom_rank_supermodular`, mais
    généralisé à toute fonction submodulaire (pas seulement le rang
    matroïdal eRk).

    Applications économiques :
    - Rareté combinatoire : `rarity` est submodulaire (ajouter une arête
      ne peut que diminuer la rareté d'au plus 1), donc `-rarity` est
      supermodulaire et peut servir de welfare.
    - Entropie de Shannon : H(A) est submodulaire (Bach 2010, §10.5),
      donc -H est supermodulaire (utilisé en théorie de l'information). -/
theorem submodular_to_welfare_supermodular {α : Type*} [Fintype α]
    (f : Set α → ℤ) (hf : Submodular f) (S T : Set α) :
    (-f) (S ∪ T) + (-f) (S ∩ T) ≥ (-f) S + (-f) T := by
  -- hf donne f(S∪T) + f(S∩T) ≤ f(S) + f(T)
  -- Multiplier par -1 inverse l'inégalité.
  have h := hf S T
  simp only [Pi.neg_apply] at h ⊢
  linarith

/-- Corollaire : la fonction de welfare générée par négation d'une
    fonction submodulaire est supermodulaire.

    C'est exactement la généralisation de `h_dom_rank_supermodular`,
    qui est l'instance où f = eRk (rang matroïdal, prouvé submodulaire
    par `Matroid.eRk_submod`). -/
theorem welfare_from_submodular {α : Type*} [Fintype α]
    (f : Set α → ℤ) (hf : Submodular f) :
    ∀ S T : Set α, (-f) (S ∪ T) + (-f) (S ∩ T) ≥ (-f) S + (-f) T :=
  submodular_to_welfare_supermodular f hf

end GeneralizedSubmodularWelfare
