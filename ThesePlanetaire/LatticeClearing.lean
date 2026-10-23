/-
  MonnaiesEndogene/LatticeClearing.lean
  Phase 6 (Block F) : Clearing sur treillis complet — opérateur de clearing
  et théorème de point fixe (Knaster-Tarski).

  Références : Csóka–Herings 2024 ; Ghrist et al. 2025 ; Bourbaki-Witt (Ch.8).
-/

import ThesePlanetaire.Basic
import ThesePlanetaire.Dioid
import Mathlib.Data.Fintype.Prod

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ### Section 1 — Opérateur de clearing sur le treillis des états d'activation

  L'espace des états d'activation `ActivationState V = Finset (V×V)` est un
  treillis complet pour `⊆` (quand V est fini). Un opérateur de clearing `Φ`
  agit sur ce treillis en produisant l'état post-clearing à partir d'un état
  pré-clearing. -/

/-- Opérateur de clearing : fonction sur le treillis des états d'activation.
    `Φ(S)` = état après application du mécanisme de clearing à `S`. -/
def ClearingOperator (V : Type*) [DecidableEq V] :=
  ActivationState V → ActivationState V

namespace ClearingOperator

/-- Un opérateur de clearing satisfait les axiomes de section (closure operator)
    s'il est :
    1. idempotent : Φ(Φ(S)) = Φ(S)
    2. extensif    : S ⊆ Φ(S)
    3. monotone    : S ⊆ T → Φ(S) ⊆ Φ(T)
    Ces trois propriétés caractérisent un opérateur de closure (Moore family). -/
structure IsClearingSection (Φ : ClearingOperator V) : Prop where
  idempotent : ∀ S, Φ (Φ S) = Φ S
  extensive  : ∀ S, S ⊆ Φ S
  monotone   : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T

/-- Un opérateur de clearing est *sovereign* s'il préserve la contrainte once-only :
    si une arête est déjà activée, le clearing ne la désactive pas. -/
def IsSovereignClearing (Φ : ClearingOperator V) : Prop :=
  ∀ S e, e ∈ S → e ∈ Φ S

/-- `IsClearingSection` implique `IsSovereignClearing`. -/
lemma clearingSection_implies_sovereign (Φ : ClearingOperator V) (h : IsClearingSection Φ) :
    IsSovereignClearing Φ := by
  intro S e he
  exact h.extensive S he

end ClearingOperator

/-! ### Section 2 — Chaînes de Bourbaki-Witt (fini)

  Deux chaînes d'itération dans le cadre fini :
  - `bourbaki_witt_chain` : depuis ∅, croissante si Φ extensif.
  - `bw_gfp_chain` : depuis univ, décroissante si Φ monotone. -/

/-- Itération de Kleene (Bourbaki-Witt) depuis ∅.
    `bourbaki_witt_chain Φ n` = état après n itérations. -/
def bourbaki_witt_chain (Φ : ClearingOperator V) : ℕ → ActivationState V
  | 0     => ∅
  | n + 1 => Φ (bourbaki_witt_chain Φ n)

/-- Itération depuis univ (pour le plus grand point fixe).
    `bw_gfp_chain Φ n` = Φ^n(univ). -/
def bw_gfp_chain (Φ : ClearingOperator V) : ℕ → ActivationState V
  | 0     => univ
  | n + 1 => Φ (bw_gfp_chain Φ n)

/-- La chaîne depuis ∅ est croissante quand Φ est monotone et extensif. -/
lemma bourbaki_witt_chain_mono (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T)
    (h_ext : ∀ S, S ⊆ Φ S) :
    ∀ n, bourbaki_witt_chain Φ n ⊆ bourbaki_witt_chain Φ (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [bourbaki_witt_chain]
  | succ n ih =>
    simp [bourbaki_witt_chain]
    exact h_mono ih

/-- La chaîne depuis univ est décroissante quand Φ est monotone. -/
lemma bw_gfp_chain_antimono (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T) :
    ∀ n, bw_gfp_chain Φ (n + 1) ⊆ bw_gfp_chain Φ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp [bw_gfp_chain] at hx ⊢
  | succ n ih =>
    simp [bw_gfp_chain]
    exact h_mono ih

/-- Dans un cadre fini, la chaîne de Bourbaki-Witt stabilise en au plus
    |V×V| étapes (pigeonhole sur les cardinaux).

    La suite S₀ = ∅, S_{n+1} = Φ(S_n) est croissante. Si elle ne stabilise pas,
    les cardinaux sont strictement croissants. Une suite strictement croissante
    de cardinaux de longueur N+1 dans [0, N] est impossible. -/
theorem bourbaki_witt_finite_stabilization (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T)
    (h_ext : ∀ S, S ⊆ Φ S)
    [Fintype V] :
    ∃ (n : ℕ), n ≤ Fintype.card V * Fintype.card V ∧
      bourbaki_witt_chain Φ n = bourbaki_witt_chain Φ (n + 1) := by
  by_contra h
  push Not at h
  -- Inclusion stricte si pas stabilisé
  have h_strict : ∀ n, n ≤ Fintype.card V * Fintype.card V →
      bourbaki_witt_chain Φ n ⊂ bourbaki_witt_chain Φ (n + 1) := by
    intro n hn
    have h_sub := bourbaki_witt_chain_mono Φ h_mono h_ext n
    have h_ne : bourbaki_witt_chain Φ n ≠ bourbaki_witt_chain Φ (n + 1) := h n hn
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨h_sub, h_ne⟩
  -- Card strictement croissant
  have h_card_strict : ∀ n, n ≤ Fintype.card V * Fintype.card V →
      (bourbaki_witt_chain Φ n).card < (bourbaki_witt_chain Φ (n + 1)).card := by
    intro n hn
    exact Finset.card_lt_card (h_strict n hn)
  -- Induction : card(m) ≥ m
  have h_ind : ∀ m, m ≤ Fintype.card V * Fintype.card V + 1 →
      (bourbaki_witt_chain Φ m).card ≥ m := by
    intro m hm
    induction m with
    | zero => simp [bourbaki_witt_chain]
    | succ m ih =>
      have hm' : m ≤ Fintype.card V * Fintype.card V := by omega
      have h_lt := h_card_strict m hm'
      have h_ih := ih (by omega)
      omega
  have h_lower := h_ind (Fintype.card V * Fintype.card V + 1) (by simp)
  have h_upper : (bourbaki_witt_chain Φ (Fintype.card V * Fintype.card V + 1)).card ≤
      Fintype.card V * Fintype.card V := by
    have h_sub : bourbaki_witt_chain Φ (Fintype.card V * Fintype.card V + 1) ⊆
        (univ : Finset (V × V)) := subset_univ _
    have h_card : (bourbaki_witt_chain Φ (Fintype.card V * Fintype.card V + 1)).card ≤
        (univ : Finset (V × V)).card := Finset.card_le_card h_sub
    rw [Finset.card_univ, Fintype.card_prod] at h_card
    exact h_card
  omega

/-- Dans un cadre fini, la chaîne depuis univ stabilise en au plus |V×V| étapes
    (pigeonhole dual). -/
theorem bw_gfp_finite_stabilization (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T)
    [Fintype V] :
    ∃ (n : ℕ), n ≤ Fintype.card V * Fintype.card V ∧
      bw_gfp_chain Φ n = bw_gfp_chain Φ (n + 1) := by
  by_contra h
  push Not at h
  -- Inclusion stricte décroissante si pas stabilisé
  have h_strict : ∀ n, n ≤ Fintype.card V * Fintype.card V →
      bw_gfp_chain Φ (n + 1) ⊂ bw_gfp_chain Φ n := by
    intro n hn
    have h_sub := bw_gfp_chain_antimono Φ h_mono n
    have h_ne : bw_gfp_chain Φ n ≠ bw_gfp_chain Φ (n + 1) := by
      intro h_eq
      have := h n hn
      rw [h_eq] at this
      contradiction
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨h_sub, by tauto⟩
  -- Card strictement décroissant
  have h_card_strict : ∀ n, n ≤ Fintype.card V * Fintype.card V →
      (bw_gfp_chain Φ (n + 1)).card < (bw_gfp_chain Φ n).card := by
    intro n hn
    exact Finset.card_lt_card (h_strict n hn)
  -- Suite décroissante : card(m) ≤ N - m pour m ≤ N
  let N := Fintype.card V * Fintype.card V
  have h_ind : ∀ m, m ≤ N → (bw_gfp_chain Φ m).card ≤ N - m := by
    intro m hm
    induction m with
    | zero =>
      dsimp [bw_gfp_chain]
      simp [Fintype.card_prod]
      omega
    | succ m ih =>
      have hm' : m ≤ N := by omega
      have h_lt := h_card_strict m hm'
      have h_ih := ih (by omega)
      omega
  have h_card_N : (bw_gfp_chain Φ N).card = 0 := by
    specialize h_ind N (by omega)
    omega
  have h_empty : bw_gfp_chain Φ N = ∅ := Finset.card_eq_zero.mp h_card_N
  have h_strict_N : bw_gfp_chain Φ (N + 1) ⊂ bw_gfp_chain Φ N := h_strict N (by omega)
  rw [h_empty] at h_strict_N
  -- On a bw_gfp_chain Φ (N + 1) ⊂ ∅, impossible
  have h_sub_empty : bw_gfp_chain Φ (N + 1) ⊆ ∅ := (Finset.ssubset_iff_subset_ne.mp h_strict_N).1
  have h_eq_empty : bw_gfp_chain Φ (N + 1) = ∅ := Finset.subset_empty.mp h_sub_empty
  have h_ne_empty : bw_gfp_chain Φ (N + 1) ≠ ∅ := (Finset.ssubset_iff_subset_ne.mp h_strict_N).2
  contradiction

/-- Si la chaîne stabilise à l'étape n, alors cet état est un point fixe de Φ. -/
theorem bourbaki_witt_fixed_point (Φ : ClearingOperator V) (n : ℕ)
    (h_stab : bourbaki_witt_chain Φ n = bourbaki_witt_chain Φ (n + 1)) :
    Φ (bourbaki_witt_chain Φ n) = bourbaki_witt_chain Φ n := by
  cases n with
  | zero =>
    simp [bourbaki_witt_chain] at h_stab ⊢
    exact h_stab.symm
  | succ n =>
    simp [bourbaki_witt_chain] at h_stab ⊢
    exact h_stab.symm

/-- Si la chaîne gfp stabilise à l'étape n, alors c'est un point fixe. -/
theorem bw_gfp_fixed_point (Φ : ClearingOperator V) (n : ℕ)
    (h_stab : bw_gfp_chain Φ n = bw_gfp_chain Φ (n + 1)) :
    Φ (bw_gfp_chain Φ n) = bw_gfp_chain Φ n := by
  cases n with
  | zero =>
    simp [bw_gfp_chain] at h_stab ⊢
    exact h_stab.symm
  | succ n =>
    simp [bw_gfp_chain] at h_stab ⊢
    exact h_stab.symm

/-! ### Section 3 — Théorème de Knaster-Tarski (cadre fini)

  Pour `ActivationState V = Finset (V×V)` avec `V` fini, tout opérateur
  monotone extensif admet un plus petit point fixe (par itération de Kleene
  depuis ∅). Tout opérateur monotone admet un plus grand point fixe (par
  chaîne décroissante depuis univ). -/

/-- Théorème de Knaster-Tarski (plus petit point fixe) dans le cadre fini.

    Preuve par itération de Kleene depuis ∅. La chaîne S₀ = ∅, S_{n+1} = Φ(S_n)
    est croissante car Φ est extensif. Dans un ensemble fini de cardinal N, elle
    stabilise en ≤ N étapes (pigeonhole). L'état de stabilisation est un point
    fixe de Φ. -/
theorem KnasterTarski_lfp_exists (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T)
    (h_ext : ∀ S, S ⊆ Φ S)
    [Fintype V] :
    ∃ (S_fix : ActivationState V), Φ S_fix = S_fix := by
  have h_stab := bourbaki_witt_finite_stabilization Φ h_mono h_ext
  rcases h_stab with ⟨n, _, h_eq⟩
  use bourbaki_witt_chain Φ n
  exact bourbaki_witt_fixed_point Φ n h_eq

/-- Théorème de Knaster-Tarski (plus grand point fixe) dans le cadre fini.

    Preuve par chaîne décroissante depuis univ. La chaîne T₀ = univ,
    T_{n+1} = Φ(T_n) est décroissante car Φ est monotone. Dans un ensemble
    fini, elle stabilise (pigeonhole). L'état de stabilisation est le plus
    grand point fixe. -/
theorem KnasterTarski_gfp_exists (Φ : ClearingOperator V)
    (h_mono : ∀ ⦃S T⦄, S ⊆ T → Φ S ⊆ Φ T)
    [Fintype V] :
    ∃ (S_fix : ActivationState V), Φ S_fix = S_fix ∧
      ∀ (T : ActivationState V), Φ T = T → T ⊆ S_fix := by
  have h_stab := bw_gfp_finite_stabilization Φ h_mono
  rcases h_stab with ⟨n, _, h_eq⟩
  use bw_gfp_chain Φ n
  constructor
  · -- Point fixe
    exact bw_gfp_fixed_point Φ n h_eq
  · -- Plus grand point fixe
    intro T h_Tfix
    have h_sub_n : ∀ n, T ⊆ bw_gfp_chain Φ n := by
      intro n
      induction n with
      | zero =>
        simp [bw_gfp_chain]
      | succ n ih =>
        have h_ΦT_sub : Φ T ⊆ Φ (bw_gfp_chain Φ n) := h_mono ih
        rw [h_Tfix] at h_ΦT_sub
        simp [bw_gfp_chain]
        exact h_ΦT_sub
    exact h_sub_n n

#check ClearingOperator
#check ClearingOperator.IsClearingSection
#check KnasterTarski_lfp_exists
