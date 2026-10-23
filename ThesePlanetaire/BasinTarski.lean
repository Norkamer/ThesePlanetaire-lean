/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/BasinTarski.lean
  Phase 11 (2026-10-02), étape 11f : Tarski par bassin (question 1 du modèle de Renn) — sans
  complémentarités globales, la meilleure réponse n'est pas monotone ; il suffit qu'elle le soit
  au-dessus d'un noyau retenu pour que les équilibres contenant ce noyau forment un treillis
  atteint par la dynamique myope.

  Développé d'abord en `BasinTarski_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase11_2026-10-02/plan_phase11.md` ; analyse :
  `cache/analyse_phase11_adhesion_emetteurs_2026-10-02.md` §7 ; sonde G8
  (`cache/phase11_2026-10-02/outils/sonde_adhesion.py`).
-/

import ThesePlanetaire.AdhesionGame

/-!
# Tarski par bassin

Dans un jeu symétrique (`symGain M` : le gain d'adhérer ne dépend que du nombre d'autres
adhérents), un profil `M` non monotone — adhérer paie seul, plus à deux, de nouveau en nombre —
rend la meilleure réponse non monotone (★ `sym_not_monotone`) : Tarski ne s'applique pas sur tout
le treillis `Set V`. L'hypothèse nommée `BrMonoAbove g N` (meilleure réponse monotone sur les
coalitions contenant `N`) suffit à le rétablir sur le bassin de `N` :

1. `basinOp g N h : X ↦ N ∪ brSet g (N ∪ X)`, monotone ; sous rétention `N ⊆ brSet g N`,
   ★ `basin_fixed_iff` : ses points fixes sont exactement les équilibres contenant `N` ;
   ★ `basin_lfp_least`, `basin_gfp_greatest` : ils ont un plus petit et un plus grand élément.
2. ★ `basin_iterate` : depuis `N`, la dynamique myope non perturbée croît jusqu'au plus petit
   équilibre contenant `N` en au plus `card V − ncard N` pas.
3. ★ `sym_mono_above` : un profil monotone à partir du rang `m`, avec `m + 1 ≤ ncard N`, donne
   `BrMonoAbove`. ★ `basin_witness` : sur `Fin 4`, le noyau `{0, 1, 2}` allume tout, tandis que
   `{0}` reste un équilibre hors du bassin (le résidu).
-/

namespace BasinTarski

open AdhesionGame

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §1. Jeux symétriques, non-isotonie -/

/-- Jeu symétrique : le gain d'adhérer ne dépend que du nombre d'autres adhérents. -/
noncomputable def symGain (M : ℕ → 𝕜) : V → Set V → 𝕜 := fun _ S => M S.ncard

omit [IsStrictOrderedRing 𝕜] in
theorem mem_brSet_sym_coe [DecidableEq V] {M : ℕ → 𝕜} (A : Finset V) (i : V) :
    i ∈ brSet (symGain M) ↑A ↔ 0 ≤ M (A.erase i).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_erase]
  rfl

/-- Profil (+, −, +, +) : adhérer paie seul, pas face à un seul autre, de nouveau face à deux
ou plus. -/
def M4 : ℕ → ℚ := fun k => if k = 1 then -1 else 1

/-- ★ **Non-isotonie** : la meilleure réponse du profil `M4` n'est pas monotone. -/
theorem sym_not_monotone :
    brSet (symGain M4) (∅ : Set (Fin 4)) = Set.univ ∧
      brSet (symGain M4) ({0} : Set (Fin 4)) = {0} ∧
      ¬ Monotone (brSet (symGain M4 : Fin 4 → Set (Fin 4) → ℚ)) := by
  have h0 : brSet (symGain M4) (∅ : Set (Fin 4)) = Set.univ := by
    rw [← Finset.coe_empty, ← Finset.coe_univ]
    ext i
    rw [mem_brSet_sym_coe, Finset.mem_coe]
    revert i
    decide
  have h1 : brSet (symGain M4) ({0} : Set (Fin 4)) = {0} := by
    rw [← Finset.coe_singleton]
    ext i
    rw [mem_brSet_sym_coe, Finset.mem_coe]
    revert i
    decide
  refine ⟨h0, h1, fun hm => ?_⟩
  have := hm (Set.empty_subset ({0} : Set (Fin 4)))
  rw [h0, h1] at this
  have := this (Set.mem_univ (1 : Fin 4))
  simp at this

/-! ### §2. L'opérateur de bassin -/

/-- ★ Hypothèse nommée : la meilleure réponse est monotone sur les coalitions contenant `N`. -/
def BrMonoAbove (g : V → Set V → 𝕜) (N : Set V) : Prop :=
  ∀ X Y, N ⊆ X → X ⊆ Y → brSet g X ⊆ brSet g Y

variable {g : V → Set V → 𝕜} {N : Set V}

omit [IsStrictOrderedRing 𝕜] in
/-- Les complémentarités globales donnent la monotonie au-dessus de tout noyau. -/
theorem Supermodular.brMonoAbove (hg : Supermodular g) (N : Set V) : BrMonoAbove g N :=
  fun _ _ _ hXY => (br g hg).monotone hXY

/-- L'opérateur de bassin : on garde `N` et on répond à `N ∪ X`. -/
def basinOp (g : V → Set V → 𝕜) (N : Set V) (h : BrMonoAbove g N) : Set V →o Set V where
  toFun X := N ∪ brSet g (N ∪ X)
  monotone' _ _ hXY := Set.union_subset_union_right N
    (h _ _ Set.subset_union_left (Set.union_subset_union_right N hXY))

omit [IsStrictOrderedRing 𝕜] in
theorem subset_basinOp (h : BrMonoAbove g N) (X : Set V) : N ⊆ basinOp g N h X :=
  fun _ ha => Or.inl ha

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Sous rétention, les points fixes du bassin sont les équilibres contenant `N`. -/
theorem basin_fixed_iff (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) {X : Set V} :
    basinOp g N h X = X ↔ IsNash g X ∧ N ⊆ X := by
  rw [isNash_iff_fixed]
  constructor
  · intro hX
    have hX' : N ∪ brSet g (N ∪ X) = X := hX
    have hNX : N ⊆ X := hX ▸ subset_basinOp h X
    rw [Set.union_eq_self_of_subset_left hNX] at hX'
    rw [Set.union_eq_self_of_subset_left (hN.trans (h _ _ le_rfl hNX))] at hX'
    exact ⟨hX', hNX⟩
  · rintro ⟨hX, hNX⟩
    show N ∪ brSet g (N ∪ X) = X
    rw [Set.union_eq_self_of_subset_left hNX, hX, Set.union_eq_self_of_subset_left hNX]

omit [IsStrictOrderedRing 𝕜] in
theorem basin_fixedPoints (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) :
    Function.fixedPoints (basinOp g N h) = {X | IsNash g X ∧ N ⊆ X} :=
  Set.ext fun _ => basin_fixed_iff h hN

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus petit équilibre contenant `N`. -/
theorem basin_lfp_least (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) :
    IsLeast {X | IsNash g X ∧ N ⊆ X} (basinOp g N h).lfp :=
  basin_fixedPoints h hN ▸ (basinOp g N h).isLeast_lfp

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus grand équilibre contenant `N`. -/
theorem basin_gfp_greatest (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) :
    IsGreatest {X | IsNash g X ∧ N ⊆ X} (basinOp g N h).gfp :=
  basin_fixedPoints h hN ▸ (basinOp g N h).isGreatest_gfp

omit [IsStrictOrderedRing 𝕜] in
/-- Depuis `N`, l'orbite de l'opérateur de bassin est celle de la meilleure réponse. -/
theorem basin_iterate_eq (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) :
    ∀ k, N ⊆ (brSet g)^[k] N ∧ (⇑(basinOp g N h))^[k] N = (brSet g)^[k] N
  | 0 => ⟨le_rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := basin_iterate_eq h hN k
    have hB : N ⊆ brSet g ((brSet g)^[k] N) := hN.trans (h _ _ le_rfl h1)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h2]
    refine ⟨hB, ?_⟩
    show N ∪ brSet g (N ∪ _) = _
    rw [Set.union_eq_self_of_subset_left h1, Set.union_eq_self_of_subset_left hB]

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Orbite du bassin** : depuis un noyau retenu, la dynamique myope atteint le plus petit
équilibre contenant `N` en au plus `card V − ncard N` pas. -/
theorem basin_iterate [Finite V] (h : BrMonoAbove g N) (hN : N ⊆ brSet g N) {k : ℕ}
    (hk : Nat.card V - N.ncard ≤ k) : (brSet g)^[k] N = (basinOp g N h).lfp := by
  rw [← (basin_iterate_eq h hN k).2, iterate_post _ (subset_basinOp h N) hk]
  set F := basinOp g N h
  have hNl : N ⊆ F.lfp := F.map_lfp ▸ subset_basinOp h F.lfp
  exact le_antisymm (lfpAbove_least F hNl F.map_lfp.le)
    (F.lfp_le fun _ hx => (lfpAbove_eq F).le (Or.inr hx))

/-! ### §3. Profils monotones au-dessus d'un rang ; le témoin -/

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Un profil monotone à partir du rang `m` est monotone au-dessus de tout noyau d'au moins
`m + 1` membres. -/
theorem sym_mono_above [Finite V] {M : ℕ → 𝕜} {m : ℕ} (hM : MonotoneOn M (Set.Ici m))
    (hN : m + 1 ≤ N.ncard) : BrMonoAbove (symGain M) N := by
  intro X Y hNX hXY i hi
  have h1 : N.ncard ≤ X.ncard := Set.ncard_le_ncard hNX
  have h2 : X.ncard - 1 ≤ (X \ {i}).ncard := Set.pred_ncard_le_ncard_diff_singleton X i
  have h3 : (X \ {i}).ncard ≤ (Y \ {i}).ncard :=
    Set.ncard_le_ncard (Set.diff_subset_diff_left hXY)
  have hm : m ≤ (X \ {i}).ncard := by omega
  change 0 ≤ M (X \ {i}).ncard at hi
  change 0 ≤ M (Y \ {i}).ncard
  exact le_trans hi (hM hm (le_trans hm h3) h3)

theorem coe_012 : ({0, 1, 2} : Set (Fin 4)) = ↑({0, 1, 2} : Finset (Fin 4)) := by simp

theorem mono_above_012 : BrMonoAbove (symGain M4) ({0, 1, 2} : Set (Fin 4)) := by
  refine sym_mono_above (m := 2) (fun a ha b hb _ => ?_) ?_
  · simp only [Set.mem_Ici] at ha hb
    simp only [M4, if_neg (show a ≠ 1 by omega), if_neg (show b ≠ 1 by omega), le_refl]
  · rw [coe_012, Set.ncard_coe_finset]
    decide

/-- ★ **Témoin** (`Fin 4`, profil `M4`) : le noyau `{0, 1, 2}` est retenu et son bassin allume
tout, alors que `{0}` est un équilibre hors du bassin. -/
theorem basin_witness :
    ({0, 1, 2} : Set (Fin 4)) ⊆ brSet (symGain M4) {0, 1, 2} ∧
      (basinOp (symGain M4) {0, 1, 2} mono_above_012).lfp = Set.univ ∧
      IsNash (symGain M4) ({0} : Set (Fin 4)) ∧ ¬ ({0, 1, 2} : Set (Fin 4)) ⊆ {0} := by
  have hB : brSet (symGain M4) ({0, 1, 2} : Set (Fin 4)) = Set.univ := by
    rw [coe_012, ← Finset.coe_univ]
    ext i
    rw [mem_brSet_sym_coe, Finset.mem_coe]
    revert i
    decide
  have hR : ({0, 1, 2} : Set (Fin 4)) ⊆ brSet (symGain M4) {0, 1, 2} := by
    rw [hB]
    exact Set.subset_univ _
  have h3 : ({0, 1, 2} : Set (Fin 4)).ncard = 3 := by
    rw [coe_012, Set.ncard_coe_finset]
    decide
  refine ⟨hR, ?_, isNash_iff_fixed.2 sym_not_monotone.2.1, fun h => ?_⟩
  · rw [← basin_iterate mono_above_012 hR (k := 1) (by simp [h3]), Function.iterate_one, hB]
  · have := h (show (1 : Fin 4) ∈ ({0, 1, 2} : Set (Fin 4)) by simp)
    simp at this

end BasinTarski

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf le témoin à quatre
joueurs (`M4`, `sym_not_monotone`, `coe_012`, `mono_above_012`, `basin_witness`), qui reste dans
`ℚ` : ses étapes `decide` y calculent.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
