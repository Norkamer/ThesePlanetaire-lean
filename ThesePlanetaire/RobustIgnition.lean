/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/RobustIgnition.lean
  Phase 11 (2026-10-02), étape 11e : l'amorçage robuste — le pire cas des érosions bornées
  minore toutes les trajectoires, et la robustesse d'un noyau est son appartenance au noyau de
  viabilité (premier consommateur de `ViabilityKernel`, non édité).

  Développé d'abord en `RobustIgnition_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase11_2026-10-02/plan_phase11.md` ; analyse :
  `cache/analyse_phase11_adhesion_emetteurs_2026-10-02.md` §6 ; sonde G7
  (`cache/phase11_2026-10-02/outils/sonde_adhesion.py`).
-/

import ThesePlanetaire.AdhesionGame
import ThesePlanetaire.ViabilityKernel

/-!
# Pire cas et noyau de viabilité

Une perturbation `δ : ℕ → V → 𝕜` décale à la date `t` le gain du joueur `i` de `δ t i` ; elle est
admissible au niveau `x` si `−x ≤ δ t i` partout (l'érosion ne dépasse jamais `x`). La dynamique
myope simultanée perturbée part d'un noyau `N` ; `N` est robuste s'il est conservé le long de
toute trajectoire admissible.

1. ★ `traj_ge_worst` : sous `Supermodular`, la trajectoire du pire cas (érosion uniforme `x`,
   soit `shift g (−x)`) est contenue dans toute trajectoire admissible : c'est le minimum de
   chemin que le modèle de Renn (arXiv 2608.12143 v3, note 3) instancie.
2. ★ `robust_iff_worst`, `robust_iff_margin` : robuste ⟺ le pire cas garde `N` ⟺ chaque membre
   de `N` a une marge au moins `x` face aux autres membres. ★ `robust_antitone` : le seuil de
   basculement est bien défini ; ★ `coord_tipping` : il vaut `1` pour la coordination à deux.
3. ★ `robust_guarantee`, `robust_floor_nash` : sous robustesse, après `card V − ncard N` pas,
   toute trajectoire admissible contient le plus petit équilibre du jeu érodé contenant `N`.
4. ★ `robust_iff_kernel` : la robustesse est l'appartenance de `N` au noyau de viabilité des
   coalitions contenant `N` pour la dynamique du pire cas (`viability_kernel_eq_gfp`).
-/

namespace RobustIgnition

open AdhesionGame

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §1. Perturbations et trajectoires -/

/-- Gain perturbé : décalage individuel `δ i`. -/
def pert (g : V → Set V → 𝕜) (δ : V → 𝕜) : V → Set V → 𝕜 := fun i S => g i S + δ i

/-- Perturbation admissible au niveau `x` : l'érosion ne dépasse jamais `x`. -/
def Admissible (x : 𝕜) (δ : ℕ → V → 𝕜) : Prop := ∀ t i, -x ≤ δ t i

/-- Trajectoire de la dynamique myope simultanée perturbée, depuis `X0`. -/
def traj (g : V → Set V → 𝕜) (δ : ℕ → V → 𝕜) (X0 : Set V) : ℕ → Set V
  | 0 => X0
  | t + 1 => brSet (pert g (δ t)) (traj g δ X0 t)

/-- `N` est robuste au niveau `x` : conservé le long de toute trajectoire admissible issue de
`N`. -/
def Robust (g : V → Set V → 𝕜) (x : 𝕜) (N : Set V) : Prop :=
  ∀ δ, Admissible x δ → ∀ t, N ⊆ traj g δ N t

/-- Le pire cas : érosion uniforme `x`. -/
def worst (x : 𝕜) : ℕ → V → 𝕜 := fun _ _ => -x

variable {g : V → Set V → 𝕜} {x : 𝕜}

omit [IsStrictOrderedRing 𝕜] in
theorem worst_admissible : Admissible x (worst (V := V) x) := fun _ _ => le_rfl

/-- La trajectoire du pire cas est l'orbite de la meilleure réponse du jeu érodé. -/
theorem traj_worst (hg : Supermodular g) (X0 : Set V) :
    ∀ t, traj g (worst x) X0 t = (⇑(br (shift g (-x)) (hg.shift (-x))))^[t] X0
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', ← traj_worst hg X0 t]
    rfl

/-- ★ **Minimum de chemin** : la trajectoire du pire cas est contenue dans toute trajectoire
admissible (départs ordonnés). -/
theorem traj_ge_worst (hg : Supermodular g) {δ : ℕ → V → 𝕜} (hδ : Admissible x δ)
    {X0 Y0 : Set V} (h0 : X0 ⊆ Y0) :
    ∀ t, (⇑(br (shift g (-x)) (hg.shift (-x))))^[t] X0 ⊆ traj g δ Y0 t
  | 0 => h0
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    intro i hi
    have hm := hg i (Set.diff_subset_diff_left (t := {i}) (traj_ge_worst hg hδ h0 t))
    have := hδ t i
    change 0 ≤ g i _ + -x at hi
    change 0 ≤ g i _ + δ t i
    linarith

/-! ### §2. Robustesse : pire cas, marge, seuil -/

/-- ★ Robuste ⟺ le pire cas garde `N` à toute date. -/
theorem robust_iff_worst (hg : Supermodular g) {N : Set V} :
    Robust g x N ↔ ∀ t, N ⊆ (⇑(br (shift g (-x)) (hg.shift (-x))))^[t] N := by
  constructor
  · intro h t
    rw [← traj_worst hg]
    exact h _ worst_admissible t
  · intro h δ hδ t
    exact (h t).trans (traj_ge_worst hg hδ subset_rfl t)

/-- ★ **Robuste ⟺ marge** : chaque membre de `N` garde un gain au moins `x` face aux autres
membres. Un seul pas du pire cas décide. -/
theorem robust_iff_margin (hg : Supermodular g) {N : Set V} :
    Robust g x N ↔ ∀ i ∈ N, x ≤ g i (N \ {i}) := by
  rw [robust_iff_worst hg]
  constructor
  · intro h i hi
    have : 0 ≤ g i (N \ {i}) + -x := h 1 hi
    linarith
  · intro h
    exact subset_iterate _ fun i hi => show 0 ≤ g i (N \ {i}) + -x by linarith [h i hi]

/-- ★ Robuste au niveau `x'` ⇒ robuste à tout niveau inférieur : le seuil de basculement
`sup {x | Robust g x N}` est bien défini. -/
theorem robust_antitone {x' : 𝕜} {N : Set V} (hx : x ≤ x') (h : Robust g x' N) :
    Robust g x N :=
  fun δ hδ => h δ fun t i => le_trans (neg_le_neg hx) (hδ t i)

/-- ★ Le seuil de basculement de la coordination à deux joueurs vaut `1`. -/
theorem coord_tipping {x : ℚ} : Robust coordGain x Set.univ ↔ x ≤ 1 := by
  rw [robust_iff_margin coordGain_super]
  have hne : ∀ i : Fin 2, (Set.univ \ {i} : Set (Fin 2)).Nonempty := by
    intro i
    fin_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  simp [coordGain, hne]

/-! ### §3. Garantie -/

/-- ★ **Garantie** : sous robustesse, après `card V − ncard N` pas, toute trajectoire admissible
contient le plus petit point fixe du jeu érodé contenant `N`. -/
theorem robust_guarantee [Finite V] (hg : Supermodular g) {N : Set V} (h : Robust g x N)
    {δ : ℕ → V → 𝕜} (hδ : Admissible x δ) {t : ℕ} (ht : Nat.card V - N.ncard ≤ t) :
    lfpAbove (br (shift g (-x)) (hg.shift (-x))) N ⊆ traj g δ N t := by
  have hN : N ⊆ br (shift g (-x)) (hg.shift (-x)) N := (robust_iff_worst hg).1 h 1
  rw [← iterate_post _ hN ht]
  exact traj_ge_worst hg hδ subset_rfl t

/-- ★ … et ce plancher est le plus petit équilibre du jeu érodé contenant `N`. -/
theorem robust_floor_nash (hg : Supermodular g) {N : Set V} (h : Robust g x N) :
    IsNash (shift g (-x)) (lfpAbove (br (shift g (-x)) (hg.shift (-x))) N) ∧
      N ⊆ lfpAbove (br (shift g (-x)) (hg.shift (-x))) N ∧
      ∀ X, IsNash (shift g (-x)) X → N ⊆ X →
        lfpAbove (br (shift g (-x)) (hg.shift (-x))) N ⊆ X := by
  have hN : N ⊆ br (shift g (-x)) (hg.shift (-x)) N := (robust_iff_worst hg).1 h 1
  exact ⟨isNash_iff_fixed.2 (lfpAbove_fixed _ hN), subset_lfpAbove _,
    fun X hX hNX => lfpAbove_least _ hNX (isNash_iff_fixed.1 hX).le⟩

/-! ### §4. Pont vers le noyau de viabilité -/

open ViabilityKernel

/-- Pas déterministe : la viabilité finitaire d'un pas singleton équivaut à ce que les itérées
restent dans `K`. -/
theorem viableN_singleton_iff {S : Type*} [DecidableEq S] [Fintype S] (K : Finset S)
    (f : S → S) : ∀ n s, viableN K (fun y => {f y}) s n ↔ ∀ k ≤ n, f^[k] s ∈ K
  | 0, s => by simp [viableN]
  | n + 1, s => by
    simp only [viableN, Finset.mem_singleton, exists_eq_left]
    rw [viableN_singleton_iff K f n (f s)]
    constructor
    · rintro ⟨hs, h⟩ k hk
      rcases k with _ | k
      · exact hs
      · rw [Function.iterate_succ_apply]
        exact h k (by omega)
    · intro h
      exact ⟨h 0 (Nat.zero_le _), fun k hk => by
        rw [← Function.iterate_succ_apply]
        exact h (k + 1) (by omega)⟩

/-- … à tout horizon : `s` est dans le noyau de viabilité ssi toute son orbite reste dans `K`. -/
theorem mem_kernel_singleton_iff {S : Type*} [DecidableEq S] [Fintype S] (K : Finset S)
    (f : S → S) (s : S) :
    s ∈ viabilityKernel K (fun y => {f y}) ↔ ∀ k, f^[k] s ∈ K := by
  rw [viability_kernel_eq_gfp]
  simp only [viableN_singleton_iff]
  exact ⟨fun h k => h k k le_rfl, fun h _ k _ => h k⟩

variable [Fintype V]

open Classical in
/-- Le pas du pire cas, sur les coalitions finies. -/
noncomputable def worstStep (g : V → Set V → 𝕜) (x : 𝕜) (X : Finset V) : Finset V :=
  Finset.univ.filter (· ∈ brSet (shift g (-x)) ↑X)

theorem coe_worstStep_iterate (hg : Supermodular g) (X : Finset V) :
    ∀ k, (↑((worstStep g x)^[k] X) : Set V) = (⇑(br (shift g (-x)) (hg.shift (-x))))^[k] ↑X
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ← coe_worstStep_iterate hg X k]
    ext i
    simp [worstStep, br]

variable [DecidableEq V]

/-- Les contraintes : les coalitions contenant `N`. -/
def keepN (N : Finset V) : Finset (Finset V) := Finset.univ.filter (N ⊆ ·)

/-- ★ **Robustesse = viabilité** : `N` est robuste au niveau `x` ssi il appartient au noyau de
viabilité des coalitions contenant `N`, pour la dynamique du pire cas. -/
theorem robust_iff_kernel (hg : Supermodular g) (N : Finset V) :
    N ∈ viabilityKernel (keepN N) (fun X => {worstStep g x X}) ↔ Robust g x ↑N := by
  rw [mem_kernel_singleton_iff, robust_iff_worst hg]
  refine forall_congr' fun k => ?_
  rw [keepN, Finset.mem_filter, ← Finset.coe_subset, coe_worstStep_iterate hg]
  simp

end RobustIgnition

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf `coord_tipping`,
qui porte sur le témoin `AdhesionGame.coordGain` et reste dans `ℚ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
