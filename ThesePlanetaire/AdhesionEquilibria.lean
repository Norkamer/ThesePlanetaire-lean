/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/AdhesionEquilibria.lean
  Phase 13 (2026-10-03) : préparation du papier 14 — équilibres de Nash standard du jeu
  d'adhésion (sélections extrêmes de la meilleure réponse) et classement de Pareto des équilibres.
  Résultats connus (Topkis 1979 ; Milgrom et Roberts 1990, th. 5 à 7), formalisés pour le
  papier : cités, non revendiqués.

  Développé d'abord en `AdhesionEquilibria_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase13_2026-10-03/plan.md` ; lectures : `cache/phase13_2026-10-03/lectures/` ;
  comparaison : `ThèseNov26/couche3_dynamique/P14_jeu_adhesion/comparaison.md`.
-/

import ThesePlanetaire.AdhesionGame

/-!
# Équilibres standard et bien-être du jeu d'adhésion

`AdhesionGame.IsNash` fait adhérer l'indifférent (`g i (X \ {i}) < 0` strict pour les
non-adhérents) : ses équilibres sont les points fixes de la **plus grande** meilleure réponse
`brSet`. L'équilibre de Nash standard en stratégies pures (`IsNashStd`) n'impose aucune règle
d'égalité. La **plus petite** meilleure réponse `brSetStrict` laisse l'indifférent dehors.

1. ★ `gfp_greatest_std`, `lfp_strict_least_std` : le plus grand équilibre standard est le `gfp`
   de `br`, le plus petit est le `lfp` de `brStrict` (Milgrom et Roberts 1990, lemme 1 et
   th. 5 ; Topkis 1979). ★ `std_unique_iff` : l'équilibre standard est unique ssi ces deux
   points coïncident. ★ `lfp_strict_eq_empty_iff`, `iterate_least_std`.
2. ★ `isNashStd_iff_of_ne_zero`, `brStrict_eq_of_ne_zero` : sans indifférence exacte, les deux
   notions coïncident. ★ `tie_witness` : pour `g ≡ 0`, `IsNash` a un seul équilibre, alors que
   tout profil est un équilibre standard.
3. Bien-être : niveaux de gain `uIn` (adhérent) et `uOut` (non-adhérent), gain net
   `netGain uIn uOut`. ★ `payoff_mono_of_subset`, `payoff_anti_of_subset` (Milgrom et Roberts
   1990, th. 7) ; ★ `pareto_gfp_best`, `pareto_lfp_worst` : sous `PositiveSpillovers` (le gain
   des non-adhérents croît avec les adhérents), le plus grand équilibre est le meilleur pour
   chacun, le plus petit le pire. ★ `welfare_reversal` : sans cette hypothèse, le plus grand
   équilibre peut être strictement pire pour tous.
-/

namespace AdhesionEquilibria

open AdhesionGame

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §1. Équilibre de Nash standard -/

/-- Équilibre de Nash en stratégies pures, sans règle d'égalité : aucun adhérent ne gagne
strictement à sortir, aucun non-adhérent ne gagne strictement à entrer. -/
def IsNashStd (g : V → Set V → 𝕜) (X : Set V) : Prop :=
  (∀ i ∈ X, 0 ≤ g i (X \ {i})) ∧ ∀ i ∉ X, g i (X \ {i}) ≤ 0

/-- La plus petite meilleure réponse : l'indifférent reste dehors. -/
def brSetStrict (g : V → Set V → 𝕜) (X : Set V) : Set V := {i | 0 < g i (X \ {i})}

/-- La plus petite meilleure réponse, monotone sous `Supermodular`. -/
def brStrict (g : V → Set V → 𝕜) (hg : Supermodular g) : Set V →o Set V where
  toFun := brSetStrict g
  monotone' _ _ h _ hi := lt_of_lt_of_le hi (hg _ (Set.diff_subset_diff_left h))

variable {g : V → Set V → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
theorem brSetStrict_subset (X : Set V) : brSetStrict g X ⊆ brSet g X := fun _ hi => le_of_lt hi

omit [IsStrictOrderedRing 𝕜] in
/-- Un équilibre « l'indifférent adhère » est un équilibre standard. -/
theorem isNashStd_of_isNash {X : Set V} (h : IsNash g X) : IsNashStd g X :=
  ⟨h.1, fun i hi => (h.2 i hi).le⟩

omit [IsStrictOrderedRing 𝕜] in
/-- Équilibre standard ⟺ post-point fixe de la plus grande meilleure réponse et pré-point fixe
de la plus petite. -/
theorem isNashStd_iff {X : Set V} : IsNashStd g X ↔ X ⊆ brSet g X ∧ brSetStrict g X ⊆ X := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => by_contra fun hX => absurd hi (not_lt.mpr (h2 i hX))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hX => not_lt.mp fun hi => hX (h2 hi)⟩

omit [IsStrictOrderedRing 𝕜] in
theorem isNashStd_of_fixed {X : Set V} (h : brSet g X = X) : IsNashStd g X :=
  isNashStd_of_isNash (isNash_iff_fixed.mpr h)

omit [IsStrictOrderedRing 𝕜] in
theorem isNashStd_of_fixed_strict {X : Set V} (h : brSetStrict g X = X) : IsNashStd g X :=
  isNashStd_iff.mpr ⟨h.ge.trans (brSetStrict_subset X), h.le⟩

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus grand équilibre standard est `gfp (br g)`. -/
theorem gfp_greatest_std (hg : Supermodular g) : IsGreatest {X | IsNashStd g X} (br g hg).gfp :=
  ⟨isNashStd_of_fixed (br g hg).map_gfp,
    fun _ hX => (br g hg).le_gfp (isNashStd_iff.mp hX).1⟩

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus petit équilibre standard est `lfp (brStrict g)`. -/
theorem lfp_strict_least_std (hg : Supermodular g) :
    IsLeast {X | IsNashStd g X} (brStrict g hg).lfp :=
  ⟨isNashStd_of_fixed_strict (brStrict g hg).map_lfp,
    fun _ hX => (brStrict g hg).lfp_le (isNashStd_iff.mp hX).2⟩

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Unicité de l'équilibre standard ⟺ `lfp (brStrict g) = gfp (br g)`.** -/
theorem std_unique_iff (hg : Supermodular g) :
    (∃! X, IsNashStd g X) ↔ (brStrict g hg).lfp = (br g hg).gfp := by
  constructor
  · rintro ⟨X, -, hX⟩
    rw [hX _ (lfp_strict_least_std hg).1, hX _ (gfp_greatest_std hg).1]
  · intro h
    refine ⟨_, (lfp_strict_least_std hg).1,
      fun Y hY => le_antisymm ?_ ((lfp_strict_least_std hg).2 hY)⟩
    rw [h]
    exact (gfp_greatest_std hg).2 hY

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus petit équilibre standard est vide ssi aucun gain isolé n'est strictement positif. -/
theorem lfp_strict_eq_empty_iff (hg : Supermodular g) :
    (brStrict g hg).lfp = ∅ ↔ ∀ i, g i ∅ ≤ 0 := by
  constructor
  · intro h i
    have h0 := (brStrict g hg).map_lfp
    rw [h] at h0
    refine not_lt.mp fun hi => ?_
    have : i ∈ brStrict g hg ∅ := by
      show 0 < g i (∅ \ {i})
      rwa [Set.empty_diff]
    rw [h0] at this
    exact this
  · intro h
    refine Set.subset_empty_iff.mp ((brStrict g hg).lfp_le fun i hi => ?_)
    have : 0 < g i (∅ \ {i}) := hi
    rw [Set.empty_diff] at this
    exact absurd (h i) (not_le.mpr this)

omit [IsStrictOrderedRing 𝕜] in
/-- ★ La dynamique myope simultanée de la plus petite meilleure réponse atteint, depuis `∅`, le
plus petit équilibre standard en au plus `card V` pas. -/
theorem iterate_least_std [Finite V] (hg : Supermodular g) :
    (⇑(brStrict g hg))^[Nat.card V] ∅ = (brStrict g hg).lfp :=
  iterate_lfp _

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Coïncidence générique** : sans indifférence exacte, équilibre standard et équilibre
« l'indifférent adhère » coïncident. -/
theorem isNashStd_iff_of_ne_zero (h0 : ∀ i S, g i S ≠ 0) {X : Set V} :
    IsNashStd g X ↔ IsNash g X :=
  ⟨fun h => ⟨h.1, fun i hi => lt_of_le_of_ne (h.2 i hi) (h0 _ _)⟩, isNashStd_of_isNash⟩

omit [IsStrictOrderedRing 𝕜] in
/-- … et les deux meilleures réponses sont égales. -/
theorem brStrict_eq_of_ne_zero (hg : Supermodular g) (h0 : ∀ i S, g i S ≠ 0) :
    brStrict g hg = br g hg :=
  OrderHom.ext _ _ <| funext fun _ => Set.ext fun i =>
    ⟨le_of_lt, fun h => lt_of_le_of_ne h (h0 i _).symm⟩

/-! ### Le témoin d'indifférence -/

/-- Gain identiquement nul : chaque joueur est indifférent. -/
def zeroGain : Fin 2 → Set (Fin 2) → ℚ := fun _ _ => 0

theorem zeroGain_super : Supermodular zeroGain := fun _ _ _ _ => le_rfl

/-- ★ **La règle d'égalité compte** : `IsNash` a un seul équilibre (`univ`), alors que tout
profil est un équilibre standard ; les équilibres standard extrêmes sont `∅` et `univ`. -/
theorem tie_witness :
    (∃! X, IsNash zeroGain X) ∧ (∀ X, IsNashStd zeroGain X) ∧
      (brStrict zeroGain zeroGain_super).lfp = ∅ ∧
      (br zeroGain zeroGain_super).gfp = Set.univ := by
  refine ⟨⟨Set.univ, ⟨fun _ _ => le_rfl, fun i hi => absurd (Set.mem_univ i) hi⟩,
    fun Y hY => ?_⟩, fun _ => ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩,
    (lfp_strict_eq_empty_iff _).mpr fun _ => le_rfl, ?_⟩
  · refine Set.eq_univ_of_forall fun i => ?_
    by_contra hi
    exact lt_irrefl (0 : ℚ) (hY.2 i hi)
  · exact Set.eq_univ_of_univ_subset
      ((br zeroGain zeroGain_super).le_gfp fun i _ => show (0 : ℚ) ≤ zeroGain i _ from le_rfl)

/-! ### §2. Bien-être des équilibres -/

/-- Gain net d'adhérer : gain d'adhérent moins gain de non-adhérent, face aux mêmes autres
adhérents. -/
def netGain (uIn uOut : V → Set V → 𝕜) : V → Set V → 𝕜 := fun i S => uIn i S - uOut i S

open Classical in
/-- Gain du joueur `i` au profil `X` : `uIn` s'il adhère, `uOut` sinon, face à `X \ {i}`. -/
noncomputable def payoff (uIn uOut : V → Set V → 𝕜) (X : Set V) (i : V) : 𝕜 :=
  if i ∈ X then uIn i (X \ {i}) else uOut i (X \ {i})

/-- Externalités positives (Milgrom et Roberts 1990, th. 7 (1)) : le gain d'un non-adhérent croît
avec les adhérents. -/
def PositiveSpillovers (uOut : V → Set V → 𝕜) : Prop := ∀ i, Monotone (uOut i)

variable {uIn uOut : V → Set V → 𝕜}

/-- Sous complémentarités, les externalités positives valent aussi pour les adhérents. -/
theorem PositiveSpillovers.in_mono (hg : Supermodular (netGain uIn uOut))
    (hO : PositiveSpillovers uOut) (i : V) : Monotone (uIn i) := fun _ _ h => by
  have h1 := hg i h
  have h2 := hO i h
  simp only [netGain] at h1
  linarith

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem payoff_le_max (uIn uOut : V → Set V → 𝕜) (X : Set V) (i : V) :
    payoff uIn uOut X i ≤ max (uIn i (X \ {i})) (uOut i (X \ {i})) := by
  unfold payoff
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- En équilibre standard, chacun obtient le meilleur de ses deux gains. -/
theorem payoff_eq_max {X : Set V} (hX : IsNashStd (netGain uIn uOut) X) (i : V) :
    payoff uIn uOut X i = max (uIn i (X \ {i})) (uOut i (X \ {i})) := by
  unfold payoff
  split_ifs with hi
  · have h := hX.1 i hi
    simp only [netGain] at h
    exact (max_eq_left (by linarith)).symm
  · have h := hX.2 i hi
    simp only [netGain] at h
    exact (max_eq_right (by linarith)).symm

/-- ★ (Milgrom et Roberts 1990, th. 7 (1)) Si le gain de non-adhérent de `i` croît avec les
adhérents, `i` préfère tout équilibre `Y` à tout profil `Z ⊆ Y`. -/
theorem payoff_mono_of_subset {i : V} (hΔ : Monotone (netGain uIn uOut i))
    (hO : Monotone (uOut i)) {Y Z : Set V} (hY : IsNashStd (netGain uIn uOut) Y) (hZY : Z ⊆ Y) :
    payoff uIn uOut Z i ≤ payoff uIn uOut Y i := by
  have hS : Z \ {i} ⊆ Y \ {i} := Set.diff_subset_diff_left hZY
  have h1 := hΔ hS
  have h2 := hO hS
  simp only [netGain] at h1
  rw [payoff_eq_max hY]
  exact (payoff_le_max _ _ _ _).trans (max_le_max (by linarith) h2)

/-- ★ (Milgrom et Roberts 1990, th. 7 (2)) Si le gain d'adhérent de `i` décroît avec les
adhérents, `i` préfère tout équilibre `Z` à tout profil `Y ⊇ Z`. -/
theorem payoff_anti_of_subset {i : V} (hΔ : Monotone (netGain uIn uOut i))
    (hI : Antitone (uIn i)) {Y Z : Set V} (hZ : IsNashStd (netGain uIn uOut) Z) (hZY : Z ⊆ Y) :
    payoff uIn uOut Y i ≤ payoff uIn uOut Z i := by
  have hS : Z \ {i} ⊆ Y \ {i} := Set.diff_subset_diff_left hZY
  have h1 := hΔ hS
  have h2 := hI hS
  simp only [netGain] at h1
  rw [payoff_eq_max hZ]
  exact (payoff_le_max _ _ _ _).trans (max_le_max h2 (by linarith))

/-- ★ **Le plus grand équilibre est le meilleur pour chacun** sous externalités positives. -/
theorem pareto_gfp_best (hg : Supermodular (netGain uIn uOut)) (hO : PositiveSpillovers uOut)
    {X : Set V} (hX : IsNashStd (netGain uIn uOut) X) (i : V) :
    payoff uIn uOut X i ≤ payoff uIn uOut (br _ hg).gfp i :=
  payoff_mono_of_subset (hg i) (hO i) (gfp_greatest_std hg).1 ((gfp_greatest_std hg).2 hX)

/-- ★ **Le plus petit équilibre est le pire pour chacun** sous externalités positives. -/
theorem pareto_lfp_worst (hg : Supermodular (netGain uIn uOut)) (hO : PositiveSpillovers uOut)
    {X : Set V} (hX : IsNashStd (netGain uIn uOut) X) (i : V) :
    payoff uIn uOut (brStrict _ hg).lfp i ≤ payoff uIn uOut X i :=
  payoff_mono_of_subset (hg i) (hO i) hX ((lfp_strict_least_std hg).2 hX)

/-! ### Le témoin de renversement -/

open Classical in
/-- Gain d'adhérent : `1` si l'autre adhère, `−1` sinon. -/
noncomputable def revIn : Fin 2 → Set (Fin 2) → ℚ := fun _ S => if S.Nonempty then 1 else -1

open Classical in
/-- Gain de non-adhérent : `5` si personne n'adhère, `0` sinon. L'adhésion de l'autre lui nuit. -/
noncomputable def revOut : Fin 2 → Set (Fin 2) → ℚ := fun _ S => if S.Nonempty then 0 else 5

theorem revNet_super : Supermodular (netGain revIn revOut) := by
  intro _ S T h
  simp only [netGain, revIn, revOut]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.mono h) h2
  · norm_num
  · exact le_rfl

/-- ★ **Renversement** : sans externalités positives, le jeu reste à complémentarités, ses
équilibres extrêmes sont `∅` et `univ`, et chacun gagne strictement moins en `univ` qu'en `∅`. -/
theorem welfare_reversal :
    (brStrict (netGain revIn revOut) revNet_super).lfp = ∅ ∧
      (br (netGain revIn revOut) revNet_super).gfp = Set.univ ∧
      (∀ i, payoff revIn revOut Set.univ i < payoff revIn revOut ∅ i) ∧
      ¬ PositiveSpillovers revOut := by
  have hne : ∀ i : Fin 2, (Set.univ \ {i} : Set (Fin 2)).Nonempty := fun i => by
    fin_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  refine ⟨(lfp_strict_eq_empty_iff _).mpr fun _ => ?_, ?_, fun i => ?_, fun hm => ?_⟩
  · simp only [netGain, revIn, revOut, Set.not_nonempty_empty, if_false]
    norm_num
  · refine Set.eq_univ_of_univ_subset ((br _ revNet_super).le_gfp fun i _ => ?_)
    show 0 ≤ netGain revIn revOut i (Set.univ \ {i})
    simp only [netGain, revIn, revOut, hne i, if_true]
    norm_num
  · simp only [payoff, Set.mem_univ, if_true, Set.mem_empty_iff_false, if_false, Set.empty_diff,
      revIn, revOut, hne i, Set.not_nonempty_empty]
    norm_num
  · have := hm 0 (Set.empty_subset (Set.univ : Set (Fin 2)))
    simp only [revOut, Set.not_nonempty_empty, if_false, Set.univ_nonempty, if_true] at this
    norm_num at this

end AdhesionEquilibria

/-!
## Domaine

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf les deux témoins
(`zeroGain`, `zeroGain_super`, `tie_witness` ; `revIn`, `revOut`, `revNet_super`,
`welfare_reversal`), qui restent dans `ℚ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `AdhesionGame` (décision
  D-13 de `ThèseNov26/00_cadre/decisions.md`) ; les énoncés précédés de `omit … in` en demandent
  moins. `ℚ` et `ℝ` en sont des instances.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
-/
