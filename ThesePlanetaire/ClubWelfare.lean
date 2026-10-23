/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/ClubWelfare.lean
  Phase 14 (2026-10-03) : préparation du papier 15, partie S — amorçage pour toute exigence
  croissante (le théorème A sans la sûreté), bien-être du club (Milgrom et Roberts 1990, th. 7,
  appliqué au club), comptabilité agrégée des transferts budgétés, témoin du bâton sans carotte.

  Développé d'abord en `ClubWelfare_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase14_2026-10-03/plan.md` ; lectures : `cache/phase14_2026-10-03/lectures/` ;
  comparaison : `ThèseNov26/couche3_dynamique/P15_adhesion_surete/comparaison.md`, partie S.
-/

import ThesePlanetaire.ClubTransfers
import ThesePlanetaire.AdhesionEquilibria

/-!
# Amorçage générique et bien-être du club

1. ★ `exists_nash_iff_of_upward`, `seeding_iff_of_upward` : pour toute exigence `P` croissante
   (un ensemble supérieur de coalitions), une coalition stable qui la vérifie existe ssi le plus
   grand équilibre la vérifie, et un amorçage temporaire y conduit ssi le plus grand équilibre la
   vérifie. `AdhesionSafety.seeding_safe_iff` en est l'instance `P = Safe …` : la sûreté n'y entre
   que par sa croissance (`safe_mono`).
2. Bien-être du club. Le club de `ClubFinancing` n'a qu'un gain net. On lui donne des niveaux :
   un non-membre reçoit le bien public `out` et paie le drain (`clubOut`) ; un membre reçoit le
   bien public, son gain intrinsèque et le transfert (`clubIn`). ★ `club_netGain_eq` : le gain
   net est `intr + drain + t`, celui de `ClubTransfers`. ★ `club_spillovers_iff` : les
   externalités sont positives ssi le bien public croît au moins autant que le drain.
   ★ `club_pareto_full` (Milgrom et Roberts 1990, th. 7 (1), appliqué) : si elles le sont et
   que le plein est un équilibre, chacun préfère le plein à tout profil.
3. ★ `club_total_eq`, `club_total_le` : sous budget, la somme des gains ne dépasse pas celle du
   bien public et des gains intrinsèques des membres ; prime et transferts redistribuent.
4. ★ `stick_witness` : un club supermodulaire, budgété, dont le plein est le plus grand équilibre
   et le vide le plus petit, où chacun est strictement plus mal au plein qu'au vide. Le plein n'y
   tient que par la menace du drain : le bâton sans la carotte, et son coût.
-/

namespace ClubWelfare

open AdhesionGame
open AdhesionEquilibria (IsNashStd brStrict netGain payoff PositiveSpillovers
  payoff_mono_of_subset lfp_strict_eq_empty_iff)
open AdhesionSafety (finOf mem_finOf)
open ClubFinancing (Club)
open ClubTransfers (Budget club_gain_eq)

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §1. Amorçage pour toute exigence croissante -/

variable {g : V → Set V → 𝕜} {P : Set V → Prop}

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Pour une exigence croissante `P`, une coalition stable qui la vérifie existe ssi le plus
grand équilibre la vérifie. -/
theorem exists_nash_iff_of_upward (hg : Supermodular g) (hP : ∀ ⦃X Y⦄, X ⊆ Y → P X → P Y) :
    (∃ X, IsNash g X ∧ P X) ↔ P (br g hg).gfp :=
  (exists_congr fun _ => and_congr_left' isNash_iff_fixed).trans
    (AdhesionSafety.exists_fixed_safe_iff hP (br g hg))

/-- ★ **Amorçage pour toute exigence croissante** : un amorçage temporaire (champ `H ≥ 0`, puis
retrait) laisse une coalition stable vérifiant `P` ssi le plus grand équilibre la vérifie. -/
theorem seeding_iff_of_upward [Fintype V] (hg : Supermodular g)
    (hP : ∀ ⦃X Y⦄, X ⊆ Y → P X → P Y) :
    (∃ H, 0 ≤ H ∧ P (afterSeed g hg H)) ↔ P (br g hg).gfp := by
  constructor
  · rintro ⟨H, hH, hS⟩
    exact hP (afterSeed_subset_gfp hg hH) hS
  · intro h
    refine ⟨∑ i, |g i ∅|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
    have hall : ∀ i, 0 ≤ g i ∅ + ∑ j, |g j ∅| := fun i => by
      have h1 : |g i ∅| ≤ ∑ j, |g j ∅| :=
        Finset.single_le_sum (f := fun j => |g j ∅|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h2 := neg_abs_le (g i ∅)
      linarith
    rw [afterSeed_full hg (ignition_all hg hall)]
    exact h

/-! ### §2. Niveaux de gain du club -/

/-- Gain d'un non-membre face aux membres `S` : bien public moins drain. -/
def clubOut (out drain : V → Set V → 𝕜) : V → Set V → 𝕜 := fun i S => out i S - drain i S

/-- Gain d'un membre face aux autres membres `S` : bien public, gain intrinsèque, transfert. -/
def clubIn (out intr t : V → Set V → 𝕜) : V → Set V → 𝕜 := fun i S => out i S + intr i S + t i S

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- ★ Le gain net d'adhérer est `intr + drain + t` : le bien public s'annule. -/
theorem club_netGain_eq (out intr drain t : V → Set V → 𝕜) :
    netGain (clubIn out intr t) (clubOut out drain) = addGain (fun i S => intr i S + drain i S) t := by
  funext i S
  simp only [netGain, clubIn, clubOut, addGain]
  ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- ★ Pont avec `ClubFinancing` : avec le transfert `prem i (insert i S)`, le gain net est le gain
du club. -/
theorem club_netGain_club (C : Club 𝕜 V) (out : V → Set V → 𝕜) :
    netGain (clubIn out C.intr fun i S => C.prem i (insert i S)) (clubOut out C.drain) = C.gain := by
  rw [club_netGain_eq, club_gain_eq]

variable {out intr drain t : V → Set V → 𝕜}

/-- ★ **Externalités positives du club** : le gain des non-membres croît avec les membres ssi le
bien public croît au moins autant que le drain. -/
theorem club_spillovers_iff :
    PositiveSpillovers (clubOut out drain) ↔
      ∀ i S T, S ⊆ T → drain i T - drain i S ≤ out i T - out i S := by
  constructor
  · intro h i S T hST
    have := h i hST
    simp only [clubOut] at this
    linarith
  · intro h i S T hST
    have := h i S T hST
    simp only [clubOut]
    linarith

/-- ★ **Le plein est le meilleur profil pour chacun** (Milgrom et Roberts 1990, th. 7 (1),
appliqué au club) : sous complémentarités et externalités positives, si le plein est un
équilibre, chacun le préfère à tout profil. -/
theorem club_pareto_full (hg : Supermodular (netGain (clubIn out intr t) (clubOut out drain)))
    (hO : PositiveSpillovers (clubOut out drain))
    (hfull : IsNash (netGain (clubIn out intr t) (clubOut out drain)) Set.univ) (X : Set V)
    (i : V) :
    payoff (clubIn out intr t) (clubOut out drain) X i ≤
      payoff (clubIn out intr t) (clubOut out drain) Set.univ i :=
  payoff_mono_of_subset (hg i) (hO i) (AdhesionEquilibria.isNashStd_of_isNash hfull)
    (Set.subset_univ X)

/-! ### §3. Comptabilité agrégée -/

variable [Fintype V] [DecidableEq V]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
open Classical in
/-- ★ **Somme des gains** : bien public, gains intrinsèques des membres, et solde des transferts
versés aux membres moins drains payés par les non-membres. -/
theorem club_total_eq (out intr drain t : V → Set V → 𝕜) (X : Set V) :
    ∑ i, payoff (clubIn out intr t) (clubOut out drain) X i =
      ∑ i, out i (X \ {i}) + ∑ i ∈ finOf X, intr i (X \ {i}) +
        (∑ i ∈ finOf X, t i (X \ {i}) - ∑ j ∈ (finOf X)ᶜ, drain j X) := by
  have hc : (finOf X)ᶜ = Finset.univ.filter (· ∉ X) := by
    ext j
    simp [mem_finOf]
  have hd : ∑ j ∈ (finOf X)ᶜ, drain j X = ∑ j ∈ (finOf X)ᶜ, drain j (X \ {j}) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Set.diff_singleton_eq_self (fun h => (Finset.mem_compl.mp hj) (mem_finOf.mpr h))]
  have hsplit : ∀ f : V → 𝕜, ∑ i, f i = ∑ i ∈ finOf X, f i + ∑ i ∈ (finOf X)ᶜ, f i :=
    fun f => (Finset.sum_add_sum_compl _ f).symm
  have hp : ∑ i, payoff (clubIn out intr t) (clubOut out drain) X i =
      ∑ i ∈ finOf X, clubIn out intr t i (X \ {i}) +
        ∑ i ∈ (finOf X)ᶜ, clubOut out drain i (X \ {i}) := by
    rw [hsplit]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by
        simp [payoff, mem_finOf.mp hi]
    · exact Finset.sum_congr rfl fun i hi => by
        have : i ∉ X := fun h => (Finset.mem_compl.mp hi) (mem_finOf.mpr h)
        simp [payoff, this]
  rw [hp, hd, hsplit fun i => out i (X \ {i})]
  simp only [clubIn, clubOut, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- ★ **Les transferts budgétés redistribuent** : sous budget, la somme des gains ne dépasse pas
celle du bien public et des gains intrinsèques des membres. -/
theorem club_total_le (hB : Budget drain t) (X : Set V) :
    ∑ i, payoff (clubIn out intr t) (clubOut out drain) X i ≤
      ∑ i, out i (X \ {i}) + ∑ i ∈ finOf X, intr i (X \ {i}) := by
  rw [club_total_eq]
  have := hB X
  linarith

/-! ### §4. Le témoin du bâton -/

open Classical in
/-- Drain du témoin : `2` face à une coalition non vide, `0` sinon. -/
noncomputable def stickDrain : Fin 2 → Set (Fin 2) → ℚ := fun _ S => if S.Nonempty then 2 else 0

/-- Club témoin : bien public nul, gain intrinsèque `−1`, aucun transfert. -/
noncomputable abbrev stickIn : Fin 2 → Set (Fin 2) → ℚ :=
  clubIn (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0)

/-- Les non-membres paient le drain. -/
noncomputable abbrev stickOut : Fin 2 → Set (Fin 2) → ℚ := clubOut (fun _ _ => 0) stickDrain

theorem stick_super : Supermodular (netGain stickIn stickOut) := by
  intro _ S T h
  simp only [netGain, clubIn, clubOut, stickDrain]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.mono h) h2
  · norm_num
  · exact le_rfl

/-- ★ **Le bâton sans la carotte, et son coût** : le club témoin est supermodulaire et budgété
sans transfert ; son plus petit équilibre est vide, son plus grand est le plein ; chacun gagne
strictement moins au plein qu'au vide, et les externalités ne sont pas positives. -/
theorem stick_witness :
    Budget stickDrain (fun _ _ => 0) ∧
      (brStrict (netGain stickIn stickOut) stick_super).lfp = ∅ ∧
      (br (netGain stickIn stickOut) stick_super).gfp = Set.univ ∧
      (∀ i, payoff stickIn stickOut Set.univ i < payoff stickIn stickOut ∅ i) ∧
      ¬ PositiveSpillovers stickOut := by
  have hne : ∀ i : Fin 2, (Set.univ \ {i} : Set (Fin 2)).Nonempty := fun i => by
    fin_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  refine ⟨fun X => ?_, (lfp_strict_eq_empty_iff _).mpr fun _ => ?_, ?_, fun i => ?_, fun hm => ?_⟩
  · simp only [Finset.sum_const_zero]
    exact Finset.sum_nonneg fun j _ => by
      unfold stickDrain
      split_ifs <;> norm_num
  · simp only [netGain, clubIn, clubOut, stickDrain, Set.not_nonempty_empty, if_false]
    norm_num
  · refine Set.eq_univ_of_univ_subset ((br _ stick_super).le_gfp fun i _ => ?_)
    show 0 ≤ netGain stickIn stickOut i (Set.univ \ {i})
    simp only [netGain, clubIn, clubOut, stickDrain, hne i, if_true]
    norm_num
  · simp only [payoff, Set.mem_univ, if_true, Set.mem_empty_iff_false, if_false, Set.empty_diff,
      clubIn, clubOut, stickDrain, Set.not_nonempty_empty]
    norm_num
  · have := hm 0 (Set.empty_subset (Set.univ : Set (Fin 2)))
    simp only [clubOut, stickDrain, Set.not_nonempty_empty, if_false, Set.univ_nonempty,
      if_true] at this
    norm_num at this

end ClubWelfare

/-!
## Domaine

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf le témoin
(`stickDrain`, `stickIn`, `stickOut`, `stick_super`, `stick_witness`), qui reste dans `ℚ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `AdhesionGame` (décision
  D-13 de `ThèseNov26/00_cadre/decisions.md`) ; les énoncés précédés de `omit … in` en demandent
  moins. `ℚ` et `ℝ` en sont des instances.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- La sûreté du papier 11 (`AdhesionSafety.Safe`) est dans `ℕ` ; `seeding_iff_of_upward` ne la
  suppose pas : elle n'en est qu'une instance.
-/
