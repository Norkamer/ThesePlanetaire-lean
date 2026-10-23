/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/ClubFinancing.lean
  Phase 11 (2026-10-02), étape 11d : qui finance la prime à pleine adhésion ? (question 2 du
  modèle de Renn) — financée par la frontière, la prime s'annule au plein ; il ne reste que le
  gain intrinsèque et la menace du drain.

  Développé d'abord en `ClubFinancing_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase11_2026-10-02/plan_phase11.md` ; analyse :
  `cache/analyse_phase11_adhesion_emetteurs_2026-10-02.md` §5 ; sonde G6
  (`cache/phase11_2026-10-02/outils/sonde_adhesion.py`).
-/

import ThesePlanetaire.AdhesionSafety

/-!
# Le financement de la prime

Un club porte trois termes de gain : `intr` (gain intrinsèque net d'adhérer), `prem` (prime versée
au membre, fonction de la coalition), `drain` (charge frontalière qu'un non-membre paie face à la
coalition, donc évitée en adhérant). Le gain d'adhérer est
`intr i S + prem i (insert i S) + drain i S`, la forme `P(k) = g(k) + m(k − 1)` que le modèle de
Renn (arXiv 2608.12143 v3) instancie dans le cas symétrique.

`BorderFinanced` : les primes des membres de `X` sont financées par les drains payés par les
non-membres de `X`.

1. ★ `border_premium_vanishes` : au plein, il n'y a plus de non-membre ; une prime positive
   financée par la frontière y est nulle.
2. ★ `full_nash_iff_border` : l'adhésion totale est un équilibre ssi, pour chacun,
   `intr + drain ≥ 0` au plein — la menace du drain (le bâton), pas la prime (la carotte).
3. ★ `premium_gap_witness` : une prime financée de l'extérieur tient le plein, aucune prime
   financée par la frontière ne le tient. Le financement interne au club (transferts de signe
   quelconque) est traité dans `ClubTransfers` (Phase 12) : son critère est la stabilité interne
   potentielle (somme des marges de pleine adhésion positive), pas `λ* ≤ 0`, qui teste les
   cycles et non le bilan.
4. ★ `club_drain_enlarges` : un drain positif élargit les équilibres extrêmes
   (`AdhesionGame.lfp_mono_gain`, `gfp_mono_gain`).
-/

namespace ClubFinancing

open AdhesionGame
open AdhesionSafety (finOf mem_finOf)

/-- Un club : gain intrinsèque, prime au membre, drain frontalier. -/
structure Club (𝕜 V : Type*) where
  intr : V → Set V → 𝕜
  prem : V → Set V → 𝕜
  drain : V → Set V → 𝕜

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Gain d'adhérer de `i` face aux autres adhérents `S`. -/
def Club.gain (C : Club 𝕜 V) : V → Set V → 𝕜 :=
  fun i S => C.intr i S + C.prem i (insert i S) + C.drain i S

/-- Le même club sans drain. -/
def Club.noDrain (C : Club 𝕜 V) : Club 𝕜 V := { C with drain := fun _ _ => 0 }

/-- ★ Un drain positif élargit les deux équilibres extrêmes. -/
theorem club_drain_enlarges (C : Club 𝕜 V) (h0 : Supermodular C.noDrain.gain)
    (hC : Supermodular C.gain) (hD : ∀ i S, 0 ≤ C.drain i S) :
    (br _ h0).lfp ⊆ (br _ hC).lfp ∧ (br _ h0).gfp ⊆ (br _ hC).gfp := by
  have h : ∀ i S, C.noDrain.gain i S ≤ C.gain i S := fun i S => by
    simp only [Club.gain, Club.noDrain, add_zero]
    linarith [hD i S]
  exact ⟨lfp_mono_gain _ _ h, gfp_mono_gain _ _ h⟩

variable [Fintype V] [DecidableEq V]

/-- Les primes des membres de `X` sont financées par les drains des non-membres de `X`. -/
def BorderFinanced (C : Club 𝕜 V) : Prop :=
  ∀ X : Set V, ∑ i ∈ finOf X, C.prem i X ≤ ∑ j ∈ (finOf X)ᶜ, C.drain j X

/-- ★ **Au plein, la prime financée par la frontière est nulle.** -/
theorem border_premium_vanishes {C : Club 𝕜 V} (hB : BorderFinanced C) (h0 : ∀ i X, 0 ≤ C.prem i X)
    (i : V) : C.prem i Set.univ = 0 := by
  have hf : finOf (Set.univ : Set V) = Finset.univ :=
    Finset.eq_univ_of_forall fun _ => mem_finOf.mpr trivial
  have h := hB Set.univ
  rw [hf, Finset.compl_univ, Finset.sum_empty] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j Set.univ).mp
    (le_antisymm h (Finset.sum_nonneg fun j _ => h0 j Set.univ))
  exact hz i (Finset.mem_univ i)

/-- ★ **Le bâton, pas la carotte** : sous financement frontalier, l'adhésion totale est un
équilibre ssi gain intrinsèque et drain évité suffisent, pour chacun. -/
theorem full_nash_iff_border {C : Club 𝕜 V} (hB : BorderFinanced C) (h0 : ∀ i X, 0 ≤ C.prem i X) :
    IsNash C.gain Set.univ ↔ ∀ i, 0 ≤ C.intr i (Set.univ \ {i}) + C.drain i (Set.univ \ {i}) := by
  have hins : ∀ i : V, insert i (Set.univ \ {i}) = Set.univ := fun i => by
    rw [Set.insert_diff_singleton, Set.insert_eq_of_mem (Set.mem_univ i)]
  have hp := border_premium_vanishes hB h0
  constructor
  · rintro ⟨h, -⟩ i
    have := h i (Set.mem_univ i)
    simp only [Club.gain, hins, hp, add_zero] at this
    exact this
  · intro h
    refine ⟨fun i _ => ?_, fun i hi => absurd (Set.mem_univ i) hi⟩
    simp only [Club.gain, hins, hp, add_zero]
    exact h i

/-- Club témoin : gain intrinsèque `−1`, aucun drain, prime `2` financée de l'extérieur. -/
def extClub : Club ℚ (Fin 2) where
  intr := fun _ _ => -1
  prem := fun _ _ => 2
  drain := fun _ _ => 0

/-- ★ **L'écart de la prime** : la prime extérieure tient le plein (mais n'est pas financée par
la frontière) ; à gain intrinsèque et drain égaux, aucune prime positive financée par la
frontière ne le tient. -/
theorem premium_gap_witness :
    IsNash extClub.gain Set.univ ∧ ¬ BorderFinanced extClub ∧
      ∀ C : Club ℚ (Fin 2), C.intr = extClub.intr → C.drain = extClub.drain → BorderFinanced C →
        (∀ i X, 0 ≤ C.prem i X) → ¬ IsNash C.gain Set.univ := by
  refine ⟨⟨fun i _ => ?_, fun i hi => absurd (Set.mem_univ i) hi⟩, fun hB => ?_, ?_⟩
  · simp only [Club.gain, extClub]
    norm_num
  · have := border_premium_vanishes hB (fun _ _ => by simp [extClub]) 0
    simp [extClub] at this
  · intro C hi hd hB h0 hN
    have := (full_nash_iff_border hB h0).mp hN 0
    rw [hi, hd] at this
    simp only [extClub] at this
    norm_num at this

end ClubFinancing

/-!
## Domaine (généralisation D-13, 2026-10-03)

Le club `Club 𝕜 V` et toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`,
sauf le club témoin (`extClub`, `premium_gap_witness`), qui reste dans `ℚ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration`. `ℚ` et
  `ℝ` en sont des instances ; les énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
