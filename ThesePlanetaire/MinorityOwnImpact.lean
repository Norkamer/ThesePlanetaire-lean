/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/MinorityOwnImpact.lean
  Phase 20 (2026-10-04) : révision du papier 12 après lecture critique — le théorème 3 (a)
  (l'impact propre ne se lit pas dans l'agrégat) pour tout nombre `N ≥ 2` d'émetteurs, tout
  nombre d'états et tout état, sur un corps ordonné.

  Développé d'abord en `MinorityOwnImpact_scratch.lean` (workflow du dépôt). Plan et trace :
  `cache/phase20_2026-10-04/`.
-/

import ThesePlanetaire.MinorityMeasures

/-!
# L'impact propre ne se lit pas dans l'agrégat, pour tout `N ≥ 2`

`MinorityMeasures.eta1_not_from_aggregateF` établit, pour deux émetteurs et un seul état, qu'aucune
fonction de la fréquentation, des écarts de charge et des scores ne donne le pas η = 1, alors
qu'une telle fonction existe pour η = 0. Ce module étend l'énoncé à tout nombre `N ≥ 2`
d'émetteurs, tout nombre d'états et tout état `μ`, en complétant les deux jeux du contre-exemple
par des émetteurs dont les deux stratégies chargent `0` (ils n'ajoutent rien à la fréquentation et
leur écart de charge est nul).

★ `eta1_not_from_aggregateN`.
-/

open Finset BigOperators

namespace MinorityOwnImpact

open MinorityMeasures

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {N P : ℕ}

/-- Premier jeu complété : les émetteurs `0` et `1` chargent `1 / 0` ; les autres, `0 / 0`. -/
def padA (N P : ℕ) : MGF 𝕜 N P :=
  ⟨fun i s _ => if i.val = 0 ∨ i.val = 1 then (if s then 1 else 0) else 0⟩

/-- Second jeu complété : l'émetteur `0` charge `2 / 1`, l'émetteur `1` charge `0 / −1` ; les
autres, `0 / 0`. -/
def padB (N P : ℕ) : MGF 𝕜 N P :=
  ⟨fun i s _ => if i.val = 0 then (if s then 2 else 1)
    else if i.val = 1 then (if s then 0 else -1) else 0⟩

/-- Les scores `1` partout : chaque émetteur joue la stratégie `true`. -/
def ones (N : ℕ) : Fin N → 𝕜 := fun _ => 1

theorem choiceF_ones (i : Fin N) : choiceF (ones (𝕜 := 𝕜) N) i = true := by
  simp [choiceF, ones]

/-- Les deux jeux complétés ont la même fréquentation, `2`, sous les scores `1`. -/
theorem attendance_padA (μ : Fin P) :
    attendanceF (padA (𝕜 := 𝕜) (N + 2) P) (ones (N + 2)) μ = 2 := by
  simp only [attendanceF, choiceF_ones, padA, if_true]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
  norm_num

theorem attendance_padB (μ : Fin P) :
    attendanceF (padB (𝕜 := 𝕜) (N + 2) P) (ones (N + 2)) μ = 2 := by
  simp only [attendanceF, choiceF_ones, padB, if_true]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
  norm_num

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Les deux jeux complétés ont les mêmes écarts de charge. -/
theorem spread_pad (μ : Fin P) :
    spread (padA (𝕜 := 𝕜) N P) μ = spread (padB N P) μ := by
  funext i
  simp only [spread, padA, padB, if_true, if_false, Bool.false_eq_true]
  by_cases h0 : i.val = 0
  · simp [h0]
    norm_num
  · by_cases h1 : i.val = 1
    · simp [h1]
    · simp [h0, h1]

/-- ★ **L'impact propre ne se lit pas dans l'agrégat**, pour tout `N ≥ 2`, tout nombre d'états et
tout état `μ`, sur tout corps ordonné : aucune fonction de la fréquentation, des écarts de charge
et des scores ne donne la mise à jour η = 1 ; la mise à jour η = 0, si. -/
theorem eta1_not_from_aggregateN (hN : 2 ≤ N) (μ : Fin P) :
    (¬ ∃ f : 𝕜 → (Fin N → 𝕜) → (Fin N → 𝕜) → (Fin N → 𝕜),
        ∀ (G : MGF 𝕜 N P) (D : Fin N → 𝕜),
          stepF G true μ D = f (attendanceF G D μ) (spread G μ) D) ∧
      ∃ f : 𝕜 → (Fin N → 𝕜) → (Fin N → 𝕜) → (Fin N → 𝕜),
        ∀ (G : MGF 𝕜 N P) (D : Fin N → 𝕜),
          stepF G false μ D = f (attendanceF G D μ) (spread G μ) D := by
  refine ⟨?_, ⟨fun A δ D i => D i - δ i * A, fun G D => by funext i; simp [stepF]⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rintro ⟨f, hf⟩
  have hA : attendanceF (padA (𝕜 := 𝕜) (n + 2) P) (ones (n + 2)) μ =
      attendanceF (padB (n + 2) P) (ones (n + 2)) μ := by
    rw [attendance_padA, attendance_padB]
  have hne := congrFun (by rw [hf (padA (n + 2) P) (ones (n + 2)), hf (padB (n + 2) P) (ones (n + 2)),
      hA, spread_pad] : stepF (padA (𝕜 := 𝕜) (n + 2) P) true μ (ones (n + 2)) =
        stepF (padB (n + 2) P) true μ (ones (n + 2))) 0
  have eA : stepF (padA (𝕜 := 𝕜) (n + 2) P) true μ (ones (n + 2)) 0 = 0 := by
    simp only [stepF]
    rw [attendance_padA]
    simp only [spread, choiceF_ones, padA, if_true, ones, Fin.val_zero]
    norm_num
  have eB : stepF (padB (𝕜 := 𝕜) (n + 2) P) true μ (ones (n + 2)) 0 = 1 := by
    simp only [stepF]
    rw [attendance_padB]
    simp only [spread, choiceF_ones, padB, if_true, ones, Fin.val_zero]
    norm_num
  rw [eA, eB] at hne
  exact zero_ne_one hne

end MinorityOwnImpact
