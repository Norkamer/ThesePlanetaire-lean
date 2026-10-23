/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/MinorityMeasures.lean
  Phase 15 (2026-10-04) : préparation du papier 12 — passage du jeu dynamique `MG` à la
  fibration `MGInst`, théorème C sur un corps ordonné et sa portée, portée du témoin η par la
  parité (Marsili, Challet et Zecchina 2000, §4).

  Développé d'abord en `MinorityMeasures_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase15_2026-10-03/plan.md` ; lectures : `cache/phase15_2026-10-03/lectures/` ;
  comparaison : `ThèseNov26/couche3_dynamique/P12_mesures_minorite/comparaison.md`.
-/

import ThesePlanetaire.MinorityWitness
import Mathlib.Data.ZMod.Basic

/-!
# Jeu de minorité dynamique, fibration et impact propre

1. Passage du jeu dynamique à la fibration. `toInst G L` est la fibration d'un jeu `G : MG N P`
   (charges converties dans `𝕜`, plafond `L`) ; `sectionOf D` est la section pure jouée par les
   scores `D`. ★ `cast_attendance` : la fréquentation est la charge de cette section, qui est dans
   la boîte (`box_sectionOf`). D'où, pour **toute** dynamique de scores et tout η :
   ★ `att_ge_minLoad`, `cum_ge_sum_minLoad` (bande atteignable) et ★ `dyn_stock_cannot` (si le
   budget de stock est infaisable pour la fibration, la dynamique le dépasse). `herdInst_eq` :
   l'instance `herdInst` de `MinorityWitness` est `toInst herd 0`, et `herd_H_frozen_dyn` lit
   `herd_H_frozen` sur la trajectoire.
2. Théorème C sur un corps ordonné. `MGF 𝕜 N P` : charges et scores dans `𝕜`. ★
   `eta1_from_recordsF`, `eta0_from_aggregateF`, `eta1_not_from_aggregateF` : les énoncés de
   `SelfImpactLedger`, sur tout corps ordonné. ★ `attendanceF_eq_load`, `attF_ge_minLoad`,
   `cumF_ge_sum_minLoad`, `dynF_stock_cannot` : le passage du §1 pour un jeu à charges dans `𝕜`.
   ★ `step_cast`, `traj_cast`, `att_cast`, `cum_cast` : la conversion `ℤ → 𝕜` commute avec la
   dynamique ; `herd_tradeoffF` en découle.
   ★ `eta1_from_aggregate_of_unit` (**portée**) : à charges `±1` (le jeu standard), le pas
   η = 1 est une fonction de la fréquentation, des écarts de charge et des scores. L'information
   qui manque à l'agrégat dans `eta1_not_from_aggregateF` est la part non ajustable propre
   `(a_true + a_false)/2`, hétérogène dans le contre-exemple.
3. Portée du témoin η par la parité. ★ `attendance_odd`, `one_le_abs_att` : à charges `±1` et
   `N` impair, la fréquentation de tout profil pur est impaire, donc `|A| ≥ 1`, pour toute
   dynamique. ★ `frozen_cum_linear`, `frozen_cum_ge` : un gel (choix et information constants)
   accumule linéairement, d'au moins `1` par pas à `N` impair. ★ `pair_eta1_cum`,
   `pair_eta0_fixed` : à `N = 2`, le profil `(−, +)` est gelé sous η = 1 à `A = 0` (cumul nul) et
   fixe sous η = 0. Marsili, Challet et Zecchina (2000, §4) énoncent la parité pour les
   équilibres de Nash purs : `|A| = 1` à `N` impair, `A = 0` à `N` pair.
-/

open Finset BigOperators

namespace MinorityMeasures

open MeasureFibration
open MinorityWitness (MG choice attendance step traj att cum cum_succ herd herdInst μ0 D₀ Frozen
  herd_eta1_frozen herd_H_frozen herd_tradeoff)

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {N P : ℕ}

/-! ### §1. Passage du jeu dynamique à la fibration -/

/-- La fibration d'un jeu dynamique : charges converties dans `𝕜`, plafond `L`. -/
def toInst (G : MG N P) (L : Fin P → 𝕜) : MGInst 𝕜 (Fin N) (Fin P) where
  aP := fun i μ => (G.a i true μ : 𝕜)
  aM := fun i μ => (G.a i false μ : 𝕜)
  L := L

/-- La section pure jouée par les scores `D` : `1` pour la stratégie `true`, `−1` sinon. -/
def sectionOf (D : Fin N → ℤ) : Fin N → 𝕜 := fun i => if choice D i then 1 else -1

/-- La section jouée est dans la boîte. -/
theorem box_sectionOf (D : Fin N → ℤ) : Box (sectionOf (𝕜 := 𝕜) D) := by
  intro i
  unfold sectionOf
  split_ifs <;> norm_num

/-- ★ La fréquentation est la charge de la section jouée. -/
theorem cast_attendance (G : MG N P) (L : Fin P → 𝕜) (D : Fin N → ℤ) (μ : Fin P) :
    ((attendance G D μ : ℤ) : 𝕜) = load (toInst G L) (sectionOf D) μ := by
  simp only [attendance, load, toInst, sectionOf, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases choice D i <;> norm_num

/-- ★ Pour toute dynamique de scores et tout η, la fréquentation au temps `t` est au-dessus de
la demande minimale atteignable de la fibre visitée. -/
theorem att_ge_minLoad (G : MG N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → ℤ) (t : ℕ) : minLoad (toInst G L) (μs t) ≤ ((att G η μs D t : ℤ) : 𝕜) := by
  rw [att, cast_attendance G L]
  exact minLoad_le_load _ (box_sectionOf _) _

/-- ★ Le cumul d'une dynamique de scores est au-dessus de la somme des demandes minimales. -/
theorem cum_ge_sum_minLoad (G : MG N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → ℤ) (T : ℕ) :
    ∑ t ∈ range T, minLoad (toInst G L) (μs t) ≤ ((cum G η μs D T : ℤ) : 𝕜) := by
  rw [cum, Int.cast_sum]
  exact Finset.sum_le_sum fun t _ => att_ge_minLoad G L η μs D t

/-- ★ Théorème B pour toute dynamique de scores : si aucune suite de mesures ne tient le budget
de stock `Bud` sur les `T` premières informations, la dynamique le dépasse, à tout η. -/
theorem dyn_stock_cannot (G : MG N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → ℤ) {T : ℕ} {Bud : 𝕜}
    (h : ¬ CapFeasible (stockAggregate (toInst G L) (fun t : Fin T => μs t) Bud)) :
    Bud < ((cum G η μs D T : ℤ) : 𝕜) := by
  rw [stock_infeasible_iff, Fin.sum_univ_eq_sum_range (fun t => minLoad (toInst G L) (μs t))] at h
  exact lt_of_lt_of_le h (cum_ge_sum_minLoad G L η μs D T)

/-- L'instance `herdInst` de `MinorityWitness` est la fibration du témoin `herd`. -/
theorem herdInst_eq : herdInst = toInst herd 0 := by
  simp [herdInst, toInst, herd]
  rfl

/-- Sous η = 1, la section jouée par le troupeau est la section gelée `(−1, 1, 1)`, d'où
`H = 1` à chaque pas. -/
theorem herd_H_frozen_dyn (t : ℕ) :
    H (toInst herd 0) (fun _ => (1 : ℚ)) (sectionOf (traj herd true μ0 D₀ t)) = 1 := by
  obtain ⟨h0, h1, h2⟩ := herd_eta1_frozen t
  have hs : sectionOf (𝕜 := ℚ) (traj herd true μ0 D₀ t) = ![-1, 1, 1] := by
    funext i
    fin_cases i <;> simp [sectionOf, choice, h1, h2, not_lt.mpr h0.le]
  rw [hs, ← herdInst_eq]
  exact herd_H_frozen

/-! ### §2. Le théorème C sur un corps ordonné -/

/-- Jeu de minorité à charges et scores dans `𝕜`. -/
structure MGF (𝕜 : Type*) (N P : ℕ) where
  /-- charge de la stratégie `s` de l'agent `i` sur l'information `μ` -/
  a : Fin N → Bool → Fin P → 𝕜

/-- Choix de l'agent : la stratégie `true` ssi son score l'emporte strictement. -/
def choiceF (D : Fin N → 𝕜) (i : Fin N) : Bool := decide (0 < D i)

/-- Fréquentation agrégée. -/
def attendanceF (G : MGF 𝕜 N P) (D : Fin N → 𝕜) (μ : Fin P) : 𝕜 :=
  ∑ i, G.a i (choiceF D i) μ

/-- Écarts de charge `a_true − a_false`. -/
def spread (G : MGF 𝕜 N P) (μ : Fin P) : Fin N → 𝕜 := fun i => G.a i true μ - G.a i false μ

/-- Un pas de la dynamique des scores. -/
def stepF (G : MGF 𝕜 N P) (η : Bool) (μ : Fin P) (D : Fin N → 𝕜) : Fin N → 𝕜 := fun i =>
  D i - spread G μ i * (attendanceF G D μ - if η then G.a i (choiceF D i) μ else 0)

/-- Mise à jour à partir d'enregistrements : total `tot`, contribution propre `rec i`. -/
def stepRecF (G : MGF 𝕜 N P) (μ : Fin P) (D : Fin N → 𝕜) (tot : 𝕜) (rec : Fin N → 𝕜) :
    Fin N → 𝕜 :=
  fun i => D i - spread G μ i * (tot - rec i)

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Avec les contributions propres et leur total, `stepRecF` est la mise à jour η = 1. -/
theorem eta1_from_recordsF (G : MGF 𝕜 N P) (μ : Fin P) (D : Fin N → 𝕜) {rec : Fin N → 𝕜}
    (hrec : ∀ i, rec i = G.a i (choiceF D i) μ) {tot : 𝕜} (htot : tot = ∑ i, rec i) :
    stepRecF G μ D tot rec = stepF G true μ D := by
  funext i
  simp only [stepRecF, stepF, attendanceF, htot, hrec, if_true]

omit [IsStrictOrderedRing 𝕜] in
/-- Sous η = 0, l'agrégat suffit (enregistrements nuls). -/
theorem eta0_from_aggregateF (G : MGF 𝕜 N P) (μ : Fin P) (D : Fin N → 𝕜) :
    stepF G false μ D = stepRecF G μ D (attendanceF G D μ) 0 := by
  funext i
  simp [stepF, stepRecF]

/-- Conversion d'un jeu à charges entières. -/
def castG (G : MG N P) : MGF 𝕜 N P := ⟨fun i s μ => (G.a i s μ : 𝕜)⟩

/-- Conversion des scores. -/
def castD (D : Fin N → ℤ) : Fin N → 𝕜 := fun i => (D i : 𝕜)

/-- La conversion préserve les choix (`0 < (d : 𝕜) ↔ 0 < d`). -/
theorem choice_cast (D : Fin N → ℤ) : choiceF (castD (𝕜 := 𝕜) D) = choice D := by
  funext i
  simp [choiceF, choice, castD]

theorem attendance_cast (G : MG N P) (D : Fin N → ℤ) (μ : Fin P) :
    attendanceF (castG (𝕜 := 𝕜) G) (castD D) μ = ((attendance G D μ : ℤ) : 𝕜) := by
  simp [attendanceF, attendance, choice_cast, castG]

/-- ★ La conversion commute avec un pas. -/
theorem step_cast (G : MG N P) (η : Bool) (μ : Fin P) (D : Fin N → ℤ) :
    stepF (castG (𝕜 := 𝕜) G) η μ (castD D) = castD (step G η μ D) := by
  funext i
  have hA := attendance_cast (𝕜 := 𝕜) G D μ
  have hc := congrFun (choice_cast (𝕜 := 𝕜) D) i
  simp only [stepF, hA, hc, spread]
  simp only [castD, castG, step]
  split_ifs <;> push_cast <;> ring

/-- Trajectoire dans `𝕜`. -/
def trajF (G : MGF 𝕜 N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → 𝕜) : ℕ → Fin N → 𝕜
  | 0 => D₀
  | t + 1 => stepF G η (μs t) (trajF G η μs D₀ t)

/-- Fréquentation au temps `t`. -/
def attF (G : MGF 𝕜 N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → 𝕜) (t : ℕ) : 𝕜 :=
  attendanceF G (trajF G η μs D₀ t) (μs t)

/-- Écart cumulé à la cible sur `[0, T)`. -/
def cumF (G : MGF 𝕜 N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → 𝕜) (T : ℕ) : 𝕜 :=
  ∑ t ∈ range T, attF G η μs D₀ t

/-- La fibration d'un jeu à charges dans `𝕜`, de plafond `L`. -/
def toInstF (G : MGF 𝕜 N P) (L : Fin P → 𝕜) : MGInst 𝕜 (Fin N) (Fin P) where
  aP := fun i μ => G.a i true μ
  aM := fun i μ => G.a i false μ
  L := L

/-- La section pure jouée par les scores `D`. -/
def sectionOfF (D : Fin N → 𝕜) : Fin N → 𝕜 := fun i => if choiceF D i then 1 else -1

theorem box_sectionOfF (D : Fin N → 𝕜) : Box (sectionOfF D) := by
  intro i
  unfold sectionOfF
  split_ifs <;> norm_num

/-- ★ Sur tout corps ordonné, la fréquentation est la charge de la section jouée. -/
theorem attendanceF_eq_load (G : MGF 𝕜 N P) (L : Fin P → 𝕜) (D : Fin N → 𝕜) (μ : Fin P) :
    attendanceF G D μ = load (toInstF G L) (sectionOfF D) μ := by
  simp only [attendanceF, load, toInstF, sectionOfF]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases choiceF D i <;> norm_num

/-- ★ Pour toute dynamique de scores dans `𝕜` et tout η : bande atteignable à chaque pas. -/
theorem attF_ge_minLoad (G : MGF 𝕜 N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → 𝕜) (t : ℕ) : minLoad (toInstF G L) (μs t) ≤ attF G η μs D t := by
  rw [attF, attendanceF_eq_load G L]
  exact minLoad_le_load _ (box_sectionOfF _) _

/-- ★ Le cumul est au-dessus de la somme des demandes minimales. -/
theorem cumF_ge_sum_minLoad (G : MGF 𝕜 N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → 𝕜) (T : ℕ) :
    ∑ t ∈ range T, minLoad (toInstF G L) (μs t) ≤ cumF G η μs D T :=
  Finset.sum_le_sum fun t _ => attF_ge_minLoad G L η μs D t

/-- ★ Théorème B pour toute dynamique de scores dans `𝕜` : si aucune suite de mesures ne tient
le budget de stock `Bud`, la dynamique le dépasse, à tout η. -/
theorem dynF_stock_cannot (G : MGF 𝕜 N P) (L : Fin P → 𝕜) (η : Bool) (μs : ℕ → Fin P)
    (D : Fin N → 𝕜) {T : ℕ} {Bud : 𝕜}
    (h : ¬ CapFeasible (stockAggregate (toInstF G L) (fun t : Fin T => μs t) Bud)) :
    Bud < cumF G η μs D T := by
  rw [stock_infeasible_iff,
    Fin.sum_univ_eq_sum_range (fun t => minLoad (toInstF G L) (μs t))] at h
  exact lt_of_lt_of_le h (cumF_ge_sum_minLoad G L η μs D T)

theorem traj_cast (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ) (t : ℕ) :
    trajF (castG (𝕜 := 𝕜) G) η μs (castD D) t = castD (traj G η μs D t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [trajF, ih, step_cast]; rfl

theorem att_cast (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ) (t : ℕ) :
    attF (castG (𝕜 := 𝕜) G) η μs (castD D) t = ((att G η μs D t : ℤ) : 𝕜) := by
  rw [attF, traj_cast, attendance_cast]; rfl

/-- ★ La conversion commute avec le cumul. -/
theorem cum_cast (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ) (T : ℕ) :
    cumF (castG (𝕜 := 𝕜) G) η μs (castD D) T = ((cum G η μs D T : ℤ) : 𝕜) := by
  simp only [cumF, cum, Int.cast_sum, att_cast]

/-- ★ Le compromis du troupeau vaut dans tout corps ordonné. -/
theorem herd_tradeoffF (k : ℕ) :
    attF (castG (𝕜 := 𝕜) herd) true μ0 (castD D₀) (2 * k + 1) ^ 2 <
        attF (castG herd) false μ0 (castD D₀) (2 * k + 1) ^ 2 ∧
      cumF (castG (𝕜 := 𝕜) herd) false μ0 (castD D₀) (2 * k + 1) = 1 ∧
      cumF (castG (𝕜 := 𝕜) herd) true μ0 (castD D₀) (2 * k + 1) = 2 * k + 1 := by
  obtain ⟨h1, h2, h3⟩ := herd_tradeoff k
  simp only [att_cast, cum_cast]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- Contre-exemple de `SelfImpactLedger` dans `𝕜` : `gA` (charges `1 / 0`). -/
def gAF : MGF 𝕜 2 1 := ⟨fun _ s _ => if s then 1 else 0⟩

/-- `gB` (agent 0 : `2 / 1`, agent 1 : `0 / −1`). -/
def gBF : MGF 𝕜 2 1 :=
  ⟨fun i s _ => if i = 0 then (if s then 2 else 1) else (if s then 0 else -1)⟩

/-- Les scores `(1, 1)`. -/
def dABF : Fin 2 → 𝕜 := ![1, 1]

/-- ★ **L'impact propre ne se lit pas dans l'agrégat**, sur tout corps ordonné : aucune
fonction de la fréquentation, des écarts de charge et des scores ne donne la mise à jour
η = 1 ; la mise à jour η = 0, si. -/
theorem eta1_not_from_aggregateF :
    (¬ ∃ f : 𝕜 → (Fin 2 → 𝕜) → (Fin 2 → 𝕜) → (Fin 2 → 𝕜),
        ∀ (G : MGF 𝕜 2 1) (D : Fin 2 → 𝕜),
          stepF G true 0 D = f (attendanceF G D 0) (spread G 0) D) ∧
      ∃ f : 𝕜 → (Fin 2 → 𝕜) → (Fin 2 → 𝕜) → (Fin 2 → 𝕜),
        ∀ (G : MGF 𝕜 2 1) (D : Fin 2 → 𝕜),
          stepF G false 0 D = f (attendanceF G D 0) (spread G 0) D := by
  refine ⟨?_, ⟨fun A δ D i => D i - δ i * A, fun G D => by funext i; simp [stepF]⟩⟩
  rintro ⟨f, hf⟩
  have hc : ∀ i, choiceF (dABF (𝕜 := 𝕜)) i = true := by
    intro i
    fin_cases i <;> simp [choiceF, dABF]
  have hA : attendanceF (gAF (𝕜 := 𝕜)) dABF 0 = attendanceF gBF dABF 0 := by
    simp only [attendanceF, Fin.sum_univ_two, hc, gAF, gBF]
    norm_num
  have hδ : spread (gAF (𝕜 := 𝕜)) 0 = spread gBF 0 := by
    funext i
    fin_cases i <;> norm_num [spread, gAF, gBF]
  have hne := congrFun (by rw [hf gAF dABF, hf gBF dABF, hA, hδ] :
    stepF (gAF (𝕜 := 𝕜)) true 0 dABF = stepF gBF true 0 dABF) 0
  have eA : stepF (gAF (𝕜 := 𝕜)) true 0 dABF 0 = 0 := by
    simp [stepF, attendanceF, spread, hc, gAF]
    norm_num [dABF]
  have eB : stepF (gBF (𝕜 := 𝕜)) true 0 dABF 0 = 1 := by
    simp [stepF, attendanceF, spread, hc, gBF]
    norm_num [dABF]
  rw [eA, eB] at hne
  exact zero_ne_one hne

/-- Charges unitaires : chaque stratégie charge `1` ou `−1` (le jeu standard). -/
def UnitLoads (G : MGF 𝕜 N P) : Prop := ∀ i s μ, G.a i s μ = 1 ∨ G.a i s μ = -1

/-- ★ **Portée du théorème C** : à charges unitaires, le pas η = 1 est une fonction de la
fréquentation, des écarts de charge et des scores (la contribution propre est `± δ / 2`).
L'énoncé `eta1_not_from_aggregateF` exige donc des parts non ajustables propres hétérogènes. -/
theorem eta1_from_aggregate_of_unit (μ : Fin P) :
    ∃ f : 𝕜 → (Fin N → 𝕜) → (Fin N → 𝕜) → (Fin N → 𝕜),
      ∀ (G : MGF 𝕜 N P), UnitLoads G → ∀ D : Fin N → 𝕜,
        stepF G true μ D = f (attendanceF G D μ) (spread G μ) D := by
  refine ⟨fun A δ D i => D i - δ i * (A - if 0 < D i then δ i / 2 else -(δ i / 2)),
    fun G hG D => ?_⟩
  funext i
  simp only [stepF, spread, choiceF, if_true]
  by_cases hD : 0 < D i
  · simp only [hD, decide_true, if_true]
    rcases hG i true μ with h1 | h1 <;> rcases hG i false μ with h2 | h2 <;> rw [h1, h2] <;> ring
  · simp only [hD, decide_false, if_false]
    rcases hG i true μ with h1 | h1 <;> rcases hG i false μ with h2 | h2 <;> rw [h1, h2] <;> ring

/-! ### §3. Portée du témoin η : la parité -/

/-- ★ À charges `±1` et `N` impair, la fréquentation de tout profil pur est impaire. -/
theorem attendance_odd (G : MG N P) (hG : ∀ i s μ, G.a i s μ = 1 ∨ G.a i s μ = -1)
    (hN : Odd N) (D : Fin N → ℤ) (μ : Fin P) : Odd (attendance G D μ) := by
  rw [← ZMod.intCast_eq_one_iff_odd, attendance, Int.cast_sum]
  have h1 : ∀ i, ((G.a i (choice D i) μ : ℤ) : ZMod 2) = 1 := fun i => by
    rcases hG i (choice D i) μ with h | h <;> rw [h] <;> decide
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_one_iff_odd).mpr hN

/-- ★ Pour toute dynamique, à charges `±1` et `N` impair : `|A| ≥ 1` à chaque pas. -/
theorem one_le_abs_att (G : MG N P) (hG : ∀ i s μ, G.a i s μ = 1 ∨ G.a i s μ = -1)
    (hN : Odd N) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ) (t : ℕ) :
    1 ≤ |att G η μs D t| := by
  refine Int.one_le_abs fun h0 => ?_
  have hodd : Odd (att G η μs D t) := attendance_odd G hG hN (traj G η μs D t) (μs t)
  rw [h0] at hodd
  simp at hodd

/-- ★ Un gel (choix et information constants à partir de `t₀`) accumule linéairement. -/
theorem frozen_cum_linear (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ)
    {t₀ : ℕ} {c : Fin N → Bool} {μ : Fin P}
    (hc : ∀ k, choice (traj G η μs D (t₀ + k)) = c) (hμ : ∀ k, μs (t₀ + k) = μ) (k : ℕ) :
    cum G η μs D (t₀ + k) = cum G η μs D t₀ + k * ∑ i, G.a i (c i) μ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, cum_succ, ih, att, attendance, hc k, hμ k]
    push_cast
    ring

/-- ★ À charges `±1` et `N` impair, un gel accumule au moins `1` par pas. -/
theorem frozen_cum_ge (G : MG N P) (hG : ∀ i s μ, G.a i s μ = 1 ∨ G.a i s μ = -1)
    (hN : Odd N) (η : Bool) (μs : ℕ → Fin P) (D : Fin N → ℤ)
    {t₀ : ℕ} {c : Fin N → Bool} {μ : Fin P}
    (hc : ∀ k, choice (traj G η μs D (t₀ + k)) = c) (hμ : ∀ k, μs (t₀ + k) = μ) (k : ℕ) :
    (k : ℤ) ≤ |cum G η μs D (t₀ + k) - cum G η μs D t₀| := by
  rw [frozen_cum_linear G η μs D hc hμ k, add_sub_cancel_left, abs_mul, Nat.abs_cast]
  have hA : 1 ≤ |∑ i, G.a i (c i) μ| := by
    have := one_le_abs_att G hG hN η μs D t₀
    rwa [att, attendance, show choice (traj G η μs D t₀) = c by simpa using hc 0,
      show μs t₀ = μ by simpa using hμ 0] at this
  nlinarith [abs_nonneg (∑ i, G.a i (c i) μ)]

/-- Deux agents aux stratégies `false ↦ −1`, `true ↦ +1`, une seule information. -/
def pair : MG 2 1 := ⟨fun _ s _ => if s then 1 else -1⟩

/-- Les scores initiaux `(−1, 1)` : le profil `(−, +)`, à `A = 0`. -/
def Dp : Fin 2 → ℤ := ![-1, 1]

/-- Le profil `(−, +)`. -/
def PairFrozen (D : Fin 2 → ℤ) : Prop := D 0 < 0 ∧ 0 < D 1

theorem pair_eta1_step {D : Fin 2 → ℤ} (h : PairFrozen D) :
    PairFrozen (step pair true 0 D) ∧ attendance pair D 0 = 0 := by
  obtain ⟨h0, h1⟩ := h
  have c0 : choice D 0 = false := by simp [choice, not_lt.mpr h0.le]
  have c1 : choice D 1 = true := by simp [choice, h1]
  have hA : attendance pair D 0 = 0 := by
    simp [attendance, Fin.sum_univ_two, c0, c1, pair]
  refine ⟨⟨?_, ?_⟩, hA⟩
  · simp only [step, if_true]
    rw [hA, c0]
    simp [pair]
    omega
  · simp only [step, if_true]
    rw [hA, c1]
    simp [pair]
    omega

theorem pair_eta1_frozen (t : ℕ) : PairFrozen (traj pair true μ0 Dp t) := by
  induction t with
  | zero => exact ⟨by decide, by decide⟩
  | succ t ih => exact (pair_eta1_step ih).1

/-- ★ À `N = 2`, sous η = 1, le profil `(−, +)` est gelé à `A = 0` : le cumul est nul. -/
theorem pair_eta1_cum (T : ℕ) : cum pair true μ0 Dp T = 0 := by
  unfold cum
  exact Finset.sum_eq_zero fun t _ => (pair_eta1_step (pair_eta1_frozen t)).2

/-- ★ Sous η = 0, le même profil est fixe (`A = 0` : aucun pas). -/
theorem pair_eta0_fixed : step pair false 0 Dp = Dp := by decide

end MinorityMeasures

/-!
## Domaine

- §1 : les fibrations `toInst G L` sont sur un corps ordonné quelconque `𝕜` ; le jeu `MG` reste
  dans `ℤ` (`MinorityWitness`, inchangé). `herd_H_frozen_dyn` est dans `ℚ`, comme `herdInst`.
- §2 : `MGF`, ses pas, sa fibration `toInstF` et les énoncés du théorème C sont sur un corps
  ordonné quelconque `𝕜` (classes `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`,
  décision D-13 de `ThèseNov26/00_cadre/decisions.md` ; les énoncés précédés de `omit … in` en
  demandent moins). Les énoncés dans `ℤ` de `MinorityWitness` et `SelfImpactLedger` en sont des
  instances par `step_cast`, `traj_cast`, `att_cast`, `cum_cast`.
- §3 : la parité est une propriété des charges entières `±1` ; elle reste dans `ℤ`. Par
  `att_cast` et `cum_cast`, elle vaut pour les mêmes charges vues dans tout corps ordonné. Les
  témoins (`pair`, `Dp`) sont dans `ℤ`.
-/
