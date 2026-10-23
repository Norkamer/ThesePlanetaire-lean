/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/MinorityWitness.lean
  Phase 9 (2026-10-02), étape 9e : témoin exact de l'impact propre η dans un jeu de minorité
  déterministe à scores entiers — troupeau sous η = 0, gel sous η = 1.

  Développé d'abord en `MinorityWitness_scratch.lean` (workflow du dépôt). Instance trouvée par
  recherche exhaustive (`cache/phase9_2026-10-02/outils/cherche_temoin_eta.py`, N ≤ 3, P ≤ 2 ;
  sortie figée `references/cherche_temoin_eta_out.txt`).

  Phase 21 (2026-10-04) : commentaire du pas η = 1 corrigé (portée de l'éq. (17) de MCZ00 ;
  registre de la couche III, R15). Énoncés et preuves inchangés.
-/

import ThesePlanetaire.MeasureFibration

/-!
# Témoin η = 0 contre η = 1

**Modèle.** `N` agents, deux stratégies `a i s μ ∈ ℤ` (`s : Bool`), information exogène `μ_t`.
L'agent `i` tient la différence de scores `D i = U_true − U_false` et joue `s_i = [D i > 0]`.
Fréquentation `A = Σ_i a i s_i μ` (cible 0 : jeu de minorité). Mise à jour :
- η = 0 : `D i −= (a i true μ − a i false μ) · A` ;
- η = 1 : `D i −= (a i true μ − a i false μ) · (A − a i s_i μ)` : l'agent retire son propre
  impact et joue contre la fréquentation des autres. C'est la règle à information complète de
  Marsili–Challet–Zecchina 2000 (éq. (17), au facteur `1/P` près) seulement si
  `(a i true μ)² = (a i false μ)²`, par exemple à charges `±1` (le témoin `herd`) ; sinon
  l'éq. (17) ajoute le terme `−((a i true μ)² − (a i false μ)²)`.

**Témoin** (`herd`) : trois agents aux stratégies identiques (`±1`), `P = 1`, `D₀ = (−1, 1, 1)`.
1. ★ η = 0 : **troupeau** — orbite de période 2 dès `t = 1`, `A = −3, 3, −3, …`, `A² = 9` ;
   le cumul reste borné (`|Σ A| ≤ 2`) ; la section moyenne sur le cycle est `0`, de `H = 0`.
2. ★ η = 1 : **gel** pour toujours sur `(−, +, +)` (récurrence : chaque pas garde le signe des
   `D i`), `A = 1`, `A² = 1 = H` ; mais l'excès est **persistant** : le cumul vaut `T`.

Lecture : l'impact propre réduit la volatilité (MCZ ; BMRZ 2001 : équilibre unique et figé),
mais fige un biais par fibre qui **s'accumule** sur un budget `stock` (sonde S12 : η = 1
aggrave l'écart cumulé). `H` mesure l'écart en moyenne, pas le cumul : seule une garde le tient
(`GuardSupervisor.stock_guard_necessary`).
-/

namespace MinorityWitness

/-- Jeu de minorité déterministe à scores entiers. -/
structure MG (N P : ℕ) where
  /-- action (`±1`, ou une charge) de la stratégie `s` de l'agent `i` sur l'information `μ` -/
  a : Fin N → Bool → Fin P → ℤ

variable {N P : ℕ}

/-- Choix de l'agent : la stratégie `true` ssi son score l'emporte strictement. -/
def choice (D : Fin N → ℤ) (i : Fin N) : Bool := decide (0 < D i)

/-- Fréquentation agrégée. -/
def attendance (G : MG N P) (D : Fin N → ℤ) (μ : Fin P) : ℤ := ∑ i, G.a i (choice D i) μ

/-- Un pas de la dynamique des scores. -/
def step (G : MG N P) (η : Bool) (μ : Fin P) (D : Fin N → ℤ) : Fin N → ℤ := fun i =>
  D i - (G.a i true μ - G.a i false μ) *
    (attendance G D μ - if η then G.a i (choice D i) μ else 0)

/-- Trajectoire des différences de scores sous l'information `μs`. -/
def traj (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → ℤ) : ℕ → Fin N → ℤ
  | 0 => D₀
  | t + 1 => step G η (μs t) (traj G η μs D₀ t)

/-- Fréquentation au temps `t`. -/
def att (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → ℤ) (t : ℕ) : ℤ :=
  attendance G (traj G η μs D₀ t) (μs t)

/-- Écart cumulé à la cible sur `[0, T)`. -/
def cum (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → ℤ) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, att G η μs D₀ t

/-! ## Le témoin -/

/-- Trois agents aux stratégies identiques `false ↦ −1`, `true ↦ +1`, une seule information. -/
def herd : MG 3 1 := ⟨fun _ s _ => if s then 1 else -1⟩

/-- Information constante. -/
def μ0 : ℕ → Fin 1 := fun _ => 0

/-- État initial. -/
def D₀ : Fin 3 → ℤ := ![-1, 1, 1]

/-! ### η = 0 : troupeau -/

theorem herd_eta0_t1 : traj herd false μ0 D₀ 1 = ![-3, -1, -1] := by decide

theorem herd_eta0_t2 : traj herd false μ0 D₀ 2 = ![3, 5, 5] := by decide

theorem herd_eta0_t3 : traj herd false μ0 D₀ 3 = traj herd false μ0 D₀ 1 := by decide

/-- ★ Orbite de période 2 dès `t = 1`. -/
theorem herd_eta0_periodic (t : ℕ) :
    traj herd false μ0 D₀ (t + 3) = traj herd false μ0 D₀ (t + 1) := by
  induction t with
  | zero => exact herd_eta0_t3
  | succ t ih =>
    show step herd false (μ0 (t + 3)) (traj herd false μ0 D₀ (t + 3))
      = step herd false (μ0 (t + 1)) (traj herd false μ0 D₀ (t + 1))
    rw [ih]
    rfl

theorem herd_eta0_odd (k : ℕ) : traj herd false μ0 D₀ (2 * k + 1) = ![-3, -1, -1] := by
  induction k with
  | zero => exact herd_eta0_t1
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, herd_eta0_periodic, ih]

theorem herd_eta0_even (k : ℕ) : traj herd false μ0 D₀ (2 * k + 2) = ![3, 5, 5] := by
  induction k with
  | zero => exact herd_eta0_t2
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = (2 * k + 1) + 3 by ring, herd_eta0_periodic,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, ih]

/-- ★ Troupeau : tous les agents basculent ensemble, `A = −3` puis `3`. -/
theorem herd_eta0_att (k : ℕ) :
    att herd false μ0 D₀ (2 * k + 1) = -3 ∧ att herd false μ0 D₀ (2 * k + 2) = 3 := by
  unfold att
  rw [herd_eta0_odd, herd_eta0_even]
  exact ⟨by simp only [μ0]; decide, by simp only [μ0]; decide⟩

theorem cum_succ (G : MG N P) (η : Bool) (μs : ℕ → Fin P) (D₀ : Fin N → ℤ) (n : ℕ) :
    cum G η μs D₀ (n + 1) = cum G η μs D₀ n + att G η μs D₀ n :=
  Finset.sum_range_succ _ _

theorem herd_eta0_cum (k : ℕ) :
    cum herd false μ0 D₀ (2 * k + 1) = 1 ∧ cum herd false μ0 D₀ (2 * k + 2) = -2 := by
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    have h3 : cum herd false μ0 D₀ (2 * (k + 1) + 1) = 1 := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, cum_succ, ih.2, (herd_eta0_att k).2]
      norm_num
    refine ⟨h3, ?_⟩
    rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by ring, cum_succ, h3,
      (herd_eta0_att (k + 1)).1]
    norm_num

/-- ★ Sous η = 0, l'écart cumulé reste borné. -/
theorem herd_eta0_cum_bounded (T : ℕ) : |cum herd false μ0 D₀ T| ≤ 2 := by
  rcases Nat.even_or_odd' T with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · decide
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, (herd_eta0_cum k).2]
      norm_num
  · rw [(herd_eta0_cum k).1]
    norm_num

/-! ### η = 1 : gel -/

/-- Invariant de gel : décisions `(false, true, true)`. -/
def Frozen (D : Fin 3 → ℤ) : Prop := D 0 < 0 ∧ 0 < D 1 ∧ 0 < D 2

theorem herd_eta1_step {D : Fin 3 → ℤ} (h : Frozen D) :
    Frozen (step herd true 0 D) ∧ attendance herd D 0 = 1 := by
  obtain ⟨h0, h1, h2⟩ := h
  have c0 : choice D 0 = false := by simp [choice, not_lt.mpr h0.le]
  have c1 : choice D 1 = true := by simp [choice, h1]
  have c2 : choice D 2 = true := by simp [choice, h2]
  have hA : attendance herd D 0 = 1 := by
    simp only [attendance, Fin.sum_univ_three, c0, c1, c2, herd]
    norm_num
  refine ⟨⟨?_, ?_, ?_⟩, hA⟩ <;> simp only [step, hA, c0, c1, c2] <;> simp [herd] <;> linarith

/-- ★ Gel pour toujours (récurrence). -/
theorem herd_eta1_frozen (t : ℕ) : Frozen (traj herd true μ0 D₀ t) := by
  induction t with
  | zero => exact ⟨by decide, by decide, by decide⟩
  | succ t ih => exact (herd_eta1_step ih).1

/-- ★ Sous η = 1, la fréquentation est `1` à chaque pas. -/
theorem herd_eta1_att (t : ℕ) : att herd true μ0 D₀ t = 1 :=
  (herd_eta1_step (herd_eta1_frozen t)).2

/-- ★ … et l'écart cumulé croît linéairement : le biais s'accumule sur un budget `stock`. -/
theorem herd_eta1_cum (T : ℕ) : cum herd true μ0 D₀ T = T := by
  unfold cum
  simp [herd_eta1_att]

/-! ### Lecture par la fibration : `H` de la section moyenne contre volatilité -/

open MeasureFibration (MGInst H)

/-- La même instance comme fibration : charges `±1`, une fibre, capacité 0. -/
def herdInst : MGInst ℚ (Fin 3) (Fin 1) where
  aP := fun _ _ => 1
  aM := fun _ _ => -1
  L := fun _ => 0

/-- ★ η = 0 : la section moyenne sur le cycle est `0` et son `H` est nul (alors que `A² = 9`). -/
theorem herd_H_mean : H herdInst (fun _ => 1) (fun _ => 0) = 0 := by
  simp [H, MeasureFibration.exc, MeasureFibration.load, herdInst]

/-- ★ η = 1 : la section gelée `(−1, 1, 1)` a `H = 1 = A²`. -/
theorem herd_H_frozen : H herdInst (fun _ => 1) ![-1, 1, 1] = 1 := by
  simp [H, MeasureFibration.exc, MeasureFibration.load, herdInst, Fin.sum_univ_three]

/-- ★ Synthèse : sous η = 1, `A² = 1 < 9 = A²` sous η = 0, mais l'écart cumulé sur `2k + 1`
pas vaut `2k + 1` contre `1`. -/
theorem herd_tradeoff (k : ℕ) :
    att herd true μ0 D₀ (2 * k + 1) ^ 2 < att herd false μ0 D₀ (2 * k + 1) ^ 2 ∧
      cum herd false μ0 D₀ (2 * k + 1) = 1 ∧
      cum herd true μ0 D₀ (2 * k + 1) = 2 * k + 1 := by
  refine ⟨?_, (herd_eta0_cum k).1, ?_⟩
  · rw [herd_eta1_att, (herd_eta0_att k).1]
    norm_num
  · rw [herd_eta1_cum]
    push_cast
    ring

end MinorityWitness
