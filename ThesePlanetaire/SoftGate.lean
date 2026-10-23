/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/SoftGate.lean
  Phase 10 (2026-10-02), étape 10f : « droit + taxe » — la soupape de prix ne tient pas le
  plafond hors de la bande atteignable ; la porte douce à rattrapage (T-M12-1b) le tient en
  différé, par une dette au moins égale à l'écart de la bande.

  Développé d'abord en `SoftGate_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase10_2026-10-02/plan_phase10.md` ; analyse :
  `cache/analyse_phase10_garde_repartie_2026-10-02.md` §7 ; sonde P1-P4
  (`cache/phase10_2026-10-02/outils/sonde_porte_douce.py`) ; amont :
  `cache/analyse_options_1_2_droit_taxe_2026-10-02.md` §3.
-/

import ThesePlanetaire.GuardSupervisor

/-!
# Soupape et porte douce

1. ★ `valve_overshoot_ge`, `valve_overshoot_pos` : un prix (taxe) n'agit que sur la section
   `m` dans la boîte. Pour **toute** réponse au prix, le dépassement du budget est au moins
   `Σ minLoad − Bud` : hors de la bande atteignable, aucun prix ne tient le plafond.
2. La **porte douce** (marché de droits avec pénalité ; directive 2003/87/CE art. 16(3)) :
   l'émission n'est jamais refusée, l'excédent sur la banque de droits devient une dette.
   - avec rattrapage (la dette est prélevée sur les allocations suivantes) :
     ★ `makeup_conservation` (`E + h = A + D`), ★ `makeup_once_only` (`E ≤ A + D` ; dette
     soldée ⇒ `E ≤ A`), ★ `makeup_debt_band` (dette ≥ écart de la bande sous une dynamique des
     mesures pure), ★ `makeup_debt_unbounded` (allocation par période sous l'émission par
     période ⇒ dette ≥ `n(d − a) − h₀`) ;
   - sans rattrapage (pénalité libératoire, soupape) : ★ `valve_unbounded` — l'émission dépasse
     les allocations d'autant qu'on veut, dette nulle.
   Lecture : la porte douce à rattrapage est la garde **différée** (le plafond tient à
   l'horizon si la dette est soldée) ; sans rattrapage, elle n'est plus une garde.
-/

namespace SoftGate

open MeasureFibration (MGInst Box load minLoad minLoad_le_load)
open GuardSupervisor (natInst pureEmit pureSection cast_pureEmit_sum)

/-! ## §1. La soupape de prix -/

section Valve

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ι B : Type*} [Fintype ι] {T : ℕ}

/-- ★ Pour toute réponse au prix à valeurs dans la boîte et **tout** prix `p`, le dépassement du
budget est au moins `Σ minLoad − Bud`. -/
theorem valve_overshoot_ge (G : MGInst 𝕜 ι B) (s : Fin T → B) (Bud : 𝕜)
    (resp : 𝕜 → Fin T → ι → 𝕜) (hresp : ∀ p t, Box (resp p t)) (p : 𝕜) :
    ∑ t, minLoad G (s t) - Bud ≤ ∑ t, load G (resp p t) (s t) - Bud :=
  sub_le_sub_right (Finset.sum_le_sum fun t _ => minLoad_le_load G (hresp p t) (s t)) Bud

/-- ★ Hors de la bande (`Bud < Σ minLoad`), aucun prix ne tient le budget. -/
theorem valve_overshoot_pos (G : MGInst 𝕜 ι B) (s : Fin T → B) {Bud : 𝕜}
    (h : Bud < ∑ t, minLoad G (s t)) (resp : 𝕜 → Fin T → ι → 𝕜)
    (hresp : ∀ p t, Box (resp p t)) (p : 𝕜) : 0 < ∑ t, load G (resp p t) (s t) - Bud := by
  have := valve_overshoot_ge G s Bud resp hresp p
  linarith

end Valve

/-! ## §2. La porte douce -/

/-- État : droits en banque `h`, dette `D`, émissions cumulées `E`. -/
structure SG where
  h : ℕ
  D : ℕ
  E : ℕ

/-- Événements : émission de `k`, top de période avec allocation `a`. -/
inductive Ev
  | emit (k : ℕ)
  | top (a : ℕ)

/-- Émettre `k` : jamais refusé ; l'excédent sur la banque devient une dette. -/
def emitSG (q : SG) (k : ℕ) : SG :=
  if k ≤ q.h then ⟨q.h - k, q.D, q.E + k⟩ else ⟨0, q.D + (k - q.h), q.E + k⟩

/-- Top avec rattrapage : la dette est prélevée sur la banque et l'allocation. -/
def topMakeup (q : SG) (a : ℕ) : SG := ⟨q.h + a - q.D, q.D - (q.h + a), q.E⟩

/-- Top sans rattrapage (pénalité libératoire) : la dette est effacée. -/
def topValve (q : SG) (a : ℕ) : SG := ⟨q.h + a, 0, q.E⟩

def sgStep (makeup : Bool) (q : SG) : Ev → SG
  | .emit k => emitSG q k
  | .top a => if makeup then topMakeup q a else topValve q a

/-- Exécution d'un mot. -/
def runSG (makeup : Bool) : SG → List Ev → SG
  | q, [] => q
  | q, e :: w => runSG makeup (sgStep makeup q e) w

/-- Allocations et émissions d'un mot. -/
def alloc : List Ev → ℕ
  | [] => 0
  | .emit _ :: w => alloc w
  | .top a :: w => a + alloc w

def emitted : List Ev → ℕ
  | [] => 0
  | .emit k :: w => k + emitted w
  | .top _ :: w => emitted w

theorem runSG_E (makeup : Bool) : ∀ (q : SG) (w : List Ev),
    (runSG makeup q w).E = q.E + emitted w
  | q, [] => rfl
  | q, .emit k :: w => by
    rw [runSG, runSG_E makeup _ w, emitted]
    simp only [sgStep, emitSG]
    split_ifs <;> simp only <;> ring
  | q, .top a :: w => by
    rw [runSG, runSG_E makeup _ w, emitted]
    simp only [sgStep]
    split_ifs <;> rfl

theorem sgStep_makeup (q : SG) (e : Ev) :
    (sgStep true q e).E + (sgStep true q e).h + q.D =
      q.E + q.h + alloc [e] + (sgStep true q e).D := by
  cases e with
  | emit k =>
    simp only [sgStep, emitSG, alloc]
    split_ifs <;> simp only <;> omega
  | top a =>
    simp only [sgStep, topMakeup, alloc, if_true]
    omega

/-- ★ **Conservation avec rattrapage** : `E' + h' + D = E + h + A + D'`. Depuis `(h₀, 0, 0)` :
`E + h = h₀ + A + D` — chaque unité émise est couverte par un droit alloué ou portée en
dette. -/
theorem makeup_conservation : ∀ (q : SG) (w : List Ev),
    (runSG true q w).E + (runSG true q w).h + q.D = q.E + q.h + alloc w + (runSG true q w).D
  | q, [] => by simp [runSG, alloc]
  | q, e :: w => by
    have ih := makeup_conservation (sgStep true q e) w
    have hs := sgStep_makeup q e
    have ha : alloc (e :: w) = alloc [e] + alloc w := by
      cases e <;> simp [alloc]
    rw [runSG, ha]
    omega

/-- ★ **Once-only différé** : depuis `(h₀, 0, 0)`, `E ≤ h₀ + A + D` ; quand la dette est soldée,
les émissions cumulées ne dépassent pas les droits alloués. -/
theorem makeup_once_only (h₀ : ℕ) (w : List Ev) :
    (runSG true ⟨h₀, 0, 0⟩ w).E ≤ h₀ + alloc w + (runSG true ⟨h₀, 0, 0⟩ w).D ∧
      ((runSG true ⟨h₀, 0, 0⟩ w).D = 0 → (runSG true ⟨h₀, 0, 0⟩ w).E ≤ h₀ + alloc w) := by
  have := makeup_conservation ⟨h₀, 0, 0⟩ w
  simp only at this
  exact ⟨by omega, fun hD => by omega⟩

/-- ★ La dette couvre au moins l'excédent des émissions sur les droits alloués. -/
theorem makeup_debt_ge (h₀ : ℕ) (w : List Ev) :
    emitted w ≤ (runSG true ⟨h₀, 0, 0⟩ w).D + h₀ + alloc w := by
  have h1 := (makeup_once_only h₀ w).1
  rw [runSG_E] at h1
  dsimp only at h1
  omega

/-- ★ **Dette non bornée** : si les émissions dépassent `n·d` et les allocations restent sous
`n·a`, la dette est au moins `n·(d − a) − h₀`. En `stock` avec des incontrôlables, l'allocation
doit tendre vers 0 (`ReserveCoverage.coverage_stock_iff`) : la dette diverge. -/
theorem makeup_debt_unbounded {h₀ n d a : ℕ} {w : List Ev} (hE : n * d ≤ emitted w)
    (hA : alloc w ≤ n * a) : n * d ≤ (runSG true ⟨h₀, 0, 0⟩ w).D + h₀ + n * a := by
  have := makeup_debt_ge h₀ w
  omega

/-- ★ **Sans rattrapage, la soupape** : pour tous `h₀`, `a`, `n`, une période émet `n` de plus
que les droits alloués, et la dette est effacée au top. -/
theorem valve_unbounded (h₀ a n : ℕ) :
    (runSG false ⟨h₀, 0, 0⟩ [.emit (h₀ + a + n), .top a]).E =
        h₀ + alloc [.emit (h₀ + a + n), .top a] + n ∧
      (runSG false ⟨h₀, 0, 0⟩ [.emit (h₀ + a + n), .top a]).D = 0 := by
  simp only [runSG, sgStep, emitSG, topValve, alloc, Bool.false_eq_true, if_false]
  split_ifs <;> dsimp only <;> exact ⟨by omega, trivial⟩

/-! ### La porte douce sous la bande atteignable -/

section Band

variable {ι B : Type*} [Fintype ι] {T : ℕ}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- ★ **Dette ≥ écart de la bande** : si les émissions sont celles d'une dynamique des mesures
pure `σ` (la porte douce ne refuse rien) et que les droits alloués restent sous le budget,
`h₀ + A ≤ Bud < Σ minLoad`, la dette à l'horizon est au moins `Σ minLoad − Bud`. -/
theorem makeup_debt_band (aP aM : ι → B → ℕ) (s : Fin T → B) (σ : Fin T → ι → Bool)
    (h₀ : ℕ) (w : List Ev) (hE : emitted w = ∑ ti, pureEmit aP aM s σ ti) {Bud : 𝕜}
    (hA : ((h₀ + alloc w : ℕ) : 𝕜) ≤ Bud) :
    ∑ t, minLoad (natInst aP aM) (s t) - Bud ≤ (runSG true ⟨h₀, 0, 0⟩ w).D := by
  have h1 : (emitted w : 𝕜) ≤ (runSG true ⟨h₀, 0, 0⟩ w).D + ((h₀ + alloc w : ℕ) : 𝕜) := by
    have := makeup_debt_ge h₀ w
    push_cast
    exact_mod_cast (by omega : emitted w ≤ (runSG true ⟨h₀, 0, 0⟩ w).D + (h₀ + alloc w))
  have hm : ∀ t, Box (pureSection (𝕜 := 𝕜) σ t) := fun t i => by
    unfold pureSection
    split_ifs <;> norm_num
  have h2 : ∑ t, minLoad (natInst aP aM) (s t) ≤ (emitted w : 𝕜) := by
    rw [hE, cast_pureEmit_sum]
    exact Finset.sum_le_sum fun t _ => minLoad_le_load _ (hm t) (s t)
  linarith

end Band

end SoftGate

/-!
## Domaine (généralisation D-13, 2026-10-03)

La section `Valve` était déjà énoncée sur un corps ordonné quelconque. La section `Band`
(`makeup_debt_band`) l'est aussi. Le reste du module est dans `ℕ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration`. `ℚ` et
  `ℝ` en sont des instances ; les énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
