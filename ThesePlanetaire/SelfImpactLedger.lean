/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/SelfImpactLedger.lean
  Phase 10 (2026-10-02), étape 10e : l'impact propre (η = 1) se lit dans le grand livre par
  détenteur, pas dans l'agrégat que lit la garde centrale (A4).

  Développé d'abord en `SelfImpactLedger_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase10_2026-10-02/plan_phase10.md` ; analyse :
  `cache/analyse_phase10_garde_repartie_2026-10-02.md` §6.
-/

import ThesePlanetaire.MinorityWitness
import ThesePlanetaire.TokenizedCommons
import ThesePlanetaire.TransferCircuit

/-!
# Impact propre et grand livre par détenteur

La mise à jour η = 1 (`MinorityWitness.step G true`) retire de l'agrégat la contribution propre
de l'agent : elle exige deux données, le total `tot` et l'enregistrement propre `rec i`.

1. ★ `eta1_from_records` : `stepRec` (total et enregistrements) est la mise à jour η = 1 dès que
   les enregistrements sont les contributions propres ; sous η = 0, l'agrégat suffit
   (`eta0_from_aggregate`).
2. ★ `eta1_from_ledger` : le grand livre tokenisé (`TokenizedCommons`, attribution
   consommateur, une lettre par agent) fournit exactement ces données : `rec = holderCum`,
   `tot = cum` (`sum_holderCum`).
3. ★ `eta1_not_from_aggregate` (contenu) : **aucune** fonction de l'agrégat, des écarts de
   charge et des scores ne calcule η = 1 ; deux jeux de même fréquentation et mêmes incréments
   η = 0 ont des incréments η = 1 différents. La garde centrale, qui ne lit que `L`, ne peut pas
   fournir l'impact propre ; les comptes par détenteur le peuvent.
4. ★ `netPos_of_not_receiver`, `finals_netPos_sum` : sur le circuit de transfert, la position
   nette d'un final est ce qu'il paie en droits (son impact propre incorporé) ; sans droit
   échoué chez les autres, ces positions somment à la charge couverte.
-/

namespace SelfImpactLedger

open MinorityWitness (MG choice attendance step)
open TokenizedCommons (Attribution holder holderCum cum sum_holderCum)
open PlanetaryLedger (Footprint)
open TransferCircuit (Circ netPos cumE sum_netPos)

variable {N P : ℕ}

/-- Mise à jour à partir d'enregistrements : total `tot`, contribution propre `rec i`. -/
def stepRec (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) (tot : ℤ) (rec : Fin N → ℤ) :
    Fin N → ℤ :=
  fun i => D i - (G.a i true μ - G.a i false μ) * (tot - rec i)

/-- ★ Avec les contributions propres et leur total, `stepRec` est la mise à jour η = 1. -/
theorem eta1_from_records (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) {rec : Fin N → ℤ}
    (hrec : ∀ i, rec i = G.a i (choice D i) μ) {tot : ℤ} (htot : tot = ∑ i, rec i) :
    stepRec G μ D tot rec = step G true μ D := by
  funext i
  simp only [stepRec, step, attendance, htot, hrec, if_true]

/-- Sous η = 0, l'agrégat suffit (enregistrements nuls). -/
theorem eta0_from_aggregate (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) :
    step G false μ D = stepRec G μ D (attendance G D μ) 0 := by
  funext i
  simp [step, stepRec]

/-! ### Le grand livre par détenteur fournit η = 1 -/

/-- ★ Si le compte de chaque détenteur enregistre sa contribution propre, le grand livre
fournit la mise à jour η = 1 : total = `cum`, enregistrement = `holderCum`. -/
theorem eta1_from_holderCum {B : Type*} (G : MG N P) (μ : Fin P) (D : Fin N → ℤ)
    (att : Attribution) (fp : Footprint (Fin N) B) (w : List (Fin N × Fin N)) (c : B)
    (h : ∀ i, holderCum att fp w i c = G.a i (choice D i) μ) :
    stepRec G μ D (cum fp w c) (fun i => holderCum att fp w i c) = step G true μ D :=
  eta1_from_records G μ D h (sum_holderCum att fp c w).symm

/-- Le grand livre d'une période : chaque agent `i` paie son fournisseur `s i` ; le paiement
porte la charge de la stratégie jouée. -/
def periodFp (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) (s : Fin N → Fin N) :
    Footprint (Fin N) Unit :=
  ⟨fun e _ => if s e.1 = e.2 then G.a e.1 (choice D e.1) μ else 0, {()}⟩

/-- Les paiements de la période, un par agent. -/
def periodWord (s : Fin N → Fin N) : List (Fin N × Fin N) := List.ofFn fun i => (i, s i)

theorem holderCum_period (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) (s : Fin N → Fin N)
    (i : Fin N) :
    holderCum .consumer (periodFp G μ D s) (periodWord s) i () = G.a i (choice D i) μ := by
  simp only [holderCum, periodWord, List.map_ofFn, List.sum_ofFn, Function.comp_def, holder,
    periodFp, if_true]
  rw [Finset.sum_ite_eq]
  simp

/-- ★ **Le grand livre par détenteur fournit η = 1** (attribution consommateur, une lettre par
agent). -/
theorem eta1_from_ledger (G : MG N P) (μ : Fin P) (D : Fin N → ℤ) (s : Fin N → Fin N) :
    stepRec G μ D (cum (periodFp G μ D s) (periodWord s) ())
        (fun i => holderCum .consumer (periodFp G μ D s) (periodWord s) i ()) =
      step G true μ D :=
  eta1_from_holderCum G μ D _ _ _ _ (holderCum_period G μ D s)

/-! ### L'agrégat ne suffit pas -/

/-- Deux jeux à deux agents : `gA` (charges `1 / 0`) et `gB` (agent 0 : `2 / 1`, agent 1 :
`0 / −1`). Mêmes écarts de charge, même fréquentation sur `D = (1, 1)`. -/
def gA : MG 2 1 := ⟨fun _ s _ => if s then 1 else 0⟩

def gB : MG 2 1 := ⟨fun i s _ => if i = 0 then (if s then 2 else 1) else (if s then 0 else -1)⟩

def dAB : Fin 2 → ℤ := ![1, 1]

theorem gAB_same_observables :
    attendance gA dAB 0 = attendance gB dAB 0 ∧
      (fun i => gA.a i true 0 - gA.a i false 0) = (fun i => gB.a i true 0 - gB.a i false 0) ∧
        step gA false 0 dAB = step gB false 0 dAB ∧ step gA true 0 dAB ≠ step gB true 0 dAB := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ★ **L'impact propre ne se lit pas dans l'agrégat** : aucune fonction de la fréquentation,
des écarts de charge et des scores ne donne la mise à jour η = 1 ; la mise à jour η = 0, si. -/
theorem eta1_not_from_aggregate :
    (¬ ∃ f : ℤ → (Fin 2 → ℤ) → (Fin 2 → ℤ) → (Fin 2 → ℤ),
        ∀ (G : MG 2 1) (D : Fin 2 → ℤ),
          step G true 0 D = f (attendance G D 0) (fun i => G.a i true 0 - G.a i false 0) D) ∧
      ∃ f : ℤ → (Fin 2 → ℤ) → (Fin 2 → ℤ) → (Fin 2 → ℤ),
        ∀ (G : MG 2 1) (D : Fin 2 → ℤ),
          step G false 0 D = f (attendance G D 0) (fun i => G.a i true 0 - G.a i false 0) D := by
  refine ⟨?_, ⟨fun A δ D i => D i - δ i * A, fun G D => by funext i; simp [step]⟩⟩
  rintro ⟨f, hf⟩
  obtain ⟨hA, hδ, -, hne⟩ := gAB_same_observables
  exact hne (by rw [hf gA dAB, hf gB dAB, hA, hδ])

/-! ### Sur le circuit de transfert : l'impact propre d'un final est ce qu'il paie -/

section Circuit

variable {V α : Type*} [DecidableEq V]

/-- ★ Un détenteur qui ne reçoit jamais (un final) a pour position nette les droits qu'il
paie. -/
theorem netPos_of_not_receiver (C : Circ V α) {v : V} :
    ∀ w : List α, (∀ a ∈ w, (C.pay a).2 ≠ v) →
      netPos C w v = ((w.map fun a => if (C.pay a).1 = v then C.req a else 0).sum : ℕ)
  | [], _ => by simp [netPos]
  | a :: w, h => by
    have ih := netPos_of_not_receiver C w fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha := h a List.mem_cons_self
    simp only [netPos, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, if_neg ha, if_neg ha]
    push_cast
    ring

/-- ★ Sans position nette hors des finals (intermédiaires équilibrés, émetteurs qui brûlent ce
qu'ils reçoivent), les positions nettes des finals somment à la charge couverte. -/
theorem finals_netPos_sum [Fintype V] (C : Circ V α) (w : List α) (finals : Finset V)
    (h : ∀ v ∉ finals, netPos C w v = 0) :
    ∑ v ∈ finals, netPos C w v = cumE C w := by
  rw [← sum_netPos]
  exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv => h v hv

end Circuit

end SelfImpactLedger
