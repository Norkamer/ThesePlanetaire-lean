/-
  ThesePlanetaire/FeedbackPlanetary.lean
  Phase 4 (2026-10-01) : classes de rétroaction du grand livre planétaire — sur l'historique
  des transactions, non sur l'ordre des effets macro.

  Développé d'abord en `FeedbackPlanetary_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 4, étape 1c) ; analyse :
  `cache/analyse_classes_parikh_2026-10-01.md`.

  Le WFA lit l'historique des transactions individuelles (`planetStep` sur `V × V`), pas la
  suite de leurs effets macro (`Footprint.emit`). [LEAN]
  1. ★ `macro_order_insufficient` : deux historiques de même suite d'effets macro, dans le
     même ordre, aboutissent à des admissions différentes (`ClimateCommons`) ; aucune fonction
     de la suite macro ne calcule les admissions ;
  2. ★ `granularity_witness` : sans garde, l'environnement est P sur les transactions (le
     stock final factorise par Parikh) mais ne factorise pas par la charge macro totale : deux
     bassins d'une même frontière ;
  3. ★ `planet_feedback_class` : le grand livre planétaire (sans horloge) n'est jamais D pour
     son indépendance statique `I_planet` ; sa composante environnementale (montants nuls) est
     P sans frontière gardée et T dès qu'une frontière gardée a deux émetteurs distincts —
     exactement `FeedbackClass.profileClass false _ .free` et `_ .gated`. Une frontière non
     gardée n'entre jamais dans l'indépendance (`I_planet_congr`).
-/

import ThesePlanetaire.PlanetaryLedger
import ThesePlanetaire.FeedbackClass

namespace FeedbackPlanetary

open PlanetaryLedger
open FeedbackClass
open LedgerCirculation (pay pay_comm)
open DualDAG (FuturePool)
open GatedStep (gatedStep_comm)
open PlanetaryBoundaries (PlanetaryBoundary)

variable {V : Type*} [Fintype V] [DecidableEq V] {B : Type*}

/-! ### 1. Jamais D ; les frontières non gardées hors de l'indépendance -/

omit [Fintype V] in
/-- Le grand livre planétaire n'est jamais D pour `I_planet`, quels que soient les montants. -/
theorem planet_not_D (demands : V × V → ℤ) (fp : Footprint V B) :
    ¬ SemClass (planetStep demands fp) (I_planet fp) .D :=
  fun h => h (planetStep_comm demands fp)

omit [Fintype V] [DecidableEq V] in
/-- Une frontière non gardée n'entre jamais dans l'indépendance : deux empreintes qui
    coïncident sur les frontières gardées ont la même `I_planet`. -/
theorem I_planet_congr {fp fp' : Footprint V B} (hg : fp'.gated = fp.gated)
    (he : ∀ e, ∀ c ∈ fp.gated, fp'.emit e c = fp.emit e c) (a b : V × V) :
    I_planet fp' a b ↔ I_planet fp a b := by
  unfold I_planet
  rw [gsupp_congr hg he a, gsupp_congr hg he b]

/-! ### 2. Composante environnementale (montants nuls) : P ou T -/

omit [Fintype V] in
lemma pay_zero (e : V × V) (bal : V → ℤ) : pay 0 e bal = bal := by
  funext v
  simp [pay]

omit [Fintype V] in
/-- Montants nuls : deux paiements d'empreintes gardées disjointes commutent, même hors
    `I_loc` (seuls les stocks gardés sont lus). -/
theorem planetStep_zero_commutes {fp : Footprint V B} {a b : V × V}
    (h : Disjoint (gsupp fp a) (gsupp fp b)) (st : PState V B) :
    CommutesAt (planetStep 0 fp) st a b := by
  refine gatedStep_comm
    (PState.ext (pay_comm 0 b a st.bal) (by funext c; simp only [planetUpd, deplete]; ring)
      (Multiset.cons_swap b a st.adm)) ?_ ?_
  · unfold planetAdmissible
    simp only [planetUpd, pay_zero]
    exact and_congr Iff.rfl (stockAdmissible_deplete_other fp st.stock a b h)
  · unfold planetAdmissible
    simp only [planetUpd, pay_zero]
    exact and_congr Iff.rfl (stockAdmissible_deplete_other fp st.stock b a h.symm)

omit [Fintype V] in
/-- Sans co-émission gardée, l'environnement est en écriture seule : classe P. -/
theorem planet_env_P {fp : Footprint V B}
    (h : ∀ a b : V × V, a ≠ b → Disjoint (gsupp fp a) (gsupp fp b)) :
    SemClass (planetStep 0 fp) (I_planet fp) .P := by
  intro st a b
  by_cases hab : a = b
  · subst hab
    rfl
  · exact planetStep_zero_commutes (h a b hab) st

omit [Fintype V] in
/-- Deux émetteurs distincts d'une frontière gardée : classe T (losange `I_planet`, mais le
    premier servi épuise le commun). -/
theorem planet_env_T {fp : Footprint V B} (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c)
    {a b : V × V} (hab : a ≠ b) (hd : ¬ Disjoint (gsupp fp a) (gsupp fp b)) :
    SemClass (planetStep 0 fp) (I_planet fp) .T := by
  refine ⟨planetStep_comm 0 fp, fun hc => ?_⟩
  obtain ⟨c, hca, hcb⟩ := Finset.not_disjoint_iff.mp hd
  have hca' := Finset.mem_filter.mp hca
  have hcb' := Finset.mem_filter.mp hcb
  have hea : 0 < fp.emit a c := lt_of_le_of_ne (h_emit a c hca'.1) (Ne.symm hca'.2)
  have heb : 0 < fp.emit b c := lt_of_le_of_ne (h_emit b c hcb'.1) (Ne.symm hcb'.2)
  let st0 : PState V B := ⟨0, fun c => max (fp.emit a c) (fp.emit b c), 0⟩
  have first : ∀ x y : V × V, (x = a ∧ y = b) ∨ (x = b ∧ y = a) →
      (planetStep 0 fp (planetStep 0 fp st0 x) y).adm = {x} := by
    intro x y hxy
    have hx : planetAdmissible 0 fp st0 x := by
      refine ⟨(ledgerAdmissible_zero _ x).mpr (le_refl 0), fun c' _ => ?_⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hy : ¬ planetAdmissible 0 fp (planetUpd 0 fp st0 x) y := by
      rintro ⟨-, hS⟩
      have hyc : c ∈ gsupp fp y := by rcases hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
      have := hS c hyc
      simp only [planetUpd, deplete, st0] at this
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases le_total (fp.emit x c) (fp.emit y c) with hle | hle <;>
        simp only [max_eq_left, max_eq_right, hle] at this <;> linarith
    rw [planetStep_of_adm hx, planetStep_of_not_adm hy]
    rfl
  have H := congrArg PState.adm (hc st0 a b)
  rw [first a b (Or.inl ⟨rfl, rfl⟩), first b a (Or.inr ⟨rfl, rfl⟩)] at H
  exact hab (Multiset.singleton_inj.mp H)

omit [Fintype V] in
/-- ★ Classe de rétroaction du grand livre planétaire (sans horloge) :
    1. jamais D pour `I_planet`, quels que soient les montants ;
    2. sans frontière gardée, l'environnement est P = `profileClass false mem .free` ;
    3. une frontière gardée à deux émetteurs distincts rend l'environnement T =
       `profileClass false mem .gated`.
    La classe est celle du système GOUVERNÉ, non une étiquette de la frontière. -/
theorem planet_feedback_class (fp : Footprint V B)
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) (mem : Memory) :
    (∀ demands : V × V → ℤ, ¬ SemClass (planetStep demands fp) (I_planet fp) .D) ∧
    (fp.gated = ∅ →
      SemClass (planetStep 0 fp) (I_planet fp) (profileClass false mem .free)) ∧
    (∀ c ∈ fp.gated, ∀ a b : V × V, a ≠ b → fp.emit a c ≠ 0 → fp.emit b c ≠ 0 →
      SemClass (planetStep 0 fp) (I_planet fp) (profileClass false mem .gated)) := by
  refine ⟨fun demands => planet_not_D demands fp, fun h0 => ?_, fun c hc a b hab ha hb => ?_⟩
  · have hP : profileClass false mem .free = .P := by cases mem <;> rfl
    rw [hP]
    refine planet_env_P fun a b _ => ?_
    simp [gsupp, h0]
  · have hT : profileClass false mem .gated = .T := by cases mem <;> rfl
    rw [hT]
    refine planet_env_T h_emit hab (Finset.not_disjoint_iff.mpr ⟨c, ?_, ?_⟩)
    · exact Finset.mem_filter.mpr ⟨hc, ha⟩
    · exact Finset.mem_filter.mpr ⟨hc, hb⟩

/-! ### 3. La suite des effets macro ne suffit pas -/

open ClimateCommons in
/-- ★ Le WFA lit l'historique des transactions, non l'ordre des effets macro : `[a, b]` et
    `[b, a]` ont la MÊME suite d'effets macro (une unité de CO₂, puis une unité de CO₂) et le
    même stock final, mais pas les mêmes admissions — le rang dans la file attribue le budget.
    Aucune fonction de la suite macro, même ordonnée, ne calcule les admissions. -/
theorem macro_order_insufficient :
    [a, b].map fp.emit = [b, a].map fp.emit ∧
    (planetFold pool demands fp S₀ [a, b]).stock = (planetFold pool demands fp S₀ [b, a]).stock ∧
    (planetFold pool demands fp S₀ [a, b]).adm ≠ (planetFold pool demands fp S₀ [b, a]).adm ∧
    ¬ ∃ F : List (PlanetaryBoundary → ℤ) → Multiset (Fin 3 × Fin 3),
        ∀ w, (planetFold pool demands fp S₀ w).adm = F (w.map fp.emit) := by
  have hmap : [a, b].map fp.emit = [b, a].map fp.emit := rfl
  have hadm : (planetFold pool demands fp S₀ [a, b]).adm ≠
      (planetFold pool demands fp S₀ [b, a]).adm := by
    rw [climate_commons.2.2.2.2.1, climate_commons.2.2.2.2.2]
    decide
  refine ⟨hmap, by decide, hadm, fun ⟨F, hF⟩ => hadm ?_⟩
  rw [hF, hF, hmap]

/-! ### 4. Granularité : Parikh sur les transactions, pas sur le total macro -/

namespace Basins

/-- Avoirs nuls (montants nuls : seuls les stocks comptent). -/
def pool : FuturePool (Fin 3) := ⟨fun _ => 0, by decide⟩

/-- Bassin d'un prélèvement : la source 2 puise dans le bassin 1, les autres dans le bassin 0. -/
def basin (e : Fin 3 × Fin 3) : Fin 2 := if e.1 = 2 then 1 else 0

/-- Eau douce en deux bassins non gardés ; chaque prélèvement retire une unité de son bassin. -/
def fp : Footprint (Fin 3) (Fin 2) := ⟨fun e c => if c = basin e then 1 else 0, ∅⟩

/-- Chaque bassin supporte un prélèvement. -/
def S₀ : Fin 2 → ℤ := fun _ => 1

def a : Fin 3 × Fin 3 := (0, 1)
def a' : Fin 3 × Fin 3 := (1, 0)
def b : Fin 3 × Fin 3 := (2, 0)

/-- Charge macro : total des émissions sur la frontière, bassins confondus. -/
def macroLoad (w : List (Fin 3 × Fin 3)) : ℤ := (w.map (fun e => ∑ c, fp.emit e c)).sum

end Basins

open Basins in
/-- ★ Granularité : sans garde, l'environnement est P sur les transactions (le stock final
    factorise par Parikh), mais pas sur la charge macro : `[a, a']` et `[a, b]` ont la même
    charge totale, l'un épuise un bassin, l'autre non. -/
theorem granularity_witness :
    SemClass (planetStep 0 fp) (I_planet fp) .P ∧
    (∀ w₁ w₂ : List (Fin 3 × Fin 3), w₁.Perm w₂ →
      (planetFold pool 0 fp S₀ w₁).stock = (planetFold pool 0 fp S₀ w₂).stock) ∧
    macroLoad [a, a'] = macroLoad [a, b] ∧
    (planetFold pool 0 fp S₀ [a, a']).stock 0 < 0 ∧
    (∀ c, 0 ≤ (planetFold pool 0 fp S₀ [a, b]).stock c) ∧
    ¬ ∃ F : ℤ → (Fin 2 → ℤ), ∀ w, (planetFold pool 0 fp S₀ w).stock = F (macroLoad w) := by
  have hP : SemClass (planetStep 0 fp) (I_planet fp) .P :=
    planet_env_P fun _ _ _ => by simp [gsupp, fp]
  have h1 : (planetFold pool 0 fp S₀ [a, a']).stock 0 < 0 := by decide
  have h2 : ∀ c, 0 ≤ (planetFold pool 0 fp S₀ [a, b]).stock c := by decide
  have hm : macroLoad [a, a'] = macroLoad [a, b] := by decide
  refine ⟨hP, fun w₁ w₂ hp => semClass_P_readout hP PState.stock hp _, hm, h1, h2,
    fun ⟨F, hF⟩ => ?_⟩
  have := h2 0
  rw [hF, ← hm, ← hF] at this
  exact absurd h1 (not_lt.mpr this)

end FeedbackPlanetary
