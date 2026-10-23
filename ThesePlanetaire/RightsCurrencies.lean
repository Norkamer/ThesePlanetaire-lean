/-
  ThesePlanetaire/RightsCurrencies.lean
  Phase 5c (2026-10-02) : M(1,2) sur le grand livre — deux droits, rectangle contre polytope ;
  droits déposables ou périssables ; l'enchère comme dotation.

  Développé d'abord en `RightsCurrencies_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 5, étape 5c, « Lecture critique du plan »
  et « Amendement à l'exécution ») ; analyse : `cache/analyse_marche_communs_2026-10-02.md`.

  1. [biens × exécution] Ombre dynamique de T-M12-2 (« rectangle optimal ⟺ dommages
     séparables », corpus M(1,2)). Deux droits, burns `(i, x)` ; indépendance par droit
     `I_right` (droits distincts). ★ `rect_diamond` : plafonds séparés (rectangle) ⇒ losange,
     deux marchés indépendants ; ★ `polytope_commutesAt_iff` : sous plafond couplé
     `e₁ + e₂ ≤ C` (dommages interactifs), deux burns sur des droits distincts commutent ⟺ la
     marge commune ne les sépare pas — l'indépendance DÉPEND DE L'ÉTAT (instance minimale du
     trou Case 2 du plan v3.2) ; ★ `polytope_not_diamond` ; ★ `rectangle_commutes_polytope_D`
     (rectangle : T ; polytope : D, relativement à `I_right`) ; ★ `no_rectangle_eq_triangle`
     (des droits à totaux fixes n'atteignent que des rectangles). L'optimalité du polytope sous
     dommages interactifs reste [ANALYSE] ;
  2. [temps × exécution] Le canal intertemporel (Hotelling, `RightsIntertemporal`) n'est pas
     lu par la classe P/T/D de la Phase 4 mais par l'EFFACEMENT au top (`PeriodCuts`) :
     ★ `periodCuts_iff` (le top efface la charge passée ⟺ `flow`, ou `regen` avec émission
     ≥ plafond de dépôt), ★ `perishable_forgets`, ★ `history_matters_iff`, ★
     `class_vs_memory` (`stock` : P et mémoire ; `regen` : T et mémoire ; `flow` : T et
     oubli). Le plan posait « déposable ⇒ P au top » : faux dès qu'il y a émission
     périodique ;
  3. [allocation primaire × exécution] L'enchère à `k` unités (`RightsAuction`) comme dotation
     de T-M12-1 (`TokenizedCommons`) : ★ `auction_cap` (émissions gardées ≤ k pour tout
     historique), ★ `auction_endowment` (gagnants à sources distinctes, émissions ≤ 1 :
     règlement tokenisé intégral dès que la partie monétaire se règle), ★
     `auction_endowment_perm` (dans tout ordre). Avec des offres véridiques, les gagnants sont
     les `k` plus hautes valeurs (`RightsAuction.kUnit_top_k`).
-/

import Mathlib.Tactic
import ThesePlanetaire.FeedbackClass
import ThesePlanetaire.TokenizedCommons
import ThesePlanetaire.RightsAuction

namespace RightsCurrencies

open GatedStep (Diamond)
open CommutativeClassification (IsCommutativeUpdate)
open FeedbackClass (FClass CommutesAt SemClass Memory Governance tickOp canonStep profileClass)

/-! ### 1. M(1,2) : rectangle contre polytope -/

/-- Burn de `x` unités du droit `i`. -/
abbrev Burn := Fin 2 × ℕ

/-- Charges cumulées des deux droits. -/
abbrev Load := Fin 2 → ℕ

/-- Ajout de la charge d'un burn sur la coordonnée de son droit. -/
def addLoad (L : Load) (a : Burn) : Load := fun j => if j = a.1 then L j + a.2 else L j

/-- Porte rectangle (dommages séparables) : un plafond par droit. -/
def rectStep (Bcap : Fin 2 → ℕ) (L : Load) (a : Burn) : Load :=
  if L a.1 + a.2 ≤ Bcap a.1 then addLoad L a else L

/-- Porte polytope (dommages interactifs) : un plafond couplé sur la charge totale. -/
def polyStep (C : ℕ) (L : Load) (a : Burn) : Load :=
  if L 0 + L 1 + a.2 ≤ C then addLoad L a else L

/-- Indépendance par droit : deux burns sur des droits distincts. -/
def I_right (a b : Burn) : Prop := a.1 ≠ b.1

lemma addLoad_comm (L : Load) (a b : Burn) :
    addLoad (addLoad L a) b = addLoad (addLoad L b) a := by
  funext j; simp only [addLoad]; split_ifs <;> omega

/-- ★ Porte rectangle : losange pour l'indépendance par droit (deux marchés indépendants). -/
theorem rect_diamond (Bcap : Fin 2 → ℕ) : Diamond (rectStep Bcap) I_right := by
  intro L a b hab
  have hab : a.1 ≠ b.1 := hab
  have hba : b.1 ≠ a.1 := Ne.symm hab
  have hLa : addLoad L b a.1 = L a.1 := by simp [addLoad, hab]
  have hLb : addLoad L a b.1 = L b.1 := by simp [addLoad, hba]
  have hcomm := addLoad_comm L a b
  unfold rectStep
  by_cases ha : L a.1 + a.2 ≤ Bcap a.1 <;> by_cases hb : L b.1 + b.2 ≤ Bcap b.1 <;>
    simp [ha, hb, hLa, hLb, hcomm]

lemma sum_addLoad (L : Load) (a : Burn) : addLoad L a 0 + addLoad L a 1 = L 0 + L 1 + a.2 := by
  rcases a with ⟨i, x⟩; fin_cases i <;> simp [addLoad] <;> omega

lemma polyStep_pos {C : ℕ} {L : Load} {a : Burn} (h : L 0 + L 1 + a.2 ≤ C) :
    polyStep C L a = addLoad L a := if_pos h

lemma polyStep_neg {C : ℕ} {L : Load} {a : Burn} (h : ¬ L 0 + L 1 + a.2 ≤ C) :
    polyStep C L a = L := if_neg h

theorem polytope_commutesAt_iff (C : ℕ) (L : Load) {a b : Burn} (hab : a.1 ≠ b.1) :
    CommutesAt (polyStep C) L a b ↔
      ¬ (L 0 + L 1 + a.2 ≤ C ∧ L 0 + L 1 + b.2 ≤ C ∧ C < L 0 + L 1 + a.2 + b.2) := by
  have sa := sum_addLoad L a
  have sb := sum_addLoad L b
  unfold CommutesAt
  by_cases ha : L 0 + L 1 + a.2 ≤ C <;> by_cases hb : L 0 + L 1 + b.2 ≤ C
  · rw [polyStep_pos ha, polyStep_pos hb]
    by_cases h2 : L 0 + L 1 + a.2 + b.2 ≤ C
    · rw [polyStep_pos (L := addLoad L a) (a := b) (by omega),
        polyStep_pos (L := addLoad L b) (a := a) (by omega), addLoad_comm L a b]
      simp only [true_iff]; rintro ⟨-, -, h3⟩; omega
    · rw [polyStep_neg (L := addLoad L a) (a := b) (by omega),
        polyStep_neg (L := addLoad L b) (a := a) (by omega)]
      have hne : addLoad L a ≠ addLoad L b := by
        intro h; have := congrFun h a.1; simp [addLoad, hab] at this; omega
      simp only [hne, false_iff, not_not]; exact ⟨ha, hb, by omega⟩
  · rw [polyStep_pos ha, polyStep_neg hb, polyStep_neg (L := addLoad L a) (a := b) (by omega),
      polyStep_pos ha]
    simp only [true_iff]; rintro ⟨-, h2, -⟩; omega
  · rw [polyStep_neg ha, polyStep_pos hb, polyStep_neg (L := addLoad L b) (a := a) (by omega)]
    simp only [true_iff]; rintro ⟨h1, -, -⟩; omega
  · rw [polyStep_neg ha, polyStep_neg hb, polyStep_neg ha]
    simp only [true_iff]; rintro ⟨h1, -, -⟩; omega

/-- ★ Porte polytope : pas de losange pour l'indépendance par droit (dès que `C ≥ 1`). -/
theorem polytope_not_diamond {C : ℕ} (hC : 1 ≤ C) : ¬ Diamond (polyStep C) I_right := by
  intro hD
  have h := (polytope_commutesAt_iff C 0 (a := (0, C)) (b := (1, C)) (by simp)).mp
    (hD 0 (0, C) (1, C) (by simp [I_right]))
  exact h ⟨by simp, by simp, by simp; omega⟩

/-- Porte rectangle, non commutative sur un même droit (dès que `Bcap 0 ≥ 2`). -/
theorem rect_not_commutative {Bcap : Fin 2 → ℕ} (h : 2 ≤ Bcap 0) :
    ¬ IsCommutativeUpdate (rectStep Bcap) := by
  intro hc
  have h1 : rectStep Bcap 0 (0, Bcap 0) = addLoad 0 (0, Bcap 0) := if_pos (by simp)
  have h2 : rectStep Bcap (addLoad 0 (0, Bcap 0)) (0, 1) = addLoad 0 (0, Bcap 0) :=
    if_neg (by simp [addLoad])
  have h3 : rectStep Bcap 0 (0, 1) = addLoad 0 (0, 1) := if_pos (by simp; omega)
  have h4 : rectStep Bcap (addLoad 0 (0, 1)) (0, Bcap 0) = addLoad 0 (0, 1) :=
    if_neg (by simp [addLoad])
  have := congrFun (hc 0 (0, Bcap 0) (0, 1)) 0
  rw [h1, h2, h3, h4] at this
  simp [addLoad] at this; omega

/-- ★ M(1,2), ombre dynamique de T-M12-2 : le rectangle (plafonds séparés) est T relativement
    à l'indépendance par droit ; le polytope (plafond couplé) est D. -/
theorem rectangle_commutes_polytope_D {Bcap : Fin 2 → ℕ} (hB : 2 ≤ Bcap 0) {C : ℕ}
    (hC : 1 ≤ C) :
    SemClass (rectStep Bcap) I_right .T ∧ SemClass (polyStep C) I_right .D :=
  ⟨⟨rect_diamond Bcap, rect_not_commutative hB⟩, polytope_not_diamond hC⟩

/-- ★ Les droits tokenisés à totaux fixes n'atteignent que des rectangles : aucun rectangle
    `[0,B₁] × [0,B₂]` ne coïncide avec le triangle `e₁ + e₂ ≤ C` (dès que `C ≥ 1`). -/
theorem no_rectangle_eq_triangle {C : ℕ} (hC : 1 ≤ C) (B₁ B₂ : ℕ) :
    ∃ e₁ e₂ : ℕ, ¬ ((e₁ ≤ B₁ ∧ e₂ ≤ B₂) ↔ e₁ + e₂ ≤ C) := by
  by_cases h₁ : B₁ < C
  · exact ⟨C, 0, by omega⟩
  by_cases h₂ : B₂ < C
  · exact ⟨0, C, by omega⟩
  exact ⟨B₁, B₂, by omega⟩

/-! ### 2. Droits déposables ou périssables : le top efface-t-il le passé ? -/

/-- Le top de période efface la charge passée (sur les charges admissibles `≤ cap`). -/
def PeriodCuts (mem : Memory) (cap r : ℕ) : Prop :=
  ∀ L L', L ≤ cap → L' ≤ cap → tickOp mem r L = tickOp mem r L'

/-- ★ Le top coupe le passé ⟺ droits périssables, ou émission périodique couvrant tout le
    plafond de dépôt. -/
theorem periodCuts_iff (mem : Memory) {cap r : ℕ} (hcap : 0 < cap) :
    PeriodCuts mem cap r ↔ mem = .flow ∨ (mem = .regen ∧ cap ≤ r) := by
  cases mem
  · simp only [PeriodCuts, tickOp, reduceCtorEq, false_and, or_self, iff_false]
    intro h; have := h 0 cap (Nat.zero_le _) le_rfl; omega
  · simp only [PeriodCuts, tickOp, reduceCtorEq, true_and, false_or]
    constructor
    · intro h; have := h 0 cap (Nat.zero_le _) le_rfl; omega
    · intro h L L' hL hL'; omega
  · simp [PeriodCuts, tickOp]

/-- ★ Droits périssables : après un top, l'histoire passée est oubliée. -/
theorem perishable_forgets {α : Type*} (gov : Governance) (e : α → ℕ) (cap r : ℕ)
    (u w : List (Option α)) (L₀ L₀' : ℕ) :
    (u ++ none :: w).foldl (canonStep true .flow gov e cap r) L₀ =
      (none :: w).foldl (canonStep true .flow gov e cap r) L₀' := by
  rw [List.foldl_append]
  simp only [List.foldl_cons, canonStep, tickOp, if_true]

/-- ★ Témoin d'histoire : une émission qui épuise le plafond, suivie d'un top, laisse une trace
    ⟺ le top ne coupe pas le passé. -/
theorem history_matters_iff {α : Type*} (mem : Memory) (gov : Governance) (e : α → ℕ)
    {cap r : ℕ} (hcap : 0 < cap) {a : α} (ha : e a = cap) :
    [some a, none].foldl (canonStep true mem gov e cap r) 0 ≠
        [none].foldl (canonStep true mem gov e cap r) 0 ↔ ¬ PeriodCuts mem cap r := by
  rw [periodCuts_iff mem hcap]
  cases mem <;> cases gov <;>
    simp only [List.foldl_cons, List.foldl_nil, canonStep, tickOp, FeedbackClass.emitOp, ha,
      if_true, zero_add, le_rfl, ne_eq, reduceCtorEq, false_and, or_self, not_false_eq_true,
      true_and, false_or, true_or, not_true_eq_false]
  all_goals constructor <;> intro h <;> first | trivial | omega

/-- ★ La classe de commutation ne détermine pas le canal intertemporel : `stock` est P et
    garde la mémoire ; `regen` (avec `r < cap`) est T et garde la mémoire ; `flow` est T et
    l'efface. -/
theorem class_vs_memory {cap r : ℕ} (hr : r < cap) :
    (profileClass true .stock .free = .P ∧ ¬ PeriodCuts .stock cap r) ∧
    (profileClass true .regen .free = .T ∧ ¬ PeriodCuts .regen cap r) ∧
    (profileClass true .flow .free = .T ∧ PeriodCuts .flow cap r) := by
  have hcap : 0 < cap := by omega
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩
  · rw [periodCuts_iff _ hcap]; simp
  · rw [periodCuts_iff _ hcap]; simp; omega
  · rw [periodCuts_iff _ hcap]; simp

/-! ### 3. L'enchère comme dotation : allocation primaire, puis règlement dans tout ordre -/

section Auction

open RightsAuction (winners kUnit_feasible)
open TokenizedCommons (Attribution RState tkFoldFrom tksettles msettles holderCum tk_cap
  tksettles_iff_holderCum)
open PlanetaryLedger (Footprint)

variable {V : Type*} [Fintype V] [LinearOrder V] {B : Type*}

/-- Dotation issue de l'enchère à `k` unités : un droit, sur chaque frontière, à chaque gagnant. -/
def auctionEndowment (k : ℕ) (b : V → ℕ) : V → B → ℤ :=
  fun v _ => if v ∈ winners k b then 1 else 0

omit [Fintype V] [LinearOrder V] in
/-- Sur un historique à sources distinctes et émissions ≤ 1, la charge attribuée à `v` est au
    plus `1`, et nulle si `v` n'est pas une source. -/
lemma src_sum_le [DecidableEq V] (f : V × V → ℤ) (v : V) :
    ∀ w : List (V × V), (w.map Prod.fst).Nodup → (∀ e ∈ w, f e ≤ 1) →
      (w.map fun e => if v = e.1 then f e else 0).sum ≤ if v ∈ w.map Prod.fst then 1 else 0
  | [], _, _ => by simp
  | e :: w, hnd, hf => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := src_sum_le f v w hnd.2 (fun x hx => hf x (List.mem_cons_of_mem e hx))
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    by_cases hv : v = e.1
    · subst hv
      rw [if_neg hnd.1] at ih
      rw [if_pos rfl, if_pos (Or.inl rfl)]
      linarith [hf e List.mem_cons_self]
    · rw [if_neg hv, zero_add]
      have : (v = e.1 ∨ v ∈ w.map Prod.fst) ↔ v ∈ w.map Prod.fst := or_iff_right hv
      rwa [if_congr this rfl rfl]

/-- La dotation de l'enchère distribue au plus `k` droits par frontière. -/
theorem auctionEndowment_total (k : ℕ) (b : V → ℕ) (c : B) :
    ∑ v, auctionEndowment k b v c ≤ k := by
  simp only [auctionEndowment, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact_mod_cast kUnit_feasible k b

/-- ★ Plafond : quel que soit l'historique, les émissions gardées réglées sur la dotation de
    l'enchère ne dépassent pas `k`. -/
theorem auction_cap (k : ℕ) (b : V → ℕ) (att : Attribution) (demands : V × V → ℤ)
    (fp : Footprint V B) (bal : V → ℤ) (w : List (V × V)) {c : B} (hc : c ∈ fp.gated) :
    ((tkFoldFrom att demands fp ⟨bal, auctionEndowment k b, 0⟩ w).adm.map
        fun e => fp.emit e c).sum ≤ k :=
  (tk_cap att demands fp bal _ (fun v _ _ => by unfold auctionEndowment; split_ifs <;> simp) w
    hc).trans (auctionEndowment_total k b c)

/-- ★ L'enchère fournit une dotation pour T-M12-1 : si les gagnants émettent chacun au plus une
    unité par frontière gardée (sources distinctes, toutes gagnantes), le grand livre tokenisé
    (attribution consommateur) règle intégralement leurs paiements dès que la partie monétaire
    se règle. -/
theorem auction_endowment (k : ℕ) (b : V → ℕ) (demands : V × V → ℤ) (fp : Footprint V B)
    (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) (h_unit : ∀ e, ∀ c ∈ fp.gated, fp.emit e c ≤ 1)
    (bal : V → ℤ) (w : List (V × V)) (hnd : (w.map Prod.fst).Nodup)
    (hwin : ∀ e ∈ w, e.1 ∈ winners k b) (hm : msettles demands bal w) :
    tksettles .consumer demands fp ⟨bal, auctionEndowment k b, 0⟩ w := by
  have hρ : ∀ v, ∀ c ∈ fp.gated, (0 : ℤ) ≤ auctionEndowment k b v c := fun v _ _ => by
    unfold auctionEndowment; split_ifs <;> simp
  refine (tksettles_iff_holderCum h_nn w _ hρ).mpr ⟨hm, fun v c hc => ?_⟩
  have h := src_sum_le (fun e => fp.emit e c) v w hnd (fun e _ => h_unit e c hc)
  refine (show holderCum .consumer fp w v c ≤ _ from h).trans ?_
  split_ifs with hv
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    simp [auctionEndowment, hwin e he]
  · exact hρ v c hc

/-- ★ Dans tout ordre : la conclusion vaut pour toute permutation de l'historique dont la partie
    monétaire se règle (les hypothèses sur les sources sont invariantes par permutation). -/
theorem auction_endowment_perm (k : ℕ) (b : V → ℕ) (demands : V × V → ℤ) (fp : Footprint V B)
    (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) (h_unit : ∀ e, ∀ c ∈ fp.gated, fp.emit e c ≤ 1)
    (bal : V → ℤ) {w w' : List (V × V)} (hp : w.Perm w') (hnd : (w.map Prod.fst).Nodup)
    (hwin : ∀ e ∈ w, e.1 ∈ winners k b) (hm : msettles demands bal w') :
    tksettles .consumer demands fp ⟨bal, auctionEndowment k b, 0⟩ w' :=
  auction_endowment k b demands fp h_nn h_unit bal w' ((hp.map Prod.fst).nodup_iff.mp hnd)
    (fun e he => hwin e (hp.mem_iff.mpr he)) hm

end Auction

end RightsCurrencies
