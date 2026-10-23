/-
  ThesePlanetaire/LedgerCirculation.lean
  Phase 2a (2026-10-01) : grand livre multi-tours (circulation) sur M(V × V, I_loc).

  Développé d'abord en `LedgerCirculation_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 2a) ; analyse :
  `cache/analyse_forte_connexite_graphe_transactions_2026-10-01.md` (§7, §11).

  Le pli RTGS de `LocalCommutation` admet dans un `Finset` : une lettre répétée est
  idempotente (`S ∪ {e} = S`), le pli ne modélise qu'UNE ronde de paiements. Ici l'état est un
  grand livre — soldes `V → ℤ` et multi-ensemble des paiements admis — et le mot peut répéter
  ses lettres : la monnaie CIRCULE. Un paiement `e` est admis si le solde de sa source reste
  ≥ 0 après paiement (une boucle s'autofinance, comme dans `rtgsAdmissible`).

  Même argument d'empreinte qu'au palier RTGS : `e` lit et écrit le solde de `e.1` et n'écrit
  (en ajoutant) que le solde de `e.2`. D'où :
  1. ★ `ledger_commutation` : commutation sous `I_loc`, sans garde, sans signe, lettres
     répétées comprises ; descente ★ `ledgerFoldTrace` sur `LocTrace V` ;
  2. ★ `ledger_swap_invariant_iff` : pour deux lettres non-boucles distinctes, l'échange est
     invariant pour TOUS avoirs et montants ssi `I_loc` — `I_loc` est la plus grande
     indépendance statique du grand livre ;
  3. invariants économiques : conservation de la masse monétaire (`ledgerFoldFrom_sum_bal`),
     aucun découvert (`ledgerFold_bal_nonneg`) ;
  4. ★ `ledgerFold_eq_rtgsFold_of_nodup` : sur un mot sans répétition, le grand livre admet
     exactement le pli RTGS, et ses soldes sont avoirs + recettes − charge (sans hypothèse de
     signe). Avec `entry_fold_eq_rtgsFold` : palier 2 = RTGS une-fois = grand livre restreint ;
  5. ★ `Circulation` : sur le 3-cycle, deux tours de 1 unité ; le grand livre admet les six
     paiements et les soldes reviennent aux avoirs (périodicité), le pli une-fois n'en admet
     que trois ;
  6. ★ `ledger_sce_fiber_nondegenerate` : le solde propre d'un agent n'est pas déterminé par sa
     vue locale (témoin `Gridlock`, agent `2`).

  Pont `SolvencyRegularity` (« huit comptable ») : à avoirs fixés et montants ≥ 0, les soldes
  restent dans `[0, M]` (`M` = masse monétaire, par 3) et `adm` est en écriture seule (il
  n'influence aucune transition) ; le grand livre est donc un automate FINI
  (≤ (M+1)^|V| états de soldes), du côté RÉGULIER de la frontière. La non-régularité du huit
  tient à la non-conservation (flux exogènes cumulés sans borne), non au crédit des recettes.
  Formalisation : `AdmissionAutomata`.
-/

import Mathlib.Tactic
import ThesePlanetaire.LocalCommutation
import ThesePlanetaire.TraceObservation
import ThesePlanetaire.GatedStep

namespace LedgerCirculation

open DualDAG (FuturePool vertex_load)
open EchelleCouplages (received)
open LocalCommutation
open TraceObservation (localObs localObs_mk localView touches)
open GatedStep (gatedStep_comm foldl_swap_of_diamond)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Grand livre -/

/-- Paiement de `e` : la source est débitée de `demands e`, la cible créditée. -/
def pay (demands : V × V → ℤ) (e : V × V) (bal : V → ℤ) : V → ℤ :=
  fun v => bal v - (if v = e.1 then demands e else 0) + (if v = e.2 then demands e else 0)

/-- Admission au grand livre : le solde de la source reste ≥ 0 après paiement. -/
def ledgerAdmissible (demands : V × V → ℤ) (bal : V → ℤ) (e : V × V) : Prop :=
  0 ≤ pay demands e bal e.1

instance (demands : V × V → ℤ) (bal : V → ℤ) (e : V × V) :
    Decidable (ledgerAdmissible demands bal e) :=
  inferInstanceAs (Decidable (0 ≤ pay demands e bal e.1))

/-- État du grand livre : soldes et multi-ensemble des paiements admis. -/
@[ext] structure LedgerState (V : Type*) where
  bal : V → ℤ
  adm : Multiset (V × V)

/-- Pas test-and-keep : un paiement admis est réglé et enregistré, sinon rien ne change. -/
def ledgerStep (demands : V × V → ℤ) (st : LedgerState V) (e : V × V) : LedgerState V :=
  if ledgerAdmissible demands st.bal e then ⟨pay demands e st.bal, e ::ₘ st.adm⟩ else st

/-- Pli du grand livre depuis un état quelconque. -/
def ledgerFoldFrom (demands : V × V → ℤ) (st : LedgerState V) (w : List (V × V)) :
    LedgerState V :=
  w.foldl (ledgerStep demands) st

/-- Pli du grand livre depuis les avoirs, aucun paiement admis. -/
def ledgerFold (pool : FuturePool V) (demands : V × V → ℤ) (w : List (V × V)) : LedgerState V :=
  ledgerFoldFrom demands ⟨pool.holdings, 0⟩ w

omit [Fintype V] in
lemma ledgerStep_of_adm {demands : V × V → ℤ} {st : LedgerState V} {e : V × V}
    (h : ledgerAdmissible demands st.bal e) :
    ledgerStep demands st e = ⟨pay demands e st.bal, e ::ₘ st.adm⟩ := if_pos h

omit [Fintype V] in
lemma ledgerStep_of_not_adm {demands : V × V → ℤ} {st : LedgerState V} {e : V × V}
    (h : ¬ ledgerAdmissible demands st.bal e) : ledgerStep demands st e = st := if_neg h

/-! ### 2. Lemmes de `pay` -/

omit [Fintype V] in
lemma pay_apply_other (demands : V × V → ℤ) (e : V × V) (bal : V → ℤ) {v : V}
    (h1 : v ≠ e.1) (h2 : v ≠ e.2) : pay demands e bal v = bal v := by
  simp [pay, h1, h2]

omit [Fintype V] in
/-- Deux paiements commutent toujours sur les soldes (les débits et crédits s'additionnent). -/
lemma pay_comm (demands : V × V → ℤ) (a b : V × V) (bal : V → ℤ) :
    pay demands a (pay demands b bal) = pay demands b (pay demands a bal) := by
  funext v
  simp only [pay]
  ring

/-- Un paiement conserve la masse monétaire. -/
lemma pay_sum (demands : V × V → ℤ) (e : V × V) (bal : V → ℤ) :
    ∑ v, pay demands e bal v = ∑ v, bal v := by
  simp [pay, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-! ### 3. Commutation sous `I_loc` -/

omit [Fintype V] in
/-- Régler `b` ne change pas le test de `a` si `b` ne débite pas `a.1` et ne le crédite pas. -/
lemma ledgerAdmissible_pay_other (demands : V × V → ℤ) (bal : V → ℤ) (a b : V × V)
    (h_src : b.1 ≠ a.1) (h_tgt : b.2 ≠ a.1) :
    ledgerAdmissible demands (pay demands b bal) a ↔ ledgerAdmissible demands bal a := by
  unfold ledgerAdmissible
  rw [pay_comm, pay_apply_other demands b _ (Ne.symm h_src) (Ne.symm h_tgt)]

omit [Fintype V] in
lemma ledgerStep_comm (demands : V × V → ℤ) (st : LedgerState V) (a b : V × V)
    (h : I_loc a b) :
    ledgerStep demands (ledgerStep demands st a) b =
    ledgerStep demands (ledgerStep demands st b) a :=
  gatedStep_comm (P := fun (s : LedgerState V) e => ledgerAdmissible demands s.bal e)
    (upd := fun (s : LedgerState V) e => ⟨pay demands e s.bal, e ::ₘ s.adm⟩)
    (LedgerState.ext (pay_comm demands b a st.bal) (Multiset.cons_swap b a st.adm))
    (ledgerAdmissible_pay_other demands st.bal a b h.1.symm h.2.2)
    (ledgerAdmissible_pay_other demands st.bal b a h.1 h.2.1)

omit [Fintype V] in
/-- ★ Commutation du grand livre : dans tout contexte et depuis tout état, échanger deux
    lettres `I_loc`-indépendantes laisse le grand livre invariant. Ni garde, ni signe, ni
    restriction de répétition. -/
theorem ledger_commutation (demands : V × V → ℤ) (st : LedgerState V) (u w : List (V × V))
    {a b : V × V} (h : I_loc a b) :
    ledgerFoldFrom demands st (u ++ a :: b :: w) = ledgerFoldFrom demands st (u ++ b :: a :: w) :=
  foldl_swap_of_diamond (ledgerStep_comm demands) st u w h

/-- ★ Le grand livre est bien défini sur M(V × V, I_loc). -/
def ledgerFoldTrace (pool : FuturePool V) (demands : V × V → ℤ) : LocTrace V → LedgerState V :=
  LocTrace.liftFold (ledgerStep demands) ⟨pool.holdings, 0⟩ (ledgerStep_comm demands)

theorem ledgerFoldTrace_mk (pool : FuturePool V) (demands : V × V → ℤ) (l : List (V × V)) :
    ledgerFoldTrace pool demands (LocTrace.mk l) = ledgerFold pool demands l := rfl

/-! ### 4. Exactitude : `I_loc` est la plus grande indépendance statique -/

/-- Avoir unité en `x`, nul ailleurs. -/
def unitPool (x : V) : FuturePool V :=
  ⟨fun v => if v = x then 1 else 0, fun v => by
    show (0 : ℤ) ≤ if v = x then 1 else 0
    split_ifs <;> norm_num⟩

/-- ★ Pour deux lettres non-boucles distinctes, l'échange est invariant pour tous avoirs et
    tous montants ssi elles sont `I_loc`-indépendantes. Témoins (montants 1, avoir unité) :
    - même source : avoir en `a.1`, admis `{a}` contre `{b}` ;
    - `a.2 = b.1` (`a` finance `b`) : avoir en `a.1`, deux admis contre un ;
    - `b.2 = a.1` (`b` finance `a`) : avoir en `b.1`, un admis contre deux.
    (Une boucle commute avec tout dès que les soldes sont ≥ 0 : elle est exclue.) -/
theorem ledger_swap_invariant_iff {a b : V × V} (ha : a.1 ≠ a.2) (hb : b.1 ≠ b.2)
    (hab : a ≠ b) :
    (∀ (pool : FuturePool V) (demands : V × V → ℤ),
        ledgerFold pool demands [a, b] = ledgerFold pool demands [b, a]) ↔ I_loc a b := by
  constructor
  · intro H
    obtain ⟨x, y⟩ := a
    obtain ⟨x', y'⟩ := b
    simp only [ne_eq] at ha hb
    by_contra hI
    by_cases h1 : x = x'
    · subst h1
      have H1 := congrArg LedgerState.adm (H (unitPool x) (fun _ => 1))
      simp [ledgerFold, ledgerFoldFrom, ledgerStep, ledgerAdmissible, pay, unitPool, ha, hb] at H1
      exact hab (by simp [H1])
    · by_cases h2 : y = x'
      · subst h2
        have H1 := congrArg (fun s => Multiset.card s.adm) (H (unitPool x) (fun _ => 1))
        simp [ledgerFold, ledgerFoldFrom, ledgerStep, ledgerAdmissible, pay, unitPool, ha, hb,
          Ne.symm h1] at H1
      · have h3 : y' = x := by
          by_contra h3
          exact hI ⟨h1, h2, h3⟩
        subst h3
        have H1 := congrArg (fun s => Multiset.card s.adm) (H (unitPool x') (fun _ => 1))
        simp [ledgerFold, ledgerFoldFrom, ledgerStep, ledgerAdmissible, pay, unitPool, ha, hb,
          h1] at H1
  · intro h pool demands
    exact ledger_commutation demands _ [] [] h

/-! ### 5. Invariants économiques -/

lemma ledgerStep_sum_bal (demands : V × V → ℤ) (st : LedgerState V) (e : V × V) :
    ∑ v, (ledgerStep demands st e).bal v = ∑ v, st.bal v := by
  by_cases h : ledgerAdmissible demands st.bal e
  · rw [ledgerStep_of_adm h]
    exact pay_sum demands e st.bal
  · rw [ledgerStep_of_not_adm h]

/-- Conservation de la masse monétaire le long de tout pli. -/
theorem ledgerFoldFrom_sum_bal (demands : V × V → ℤ) :
    ∀ (w : List (V × V)) (st : LedgerState V),
      ∑ v, (ledgerFoldFrom demands st w).bal v = ∑ v, st.bal v
  | [], _ => rfl
  | e :: w, st =>
    (ledgerFoldFrom_sum_bal demands w (ledgerStep demands st e)).trans
      (ledgerStep_sum_bal demands st e)

theorem ledgerFold_sum_bal (pool : FuturePool V) (demands : V × V → ℤ) (w : List (V × V)) :
    ∑ v, (ledgerFold pool demands w).bal v = ∑ v, pool.holdings v :=
  ledgerFoldFrom_sum_bal demands w _

omit [Fintype V] in
lemma ledgerStep_bal_nonneg {demands : V × V → ℤ} (h_nn : ∀ e, 0 ≤ demands e)
    {st : LedgerState V} (hst : ∀ v, 0 ≤ st.bal v) (e : V × V) :
    ∀ v, 0 ≤ (ledgerStep demands st e).bal v := by
  intro v
  by_cases h : ledgerAdmissible demands st.bal e
  · rw [ledgerStep_of_adm h]
    show 0 ≤ pay demands e st.bal v
    by_cases hv : v = e.1
    · subst hv
      exact h
    · have h1 := hst v
      have h2 := h_nn e
      simp only [pay, if_neg hv, sub_zero]
      split_ifs <;> linarith
  · rw [ledgerStep_of_not_adm h]
    exact hst v

omit [Fintype V] in
lemma ledgerFoldFrom_bal_nonneg {demands : V × V → ℤ} (h_nn : ∀ e, 0 ≤ demands e) :
    ∀ (w : List (V × V)) (st : LedgerState V), (∀ v, 0 ≤ st.bal v) →
      ∀ v, 0 ≤ (ledgerFoldFrom demands st w).bal v
  | [], _, hst => hst
  | e :: w, _, hst =>
    ledgerFoldFrom_bal_nonneg h_nn w _ (ledgerStep_bal_nonneg h_nn hst e)

/-- Aucun découvert : sous montants ≥ 0, tous les soldes restent ≥ 0. -/
theorem ledgerFold_bal_nonneg (pool : FuturePool V) {demands : V × V → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) (w : List (V × V)) :
    ∀ v, 0 ≤ (ledgerFold pool demands w).bal v :=
  ledgerFoldFrom_bal_nonneg h_nn w _ pool.h_holdings_nonneg

/-! ### 6. Lien au pli RTGS committé (mots sans répétition) -/

omit [Fintype V] in
lemma vertex_load_union_singleton (demands : V × V → ℤ) (S : ActivationState V) {e : V × V}
    (he : e ∉ S) (v : V) :
    vertex_load demands (S ∪ {e}) v =
      vertex_load demands S v + (if v = e.1 then demands e else 0) := by
  unfold vertex_load
  rw [Finset.filter_union, Finset.sum_union
    (Finset.disjoint_filter_filter (Finset.disjoint_singleton_right.mpr he)),
    Finset.filter_singleton]
  by_cases h : v = e.1
  · simp [h]
  · simp [h, Ne.symm h]

omit [Fintype V] in
lemma received_union_singleton (demands : V × V → ℤ) (S : ActivationState V) {e : V × V}
    (he : e ∉ S) (v : V) :
    received demands (S ∪ {e}) v =
      received demands S v + (if v = e.2 then demands e else 0) := by
  unfold received
  rw [Finset.filter_union, Finset.sum_union
    (Finset.disjoint_filter_filter (Finset.disjoint_singleton_right.mpr he)),
    Finset.filter_singleton]
  by_cases h : v = e.2
  · simp [h]
  · simp [h, Ne.symm h]

section Nodup

variable (pool : FuturePool V) (demands : V × V → ℤ)

/-- Correspondance grand livre / état RTGS : mêmes admis, soldes = avoirs + recettes − charge. -/
def Corresp (st : LedgerState V) (S : ActivationState V) : Prop :=
  st.adm = S.val ∧
    ∀ v, st.bal v = pool.holdings v + received demands S v - vertex_load demands S v

lemma ledgerAdmissible_iff_rtgs {st : LedgerState V} {S : ActivationState V}
    (hc : Corresp pool demands st S) {e : V × V} (he : e ∉ S) :
    ledgerAdmissible demands st.bal e ↔ rtgsAdmissible pool demands S e := by
  unfold ledgerAdmissible rtgsAdmissible pay
  rw [vertex_load_union_singleton demands S he, received_union_singleton demands S he, hc.2]
  constructor <;> intro <;> linarith

lemma corresp_step {st : LedgerState V} {S : ActivationState V}
    (hc : Corresp pool demands st S) {e : V × V} (he : e ∉ S) :
    Corresp pool demands (ledgerStep demands st e) (rtgsStep pool demands S e) := by
  have hiff := ledgerAdmissible_iff_rtgs pool demands hc he
  by_cases hr : rtgsAdmissible pool demands S e
  · have hS : rtgsStep pool demands S e = S ∪ {e} := if_pos hr
    rw [ledgerStep_of_adm (hiff.mpr hr), hS]
    refine ⟨?_, fun v => ?_⟩
    · show e ::ₘ st.adm = (S ∪ {e}).val
      rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_val_of_notMem he, hc.1]
    · show pay demands e st.bal v = _
      rw [vertex_load_union_singleton demands S he, received_union_singleton demands S he]
      simp only [pay, hc.2 v]
      ring
  · have hS : rtgsStep pool demands S e = S := if_neg hr
    rw [ledgerStep_of_not_adm (fun h => hr (hiff.mp h)), hS]
    exact hc

lemma corresp_fold :
    ∀ (w : List (V × V)) (st : LedgerState V) (S : ActivationState V),
      w.Nodup → (∀ e ∈ w, e ∉ S) → Corresp pool demands st S →
      Corresp pool demands (ledgerFoldFrom demands st w) (w.foldl (rtgsStep pool demands) S)
  | [], _, _, _, _, hc => hc
  | e :: w, st, S, hnd, hout, hc => by
    have hnd' := List.nodup_cons.mp hnd
    refine corresp_fold w _ _ hnd'.2 (fun e' he' hmem => ?_)
      (corresp_step pool demands hc (hout e (List.mem_cons_self ..)))
    have hS : rtgsStep pool demands S e ⊆ S ∪ {e} := by
      unfold rtgsStep
      split_ifs
      · exact subset_rfl
      · exact Finset.subset_union_left
    rcases Finset.mem_union.mp (hS hmem) with h | h
    · exact hout e' (List.mem_cons_of_mem _ he') h
    · exact hnd'.1 (Finset.mem_singleton.mp h ▸ he')

/-- ★ Sur un mot sans répétition, le grand livre admet exactement le pli RTGS, et chaque solde
    vaut avoirs + recettes − charge de l'ensemble admis. Aucune hypothèse de signe. -/
theorem ledgerFold_eq_rtgsFold_of_nodup {w : List (V × V)} (hw : w.Nodup) :
    (ledgerFold pool demands w).adm = (rtgsFold pool demands w).val ∧
      ∀ v, (ledgerFold pool demands w).bal v =
        pool.holdings v + received demands (rtgsFold pool demands w) v -
          vertex_load demands (rtgsFold pool demands w) v := by
  rw [rtgsFold_eq_foldl]
  refine corresp_fold pool demands w _ ∅ hw (fun _ _ => Finset.notMem_empty _) ⟨rfl, fun v => ?_⟩
  simp [received, vertex_load]

end Nodup

/-! ### 7. Circulation : deux tours sur le 3-cycle -/

namespace Circulation

/-- Avoirs `(1, 0, 0)`. -/
def pool : FuturePool (Fin 3) := ⟨fun v => if v = 0 then 1 else 0, by decide⟩

def demands : Fin 3 × Fin 3 → ℤ := fun _ => 1

/-- Un tour du cycle `0 → 1 → 2 → 0`. -/
def round : List (Fin 3 × Fin 3) := [(0, 1), (1, 2), (2, 0)]

/-- Deux tours. -/
def w : List (Fin 3 × Fin 3) := round ++ round

/-- Le grand livre admet les six paiements. -/
theorem ledger_adm : (ledgerFold pool demands w).adm = (w : Multiset (Fin 3 × Fin 3)) := by
  decide

/-- Les soldes reviennent aux avoirs : la circulation est périodique. -/
theorem ledger_periodic : (ledgerFold pool demands w).bal = pool.holdings := by
  decide

/-- La sémantique une-fois perd le second tour. -/
theorem rtgs_card : (rtgsFold pool demands w).card = 3 := by
  decide

end Circulation

open Circulation in
/-- ★ Circulation : le grand livre règle deux tours complets du 3-cycle (six paiements) et
    revient aux avoirs ; le pli RTGS une-fois n'en admet que trois. -/
theorem circulation_two_rounds :
    Multiset.card (ledgerFold pool demands w).adm = 6 ∧
    (ledgerFold pool demands w).bal = pool.holdings ∧
    (rtgsFold pool demands w).card = 3 := by
  refine ⟨?_, ledger_periodic, rtgs_card⟩
  rw [ledger_adm]
  rfl

/-! ### 8. Fibre SCE en soldes -/

/-- Solde propre de `i` : bien défini sur les traces, comme composée de `ledgerFoldTrace`. -/
def ownBalance (pool : FuturePool V) (demands : V × V → ℤ) (i : V) (t : LocTrace V) : ℤ :=
  (ledgerFoldTrace pool demands t).bal i

open LocalCommutation.Gridlock in
/-- ★ L'agent `2` a la même vue locale dans `[g, f, a]` et `[f, g, a]` ; son solde final vaut
    `1` dans le premier, `0` dans le second. -/
theorem ledger_sce_fiber_nondegenerate :
    localObs (2 : Fin 4) (LocTrace.mk [g, f, a]) = localObs 2 (LocTrace.mk [f, g, a]) ∧
    ownBalance pool demands 2 (LocTrace.mk [g, f, a]) = 1 ∧
    ownBalance pool demands 2 (LocTrace.mk [f, g, a]) = 0 := by
  refine ⟨TraceObservation.sce_fiber_nondegenerate.2.2.2.1, ?_, ?_⟩
  · show (ledgerFold pool demands [g, f, a]).bal 2 = 1
    decide
  · show (ledgerFold pool demands [f, g, a]).bal 2 = 0
    decide

end LedgerCirculation
