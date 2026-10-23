/-
  ThesePlanetaire/AdmissionAutomata.lean
  Phase 2b (2026-10-01) : les plis RTGS et grand livre comme automates — WFA, langages
  réguliers reconnaissables sur M(V × V, I_loc), et frontière de conservation face au huit.

  Développé d'abord en `AdmissionAutomata_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 2b, étape 4) ; analyse :
  `cache/analyse_forte_connexite_graphe_transactions_2026-10-01.md` (§12).

  1. RTGS = WFA. `rtgsFold` est `admissionFoldP rtgsAdmissible`, donc l'unique exécution
     depuis ∅ du WFA « tester puis garder » `rtgsGatedWFA` (★ `rtgsFold_wfa_terminal`). Sous
     montants ≥ 0, le pli du palier 2 est l'unique exécution du MÊME WFA
     (★ `entryFold_wfa_terminal`, via `entry_fold_eq_rtgsFold`), et l'exécution ne dépend que
     de la trace (★ `rtgs_wfa_trace_invariant`).
  2. Langages de traces. Pour toute condition d'acceptation sur l'état admis, le langage RTGS
     est régulier (★ `rtgs_language_isRegular`, états `Finset` en nombre fini) et clos par
     la congruence de `I_loc` (`rtgs_language_trace_closed`) : un langage de traces
     reconnaissable. Image de Parikh `LocTrace.toMultiset`.
  3. Le grand livre est fini. `adm` est en écriture seule (`ledgerFoldFrom_bal`) ; sous
     montants ≥ 0, les soldes restent dans `BalInv M` (≥ 0, de somme `M`), ensemble fini
     (`balInv_finite`) stable par le pas (`balStep_balInv`). D'où ★
     `ledger_balance_language_isRegular` (toute condition sur les soldes finaux) et ★
     `ledger_settles_isRegular` : le langage de RÈGLEMENT INTÉGRAL (`settles` : chaque paiement
     admis à son tour — l'analogue d'`isSelfFinancing` pour le grand livre) est régulier ; il
     est lu sur le pli commité (`settles_iff_card`) et clos par traces (★
     `settles_trace_closed`), non vide et non plein (`circulation_settles`). Clôture :
     intersection avec `.*A$` (`settles_endAnchor_isRegular`).
  4. Frontière de conservation (★ `frontiere_conservation`, miroir de
     `SolvencyRegularity.frontiere_memoire_finie_de_la_solvabilite`) : à masse monétaire
     conservée, le langage de règlement est régulier pour tous avoirs et montants ≥ 0 ; le
     langage d'auto-financement du huit, à flux exogènes cumulés, ne l'est pas. Aucun langage
     de règlement ni de soldes ne vaut le huit (★ `ledger_settles_ne_huit`,
     ★ `ledger_balance_language_ne_huit`).

  Remarque [ANALYSE, non formalisée] : avec des montants signés, `balStep_balInv` tombe (un
  paiement négatif peut rendre la cible négative, et les soldes ne sont plus bornés) ; on
  n'affirme pas la régularité dans ce cas.

  Regexp au sens strict : le théorème de Kleene n'est pas dans le Mathlib local (cf.
  `AutomatonRegularity`) ; les énoncés portent sur `Language.IsRegular` (DFA finis).
-/

import ThesePlanetaire.AutomatonRegularity
import ThesePlanetaire.LedgerCirculation
import ThesePlanetaire.PivotWFA

namespace AdmissionAutomata

open DualDAG (FuturePool admissionFoldP)
open EchelleCouplages (entry_admissible)
open FlowAdmission (WFAReaches)
open PivotWFA (gatedWFA gatedWFA_reaches_iff admissionFoldP_wfa_terminal)
open LocalCommutation
open LedgerCirculation
open AutomatonRegularity (isRegular_of_finite_invariant isRegular_of_finite_states
  huit_not_isRegular ne_huit_of_isRegular endAnchor_isRegular)
open EndAnchor (satisfiesEndAnchor)
open OrganicLP (isSelfFinancing)
open SolvencyRegularity (huitTEG)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Le pli RTGS est l'exécution d'un WFA -/

/-- WFA « tester puis garder » de l'admission RTGS. -/
def rtgsGatedWFA (pool : FuturePool V) (demands : V × V → ℤ) :
    WeightedAutomaton Bool (V × V) (ActivationState V) :=
  gatedWFA (rtgsAdmissible pool demands)

/-- Le WFA RTGS atteint `T` depuis ∅ sur `w` ssi `T` est le pli RTGS. -/
theorem rtgs_wfa_reaches_iff (pool : FuturePool V) (demands : V × V → ℤ) (w : List (V × V))
    (T : ActivationState V) :
    WFAReaches (rtgsGatedWFA pool demands) ∅ w T ↔ T = rtgsFold pool demands w :=
  gatedWFA_reaches_iff (rtgsAdmissible pool demands) w ∅ T

/-- ★ Le pli RTGS est l'unique exécution de `rtgsGatedWFA` depuis ∅. -/
theorem rtgsFold_wfa_terminal (pool : FuturePool V) (demands : V × V → ℤ) (w : List (V × V)) :
    (rtgsGatedWFA pool demands).init ∅ = true ∧
    WFAReaches (rtgsGatedWFA pool demands) ∅ w (rtgsFold pool demands w) ∧
      ∀ T, WFAReaches (rtgsGatedWFA pool demands) ∅ w T → T = rtgsFold pool demands w :=
  admissionFoldP_wfa_terminal (rtgsAdmissible pool demands) w

/-- ★ Sous montants ≥ 0, le pli du palier 2 (rondes de clearing à chaque insertion) est
    l'unique exécution du MÊME WFA. -/
theorem entryFold_wfa_terminal (pool : FuturePool V) (demands : V × V → ℤ)
    (h_nn : ∀ e, 0 ≤ demands e) (w : List (V × V)) :
    WFAReaches (rtgsGatedWFA pool demands) ∅ w (admissionFoldP (entry_admissible pool demands) w) ∧
      ∀ T, WFAReaches (rtgsGatedWFA pool demands) ∅ w T →
        T = admissionFoldP (entry_admissible pool demands) w := by
  rw [entry_fold_eq_rtgsFold pool demands h_nn]
  exact (rtgsFold_wfa_terminal pool demands w).2

/-- ★ L'exécution du WFA RTGS ne dépend que de la trace. -/
theorem rtgs_wfa_trace_invariant (pool : FuturePool V) (demands : V × V → ℤ)
    {w w' : List (V × V)} (h : LocTrace.mk w = LocTrace.mk w') (T : ActivationState V) :
    WFAReaches (rtgsGatedWFA pool demands) ∅ w T ↔ WFAReaches (rtgsGatedWFA pool demands) ∅ w' T := by
  have hw : rtgsFold pool demands w = rtgsFold pool demands w' := by
    rw [← rtgsFoldTrace_mk, ← rtgsFoldTrace_mk, h]
  rw [rtgs_wfa_reaches_iff, rtgs_wfa_reaches_iff, hw]

/-! ### 2. Langages de traces reconnaissables -/

/-- ★ Pour toute condition d'acceptation sur l'état admis, le langage RTGS est régulier. -/
theorem rtgs_language_isRegular (pool : FuturePool V) (demands : V × V → ℤ)
    (acc : ActivationState V → Bool) :
    Language.IsRegular ({w | acc (rtgsFold pool demands w) = true} : Language (V × V)) :=
  isRegular_of_finite_states (rtgsStep pool demands) ∅ acc

/-- Le langage RTGS est clos par la congruence de `I_loc`. -/
theorem rtgs_language_trace_closed (pool : FuturePool V) (demands : V × V → ℤ)
    (acc : ActivationState V → Bool) {w w' : List (V × V)} (h : LocTrace.mk w = LocTrace.mk w') :
    acc (rtgsFold pool demands w) = true ↔ acc (rtgsFold pool demands w') = true := by
  rw [← rtgsFoldTrace_mk, ← rtgsFoldTrace_mk, h]

/-- Image de Parikh : le multi-ensemble des lettres descend aux traces. -/
def LocTrace.toMultiset : LocTrace V → Multiset (V × V) :=
  Quot.lift (fun l => (l : Multiset (V × V))) (by
    intro _ _ h
    obtain ⟨u, w, a, b, _⟩ := h
    exact Multiset.coe_eq_coe.mpr ((List.Perm.swap b a w).append_left u))

omit [Fintype V] [DecidableEq V] in
theorem LocTrace.toMultiset_mk (l : List (V × V)) :
    LocTrace.toMultiset (LocTrace.mk l) = (l : Multiset (V × V)) := rfl

omit [Fintype V] [DecidableEq V] in
/-- La longueur est un invariant de trace. -/
theorem LocTrace.length_eq {w w' : List (V × V)} (h : LocTrace.mk w = LocTrace.mk w') :
    w.length = w'.length := by
  have := congrArg (fun t => Multiset.card (LocTrace.toMultiset t)) h
  simpa only [LocTrace.toMultiset_mk, Multiset.coe_card] using this

/-! ### 3. Le grand livre est un automate fini -/

/-- Pas du grand livre sur les soldes seuls. -/
def balStep (demands : V × V → ℤ) (bal : V → ℤ) (e : V × V) : V → ℤ :=
  (ledgerStep demands ⟨bal, 0⟩ e).bal

omit [Fintype V] in
lemma ledgerStep_bal (demands : V × V → ℤ) (st : LedgerState V) (e : V × V) :
    (ledgerStep demands st e).bal = balStep demands st.bal e := by
  unfold balStep ledgerStep
  by_cases h : ledgerAdmissible demands st.bal e <;> simp [h]

omit [Fintype V] in
/-- `adm` est en écriture seule : les soldes finaux sont le pli de `balStep`. -/
theorem ledgerFoldFrom_bal (demands : V × V → ℤ) :
    ∀ (w : List (V × V)) (st : LedgerState V),
      (ledgerFoldFrom demands st w).bal = w.foldl (balStep demands) st.bal
  | [], _ => rfl
  | e :: w, st => by
    rw [List.foldl_cons, ← ledgerStep_bal]
    exact ledgerFoldFrom_bal demands w (ledgerStep demands st e)

/-- Invariant des soldes : positifs, de somme `M`. -/
def BalInv (M : ℤ) (bal : V → ℤ) : Prop :=
  (∀ v, 0 ≤ bal v) ∧ ∑ v, bal v = M

omit [DecidableEq V] in
/-- L'invariant des soldes est fini : chaque solde est dans `[0, M]`. -/
theorem balInv_finite (M : ℤ) : {bal : V → ℤ | BalInv M bal}.Finite := by
  refine (Set.Finite.pi' (t := fun _ : V => Set.Icc (0 : ℤ) M)
    (fun _ => Set.finite_Icc 0 M)).subset ?_
  rintro bal ⟨h0, hsum⟩ v
  refine ⟨h0 v, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ v)

lemma balStep_balInv {demands : V × V → ℤ} (h_nn : ∀ e, 0 ≤ demands e) {M : ℤ}
    {bal : V → ℤ} (h : BalInv M bal) (e : V × V) : BalInv M (balStep demands bal e) :=
  ⟨ledgerStep_bal_nonneg h_nn (st := ⟨bal, 0⟩) h.1 e,
    (ledgerStep_sum_bal demands ⟨bal, 0⟩ e).trans h.2⟩

/-- ★ Sous montants ≥ 0, pour toute condition sur les soldes finaux, le langage du grand livre
    est régulier. -/
theorem ledger_balance_language_isRegular (pool : FuturePool V) {demands : V × V → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) (acc : (V → ℤ) → Bool) :
    Language.IsRegular ({w | acc (ledgerFold pool demands w).bal = true} : Language (V × V)) := by
  simp only [ledgerFold, ledgerFoldFrom_bal]
  exact isRegular_of_finite_invariant (balStep demands) pool.holdings
    (balInv_finite (∑ v, pool.holdings v)) ⟨pool.h_holdings_nonneg, rfl⟩
    (fun _ _ h => balStep_balInv h_nn h _) acc

/-- Règlement intégral : chaque paiement du mot est admis à son tour (analogue, pour le grand
    livre, d'`isSelfFinancing`). -/
def settles (demands : V × V → ℤ) : (V → ℤ) → List (V × V) → Prop
  | _, [] => True
  | bal, e :: w => ledgerAdmissible demands bal e ∧ settles demands (pay demands e bal) w

/-- Pas de règlement : `none` est l'état mort (un paiement a été rejeté). -/
def settleStep (demands : V × V → ℤ) : Option (V → ℤ) → V × V → Option (V → ℤ)
  | none, _ => none
  | some bal, e => if ledgerAdmissible demands bal e then some (pay demands e bal) else none

omit [Fintype V] in
lemma foldl_settleStep_none (demands : V × V → ℤ) :
    ∀ w : List (V × V), w.foldl (settleStep demands) none = none
  | [] => rfl
  | _ :: w => foldl_settleStep_none demands w

omit [Fintype V] in
lemma settles_iff_foldl (demands : V × V → ℤ) :
    ∀ (w : List (V × V)) (bal : V → ℤ),
      settles demands bal w ↔ (w.foldl (settleStep demands) (some bal)).isSome = true
  | [], _ => by simp [settles]
  | e :: w, bal => by
    simp only [settles, List.foldl_cons, settleStep]
    by_cases h : ledgerAdmissible demands bal e
    · rw [if_pos h, ← settles_iff_foldl demands w]
      exact and_iff_right h
    · rw [if_neg h, foldl_settleStep_none]
      simp [h]

omit [Fintype V] in
lemma card_adm_le (demands : V × V → ℤ) :
    ∀ (w : List (V × V)) (st : LedgerState V),
      Multiset.card (ledgerFoldFrom demands st w).adm ≤ Multiset.card st.adm + w.length
  | [], _ => by simp [ledgerFoldFrom]
  | e :: w, st => by
    have ih := card_adm_le demands w (ledgerStep demands st e)
    have hstep : Multiset.card (ledgerStep demands st e).adm ≤ Multiset.card st.adm + 1 := by
      by_cases h : ledgerAdmissible demands st.bal e
      · rw [ledgerStep_of_adm h, Multiset.card_cons]
      · rw [ledgerStep_of_not_adm h]
        omega
    simp only [ledgerFoldFrom, List.foldl_cons, List.length_cons] at ih ⊢
    omega

omit [Fintype V] in
/-- Le règlement intégral se lit sur le pli commité : tous les paiements sont admis. -/
theorem settles_iff_card (demands : V × V → ℤ) :
    ∀ (w : List (V × V)) (st : LedgerState V),
      settles demands st.bal w ↔
        Multiset.card (ledgerFoldFrom demands st w).adm = Multiset.card st.adm + w.length
  | [], _ => by simp [settles, ledgerFoldFrom]
  | e :: w, st => by
    have hfold : ledgerFoldFrom demands st (e :: w) =
        ledgerFoldFrom demands (ledgerStep demands st e) w := rfl
    rw [hfold, List.length_cons]
    by_cases h : ledgerAdmissible demands st.bal e
    · have ih := settles_iff_card demands w ⟨pay demands e st.bal, e ::ₘ st.adm⟩
      rw [ledgerStep_of_adm h]
      simp only [settles, Multiset.card_cons] at ih ⊢
      rw [and_iff_right h, ih]
      omega
    · have hle := card_adm_le demands w st
      rw [ledgerStep_of_not_adm h]
      simp only [settles, h, false_and, false_iff]
      omega

/-- ★ Sous montants ≥ 0, le langage de règlement intégral du grand livre est régulier. -/
theorem ledger_settles_isRegular (pool : FuturePool V) {demands : V × V → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) :
    Language.IsRegular ({w | settles demands pool.holdings w} : Language (V × V)) := by
  simp only [settles_iff_foldl]
  set M := ∑ v, pool.holdings v
  refine isRegular_of_finite_invariant (settleStep demands) (some pool.holdings)
    (Inv := fun o => ∀ bal, o = some bal → BalInv M bal) ?_ ?_ ?_ Option.isSome
  · refine (((balInv_finite M).image some).insert none).subset ?_
    intro o ho
    cases o with
    | none => exact Set.mem_insert _ _
    | some bal => exact Set.mem_insert_of_mem _ ⟨bal, ho bal rfl, rfl⟩
  · rintro bal ⟨⟩
    exact ⟨pool.h_holdings_nonneg, rfl⟩
  · intro o e ho bal' hbal'
    cases o with
    | none => cases hbal'
    | some bal =>
      simp only [settleStep] at hbal'
      split_ifs at hbal' with hadm
      cases hbal'
      have := balStep_balInv h_nn (ho bal rfl) e
      unfold balStep at this
      rwa [ledgerStep_of_adm (st := ⟨bal, 0⟩) hadm] at this

omit [Fintype V] in
/-- ★ Le règlement intégral est une propriété de la trace. -/
theorem settles_trace_closed (demands : V × V → ℤ) (bal : V → ℤ) {w w' : List (V × V)}
    (h : LocTrace.mk w = LocTrace.mk w') : settles demands bal w ↔ settles demands bal w' := by
  have hf : ledgerFoldFrom demands ⟨bal, 0⟩ w = ledgerFoldFrom demands ⟨bal, 0⟩ w' :=
    congrArg (LocTrace.liftFold (ledgerStep demands) ⟨bal, 0⟩ (ledgerStep_comm demands)) h
  refine (settles_iff_card demands w ⟨bal, 0⟩).trans (Iff.trans ?_
    (settles_iff_card demands w' ⟨bal, 0⟩).symm)
  rw [hf, LocTrace.length_eq h]

open LedgerCirculation.Circulation in
/-- Non-vacuité : les deux tours de la circulation (`LedgerCirculation.Circulation`) se règlent
    intégralement ; `(1, 2)` seul, sans avoir en `1`, ne se règle pas. -/
theorem circulation_settles :
    settles demands pool.holdings w ∧ ¬ settles demands pool.holdings [(1, 2)] :=
  ⟨(settles_iff_foldl demands w pool.holdings).mpr (by decide),
    fun h => absurd ((settles_iff_foldl demands _ pool.holdings).mp h) (by decide)⟩

/-- Clôture : règlement intégral ET dernière lettre dans `A` (`.*A$`) reste régulier. -/
theorem settles_endAnchor_isRegular (pool : FuturePool V) {demands : V × V → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) (anchor : EndAnchor.EndAnchor (V × V)) :
    Language.IsRegular (({w | settles demands pool.holdings w} : Language (V × V)) ⊓
      {w | satisfiesEndAnchor anchor w}) :=
  (ledger_settles_isRegular pool h_nn).inf (endAnchor_isRegular anchor)

/-! ### 4. Frontière de conservation -/

/-- ★ Aucun langage de règlement du grand livre n'est le langage du huit. -/
theorem ledger_settles_ne_huit (pool : FuturePool (Fin 3)) {demands : Fin 3 × Fin 3 → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) :
    ({w | settles demands pool.holdings w} : Language (Fin 3 × Fin 3)) ≠
      {w | isSelfFinancing huitTEG w} :=
  ne_huit_of_isRegular (ledger_settles_isRegular pool h_nn)

/-- ★ Aucune condition sur les soldes finaux du grand livre ne reconnaît le huit. -/
theorem ledger_balance_language_ne_huit (pool : FuturePool (Fin 3))
    {demands : Fin 3 × Fin 3 → ℤ} (h_nn : ∀ e, 0 ≤ demands e) (acc : (Fin 3 → ℤ) → Bool) :
    ({w | acc (ledgerFold pool demands w).bal = true} : Language (Fin 3 × Fin 3)) ≠
      {w | isSelfFinancing huitTEG w} :=
  ne_huit_of_isRegular (ledger_balance_language_isRegular pool h_nn acc)

/-- ★ Frontière de conservation : à masse monétaire conservée (grand livre, montants ≥ 0), le
    langage de règlement intégral est régulier pour tous avoirs ; à flux exogènes cumulés (huit
    comptable), le langage d'auto-financement ne l'est pas. -/
theorem frontiere_conservation :
    (∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (pool : FuturePool V)
       (demands : V × V → ℤ), (∀ e, 0 ≤ demands e) →
       Language.IsRegular ({w | settles demands pool.holdings w} : Language (V × V)))
    ∧ ¬ Language.IsRegular ({w | isSelfFinancing huitTEG w} : Language (Fin 3 × Fin 3)) :=
  ⟨fun _ _ _ pool _ h_nn => ledger_settles_isRegular pool h_nn, huit_not_isRegular⟩

end AdmissionAutomata
