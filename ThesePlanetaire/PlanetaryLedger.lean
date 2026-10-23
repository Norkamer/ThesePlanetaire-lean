/-
  ThesePlanetaire/PlanetaryLedger.lean
  Phase 3a (2026-10-01) : externalités planétaires dans le grand livre — les frontières
  gardées comme comptes communs, commutation sous `I_planet`, dommage de Parikh, structure de
  dépendance dérivée, régularité du règlement.

  Développé d'abord en `PlanetaryLedger_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 3, étape 3a) ; analyse :
  `cache/analyse_externalites_retroaction_regex_2026-10-01.md`.

  Externalité planétaire : un stock s'épuise sans coût courant, d'où une perte future. Chaque
  paiement émet sur des frontières (`Footprint.emit`) ; certaines sont GARDÉES
  (`Footprint.gated`, stock limitant). Le grand livre planétaire (`PState` : soldes, stocks,
  admis) admet un paiement si sa source reste solvable ET si chaque stock gardé couvre son
  émission (`planetAdmissible`) ; le pas est `GatedStep.gatedStep`. Une frontière gardée est
  un COMPTE COMMUN débité par tous ses émetteurs.
  1. ★ `planet_commutation` : commutation sous `I_planet` = `I_loc` ∧ empreintes gardées
     disjointes (`planetStep_comm`, argument d'empreinte) ; descente ★ `planetFoldTrace` sur
     M(V × V, I_planet) (`GatedStep.TraceQ`). Sans garde, `I_planet = I_loc`
     (`I_planet_of_no_gate`) ;
  2. ★ `planet_swap_invariant_iff` : pour deux non-boucles distinctes et des émissions gardées
     ≥ 0, l'échange est invariant pour tous avoirs, montants et stocks ssi `I_planet` — c'est la
     plus grande indépendance statique. Témoin du commun partagé : le premier servi épuise le
     stock ;
  3. invariants : conservation de la monnaie, aucun découvert, stocks gardés ≥ 0 (sans
     hypothèse de signe), ★ `planet_stock_parikh` (le stock final de TOUTE frontière est le
     stock initial moins les émissions cumulées admises : fonction de Parikh), ★
     `planet_emission_le_stock` (plafond garanti sur les frontières gardées) ;
  4. ★ `dependance_structure` : le dommage est additif (k = 0) ; la garde crée une dépendance
     d'ALLOCATION exactement entre co-émetteurs ; les frontières non gardées sont en écriture
     seule. Lecture [ANALYSE] corrigée en Phase 4 (erratum ci-dessous, `FeedbackPlanetary`) :
     la garde est une LECTURE du stock, donc une rétroaction de classe T sur l'historique ;
  5. ★ `internalisation` (un paiement solvable rejeté faute de stock) et ★ `climate_commons`
     (instance `PlanetaryBoundary` : deux paiements `I_loc`-indépendants se disputent un budget
     carbone, l'ordre l'attribue) ;
  6. ★ `planet_settles_isRegular` : sous montants et émissions gardées ≥ 0, le langage de
     règlement intégral planétaire (`psettles`) est régulier — l'automate ne garde que les
     soldes et les stocks gardés (`Footprint.restrict`) ; il est clos par traces de `I_planet`
     (★ `psettles_trace_closed`), non vide et non plein (`climate_settles`).
-/

import ThesePlanetaire.AdmissionAutomata
import ThesePlanetaire.PlanetaryBoundaries

namespace PlanetaryLedger

open DualDAG (FuturePool)
open LocalCommutation (I_loc I_loc_symm)
open LedgerCirculation
open GatedStep (gatedStep gatedStep_comm Diamond foldl_swap_of_diamond TraceQ)

variable {V : Type*} [Fintype V] [DecidableEq V] {B : Type*}

/-! ### 1. Empreinte planétaire et grand livre planétaire -/

/-- Empreinte planétaire : émission de chaque paiement sur chaque frontière, et frontières
    GARDÉES (à stock limitant). -/
structure Footprint (V B : Type*) where
  emit : V × V → B → ℤ
  gated : Finset B

/-- Prélèvement de `e` sur les stocks. -/
def deplete (fp : Footprint V B) (e : V × V) (stock : B → ℤ) : B → ℤ :=
  fun c => stock c - fp.emit e c

/-- Empreinte gardée de `e` : frontières gardées sur lesquelles `e` émet. -/
def gsupp (fp : Footprint V B) (e : V × V) : Finset B :=
  fp.gated.filter (fun c => fp.emit e c ≠ 0)

/-- Admission planétaire : chaque stock gardé couvre l'émission de `e`. -/
def stockAdmissible (fp : Footprint V B) (stock : B → ℤ) (e : V × V) : Prop :=
  ∀ c ∈ gsupp fp e, fp.emit e c ≤ stock c

instance (fp : Footprint V B) (stock : B → ℤ) (e : V × V) :
    Decidable (stockAdmissible fp stock e) :=
  Finset.decidableDforallFinset

/-- État du grand livre planétaire : soldes, stocks, paiements admis. -/
@[ext] structure PState (V B : Type*) where
  bal : V → ℤ
  stock : B → ℤ
  adm : Multiset (V × V)

/-- Projection sur le grand livre monétaire. -/
def PState.toLedger (st : PState V B) : LedgerState V := ⟨st.bal, st.adm⟩

/-- Un paiement est admis si sa source reste solvable ET si les stocks gardés couvrent son
    émission. -/
def planetAdmissible (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B) (e : V × V) :
    Prop :=
  ledgerAdmissible demands st.bal e ∧ stockAdmissible fp st.stock e

instance (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B) (e : V × V) :
    Decidable (planetAdmissible demands fp st e) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Règlement planétaire : paiement, prélèvement, enregistrement. -/
def planetUpd (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B) (e : V × V) :
    PState V B :=
  ⟨pay demands e st.bal, deplete fp e st.stock, e ::ₘ st.adm⟩

/-- Pas « tester puis garder » du grand livre planétaire. -/
def planetStep (demands : V × V → ℤ) (fp : Footprint V B) : PState V B → V × V → PState V B :=
  gatedStep (planetAdmissible demands fp) (planetUpd demands fp)

def planetFoldFrom (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B)
    (w : List (V × V)) : PState V B :=
  w.foldl (planetStep demands fp) st

/-- Pli planétaire depuis les avoirs et les stocks initiaux `S₀`. -/
def planetFold (pool : FuturePool V) (demands : V × V → ℤ) (fp : Footprint V B) (S₀ : B → ℤ)
    (w : List (V × V)) : PState V B :=
  planetFoldFrom demands fp ⟨pool.holdings, S₀, 0⟩ w

omit [Fintype V] in
lemma planetStep_of_adm {demands : V × V → ℤ} {fp : Footprint V B} {st : PState V B}
    {e : V × V} (h : planetAdmissible demands fp st e) :
    planetStep demands fp st e = planetUpd demands fp st e := if_pos h

omit [Fintype V] in
lemma planetStep_of_not_adm {demands : V × V → ℤ} {fp : Footprint V B} {st : PState V B}
    {e : V × V} (h : ¬ planetAdmissible demands fp st e) : planetStep demands fp st e = st :=
  if_neg h

/-! ### 2. Commutation sous `I_planet` -/

/-- Indépendance planétaire : `I_loc` ET empreintes gardées disjointes (pas de commun partagé). -/
def I_planet (fp : Footprint V B) (a b : V × V) : Prop :=
  I_loc a b ∧ Disjoint (gsupp fp a) (gsupp fp b)

omit [Fintype V] [DecidableEq V] in
theorem I_planet_symm {fp : Footprint V B} {a b : V × V} (h : I_planet fp a b) :
    I_planet fp b a :=
  ⟨I_loc_symm h.1, h.2.symm⟩

omit [Fintype V] [DecidableEq V] in
theorem I_planet_imp_I_loc {fp : Footprint V B} {a b : V × V} (h : I_planet fp a b) :
    I_loc a b := h.1

omit [Fintype V] [DecidableEq V] in
/-- Sans frontière gardée, l'indépendance planétaire est l'indépendance monétaire. -/
theorem I_planet_of_no_gate {fp : Footprint V B} (h : fp.gated = ∅) (a b : V × V) :
    I_planet fp a b ↔ I_loc a b := by
  refine ⟨fun h' => h'.1, fun h' => ⟨h', ?_⟩⟩
  simp [gsupp, h]

omit [Fintype V] [DecidableEq V] in
lemma emit_eq_zero_of_not_mem {fp : Footprint V B} {e : V × V} {c : B} (hc : c ∈ fp.gated)
    (hn : c ∉ gsupp fp e) : fp.emit e c = 0 := by
  by_contra h
  exact hn (Finset.mem_filter.mpr ⟨hc, h⟩)

omit [Fintype V] [DecidableEq V] in
/-- Argument d'empreinte : prélever pour `b` ne change pas le test de `a` si leurs empreintes
    gardées sont disjointes. -/
lemma stockAdmissible_deplete_other (fp : Footprint V B) (stock : B → ℤ) (a b : V × V)
    (h : Disjoint (gsupp fp a) (gsupp fp b)) :
    stockAdmissible fp (deplete fp b stock) a ↔ stockAdmissible fp stock a := by
  unfold stockAdmissible
  refine forall₂_congr fun c hc => ?_
  rw [deplete, emit_eq_zero_of_not_mem (Finset.mem_filter.mp hc).1
    (Finset.disjoint_left.mp h hc), sub_zero]

omit [Fintype V] in
/-- ★ Losange du grand livre planétaire pour `I_planet`. -/
theorem planetStep_comm (demands : V × V → ℤ) (fp : Footprint V B) :
    Diamond (planetStep demands fp) (I_planet fp) := by
  intro st a b h
  exact gatedStep_comm
    (PState.ext (pay_comm demands b a st.bal) (by funext c; simp only [planetUpd, deplete]; ring)
      (Multiset.cons_swap b a st.adm))
    (and_congr (ledgerAdmissible_pay_other demands st.bal a b h.1.1.symm h.1.2.2)
      (stockAdmissible_deplete_other fp st.stock a b h.2))
    (and_congr (ledgerAdmissible_pay_other demands st.bal b a h.1.1 h.1.2.1)
      (stockAdmissible_deplete_other fp st.stock b a h.2.symm))

omit [Fintype V] in
/-- ★ Commutation planétaire : échanger deux lettres `I_planet`-indépendantes, dans tout
    contexte et depuis tout état, laisse le grand livre planétaire invariant. -/
theorem planet_commutation (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B)
    (u w : List (V × V)) {a b : V × V} (h : I_planet fp a b) :
    planetFoldFrom demands fp st (u ++ a :: b :: w) =
      planetFoldFrom demands fp st (u ++ b :: a :: w) :=
  foldl_swap_of_diamond (planetStep_comm demands fp) st u w h

/-- ★ Le grand livre planétaire est bien défini sur M(V × V, I_planet). -/
def planetFoldTrace (pool : FuturePool V) (demands : V × V → ℤ) (fp : Footprint V B)
    (S₀ : B → ℤ) : TraceQ (I_planet fp) → PState V B :=
  TraceQ.liftFold (planetStep demands fp) ⟨pool.holdings, S₀, 0⟩ (planetStep_comm demands fp)

theorem planetFoldTrace_mk (pool : FuturePool V) (demands : V × V → ℤ) (fp : Footprint V B)
    (S₀ : B → ℤ) (l : List (V × V)) :
    planetFoldTrace pool demands fp S₀ (TraceQ.mk _ l) = planetFold pool demands fp S₀ l := rfl

/-! ### 3. Exactitude : `I_planet` est la plus grande indépendance statique -/

omit [Fintype V] in
/-- Stocks amples : si chaque stock gardé couvre les émissions cumulées du mot, le grand livre
    planétaire admet exactement ce qu'admet le grand livre monétaire. -/
theorem planetFoldFrom_eq_ledger_of_ample (demands : V × V → ℤ) (fp : Footprint V B)
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    ∀ (w : List (V × V)) (st : PState V B),
      (∀ c ∈ fp.gated, (w.map (fun e => fp.emit e c)).sum ≤ st.stock c) →
      (planetFoldFrom demands fp st w).toLedger = ledgerFoldFrom demands st.toLedger w
  | [], _, _ => rfl
  | e :: w, st, hst => by
    have hrest : ∀ c ∈ fp.gated, 0 ≤ (w.map (fun e => fp.emit e c)).sum := fun c hc =>
      List.sum_nonneg (by
        intro x hx
        obtain ⟨e', _, rfl⟩ := List.mem_map.mp hx
        exact h_emit e' c hc)
    have hS : stockAdmissible fp st.stock e := by
      intro c hc
      have hc' := (Finset.mem_filter.mp hc).1
      have := hst c hc'
      simp only [List.map_cons, List.sum_cons] at this
      linarith [hrest c hc']
    show (planetFoldFrom demands fp (planetStep demands fp st e) w).toLedger =
      ledgerFoldFrom demands (ledgerStep demands st.toLedger e) w
    by_cases hL : ledgerAdmissible demands st.bal e
    · rw [planetStep_of_adm ⟨hL, hS⟩, ledgerStep_of_adm (st := st.toLedger) hL]
      refine planetFoldFrom_eq_ledger_of_ample demands fp h_emit w _ (fun c hc => ?_)
      have := hst c hc
      simp only [List.map_cons, List.sum_cons] at this
      show _ ≤ st.stock c - fp.emit e c
      linarith
    · rw [planetStep_of_not_adm (fun h => hL h.1), ledgerStep_of_not_adm (st := st.toLedger) hL]
      refine planetFoldFrom_eq_ledger_of_ample demands fp h_emit w _ (fun c hc => ?_)
      have := hst c hc
      simp only [List.map_cons, List.sum_cons] at this
      linarith [h_emit e c hc]

omit [Fintype V] in
lemma ledgerAdmissible_zero (bal : V → ℤ) (e : V × V) :
    ledgerAdmissible 0 bal e ↔ 0 ≤ bal e.1 := by
  simp [ledgerAdmissible, pay]

/-- ★ Pour deux lettres non-boucles distinctes et des émissions gardées ≥ 0, l'échange est
    invariant pour tous avoirs, montants et stocks initiaux ssi elles sont
    `I_planet`-indépendantes. Témoins :
    - hors `I_loc` : stocks amples, on retombe sur `ledger_swap_invariant_iff` ;
    - commun partagé `c` : montants nuls, stock `max (emit a c) (emit b c)` ; le premier servi
      épuise le commun, l'ordre décide qui est admis (`{a}` contre `{b}`). -/
theorem planet_swap_invariant_iff (fp : Footprint V B)
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) {a b : V × V} (ha : a.1 ≠ a.2)
    (hb : b.1 ≠ b.2) (hab : a ≠ b) :
    (∀ (pool : FuturePool V) (demands : V × V → ℤ) (S₀ : B → ℤ),
        planetFold pool demands fp S₀ [a, b] = planetFold pool demands fp S₀ [b, a]) ↔
      I_planet fp a b := by
  constructor
  · intro H
    have hloc : I_loc a b := by
      refine (ledger_swap_invariant_iff ha hb hab).mp (fun pool demands => ?_)
      have H1 := congrArg PState.toLedger
        (H pool demands (fun c => fp.emit a c + fp.emit b c))
      unfold planetFold at H1
      rwa [planetFoldFrom_eq_ledger_of_ample demands fp h_emit _ _ (fun c _ => by simp),
        planetFoldFrom_eq_ledger_of_ample demands fp h_emit _ _ (fun c _ => by
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          linarith)] at H1
    refine ⟨hloc, ?_⟩
    by_contra hd
    obtain ⟨c, hca, hcb⟩ := Finset.not_disjoint_iff.mp hd
    have hca' := Finset.mem_filter.mp hca
    have hcb' := Finset.mem_filter.mp hcb
    have hea : 0 < fp.emit a c := lt_of_le_of_ne (h_emit a c hca'.1) (Ne.symm hca'.2)
    have heb : 0 < fp.emit b c := lt_of_le_of_ne (h_emit b c hcb'.1) (Ne.symm hcb'.2)
    let pool0 : FuturePool V := ⟨0, fun _ => le_refl 0⟩
    let S : B → ℤ := fun c => max (fp.emit a c) (fp.emit b c)
    -- le premier servi est admis, le second est rejeté au commun `c`
    have first : ∀ x y : V × V, (x = a ∧ y = b) ∨ (x = b ∧ y = a) →
        (planetFold pool0 0 fp S [x, y]).adm = {x} := by
      intro x y hxy
      have hx : planetAdmissible 0 fp ⟨pool0.holdings, S, 0⟩ x := by
        refine ⟨(ledgerAdmissible_zero _ x).mpr (le_refl 0), fun c' _ => ?_⟩
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact le_max_left _ _
        · exact le_max_right _ _
      have hy : ¬ planetAdmissible 0 fp (planetUpd 0 fp ⟨pool0.holdings, S, 0⟩ x) y := by
        rintro ⟨-, hS⟩
        have hyc : c ∈ gsupp fp y := by rcases hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
        have := hS c hyc
        simp only [planetUpd, deplete, S] at this
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases le_total (fp.emit x c) (fp.emit y c) with hle | hle <;>
          simp only [max_eq_left, max_eq_right, hle] at this <;> linarith
      show (planetStep 0 fp (planetStep 0 fp ⟨pool0.holdings, S, 0⟩ x) y).adm = {x}
      rw [planetStep_of_adm hx, planetStep_of_not_adm hy]
      rfl
    have H1 := congrArg PState.adm (H pool0 0 S)
    rw [first a b (Or.inl ⟨rfl, rfl⟩), first b a (Or.inr ⟨rfl, rfl⟩)] at H1
    exact hab (Multiset.singleton_inj.mp H1)
  · intro h pool demands S₀
    exact planet_commutation demands fp _ [] [] h

/-! ### 4. Invariants : conservation, stocks, dommage de Parikh -/

lemma planetStep_sum_bal (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B)
    (e : V × V) : ∑ v, (planetStep demands fp st e).bal v = ∑ v, st.bal v := by
  by_cases h : planetAdmissible demands fp st e
  · rw [planetStep_of_adm h]
    exact pay_sum demands e st.bal
  · rw [planetStep_of_not_adm h]

/-- Conservation de la masse monétaire. -/
theorem planetFoldFrom_sum_bal (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B),
      ∑ v, (planetFoldFrom demands fp st w).bal v = ∑ v, st.bal v
  | [], _ => rfl
  | e :: w, st =>
    (planetFoldFrom_sum_bal demands fp w (planetStep demands fp st e)).trans
      (planetStep_sum_bal demands fp st e)

omit [Fintype V] in
lemma planetStep_bal_nonneg {demands : V × V → ℤ} (h_nn : ∀ e, 0 ≤ demands e)
    {fp : Footprint V B} {st : PState V B} (hst : ∀ v, 0 ≤ st.bal v) (e : V × V) :
    ∀ v, 0 ≤ (planetStep demands fp st e).bal v := by
  by_cases h : planetAdmissible demands fp st e
  · rw [planetStep_of_adm h]
    have := ledgerStep_bal_nonneg h_nn (st := st.toLedger) hst e
    rwa [ledgerStep_of_adm (st := st.toLedger) h.1] at this
  · rw [planetStep_of_not_adm h]
    exact hst

omit [Fintype V] in
/-- Aucun découvert sous montants ≥ 0. -/
theorem planetFoldFrom_bal_nonneg {demands : V × V → ℤ} (h_nn : ∀ e, 0 ≤ demands e)
    (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B), (∀ v, 0 ≤ st.bal v) →
      ∀ v, 0 ≤ (planetFoldFrom demands fp st w).bal v
  | [], _, hst => hst
  | e :: w, _, hst =>
    planetFoldFrom_bal_nonneg h_nn fp w _ (planetStep_bal_nonneg h_nn hst e)

omit [Fintype V] in
lemma planetStep_stock_nonneg {demands : V × V → ℤ} {fp : Footprint V B} {st : PState V B}
    (hst : ∀ c ∈ fp.gated, 0 ≤ st.stock c) (e : V × V) :
    ∀ c ∈ fp.gated, 0 ≤ (planetStep demands fp st e).stock c := by
  intro c hc
  by_cases h : planetAdmissible demands fp st e
  · rw [planetStep_of_adm h]
    show 0 ≤ st.stock c - fp.emit e c
    by_cases he : fp.emit e c = 0
    · rw [he, sub_zero]
      exact hst c hc
    · have := h.2 c (Finset.mem_filter.mpr ⟨hc, he⟩)
      linarith
  · rw [planetStep_of_not_adm h]
    exact hst c hc

omit [Fintype V] in
/-- Les stocks gardés restent ≥ 0 (aucune hypothèse de signe sur les émissions). -/
theorem planetFoldFrom_stock_nonneg (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B), (∀ c ∈ fp.gated, 0 ≤ st.stock c) →
      ∀ c ∈ fp.gated, 0 ≤ (planetFoldFrom demands fp st w).stock c
  | [], _, hst => hst
  | e :: w, _, hst =>
    planetFoldFrom_stock_nonneg demands fp w _ (planetStep_stock_nonneg hst e)

omit [Fintype V] in
theorem planet_stock_parikh_from (demands : V × V → ℤ) (fp : Footprint V B) (c : B) :
    ∀ (w : List (V × V)) (st : PState V B),
      (planetFoldFrom demands fp st w).stock c +
          ((planetFoldFrom demands fp st w).adm.map (fp.emit · c)).sum =
        st.stock c + (st.adm.map (fp.emit · c)).sum
  | [], _ => rfl
  | e :: w, st => by
    show (planetFoldFrom demands fp (planetStep demands fp st e) w).stock c +
        ((planetFoldFrom demands fp (planetStep demands fp st e) w).adm.map (fp.emit · c)).sum = _
    rw [planet_stock_parikh_from demands fp c w]
    by_cases h : planetAdmissible demands fp st e
    · rw [planetStep_of_adm h]
      simp only [planetUpd, deplete, Multiset.map_cons, Multiset.sum_cons]
      ring
    · rw [planetStep_of_not_adm h]

/-- ★ Dommage de Parikh : pour TOUTE frontière, gardée ou non, le stock final est le stock
    initial moins les émissions cumulées des paiements admis — une fonction de l'image de Parikh
    du multi-ensemble admis, indépendante de l'ordre. -/
theorem planet_stock_parikh (pool : FuturePool V) (demands : V × V → ℤ) (fp : Footprint V B)
    (S₀ : B → ℤ) (w : List (V × V)) (c : B) :
    (planetFold pool demands fp S₀ w).stock c =
      S₀ c - ((planetFold pool demands fp S₀ w).adm.map (fp.emit · c)).sum := by
  have := planet_stock_parikh_from demands fp c w ⟨pool.holdings, S₀, 0⟩
  simp only [Multiset.map_zero, Multiset.sum_zero, add_zero] at this
  unfold planetFold
  linarith

/-- ★ Plafond garanti : sur une frontière gardée de stock initial ≥ 0, les émissions cumulées
    admises ne dépassent jamais le stock initial. -/
theorem planet_emission_le_stock (pool : FuturePool V) (demands : V × V → ℤ)
    (fp : Footprint V B) {S₀ : B → ℤ} (hS₀ : ∀ c ∈ fp.gated, 0 ≤ S₀ c) (w : List (V × V))
    {c : B} (hc : c ∈ fp.gated) :
    ((planetFold pool demands fp S₀ w).adm.map (fp.emit · c)).sum ≤ S₀ c := by
  have h1 := planet_stock_parikh pool demands fp S₀ w c
  have h2 : 0 ≤ (planetFold pool demands fp S₀ w).stock c :=
    planetFoldFrom_stock_nonneg demands fp w ⟨pool.holdings, S₀, 0⟩ hS₀ c hc
  linarith

/-- Sous émissions ≥ 0, les stocks sont décroissants. -/
theorem planet_stock_le (pool : FuturePool V) (demands : V × V → ℤ) (fp : Footprint V B)
    (h_emit : ∀ e c, 0 ≤ fp.emit e c) (S₀ : B → ℤ) (w : List (V × V)) (c : B) :
    (planetFold pool demands fp S₀ w).stock c ≤ S₀ c := by
  rw [planet_stock_parikh]
  have : 0 ≤ ((planetFold pool demands fp S₀ w).adm.map (fp.emit · c)).sum :=
    Multiset.sum_nonneg (fun x hx => by
      obtain ⟨e, _, rfl⟩ := Multiset.mem_map.mp hx
      exact h_emit e c)
  linarith

/-! ### 5. Structure de dépendance dérivée -/

omit [Fintype V] [DecidableEq V] in
lemma gsupp_congr {fp fp' : Footprint V B} (hg : fp'.gated = fp.gated)
    (he : ∀ e, ∀ c ∈ fp.gated, fp'.emit e c = fp.emit e c) (e : V × V) :
    gsupp fp' e = gsupp fp e := by
  unfold gsupp
  rw [hg]
  exact Finset.filter_congr (fun c hc => by rw [he e c hc])

omit [Fintype V] [DecidableEq V] in
lemma stockAdmissible_congr {fp fp' : Footprint V B} (hg : fp'.gated = fp.gated)
    (he : ∀ e, ∀ c ∈ fp.gated, fp'.emit e c = fp.emit e c) {stock stock' : B → ℤ}
    (hs : ∀ c ∈ fp.gated, stock c = stock' c) (e : V × V) :
    stockAdmissible fp' stock' e ↔ stockAdmissible fp stock e := by
  unfold stockAdmissible
  rw [gsupp_congr hg he e]
  refine forall₂_congr fun c hc => ?_
  have hc' := (Finset.mem_filter.mp hc).1
  rw [he e c hc', hs c hc']

/-- Deux états qui coïncident sur les soldes, les admis et les stocks gardés. -/
def GatedAgree (fp : Footprint V B) (st st' : PState V B) : Prop :=
  st.bal = st'.bal ∧ st.adm = st'.adm ∧ ∀ c ∈ fp.gated, st.stock c = st'.stock c

omit [Fintype V] in
/-- Deux empreintes qui coïncident sur les frontières gardées donnent les mêmes admissions, les
    mêmes soldes et les mêmes stocks gardés. -/
theorem planetFoldFrom_congr (demands : V × V → ℤ) {fp fp' : Footprint V B}
    (hg : fp'.gated = fp.gated) (he : ∀ e, ∀ c ∈ fp.gated, fp'.emit e c = fp.emit e c) :
    ∀ (w : List (V × V)) (st st' : PState V B), GatedAgree fp st st' →
      GatedAgree fp (planetFoldFrom demands fp st w) (planetFoldFrom demands fp' st' w)
  | [], _, _, h => h
  | e :: w, st, st', ⟨hb, ha, hs⟩ => by
    refine planetFoldFrom_congr demands hg he w _ _ ?_
    have hP : planetAdmissible demands fp' st' e ↔ planetAdmissible demands fp st e := by
      unfold planetAdmissible
      rw [← hb, stockAdmissible_congr hg he hs e]
    by_cases hA : planetAdmissible demands fp st e
    · rw [planetStep_of_adm hA, planetStep_of_adm (hP.mpr hA)]
      refine ⟨by simp only [planetUpd, hb], by simp only [planetUpd, ha], fun c hc => ?_⟩
      simp only [planetUpd, deplete]
      rw [hs c hc, he e c hc]
    · rw [planetStep_of_not_adm hA, planetStep_of_not_adm (fun h => hA (hP.mp h))]
      exact ⟨hb, ha, hs⟩

/-- ★ Structure de dépendance dérivée (et non stipulée) :
    1. le dommage est toujours ADDITIF : sur toute frontière, le stock final est une fonction de
       l'image de Parikh des admis (k = 0 au sens de `TraceAdmissibility`) ;
    2. GARDER une frontière crée une dépendance d'ALLOCATION, exactement entre co-émetteurs :
       sous `I_loc`, l'ordre est indifférent ssi les empreintes gardées sont disjointes ;
    3. une frontière NON gardée n'en crée aucune : elle est en écriture seule (deux empreintes
       qui coïncident sur les frontières gardées admettent exactement les mêmes paiements).

    [ANALYSE, erratum Phase 4] La lecture initiale (« k ≥ 1 exige un dommage non additif ; la
    garde ajoute un rationnement, non un effet de chemin ») est fausse dans les deux sens : un
    dommage non additif évalué en fin d'historique reste une fonction de Parikh (classe P,
    `FeedbackClass.nonlinear_readout_P`, `cascade_closure_P`), et la garde, qui LIT le stock,
    rend l'historique des transactions sensible à l'ordre (classe T,
    `FeedbackPlanetary.planet_feedback_class`). La classe mesure la rétroaction, non la forme
    du dommage ; `parikhClass` est désormais dérivée (`PlanetaryBoundaries.parikhClassIn`). -/
theorem dependance_structure (fp : Footprint V B) (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    (∀ (pool : FuturePool V) (demands : V × V → ℤ) (S₀ : B → ℤ) (w : List (V × V)) (c : B),
        (planetFold pool demands fp S₀ w).stock c =
          S₀ c - ((planetFold pool demands fp S₀ w).adm.map (fp.emit · c)).sum) ∧
    (∀ a b : V × V, a.1 ≠ a.2 → b.1 ≠ b.2 → a ≠ b → I_loc a b →
        ((∀ (pool : FuturePool V) (demands : V × V → ℤ) (S₀ : B → ℤ),
            planetFold pool demands fp S₀ [a, b] = planetFold pool demands fp S₀ [b, a]) ↔
          Disjoint (gsupp fp a) (gsupp fp b))) ∧
    (∀ fp' : Footprint V B, fp'.gated = fp.gated →
        (∀ e, ∀ c ∈ fp.gated, fp'.emit e c = fp.emit e c) →
        ∀ (pool : FuturePool V) (demands : V × V → ℤ) (S₀ : B → ℤ) (w : List (V × V)),
          (planetFold pool demands fp' S₀ w).adm = (planetFold pool demands fp S₀ w).adm) := by
  refine ⟨fun pool demands S₀ w c => planet_stock_parikh pool demands fp S₀ w c,
    fun a b ha hb hab hI => ?_, fun fp' hg he pool demands S₀ w => ?_⟩
  · rw [planet_swap_invariant_iff fp h_emit ha hb hab]
    exact ⟨fun h => h.2, fun h => ⟨hI, h⟩⟩
  · exact (planetFoldFrom_congr demands hg he w _ _ ⟨rfl, rfl, fun _ _ => rfl⟩).2.1.symm

/-! ### 6. Internalisation et commun climatique -/

namespace Internalisation

/-- Avoirs `(1, 0)`. -/
def pool : FuturePool (Fin 2) := ⟨fun v => if v = 0 then 1 else 0, by decide⟩

def demands : Fin 2 × Fin 2 → ℤ := fun _ => 1

/-- Une frontière gardée ; chaque paiement y émet une unité. -/
def fp : Footprint (Fin 2) Unit := ⟨fun _ _ => 1, {()}⟩

end Internalisation

open Internalisation in
/-- ★ Internalisation : un paiement solvable, que le grand livre monétaire règle, est rejeté par
    le grand livre planétaire quand le stock est épuisé ; il est réglé dès que le stock le
    couvre. L'externalité devient une contrainte d'admission. -/
theorem internalisation :
    (ledgerFold pool demands [(0, 1)]).adm = {(0, 1)} ∧
    (planetFold pool demands fp (fun _ => 0) [(0, 1)]).adm = 0 ∧
    (planetFold pool demands fp (fun _ => 1) [(0, 1)]).adm = {(0, 1)} := by
  decide

namespace ClimateCommons

open PlanetaryBoundaries (PlanetaryBoundary)

/-- Avoirs `(1, 1, 0)`. -/
def pool : FuturePool (Fin 3) := ⟨fun v => if v = 2 then 0 else 1, by decide⟩

def demands : Fin 3 × Fin 3 → ℤ := fun _ => 1

/-- Chaque paiement émet une unité de CO₂ ; seul le climat est gardé. -/
def fp : Footprint (Fin 3) PlanetaryBoundary :=
  ⟨fun _ c => if c = .climateChange then 1 else 0, {.climateChange}⟩

/-- Budget carbone restant : une unité. -/
def S₀ : PlanetaryBoundary → ℤ := fun c => if c = .climateChange then 1 else 0

def a : Fin 3 × Fin 3 := (0, 2)
def b : Fin 3 × Fin 3 := (1, 2)

end ClimateCommons

open ClimateCommons in
/-- ★ Commun climatique : deux paiements `I_loc`-indépendants (sources distinctes, récepteur
    commun) que le grand livre monétaire règle dans les deux ordres ; sur le grand livre
    planétaire, ils se partagent un budget carbone d'une unité et l'ordre attribue le budget. -/
theorem climate_commons :
    I_loc a b ∧ ¬ Disjoint (gsupp fp a) (gsupp fp b) ∧
    (ledgerFold pool demands [a, b]).adm = (ledgerFold pool demands [b, a]).adm ∧
    Multiset.card (ledgerFold pool demands [a, b]).adm = 2 ∧
    (planetFold pool demands fp S₀ [a, b]).adm = {a} ∧
    (planetFold pool demands fp S₀ [b, a]).adm = {b} := by
  decide

/-! ### 7. Régularité du règlement planétaire -/

/-- Règlement intégral planétaire : chaque paiement est admis à son tour. -/
def psettles (demands : V × V → ℤ) (fp : Footprint V B) : PState V B → List (V × V) → Prop
  | _, [] => True
  | st, e :: w => planetAdmissible demands fp st e ∧ psettles demands fp (planetUpd demands fp st e) w

omit [Fintype V] in
lemma planet_card_adm_le (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B),
      Multiset.card (planetFoldFrom demands fp st w).adm ≤ Multiset.card st.adm + w.length
  | [], _ => by simp [planetFoldFrom]
  | e :: w, st => by
    have ih := planet_card_adm_le demands fp w (planetStep demands fp st e)
    have hstep : Multiset.card (planetStep demands fp st e).adm ≤ Multiset.card st.adm + 1 := by
      by_cases h : planetAdmissible demands fp st e
      · rw [planetStep_of_adm h]
        simp [planetUpd]
      · rw [planetStep_of_not_adm h]
        omega
    simp only [planetFoldFrom, List.foldl_cons, List.length_cons] at ih ⊢
    omega

omit [Fintype V] in
/-- Le règlement intégral se lit sur le pli : tous les paiements sont admis. -/
theorem psettles_iff_card (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B),
      psettles demands fp st w ↔
        Multiset.card (planetFoldFrom demands fp st w).adm = Multiset.card st.adm + w.length
  | [], _ => by simp [psettles, planetFoldFrom]
  | e :: w, st => by
    have hfold : planetFoldFrom demands fp st (e :: w) =
        planetFoldFrom demands fp (planetStep demands fp st e) w := rfl
    rw [hfold, List.length_cons]
    by_cases h : planetAdmissible demands fp st e
    · have ih := psettles_iff_card demands fp w (planetUpd demands fp st e)
      rw [planetStep_of_adm h]
      simp only [psettles]
      rw [and_iff_right h, ih]
      simp only [planetUpd, Multiset.card_cons]
      omega
    · have hle := planet_card_adm_le demands fp w st
      rw [planetStep_of_not_adm h]
      simp only [psettles, h, false_and, false_iff]
      omega

omit [Fintype V] in
/-- ★ Le règlement intégral planétaire est une propriété de la trace sur M(V × V, I_planet). -/
theorem psettles_trace_closed (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B)
    {w w' : List (V × V)} (h : TraceQ.mk (I_planet fp) w = TraceQ.mk (I_planet fp) w') :
    psettles demands fp st w ↔ psettles demands fp st w' := by
  have hf : planetFoldFrom demands fp st w = planetFoldFrom demands fp st w' :=
    congrArg (TraceQ.liftFold (planetStep demands fp) st (planetStep_comm demands fp)) h
  rw [psettles_iff_card, psettles_iff_card, hf, TraceQ.length_eq h]

/-- Pas de règlement sur les soldes et les stocks : `none` est l'état mort. -/
def psettleStep (demands : V × V → ℤ) (fp : Footprint V B) :
    Option ((V → ℤ) × (B → ℤ)) → V × V → Option ((V → ℤ) × (B → ℤ))
  | none, _ => none
  | some p, e =>
    if ledgerAdmissible demands p.1 e ∧ stockAdmissible fp p.2 e then
      some (pay demands e p.1, deplete fp e p.2)
    else none

omit [Fintype V] in
lemma foldl_psettleStep_none (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ w : List (V × V), w.foldl (psettleStep demands fp) none = none
  | [] => rfl
  | _ :: w => foldl_psettleStep_none demands fp w

omit [Fintype V] in
lemma psettles_iff_foldl (demands : V × V → ℤ) (fp : Footprint V B) :
    ∀ (w : List (V × V)) (st : PState V B),
      psettles demands fp st w ↔
        (w.foldl (psettleStep demands fp) (some (st.bal, st.stock))).isSome = true
  | [], _ => by simp [psettles]
  | e :: w, st => by
    simp only [psettles, List.foldl_cons, psettleStep]
    by_cases h : ledgerAdmissible demands st.bal e ∧ stockAdmissible fp st.stock e
    · rw [if_pos h]
      exact (and_iff_right h).trans (psettles_iff_foldl demands fp w (planetUpd demands fp st e))
    · rw [if_neg h, foldl_psettleStep_none]
      exact ⟨fun h' => absurd h'.1 h, fun h' => by simp at h'⟩

section Regularity

variable [DecidableEq B]

/-- Restriction de l'empreinte aux frontières gardées : les autres ne sont plus débitées. -/
def Footprint.restrict (fp : Footprint V B) : Footprint V B :=
  ⟨fun e c => if c ∈ fp.gated then fp.emit e c else 0, fp.gated⟩

omit [Fintype V] in
lemma psettles_restrict (demands : V × V → ℤ) (fp : Footprint V B) (st : PState V B)
    (w : List (V × V)) : psettles demands fp.restrict st w ↔ psettles demands fp st w := by
  rw [psettles_iff_card, psettles_iff_card,
    ← (planetFoldFrom_congr demands (fp := fp) (fp' := fp.restrict) rfl (fun e c hc => if_pos hc) w st st
      ⟨rfl, rfl, fun _ _ => rfl⟩).2.1]

/-- ★ Sous montants ≥ 0 et émissions gardées ≥ 0, pour tous avoirs et stocks initiaux, le
    langage de règlement intégral planétaire est régulier. L'automate n'a besoin que des
    soldes (`BalInv`) et des stocks GARDÉS (dans `[min S₀ 0, S₀]`) : les frontières non gardées
    sont en écriture seule (`Footprint.restrict`). -/
theorem planet_settles_isRegular [Fintype B] (pool : FuturePool V) {demands : V × V → ℤ}
    (h_nn : ∀ e, 0 ≤ demands e) (fp : Footprint V B)
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) (S₀ : B → ℤ) :
    Language.IsRegular ({w | psettles demands fp ⟨pool.holdings, S₀, 0⟩ w} : Language (V × V)) := by
  have hset : ({w | psettles demands fp ⟨pool.holdings, S₀, 0⟩ w} : Language (V × V)) =
      {w | psettles demands fp.restrict ⟨pool.holdings, S₀, 0⟩ w} := by
    ext w
    exact (psettles_restrict demands fp _ w).symm
  rw [hset]
  simp only [psettles_iff_foldl]
  set M := ∑ v, pool.holdings v
  refine AutomatonRegularity.isRegular_of_finite_invariant (psettleStep demands fp.restrict)
    (some (pool.holdings, S₀))
    (Inv := fun o => ∀ p, o = some p →
      AdmissionAutomata.BalInv M p.1 ∧ ∀ c, min (S₀ c) 0 ≤ p.2 c ∧ p.2 c ≤ S₀ c)
    ?_ ?_ ?_ Option.isSome
  · have hT : {p : (V → ℤ) × (B → ℤ) |
        AdmissionAutomata.BalInv M p.1 ∧ ∀ c, min (S₀ c) 0 ≤ p.2 c ∧ p.2 c ≤ S₀ c}.Finite := by
      refine ((AdmissionAutomata.balInv_finite M).prod (Set.Finite.pi'
        (t := fun c => Set.Icc (min (S₀ c) 0) (S₀ c)) (fun c => Set.finite_Icc _ _))).subset ?_
      rintro ⟨bal, stock⟩ ⟨hb, hs⟩
      exact ⟨hb, fun c => hs c⟩
    refine ((hT.image some).insert none).subset ?_
    intro o ho
    cases o with
    | none => exact Set.mem_insert _ _
    | some p => exact Set.mem_insert_of_mem _ ⟨p, ho p rfl, rfl⟩
  · rintro p ⟨⟩
    exact ⟨⟨pool.h_holdings_nonneg, rfl⟩, fun c => ⟨min_le_left _ _, le_refl _⟩⟩
  · intro o e ho p' hp'
    cases o with
    | none => cases hp'
    | some p =>
      simp only [psettleStep] at hp'
      split_ifs at hp' with hadm
      cases hp'
      obtain ⟨hb, hs⟩ := ho p rfl
      refine ⟨?_, fun c => ?_⟩
      · have := AdmissionAutomata.balStep_balInv h_nn hb e
        unfold AdmissionAutomata.balStep at this
        rwa [ledgerStep_of_adm (st := ⟨p.1, 0⟩) hadm.1] at this
      · show min (S₀ c) 0 ≤ p.2 c - fp.restrict.emit e c ∧ p.2 c - fp.restrict.emit e c ≤ S₀ c
        by_cases hz : fp.restrict.emit e c = 0
        · rw [hz, sub_zero]
          exact hs c
        · have hcg : c ∈ fp.gated := by
            by_contra hcg
            exact hz (if_neg hcg)
          have hle : fp.restrict.emit e c ≤ p.2 c :=
            hadm.2 c (Finset.mem_filter.mpr ⟨hcg, hz⟩)
          have hpos : 0 ≤ fp.restrict.emit e c := by
            show 0 ≤ if c ∈ fp.gated then fp.emit e c else 0
            rw [if_pos hcg]
            exact h_emit e c hcg
          exact ⟨by linarith [min_le_right (S₀ c) 0], by linarith [(hs c).2]⟩

end Regularity

open ClimateCommons in
/-- Non-vacuité : sur le commun climatique, `[a]` se règle intégralement, `[a, b]` non. -/
theorem climate_settles :
    psettles demands fp ⟨pool.holdings, S₀, 0⟩ [a] ∧
      ¬ psettles demands fp ⟨pool.holdings, S₀, 0⟩ [a, b] :=
  ⟨(psettles_iff_foldl demands fp [a] _).mpr (by decide),
    fun h => absurd ((psettles_iff_foldl demands fp _ _).mp h) (by decide)⟩

end PlanetaryLedger
