/-
  ThesePlanetaire/LocalCommutation.lean
  Phase 1b (2026-10-01) : commutation LOCALE de l'admission RTGS (lecture recettes) et
  monoïde de traces non dégénéré M(V × V, I_loc).

  Développé d'abord en `LocalCommutation_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 1b réordonnée) ; analyse :
  `cache/analyse_forte_connexite_graphe_transactions_2026-10-01.md` (§V151).

  Sous la lecture CRÉDIT (PivotPotential), l'indépendance `I_LP G` est statique mais vide
  sur tout graphe garde fortement connexe (`I_LP_empty_of_strongly_connected`) — or le graphe
  des transactions monétaires l'est (presque) toujours. Sous la lecture RECETTES (palier 2 de
  l'échelle des couplages, `EchelleCouplages.received`), une lettre `a` lit la charge et les
  recettes de `a.1` et n'écrit que la charge de `a.1` et les recettes de `a.2`. Deux lettres
  commutent donc dès que

      I_loc a b := a.1 ≠ b.1 ∧ a.2 ≠ b.1 ∧ b.2 ≠ a.1

  (sources distinctes, aucune ne finance la source de l'autre). `I_loc` ne dépend ni du
  graphe, ni de l'état, ni des montants : c'est une relation de Mazurkiewicz sur l'alphabet
  `V × V` entier, et deux émetteurs vers un même récepteur commutent toujours
  (`I_loc_shared_receiver`) — y compris sur un graphe fortement connexe
  (`I_LP_empty_but_I_loc`).

  Contenu :
  1. `I_loc`, échelle `edge_indep ⊆ I_LP ⊆ I_loc ⊆ I₁` (sources distinctes) ;
  2. `rtgsAdmissible` / `rtgsFold` et ★ `rtgs_commutation` (sans garde, sans graphe) ;
  3. `LocTrace V := M(V × V, I_loc)`, descente ★ `rtgsFoldTrace`, morphisme `LPTrace G → LocTrace V` ;
  4. ★ lien au palier 2 committé : sous demandes ≥ 0, le pli `entry_admissible` (rondes de
     clearing à chaque insertion) ÉGALE le pli RTGS (`entry_fold_eq_rtgsFold`) ; il commute
     donc sous `I_loc` (`entry_fold_commutation`) ;
  5. contrastes : le crédit statique ne commute pas sous `I_loc`
     (`pivot_not_commute_under_I_loc`) ; le blocage de financement (`Gridlock`,
     `rtgs_gridlock`) montre que la clause `a.2 ≠ b.1` est nécessaire.
-/

import Mathlib.Tactic
import ThesePlanetaire.EchelleCouplages
import ThesePlanetaire.BudgetGatedIndep
import ThesePlanetaire.PivotCommutation
import ThesePlanetaire.GatedStep

namespace LocalCommutation

open DualDAG (FuturePool vertex_load admissionFoldP)
open BudgetGatedIndep (vertex_load_insert_other)
open EchelleCouplages (received entry_coupled_operator entry_coupled_contractive entry_chain
  entry_admissible received_antitone_subset)
open PivotPotential (pivotAdmissionFold pivot_order_dependent_despite_edge_indep)
open PivotCommutation (I_LP I_LP_ne I_LP_empty_of_strongly_connected GEdge LPSwap LPTrace)
open GatedStep (union_singleton_comm insertStep_comm Diamond foldl_swap_of_diamond)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. La relation locale `I_loc` et l'échelle des indépendances -/

/-- Indépendance locale : sources distinctes, et aucune des deux lettres ne crédite la source
    de l'autre. Ne dépend ni d'un graphe garde, ni de l'état, ni des montants. -/
def I_loc (a b : V × V) : Prop :=
  a.1 ≠ b.1 ∧ a.2 ≠ b.1 ∧ b.2 ≠ a.1

instance (a b : V × V) : Decidable (I_loc a b) :=
  inferInstanceAs (Decidable (a.1 ≠ b.1 ∧ a.2 ≠ b.1 ∧ b.2 ≠ a.1))

omit [Fintype V] [DecidableEq V] in
theorem I_loc_symm {a b : V × V} (h : I_loc a b) : I_loc b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

omit [Fintype V] [DecidableEq V] in
theorem I_loc_irrefl (a : V × V) : ¬ I_loc a a :=
  fun h => h.1 rfl

omit [Fintype V] [DecidableEq V] in
/-- `I_loc` ⊆ I₁ (sources distinctes, palier 1 : `BudgetGatedIndep.cone_commutation_invariant`). -/
theorem I_loc_imp_src_ne {a b : V × V} (h : I_loc a b) : a.1 ≠ b.1 :=
  h.1

omit [Fintype V] [DecidableEq V] in
/-- `edge_indep` (sommets disjoints) ⊆ `I_loc`. -/
theorem edge_indep_imp_I_loc {a b : V × V} (h : EdgeIndependence.edge_indep a b) :
    I_loc a b :=
  ⟨h.1, h.2.2.1, fun e => h.2.1 e.symm⟩

omit [Fintype V] [DecidableEq V] in
/-- `I_LP G` ⊆ `I_loc` pour tout graphe garde `G` : c'est exactement la conclusion de `I_LP_ne`. -/
theorem I_LP_imp_I_loc {G : DirectedGraph V} {a b : V × V} (h : I_LP G a b) : I_loc a b :=
  ⟨(I_LP_ne h).1, (I_LP_ne h).2.2, (I_LP_ne h).2.1⟩

omit [Fintype V] [DecidableEq V] in
/-- Deux émetteurs distincts vers un même récepteur (distinct d'eux) sont `I_loc`-indépendants :
    les paiements entrants d'un agent commutent toujours. -/
theorem I_loc_shared_receiver {x y i : V} (hxy : x ≠ y) (hxi : x ≠ i) (hyi : y ≠ i) :
    I_loc (x, i) (y, i) :=
  ⟨hxy, fun e => hyi e.symm, fun e => hxi e.symm⟩

/-- ★ Non-dégénérescence : sur tout graphe garde fortement connexe, `I_LP` est vide mais
    `I_loc` ne l'est pas (récepteur partagé). -/
theorem I_LP_empty_but_I_loc (G : DirectedGraph (Fin 3)) (h : ∀ u v, Reachable G u v) :
    ¬ I_LP G ((0, 2) : Fin 3 × Fin 3) (1, 2) ∧ I_loc ((0, 2) : Fin 3 × Fin 3) (1, 2) :=
  ⟨I_LP_empty_of_strongly_connected G h _ _, by decide⟩

/-! ### 2. Admission RTGS (lecture recettes) -/

/-- Admission RTGS : la charge sortante de la source, `e` comprise, est couverte par ses
    avoirs et ses recettes déjà admises (`e` comprise si boucle). C'est le test de survie de
    `e` dans `entry_coupled_operator (S ∪ {e})` (palier 2), évalué une seule fois. -/
def rtgsAdmissible (pool : FuturePool V) (demands : V × V → ℤ) (S : ActivationState V)
    (e : V × V) : Prop :=
  vertex_load demands (S ∪ {e}) e.1 ≤ pool.holdings e.1 + received demands (S ∪ {e}) e.1

instance (pool : FuturePool V) (demands : V × V → ℤ) (S : ActivationState V) (e : V × V) :
    Decidable (rtgsAdmissible pool demands S e) :=
  inferInstanceAs (Decidable (vertex_load demands (S ∪ {e}) e.1 ≤
    pool.holdings e.1 + received demands (S ∪ {e}) e.1))

/-- Pas test-and-keep RTGS (defeq à la lambda d'`admissionFoldP`). -/
def rtgsStep (pool : FuturePool V) (demands : V × V → ℤ) :
    ActivationState V → V × V → ActivationState V :=
  fun cur e => if rtgsAdmissible pool demands cur e then cur ∪ {e} else cur

/-- Pli RTGS : admission en ligne, une lettre à la fois. -/
def rtgsFold (pool : FuturePool V) (demands : V × V → ℤ) (edges : List (V × V)) :
    ActivationState V :=
  admissionFoldP (rtgsAdmissible pool demands) edges

lemma rtgsFold_eq_foldl (pool : FuturePool V) (demands : V × V → ℤ) (edges : List (V × V)) :
    rtgsFold pool demands edges = edges.foldl (rtgsStep pool demands) ∅ := rfl

/-! ### 3. Commutation du pas, puis du pli -/

omit [Fintype V] in
/-- Miroir de `vertex_load_insert_other` : insérer `b` (cible ≠ `v`) ne change pas les
    recettes de `v`. -/
lemma received_insert_other (demands : V × V → ℤ) (S : ActivationState V) (b : V × V) (v : V)
    (h_tgt : b.2 ≠ v) :
    received demands (S ∪ {b}) v = received demands S v := by
  unfold received
  rw [Finset.filter_union]
  have hb : (({b} : Finset (V × V)).filter fun x => x.2 = v) = ∅ := by
    rw [Finset.filter_singleton, if_neg h_tgt]
  rw [hb, Finset.union_empty]

/-- Admettre `b` ne change pas le test de `a` si `b` ne débite pas `a.1` (`b.1 ≠ a.1`) et ne
    le crédite pas (`b.2 ≠ a.1`). -/
lemma rtgsAdmissible_insert_other (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (a b : V × V) (h_src : b.1 ≠ a.1) (h_tgt : b.2 ≠ a.1) :
    rtgsAdmissible pool demands (S ∪ {b}) a ↔ rtgsAdmissible pool demands S a := by
  unfold rtgsAdmissible
  rw [union_singleton_comm S b a, vertex_load_insert_other demands (S ∪ {a}) b a.1 h_src,
    received_insert_other demands (S ∪ {a}) b a.1 h_tgt]

lemma rtgsStep_comm (pool : FuturePool V) (demands : V × V → ℤ) (S : ActivationState V)
    (a b : V × V) (h : I_loc a b) :
    rtgsStep pool demands (rtgsStep pool demands S a) b =
    rtgsStep pool demands (rtgsStep pool demands S b) a :=
  insertStep_comm (rtgsAdmissible_insert_other pool demands S a b h.1.symm h.2.2)
    (rtgsAdmissible_insert_other pool demands S b a h.1 h.2.1)

/-- ★ Commutation RTGS : dans tout contexte, échanger deux lettres `I_loc`-indépendantes laisse
    le pli invariant. Aucune garde, aucun graphe, aucune hypothèse sur les montants. -/
theorem rtgs_commutation (pool : FuturePool V) (demands : V × V → ℤ) (u w : List (V × V))
    {a b : V × V} (h : I_loc a b) :
    rtgsFold pool demands (u ++ a :: b :: w) = rtgsFold pool demands (u ++ b :: a :: w) :=
  foldl_swap_of_diamond (rtgsStep_comm pool demands) ∅ u w h

/-! ### 4. Le monoïde de traces M(V × V, I_loc) -/

/-- Générateurs de la congruence de Mazurkiewicz pour `I_loc` (échange en contexte). -/
inductive LocSwap : List (V × V) → List (V × V) → Prop
  | swap (u w : List (V × V)) (a b : V × V) (h : I_loc a b) :
      LocSwap (u ++ a :: b :: w) (u ++ b :: a :: w)

variable (V) in
/-- Monoïde de traces M(V × V, I_loc) : mots de transactions modulo la clôture d'équivalence
    des échanges `I_loc`. Alphabet entier, sans garde : tout sous-alphabet en est un
    sous-monoïde. -/
def LocTrace := Quot (LocSwap (V := V))

/-- Classe d'un mot. -/
def LocTrace.mk (l : List (V × V)) : LocTrace V := Quot.mk _ l

omit [Fintype V] [DecidableEq V] in
theorem LocTrace.mk_swap (u w : List (V × V)) {a b : V × V} (h : I_loc a b) :
    LocTrace.mk (u ++ a :: b :: w) = LocTrace.mk (u ++ b :: a :: w) :=
  Quot.sound (LocSwap.swap u w a b h)

/-- Concaténation : `LocSwap` est stable par contexte, donc la concaténation descend. -/
def LocTrace.append : LocTrace V → LocTrace V → LocTrace V :=
  Quot.map₂ (· ++ ·)
    (fun l _ _ h => by
      obtain ⟨u, w, a, b, hI⟩ := h
      simpa only [List.append_assoc] using LocSwap.swap (l ++ u) w a b hI)
    (fun _ _ l h => by
      obtain ⟨u, w, a, b, hI⟩ := h
      simpa only [List.append_assoc, List.cons_append] using LocSwap.swap u (w ++ l) a b hI)

/-- Descente sur M(V × V, I_loc) de tout pli dont le pas a la propriété de losange pour
    `I_loc` (`GatedStep.Diamond`). -/
def LocTrace.liftFold {σ : Type*} (δ : σ → V × V → σ) (s₀ : σ) (hD : Diamond δ I_loc) :
    LocTrace V → σ :=
  Quot.lift (fun l => l.foldl δ s₀) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact foldl_swap_of_diamond hD s₀ u w hI)

/-- ★ Le pli RTGS est bien défini sur M(V × V, I_loc) (`LocTrace.liftFold` + `rtgsStep_comm`). -/
def rtgsFoldTrace (pool : FuturePool V) (demands : V × V → ℤ) : LocTrace V → ActivationState V :=
  LocTrace.liftFold (rtgsStep pool demands) ∅ (rtgsStep_comm pool demands)

theorem rtgsFoldTrace_mk (pool : FuturePool V) (demands : V × V → ℤ) (l : List (V × V)) :
    rtgsFoldTrace pool demands (LocTrace.mk l) = rtgsFold pool demands l := rfl

/-- Échelle au niveau des monoïdes : `I_LP G ⊆ I_loc`, donc l'oubli de la garde induit un
    morphisme M(G, I_LP) → M(V × V, I_loc). -/
def LPTrace.toLoc (G : DirectedGraph V) : LPTrace G → LocTrace V :=
  Quot.lift (fun l => LocTrace.mk (l.map Subtype.val)) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    simp only [List.map_append, List.map_cons]
    exact LocTrace.mk_swap _ _ (I_LP_imp_I_loc hI))

/-! ### 5. Lien au palier 2 : le pli `entry_admissible` est le pli RTGS

  `entry_admissible current e` relance les rondes de clearing du palier 2 sur `current ∪ {e}`.
  Le long d'un pli, l'état courant est toujours un point fixe de `entry_coupled_operator` ;
  partant d'un point fixe, la survie de `e` ne dépend que du test RTGS de sa source (hors
  `e.1`, la charge est inchangée et les recettes croissent, demandes ≥ 0). -/

section Palier2

variable (pool : FuturePool V) (demands : V × V → ℤ)

lemma entry_chain_fixed {S : ActivationState V}
    (hS : entry_coupled_operator pool demands S = S) :
    ∀ n, entry_chain pool demands S n = S
  | 0 => rfl
  | n + 1 => by
    show entry_coupled_operator pool demands (entry_chain pool demands S n) = S
    rw [entry_chain_fixed hS n, hS]

lemma entry_chain_succ_subset_one (S₀ : ActivationState V) :
    ∀ n, entry_chain pool demands S₀ (n + 1) ⊆ entry_chain pool demands S₀ 1
  | 0 => subset_rfl
  | n + 1 =>
    (entry_coupled_contractive pool demands (entry_chain pool demands S₀ (n + 1))).trans
      (entry_chain_succ_subset_one S₀ n)

lemma entry_chain_not_mem {S₀ : ActivationState V} {e : V × V}
    (he : e ∉ entry_coupled_operator pool demands S₀) (n : ℕ) :
    e ∉ entry_chain pool demands S₀ (n + 1) :=
  fun h => he (entry_chain_succ_subset_one pool demands S₀ n h)

/-- Partant d'un point fixe, une admission RTGS donne encore un point fixe. -/
lemma rtgs_insert_fixpoint (h_nn : ∀ e, 0 ≤ demands e) {S : ActivationState V} {e : V × V}
    (hS : entry_coupled_operator pool demands S = S) (he : rtgsAdmissible pool demands S e) :
    entry_coupled_operator pool demands (S ∪ {e}) = S ∪ {e} := by
  unfold entry_coupled_operator
  apply Finset.filter_true_of_mem
  intro f hf
  by_cases hfe : f.1 = e.1
  · rw [hfe]; exact he
  · have hfS : f ∈ S := by
      rcases Finset.mem_union.mp hf with h | h
      · exact h
      · exact absurd (by rw [Finset.mem_singleton.mp h]) hfe
    have hcond := (Finset.mem_filter.mp (hS.symm ▸ hfS : f ∈ entry_coupled_operator pool demands S)).2
    rw [vertex_load_insert_other demands S e f.1 (Ne.symm hfe)]
    exact hcond.trans (add_le_add le_rfl
      (received_antitone_subset demands h_nn Finset.subset_union_left f.1))

/-- Depuis un point fixe, l'admission du palier 2 coïncide avec l'admission RTGS. -/
lemma entry_admissible_iff_rtgs_of_fixpoint (h_nn : ∀ e, 0 ≤ demands e)
    {S : ActivationState V} (hS : entry_coupled_operator pool demands S = S) (e : V × V) :
    entry_admissible pool demands S e ↔ rtgsAdmissible pool demands S e := by
  constructor
  · intro h
    by_contra hr
    have hnot : e ∉ entry_coupled_operator pool demands (S ∪ {e}) := fun hm =>
      hr (Finset.mem_filter.mp hm).2
    obtain ⟨m, hm⟩ : ∃ m, (S ∪ {e}).card = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero
        (Finset.card_ne_zero_of_mem (Finset.mem_union_right S (Finset.mem_singleton_self e)))
    unfold entry_admissible at h
    rw [hm] at h
    exact entry_chain_not_mem pool demands hnot m h
  · intro hr
    unfold entry_admissible
    rw [entry_chain_fixed pool demands (rtgs_insert_fixpoint pool demands h_nn hS hr)]
    exact Finset.mem_union_right S (Finset.mem_singleton_self e)

lemma foldl_entry_eq_rtgs (h_nn : ∀ e, 0 ≤ demands e) :
    ∀ (w : List (V × V)) (S : ActivationState V),
      entry_coupled_operator pool demands S = S →
      w.foldl (fun cur e => if entry_admissible pool demands cur e then cur ∪ {e} else cur) S =
        w.foldl (rtgsStep pool demands) S
  | [], _, _ => rfl
  | e :: w, S, hS => by
    simp only [List.foldl_cons]
    have hiff := entry_admissible_iff_rtgs_of_fixpoint pool demands h_nn hS e
    by_cases he : rtgsAdmissible pool demands S e
    · have hstep : rtgsStep pool demands S e = S ∪ {e} := if_pos he
      rw [if_pos (hiff.mpr he), hstep]
      exact foldl_entry_eq_rtgs h_nn w _ (rtgs_insert_fixpoint pool demands h_nn hS he)
    · have hstep : rtgsStep pool demands S e = S := if_neg he
      rw [if_neg (fun h => he (hiff.mp h)), hstep]
      exact foldl_entry_eq_rtgs h_nn w S hS

/-- ★ Sous demandes ≥ 0, le pli du palier 2 (rondes de clearing à chaque insertion) est le
    pli RTGS en ligne. -/
theorem entry_fold_eq_rtgsFold (h_nn : ∀ e, 0 ≤ demands e) (w : List (V × V)) :
    admissionFoldP (entry_admissible pool demands) w = rtgsFold pool demands w :=
  foldl_entry_eq_rtgs pool demands h_nn w ∅ (Finset.filter_empty _)

/-- ★ Corollaire : le pli du palier 2 commute sous `I_loc`, sur tout graphe. -/
theorem entry_fold_commutation (h_nn : ∀ e, 0 ≤ demands e) (u w : List (V × V))
    {a b : V × V} (h : I_loc a b) :
    admissionFoldP (entry_admissible pool demands) (u ++ a :: b :: w) =
      admissionFoldP (entry_admissible pool demands) (u ++ b :: a :: w) := by
  rw [entry_fold_eq_rtgsFold pool demands h_nn, entry_fold_eq_rtgsFold pool demands h_nn,
    rtgs_commutation pool demands u w h]

end Palier2

/-! ### 6. Contrastes -/

/-- Le crédit statique (Phase 1) ne commute pas sous `I_loc` : le témoin de PivotPotential
    est `edge_indep`, donc `I_loc`. Le coupable est la lecture transitive du crédit. -/
theorem pivot_not_commute_under_I_loc :
    ∃ (pool : FuturePool (Fin 4)) (demands : Fin 4 × Fin 4 → ℤ) (c a b : Fin 4 × Fin 4),
      I_loc a b ∧
      pivotAdmissionFold pool demands [c, a, b] ≠ pivotAdmissionFold pool demands [c, b, a] := by
  obtain ⟨pool, demands, c, a, b, hind, hne⟩ := pivot_order_dependent_despite_edge_indep
  exact ⟨pool, demands, c, a, b, edge_indep_imp_I_loc hind, hne⟩

/-! Blocage de financement (gridlock) : `V = Fin 4`, chaîne `0 → 1 → 2 → 3`, `g = (0,1)`,
  `f = (1,2)`, `a = (2,3)`, demandes 3, 2, 1, avoirs `(4, 0, 0, 0)`.
  - `[g, f, a]` : `3 ≤ 4`, `2 ≤ 0 + 3`, `1 ≤ 0 + 2` : tout est admis.
  - `[f, g, a]` : `f` rejetée (`2 > 0`), `g` admise, `a` rejetée (`1 > 0`).
  Marges strictes ≥ 1 partout (robustesse, D1). `g.2 = f.1` : la clause `a.2 ≠ b.1` de
  `I_loc` est nécessaire. -/

namespace Gridlock

def pool : FuturePool (Fin 4) := ⟨fun v => if v = 0 then 4 else 0, by decide⟩
def demands : Fin 4 × Fin 4 → ℤ := fun e => if e = (0, 1) then 3 else if e = (1, 2) then 2 else 1
def g : Fin 4 × Fin 4 := (0, 1)
def f : Fin 4 × Fin 4 := (1, 2)
def a : Fin 4 × Fin 4 := (2, 3)

theorem fold_gfa : rtgsFold pool demands [g, f, a] = {g, f, a} := by decide

theorem fold_fga : rtgsFold pool demands [f, g, a] = {g} := by decide

end Gridlock

open Gridlock in
/-- ★ L'ordre compte pour les paires liées par le financement : `[g, f, a]` et `[f, g, a]`
    diffèrent, et `g, f` ne sont pas `I_loc`-indépendantes. -/
theorem rtgs_gridlock :
    ¬ I_loc g f ∧ rtgsFold pool demands [g, f, a] ≠ rtgsFold pool demands [f, g, a] := by
  refine ⟨by decide, ?_⟩
  rw [fold_gfa, fold_fga]
  decide

end LocalCommutation
