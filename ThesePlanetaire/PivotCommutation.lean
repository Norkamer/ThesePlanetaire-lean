/-
  ThesePlanetaire/PivotCommutation.lean
  Pivot d'admission, phase 1 : commutation sous relation STATIQUE `I_LP` et descente
  de `pivotAdmissionFold` au monoïde de traces M(G, I_LP) (amendement A).

  Provenance : scratch PivotCommutation_scratch, porté verbatim (2026-10-01). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (amendement A).

  Sous le pivot (PivotPotential), « sources distinctes » (`I_src`, qui suffit pour
  `admissionFold`, `BudgetGatedIndep.cone_commutation_invariant`) ne suffit plus : le crédit
  amont `π(a.1)` lit les arêtes admises en amont de `a.1`, donc admettre `b` peut changer le
  test de `a` si `b.2` est en amont de `a.1`. La relation de commutation porte ici sur un
  graphe GARDE `G` fixé (les transactions potentielles), pas sur l'état admis : c'est une
  vraie relation de Mazurkiewicz (statique, symétrique, irréflexive), pas une trace
  généralisée au sens de Sassone-Nielsen-Winskel (1993) — condition requise pour
  normalisation de Möbius, Cartier-Foata, projection de Zielonka.

  ★ Alphabet = arêtes de `G` (sous-type `GEdge G`), pas `V × V` : la commutation exige que
  le PRÉFIXE entier vive dans `G` (`h_guard`), ce qu'aucune condition sur la seule paire
  `(a, b)` ne garantit. Sur `List (V × V)` le quotient par `I_LP` ne descendrait pas.

  ★ Portée honnête : si `G` est fortement connexe (circulation monétaire typique),
  `I_LP` est VIDE (`I_LP_empty_of_strongly_connected`) et M(G, I_LP) est le monoïde libre :
  sous la lecture crédit, l'ordre compte alors pour TOUTE paire. `I_LP` et `edge_indep`
  sont incomparables (`edge_indep` ⊄ `I_LP` : témoin de PivotPotential ; `I_LP` ⊄
  `edge_indep` : récepteur partagé, `I_LP_not_imp_edge_indep`).
-/

import Mathlib.Tactic
import ThesePlanetaire.PivotPotential
import ThesePlanetaire.BudgetGatedIndep
import ThesePlanetaire.GatedStep

namespace PivotCommutation

open DualDAG (FuturePool vertex_load admissionFoldP)
open BudgetGatedIndep (vertex_load_insert_other)
open PivotPotential
open GatedStep (union_singleton_comm insertStep_comm foldl_swap_of_step_comm)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Pas élémentaire et invariant de garde -/

/-- Pas test-and-keep du fold pivot (defeq à la lambda d'`admissionFoldP`). -/
def pivotStep (pool : FuturePool V) (demands : V × V → ℤ) :
    ActivationState V → V × V → ActivationState V :=
  fun cur e => if pivotAdmissible pool demands cur e then cur ∪ {e} else cur

lemma pivotAdmissionFold_eq_foldl (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    pivotAdmissionFold pool demands edges = edges.foldl (pivotStep pool demands) ∅ := rfl

/-- Le fold n'admet que des lettres lues : partant d'un état dans `target`, il y reste si
    toutes les lettres y sont. -/
lemma foldl_pivotStep_subset (pool : FuturePool V) (demands : V × V → ℤ)
    (target : Finset (V × V)) :
    ∀ (l : List (V × V)) (cur : ActivationState V), cur ⊆ target → (∀ e ∈ l, e ∈ target) →
      l.foldl (pivotStep pool demands) cur ⊆ target
  | [], _, h_cur, _ => h_cur
  | e :: l, cur, h_cur, h_l => by
    simp only [List.foldl_cons]
    refine foldl_pivotStep_subset pool demands target l _ ?_ (fun x hx => h_l x (.tail e hx))
    unfold pivotStep
    split
    · exact Finset.union_subset h_cur (Finset.singleton_subset_iff.mpr (h_l e (.head l)))
    · exact h_cur

/-- Sous la garde, l'état admis reste dans `G`. -/
lemma pivotAdmissionFold_subset_of_guard (G : DirectedGraph V) (pool : FuturePool V)
    (demands : V × V → ℤ) (u : List (V × V)) (h : ∀ e ∈ u, e ∈ G.edges) :
    pivotAdmissionFold pool demands u ⊆ G.edges :=
  foldl_pivotStep_subset pool demands G.edges u ∅ (Finset.empty_subset _) h

/-! ### 2. Commutation du pas (hypothèses sur l'état) -/

/-- Admettre `b` ne change pas le test de `a` si les sources diffèrent (charge en `a.1`
    inchangée, `vertex_load_insert_other`) et si `b.2` n'est pas en amont de `a.1` (crédit
    `π(a.1)` inchangé, `upstreamPotential_insert_eq`). -/
lemma pivotAdmissible_insert_other (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (a b : V × V) (h_src : a.1 ≠ b.1)
    (h_reach : ¬ reachesIn (S ∪ {b}) b.2 a.1) :
    pivotAdmissible pool demands (S ∪ {b}) a ↔ pivotAdmissible pool demands S a := by
  unfold pivotAdmissible
  rw [union_singleton_comm S b a, vertex_load_insert_other demands (S ∪ {a}) b a.1 h_src.symm,
    upstreamPotential_insert_eq demands S b a.1 h_reach]

lemma pivotStep_comm (pool : FuturePool V) (demands : V × V → ℤ) (S : ActivationState V)
    (a b : V × V) (h_src : a.1 ≠ b.1)
    (h_ab : ¬ reachesIn (S ∪ {b}) b.2 a.1) (h_ba : ¬ reachesIn (S ∪ {a}) a.2 b.1) :
    pivotStep pool demands (pivotStep pool demands S a) b =
    pivotStep pool demands (pivotStep pool demands S b) a :=
  insertStep_comm (pivotAdmissible_insert_other pool demands S a b h_src h_ab)
    (pivotAdmissible_insert_other pool demands S b a h_src.symm h_ba)

/-! ### 3. Énoncé de classe — hypothèses STATIQUES sur la garde `G` -/

/-- ★★ Dans tout contexte (préfixe `u`, suffixe `w`) vivant dans le graphe garde `G`,
    échanger `a, b` laisse `pivotAdmissionFold` invariant dès que les sources diffèrent et
    qu'aucune des deux cibles n'est en amont (dans `G`) de la source de l'autre. Les
    hypothèses de non-atteignabilité ne dépendent ni de `pool`, ni de `demands`, ni de
    l'état admis : elles sont relevées à l'état admis par `reachable_mono`, celui-ci restant
    dans `G` (`pivotAdmissionFold_subset_of_guard`). -/
theorem pivot_cone_commutation_invariant (G : DirectedGraph V) (pool : FuturePool V)
    (demands : V × V → ℤ) (u w : List (V × V)) (a b : V × V)
    (h_guard : (∀ e ∈ u, e ∈ G.edges) ∧ a ∈ G.edges ∧ b ∈ G.edges)
    (h_src : a.1 ≠ b.1)
    (h_ab : ¬ Reachable G b.2 a.1)
    (h_ba : ¬ Reachable G a.2 b.1) :
    pivotAdmissionFold pool demands (u ++ a :: b :: w) =
    pivotAdmissionFold pool demands (u ++ b :: a :: w) := by
  simp only [pivotAdmissionFold_eq_foldl]
  have hT : u.foldl (pivotStep pool demands) ∅ ⊆ G.edges :=
    pivotAdmissionFold_subset_of_guard G pool demands u h_guard.1
  have hTa : u.foldl (pivotStep pool demands) ∅ ∪ {a} ⊆ G.edges :=
    Finset.union_subset hT (Finset.singleton_subset_iff.mpr h_guard.2.1)
  have hTb : u.foldl (pivotStep pool demands) ∅ ∪ {b} ⊆ G.edges :=
    Finset.union_subset hT (Finset.singleton_subset_iff.mpr h_guard.2.2)
  exact foldl_swap_of_step_comm _ ∅ u w (pivotStep_comm pool demands _ a b h_src
    (fun h => h_ab (reachable_mono hTb h)) (fun h => h_ba (reachable_mono hTa h)))

/-! ### 4. Amendement A — relation statique `I_LP` -/

/-- Indépendance statique sur le graphe garde `G` : sources distinctes, et aucune cible
    en amont de la source de l'autre. Ne dépend que de `G`. -/
def I_LP (G : DirectedGraph V) (a b : V × V) : Prop :=
  a.1 ≠ b.1 ∧ ¬ Reachable G b.2 a.1 ∧ ¬ Reachable G a.2 b.1

omit [Fintype V] [DecidableEq V] in
theorem I_LP_symm {G : DirectedGraph V} {a b : V × V} (h : I_LP G a b) : I_LP G b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

omit [Fintype V] [DecidableEq V] in
theorem I_LP_irrefl (G : DirectedGraph V) (a : V × V) : ¬ I_LP G a a :=
  fun h => h.1 rfl

omit [Fintype V] [DecidableEq V] in
/-- `I_LP` ⊆ `I_src` (sources distinctes), et exclut aussi `a.1 = b.2`, `a.2 = b.1`
    (via `Reachable.refl`). -/
theorem I_LP_ne {G : DirectedGraph V} {a b : V × V} (h : I_LP G a b) :
    a.1 ≠ b.1 ∧ b.2 ≠ a.1 ∧ a.2 ≠ b.1 :=
  ⟨h.1, fun e => h.2.1 (e ▸ Reachable.refl _), fun e => h.2.2 (e ▸ Reachable.refl _)⟩

omit [Fintype V] [DecidableEq V] in
/-- ★ Limite : sur un graphe garde fortement connexe, `I_LP` est vide (monoïde libre). -/
theorem I_LP_empty_of_strongly_connected (G : DirectedGraph V)
    (h : ∀ u v, Reachable G u v) (a b : V × V) : ¬ I_LP G a b :=
  fun hI => hI.2.1 (h _ _)

/-- `I_LP` n'implique pas `edge_indep` : deux émetteurs vers un même récepteur sans
    successeur commutent sous le pivot. -/
theorem I_LP_not_imp_edge_indep :
    ∃ (G : DirectedGraph (Fin 3)) (a b : Fin 3 × Fin 3),
      I_LP G a b ∧ ¬ EdgeIndependence.edge_indep a b := by
  refine ⟨⟨{(0, 2), (1, 2)}⟩, (0, 2), (1, 2), ⟨by decide, ?_, ?_⟩, by decide⟩
  all_goals
    intro h
    cases h with
    | step _ v _ hv _ => simp at hv

/-! ### 5. Descente au monoïde de traces M(G, I_LP) -/

/-- Alphabet des transactions potentielles : arêtes du graphe garde. -/
abbrev GEdge (G : DirectedGraph V) := {e : V × V // e ∈ G.edges}

/-- Générateurs de la congruence de Mazurkiewicz pour `I_LP` (échange en contexte). -/
inductive LPSwap (G : DirectedGraph V) : List (GEdge G) → List (GEdge G) → Prop
  | swap (u w : List (GEdge G)) (a b : GEdge G) (h : I_LP G a.1 b.1) :
      LPSwap G (u ++ a :: b :: w) (u ++ b :: a :: w)

/-- Monoïde de traces M(G, I_LP) : mots sur `GEdge G` modulo la clôture d'équivalence des
    échanges `I_LP` (gérée par `Quot`/`Quot.sound`). -/
def LPTrace (G : DirectedGraph V) := Quot (LPSwap G)

/-- Concaténation : `LPSwap` est stable par contexte, donc la concaténation descend. -/
def LPTrace.append (G : DirectedGraph V) : LPTrace G → LPTrace G → LPTrace G :=
  Quot.map₂ (· ++ ·)
    (fun l _ _ h => by
      obtain ⟨u, w, a, b, hI⟩ := h
      simpa only [List.append_assoc] using LPSwap.swap (l ++ u) w a b hI)
    (fun _ _ l h => by
      obtain ⟨u, w, a, b, hI⟩ := h
      simpa only [List.append_assoc, List.cons_append] using LPSwap.swap u (w ++ l) a b hI)

/-- ★★ `pivotAdmissionFold` est bien définie sur M(G, I_LP) : `Quot.lift` n'exige que
    l'invariance sous les GÉNÉRATEURS, i.e. `pivot_cone_commutation_invariant`. -/
def pivotAdmissionFoldTrace (G : DirectedGraph V) (pool : FuturePool V)
    (demands : V × V → ℤ) : LPTrace G → ActivationState V :=
  Quot.lift (fun l => pivotAdmissionFold pool demands (l.map Subtype.val)) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    simp only [List.map_append, List.map_cons]
    refine pivot_cone_commutation_invariant G pool demands _ _ a.1 b.1
      ⟨fun e he => ?_, a.2, b.2⟩ hI.1 hI.2.1 hI.2.2
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
    exact x.2)

theorem pivotAdmissionFoldTrace_mk (G : DirectedGraph V) (pool : FuturePool V)
    (demands : V × V → ℤ) (l : List (GEdge G)) :
    pivotAdmissionFoldTrace G pool demands (Quot.mk _ l) =
      pivotAdmissionFold pool demands (l.map Subtype.val) := rfl

end PivotCommutation
