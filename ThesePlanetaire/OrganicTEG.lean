/-
  MonnaiesEndogene/OrganicTEG.lean
  Phase 2 (v3) : TEG monétaire enrichi avec garde réglementaire.

  Architecture v3 (post-analyse critique O1–O7) :
  - Alphabet = arêtes du graphe (V × V), pas Letter × Fin 3 (infini)
  - État = sommets V (comme dans BridgeRegex.valuationWFA)
  - Enrichit BridgeRegex.valuationWFA avec garde + end-anchor + holding_time
  - holding_time sur les transitions (V → V → Z_max), pas sur les lettres
  - Pas d'import de InfiniteTraceSpace ni ExtensionInfinie
  - Score social IMPLICITE : aucune variable `social_score` explicite dans ce
    module (le score émerge du shadow price λ_soc dans OrganicLP.lean, Phase 4)

  Références : Baccelli–Cohen–Olsder–Quadrat (1992), Ch. 2 ;
  Brunsch–Raisch–Hardouin–Boutin (2013), Ch. 4.
-/

import ThesePlanetaire.Basic
import ThesePlanetaire.BridgeRegex
import ThesePlanetaire.EndAnchor

namespace OrganicTEG

open BridgeRegex WeightedAutomaton EndAnchor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Garde réglementaire sur les transitions

    Un `RegulatoryGuard` est un sous-ensemble d'arêtes autorisées.
    C'est la sémantique de la réglementation (EU Taxonomy, frontières
    planétaires) appliquée au graphe monétaire. -/

/-- Garde réglementaire : sous-ensemble d'arêtes autorisées. -/
structure RegulatoryGuard (V : Type*) [DecidableEq V] where
  allowedEdges : Finset (V × V)
  h_non_empty : allowedEdges.Nonempty

/-! ### 2. TEG organique : graphe monétaire enrichi

    Le TEG organique enrichit le `LoopfreeDigraph` existant avec :
    - cash_flow (cash-flow par sommet, comme dans BridgeRegex)
    - guard (garde réglementaire sur les arêtes)
    - end_anchor (contrainte terminale sur les arêtes)
    - holding_time (temps de détention par transition, max-plus)

    NOTE : aucun score social explicite ici. Le score social est une
    propriété IMPLICITE (émerge du shadow price λ_soc dans le LP, Phase 4),
    conformément au modèle CapsPapers (social_score_implicit_demo.py).
    Voir plan_organic_teg_lp.md §Phase 4 (v3). -/

/-- TEG monétaire organique : graphe enrichi avec contraintes réglementaires. -/
structure OrganicTEG (V : Type*) [Fintype V] [DecidableEq V] where
  graph : LoopfreeDigraph V
  cash_flow : V → ℤ
  guard : RegulatoryGuard V
  end_anchor : EndAnchor (V × V)
  holding_time : V → V → Z_max

/-! ### 3. WFA max-plus organique

    Le WFA organique est le `valuationWFA` de BridgeRegex enrichi avec
    la garde réglementaire. Seules les arêtes dans `guard.allowedEdges`
    ont un poids fini (holding_time) ; toutes les autres ont `-∞`.

    C'est un enrichissement, pas une réinvention : on réutilise la
    structure `WeightedAutomaton Z_max (V × V) V` de BridgeRegex. -/

/-- WFA max-plus du TEG organique.
    Alphabet = arêtes (V × V). État = sommets V.
    Transition : poids fini ssi l'arête est autorisée et exacte. -/
def organicValuationWFA (teg : OrganicTEG V) : WeightedAutomaton Z_max (V × V) V where
  init _ := Z_max.ofInt 0
  trans u e v :=
    if e ∈ teg.guard.allowedEdges ∧ u = e.1 ∧ v = e.2 then teg.holding_time u v else Z_max.negInf
  final _ := Z_max.ofInt 0

/-! ### 4. Chemins continus et gardés

    Un chemin est continu si chaque arête commence où la précédente finit.
    Il est gardé si toutes ses arêtes sont dans `guard.allowedEdges`. -/

/-- Un mot sur les arêtes est un chemin continu si les extrémités
    se succèdent. -/
def isContinuousPath : List (V × V) → Prop
  | [] => True
  | [_] => True
  | e1 :: e2 :: w => e1.2 = e2.1 ∧ isContinuousPath (e2 :: w)

/-- Un chemin est gardé s'il est continu et toutes ses arêtes sont autorisées. -/
def isGuardedPath (teg : OrganicTEG V) (w : List (V × V)) : Prop :=
  isContinuousPath w ∧ ∀ e ∈ w, e ∈ teg.guard.allowedEdges

/-! ### 5. Trace valide

    Une trace valide est :
    1. un chemin dans le graphe (accepté par le WFA booléen)
    2. toutes les arêtes sont autorisées par la garde
    3. la dernière arête satisfait l'end-anchor -/

/-- Prédicat : le mot est une trace valide du TEG organique. -/
def isValidTEGTrace (teg : OrganicTEG V) (w : List (V × V)) : Prop :=
  isContinuousPath w ∧
  (∀ e ∈ w, e ∈ teg.graph.edges) ∧
  (∀ e ∈ w, e ∈ teg.guard.allowedEdges) ∧
  satisfiesEndAnchor teg.end_anchor w

/-! ### 6. Théorèmes de base -/

/-- Théorème : la garde réglementaire est non vide. -/
theorem organic_teg_guard_nonempty (teg : OrganicTEG V) :
    teg.guard.allowedEdges.Nonempty :=
  teg.guard.h_non_empty

/-- Théorème : toute trace valide a toutes ses arêtes dans la garde. -/
theorem valid_trace_implies_guarded (teg : OrganicTEG V) (w : List (V × V))
    (h : isValidTEGTrace teg w) :
    ∀ e ∈ w, e ∈ teg.guard.allowedEdges :=
  h.2.2.1

/-- Théorème : toute trace valide satisfait l'end-anchor. -/
theorem valid_trace_implies_end_anchor (teg : OrganicTEG V) (w : List (V × V))
    (h : isValidTEGTrace teg w) :
    satisfiesEndAnchor teg.end_anchor w :=
  h.2.2.2

/-- Lemme : si l'arête n'est pas autorisée, la transition du WFA
    organique est `-∞`. -/
lemma trans_organic_negInf_of_not_allowed (teg : OrganicTEG V) (u : V) (e : V × V) (v : V)
    (h : e ∉ teg.guard.allowedEdges) :
    (organicValuationWFA teg).trans u e v = Z_max.negInf := by
  unfold organicValuationWFA
  simp [h]

/-- Lemme : si l'état source ou cible ne correspond pas à l'arête,
    la transition est `-∞`. -/
lemma trans_organic_negInf_of_mismatch (teg : OrganicTEG V) (u : V) (e : V × V) (v : V)
    (h : u ≠ e.1 ∨ v ≠ e.2) :
    (organicValuationWFA teg).trans u e v = Z_max.negInf := by
  unfold organicValuationWFA
  cases h with
  | inl h1 => simp [h1]
  | inr h2 => simp [h2]

/-- Lemme : la transition du WFA organique est finie ssi l'arête est
    exactement `(u,v)` et autorisée. -/
lemma trans_organic_finite_eq (teg : OrganicTEG V) (u : V) (e : V × V) (v : V)
    (h_guard : e ∈ teg.guard.allowedEdges) (h_eq : u = e.1 ∧ v = e.2) :
    (organicValuationWFA teg).trans u e v = teg.holding_time u v := by
  unfold organicValuationWFA
  simp [h_guard, h_eq]

/-- Théorème : si une arête est autorisée et exacte, la transition du
    WFA organique retourne exactement le holding_time.
    C'est le pont entre la garde réglementaire et la valuation max-plus. -/
theorem trans_organic_eq_holding_time (teg : OrganicTEG V) (u v : V)
    (h_guard : (u, v) ∈ teg.guard.allowedEdges) :
    (organicValuationWFA teg).trans u (u, v) v = teg.holding_time u v := by
  unfold organicValuationWFA
  simp [h_guard]

/-- Théorème : l'end-anchor du TEG est non vide (existence d'au moins
    une arête terminale autorisée). -/
theorem organic_teg_end_anchor_nonempty (teg : OrganicTEG V) :
    teg.end_anchor.terminalLetters.Nonempty :=
  teg.end_anchor.h_non_empty

/-- Théorème : la composition de la garde et de l'end-anchor est
    cohérente — l'intersection de `guard.allowedEdges` et
    `end_anchor.terminalLetters` est non vide si les deux sont compatibles.
    C'est un prérequis pour l'existence de traces valides. -/
theorem guard_and_anchor_compatible (teg : OrganicTEG V)
    (h_compat : teg.guard.allowedEdges ∩ teg.end_anchor.terminalLetters ≠ ∅) :
    ∃ e, e ∈ teg.guard.allowedEdges ∧ e ∈ teg.end_anchor.terminalLetters := by
  have h : (teg.guard.allowedEdges ∩ teg.end_anchor.terminalLetters).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact h_compat
  rcases h with ⟨e, he⟩
  simp at he
  exact ⟨e, he⟩

/-- Théorème : toute trace non vide a une dernière arête. -/
theorem valid_trace_last_edge (teg : OrganicTEG V) (w : List (V × V))
    (h : isValidTEGTrace teg w) (h_ne : w ≠ []) :
    ∃ e, e ∈ w ∧ e ∈ teg.end_anchor.terminalLetters := by
  have h_anchor : satisfiesEndAnchor teg.end_anchor w := h.2.2.2
  cases w with
  | nil => contradiction
  | cons a l =>
    have h_last : lastLetter (a :: l) = some ((a :: l).getLast (List.cons_ne_nil a l)) := by
      simp [lastLetter]
    use (a :: l).getLast (List.cons_ne_nil a l)
    constructor
    · exact List.getLast_mem (List.cons_ne_nil a l)
    · unfold satisfiesEndAnchor at h_anchor
      simp [h_last] at h_anchor
      exact h_anchor

end OrganicTEG
