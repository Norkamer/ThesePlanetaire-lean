/-
  MonnaiesEndogene/Basic.lean
  Core definitions for VT-GRE-EXT formalization:
  - Directed graph (DAG) on finite edge set
  - Once-only monoid (activation set)
  - Forest E \ M_p
  - Class decomposition (DCM)
  - Strongly connected component condition (H-ENR / EN01)
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Rank.ENat

-- Placeholder: finite edge set
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A directed graph on vertices V with edge set E ⊆ V × V -/
structure DirectedGraph (V : Type*) where
  edges : Finset (V × V)

/-- A directed graph with no self-loops -/
structure LoopfreeDigraph (V : Type*) extends DirectedGraph V where
  no_loops : ∀ v, (v, v) ∉ edges

/-- The matching M_p ⊆ E (perfect matching on the bipartite graph) -/
structure Matching (V : Type*) extends DirectedGraph V where
  is_matching : True  -- TODO: formalize matching property

/-- Forest F = E \ M_p — the complement of the matching in the edge set -/
def forest_edges (G : DirectedGraph V) (M : Matching V) : Finset (V × V) :=
  G.edges \ M.edges

/-- The once-only activation state: a Finset of activated edges.
    Using `abbrev` (transparent) so Lean inherits all Finset instances.
    With ∪ and ∅, this is the once-only (idempotent commutative) monoid:
    re-adding an already-activated edge is a no-op (∪ is idempotent). -/
abbrev ActivationState (V : Type*) [DecidableEq V] := Finset (V × V)

-- Phase 23 L2: Dom_eff as filter on activation states (proof_critic Phase 23)
section DomEff

/-- Dom_eff(S₀): activation states that extend baseline S₀.
    Principal filter ↑S₀ in the Finset lattice. -/
def DomEff {V : Type*} [DecidableEq V]
    (S₀ : Finset (V × V)) (S : Finset (V × V)) : Prop :=
  S₀ ⊆ S

/-- Dom_eff is closed under union (join in the lattice). -/
lemma domEff_sup_closed {V : Type*} [DecidableEq V]
    (S₀ S₁ S₂ : Finset (V × V))
    (h₁ : DomEff S₀ S₁) (_ : DomEff S₀ S₂) :
    DomEff S₀ (S₁ ∪ S₂) :=
  h₁.trans Finset.subset_union_left

/-- Dom_eff is closed under intersection (meet in the lattice). -/
lemma domEff_inf_closed {V : Type*} [DecidableEq V]
    (S₀ S₁ S₂ : Finset (V × V))
    (h₁ : DomEff S₀ S₁) (h₂ : DomEff S₀ S₂) :
    DomEff S₀ (S₁ ∩ S₂) :=
  Finset.subset_inter h₁ h₂

/-- Reflexivity: baseline is in Dom_eff. -/
lemma domEff_refl {V : Type*} [DecidableEq V]
    (S₀ : Finset (V × V)) : DomEff S₀ S₀ :=
  Finset.Subset.refl S₀

/-- Once-only monotonicity: activation states grow monotonically (EXT1). -/
lemma domEff_once_only_chain {V : Type*} [DecidableEq V]
    (states : ℕ → Finset (V × V))
    (h_grow : ∀ t, states t ⊆ states (t + 1))
    : ∀ t₀ t : ℕ, t₀ ≤ t → DomEff (states t₀) (states t) := by
  intro t₀ t h
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (h_grow _)

end DomEff

/-- Activation count under once-only semantics: 0 if not activated, 1 if activated.
    Count is always ≤ 1 by construction — the once-only monoïd property. -/
def activation_count {V : Type*} [DecidableEq V]
    (state : ActivationState V) (e : V × V) : ℕ :=
  if e ∈ state then 1 else 0

/-- The once-only property: activation count is always ≤ 1. -/
theorem activation_count_once_only {V : Type*} [DecidableEq V]
    (state : ActivationState V) (e : V × V) :
    activation_count state e ≤ 1 := by
  unfold activation_count
  by_cases h : e ∈ state <;> simp [h]

/-- Convert a loopfree directed graph to a simple (undirected) graph -/
noncomputable def LoopfreeDigraph.toSimpleGraph (G : LoopfreeDigraph V) : SimpleGraph V where
  Adj u v := (u, v) ∈ G.edges ∨ (v, u) ∈ G.edges
  symm := fun {u v} h => by rcases h with h | h; exact Or.inr h; exact Or.inl h
  loopless := ⟨fun {v} h => by rcases h with h | h <;> exact absurd h (G.no_loops v)⟩

/-- Decidability of adjacency in the symmetrized graph -/
instance (G : LoopfreeDigraph V) :
    DecidableRel G.toSimpleGraph.Adj :=
  fun _ _ => instDecidableOr

/-- k(t) = number of connected components in the underlying undirected forest.
    Requires the forest graph to be loopfree (which it is, since forest edges
    connect distinct vertices in bipartite matching complements). -/
noncomputable def num_components (G : LoopfreeDigraph V) : ℕ :=
  Fintype.card G.toSimpleGraph.ConnectedComponent

/-- EXT-3 target: k(t) is monotonically non-increasing under R2/R3 dynamics.
    This is a definitional placeholder — the real content is in EXT3.lean
    where k is abstracted as a ℕ → ℕ function with explicit hypotheses. -/
theorem k_monotone_decreasing : True := trivial

/-- Reachable u v g : there exists a directed path from u to v in graph g.

    `refl` : every vertex reaches itself (empty path).
    `step` : if there is an edge u → v in g, and v can reach w,
             then u can reach w (prepend one edge). -/
inductive Reachable {V : Type*} (g : DirectedGraph V) : V → V → Prop where
  | refl : ∀ (u : V), Reachable g u u
  | step : ∀ (u v w : V), (u, v) ∈ g.edges → Reachable g v w → Reachable g u w

/-- H-ENR (EN01): Every strongly connected component of the activation graph
    has at least one node with positive external cash-flow.
    ∀ S ⊊ G_R, ∃ i ∈ S, e_i > 0.

    Modeled as: for every nonempty proper subset S of vertices that is
    closed under outgoing edges (SCC-like), some vertex has positive cash flow. -/
def h_enr (G : DirectedGraph V) (cash_flow : V → ℤ) : Prop :=
  ∀ (S : Finset V),
    S.Nonempty →
    S ⊂ Finset.univ →
    (∀ u ∈ S, ∀ v, (u, v) ∈ G.edges → v ∈ S) →
    ∃ i ∈ S, cash_flow i > 0

-- Phase 24 L3: Dom_eff as UpperSet — CompleteLattice instance
-- lean4_prover Phase 24: UpperSet.Ici route (diamond-free vs Subtype+Fintype route)
-- Mathlib: Mathlib.Order.UpperLower.CompleteLattice (UpperSet.instCompleteLattice)
section DomEffCompleteLattice

/-- Dom_eff(S₀) as a principal upper set under ⊆-order.
    UpperSet.instCompleteLattice provides CompleteLattice automatically.
    Avoids diamond risk from Fintype.toCompleteLattice (Mathlib warning line 124). -/
def DomEff_upper {V : Type*} [DecidableEq V]
    (S₀ : Finset (V × V)) : UpperSet (Finset (V × V)) :=
  UpperSet.Ici S₀

/-- Bridge: membership in DomEff_upper S₀ is exactly DomEff S₀ S. -/
lemma domEff_upper_iff {V : Type*} [DecidableEq V]
    (S₀ S : Finset (V × V)) :
    S ∈ DomEff_upper S₀ ↔ DomEff S₀ S :=
  Iff.rfl

end DomEffCompleteLattice

-- Phase 24 L4: Linear Resource Bridge — structural annotation EXT1 ↔ Girard 1987
-- lean4_prover Phase 24: custom LinearResource typeclass (NOT Mathlib.LinearMap which
-- captures algebraic linearity R-modules, categorically distinct from Girard resource linearity)
-- [REPRÉSENTATION — lambda_linear_ext1.md §1, credence 0.92]
section LinearResourceBridge

/-- LinearResource: typeclass for resources consumed at most once.
    Structural bridge EXT1 once-only ↔ variable linéaire Girard (1987).
    A ⊸ B in linear logic = A consumed exactly once.
    This is a REPRESENTATIONAL annotation — does not add new proofs. -/
class LinearResource (α : Type*) where
  consumeCount : α → ℕ
  once_only : ∀ a, consumeCount a ≤ 1

/-- EXT1 activation states satisfy LinearResource:
    activation_count ∈ {0,1} directly witnesses the Girard linear variable constraint. -/
instance linearResourceActivation {V : Type*} [DecidableEq V] :
    LinearResource (ActivationState V × (V × V)) where
  consumeCount := fun ⟨state, e⟩ => activation_count state e
  once_only    := fun ⟨state, e⟩ => activation_count_once_only state e

end LinearResourceBridge

section GraphicMatroidBridge

/-- Matroïde "libre" (free) sur V×V : tout sous-ensemble est indépendant.
    Approximation conservatrice pour Phase 48 — bridge conceptuel vers eRk_submod.
    Raffinement futur : matroïde graphique réel (I acyclique ⇔ G[I] forêt). -/
noncomputable def forestMatroid (m : ℕ) : Matroid (Fin m × Fin m) :=
  Matroid.freeOn (Set.univ)

/-- Rang du forestMatroid sur S = cardinalité de S (en ℕ∞). -/
lemma forestMatroid_eRk_eq (m : ℕ) (S : Set (Fin m × Fin m)) :
    (forestMatroid m).eRk S = S.encard := by
  simp [forestMatroid, Matroid.eRk_freeOn (Set.subset_univ S)]

end GraphicMatroidBridge

/- ### GRE26 Phase 0 : séparation des régimes Normal / Omega

    La formalisation GRE26 requiert une séparation stricte entre :
    - RegimeNormal : espace fini, once-only, closure-first (théorème-pont)
    - RegimeOmega  : espace infini, liveness-sensitive, dépend du pont fini/infini

    Aucun théorème ne doit quantifier sur les deux régimes sans nommer
    explicitement le pont comme lemme séparé. -/

section GRE26Regimes

/-- RegimeNormal : graphe dirigé sans boucle avec out-degree ≤ 1
    et cash-flow positif sur tous les sommets (condition W5 simplifiée). -/
def RegimeNormal (G : LoopfreeDigraph V) (cash_flow : V → ℤ) : Prop :=
  (∀ v, (Finset.filter (fun (x, _) => x = v) G.edges).card ≤ 1) ∧
   (∀ v, cash_flow v > 0)

/-- RegimeOmega : complémentaire de RegimeNormal — tout graphe non-normal.
    C'est une condition existentielle : ∃ v, out-degree > 1 ∨ cash_flow ≤ 0. -/
def RegimeOmega (G : LoopfreeDigraph V) (cash_flow : V → ℤ) : Prop :=
  ¬ RegimeNormal G cash_flow

/-- Les deux régimes sont disjoints par construction. -/
lemma regime_disjoint (G : LoopfreeDigraph V) (cash_flow : V → ℤ) :
    ¬ (RegimeNormal G cash_flow ∧ RegimeOmega G cash_flow) := by
  unfold RegimeOmega
  tauto

/-- Extraction du sous-graphe souverain : sommets avec cash_flow > 0.
    La restriction souveraine est le support de l'ancre. -/
def sovereign_vertices (cash_flow : V → ℤ) : Finset V :=
  Finset.filter (fun v => cash_flow v > 0) Finset.univ

/-- Sous-graphe souverain : restriction du DAG aux sommets avec cash_flow > 0. -/
def sovereign_restriction (G : LoopfreeDigraph V) (cash_flow : V → ℤ)
    : DirectedGraph V where
  edges := G.edges.filter (fun (u, v) => cash_flow u > 0 ∧ cash_flow v > 0)

end GRE26Regimes
