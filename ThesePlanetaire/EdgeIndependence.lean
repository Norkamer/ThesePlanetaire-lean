/-
  ThesePlanetaire/EdgeIndependence.lean
  Relation d'indépendance vertex-sharing sur les arêtes du DualDAG.

  Deux arêtes sont vertex-sharing-indépendantes si elles ne partagent aucun sommet
  (ni source, ni cible). C'est la relation de Mazurkiewicz utilisée dans
  foata_height (Python, curvature.py) sur les ActivationState.

  dep_neighbors_card_decomp : les voisins dépendants de (u,v) excluant (u,v) se
  décomposent exactement en 4 filtres disjoints. F_simp n'utilise que A+B.
-/
import ThesePlanetaire.DualDAG
import Mathlib.Tactic

open Finset DualDAG

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace EdgeIndependence

/-- Deux arêtes sont indépendantes si elles ne partagent aucun sommet. -/
def edge_indep (e1 e2 : V × V) : Prop :=
  e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2

instance (e1 e2 : V × V) : Decidable (edge_indep e1 e2) := by
  unfold edge_indep; exact inferInstance

theorem edge_indep_symm (e1 e2 : V × V) (h : edge_indep e1 e2) : edge_indep e2 e1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩

theorem edge_indep_irrefl (e : V × V) : ¬ edge_indep e e := by
  simp [edge_indep]

/-! ### Décomposition des voisins dépendants

  Les voisins vertex-sharing-dépendants de (u,v) dans S, excluant (u,v) lui-même,
  se décomposent exactement en 4 filtres disjoints.
  F_simp n'utilise que les filtres A (outdeg_excl_v) et B (indeg_excl_u). -/

/-- Décomposition exacte en 4 filtres disjoints des voisins dépendants de (u,v). -/
theorem dep_neighbors_card_decomp
    (S : ActivationState V) (u v : V) :
    (S.filter (fun f => ¬ edge_indep (u, v) f ∧ f ≠ (u, v))).card =
    (S.filter (fun f => f.1 = u ∧ f.2 ≠ v)).card +              -- A : outdeg_excl_v
    (S.filter (fun f => f.1 ≠ u ∧ f.2 = v)).card +              -- B : indeg_excl_u
    (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u)).card +   -- C : incl_u
    (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v)).card := by  -- D : out_v
  -- Étape 1 : égalité ensembliste dep = A ∪ B ∪ C ∪ D
  have hset : S.filter (fun f => ¬ edge_indep (u, v) f ∧ f ≠ (u, v)) =
      S.filter (fun f => f.1 = u ∧ f.2 ≠ v) ∪
      S.filter (fun f => f.1 ≠ u ∧ f.2 = v) ∪
      S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u) ∪
      S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_union, edge_indep, ne_eq,
               Prod.ext_iff, not_and_or, not_not]
    tauto
  -- Étape 2 : 6 preuves de disjointance
  have hAB : Disjoint (S.filter (fun f => f.1 = u ∧ f.2 ≠ v))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 = v)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨h, _⟩ ⟨h', _⟩ => h' h)
  have hAC : Disjoint (S.filter (fun f => f.1 = u ∧ f.2 ≠ v))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨h, _⟩ ⟨h', _, _⟩ => h' h)
  have hAD : Disjoint (S.filter (fun f => f.1 = u ∧ f.2 ≠ v))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨h, _⟩ ⟨h', _, _, _⟩ => h' h)
  have hBC : Disjoint (S.filter (fun f => f.1 ≠ u ∧ f.2 = v))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨_, h⟩ ⟨_, h', _⟩ => h' h)
  have hBD : Disjoint (S.filter (fun f => f.1 ≠ u ∧ f.2 = v))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨_, h⟩ ⟨_, h', _, _⟩ => h' h)
  have hCD : Disjoint (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u))
                      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v)) :=
    Finset.disjoint_filter.mpr (fun f _ ⟨_, _, h⟩ ⟨_, _, h', _⟩ => h' h)
  -- Étape 3 : card_union_of_disjoint ×3
  have hABC_D : Disjoint
      (S.filter (fun f => f.1 = u ∧ f.2 ≠ v) ∪
       S.filter (fun f => f.1 ≠ u ∧ f.2 = v) ∪
       S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u))
      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 ≠ u ∧ f.1 = v)) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩, hCD⟩
  have hAB_C : Disjoint
      (S.filter (fun f => f.1 = u ∧ f.2 ≠ v) ∪
       S.filter (fun f => f.1 ≠ u ∧ f.2 = v))
      (S.filter (fun f => f.1 ≠ u ∧ f.2 ≠ v ∧ f.2 = u)) :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  rw [hset,
      Finset.card_union_of_disjoint hABC_D,
      Finset.card_union_of_disjoint hAB_C,
      Finset.card_union_of_disjoint hAB]

/-- Les degrés de F_simp (outdeg_excl_v + indeg_excl_u) ne comptent que les filtres A et B,
    sous-ensemble strict des voisins dépendants. -/
lemma forman_degrees_le_dep_count
    (S : ActivationState V) (u v : V) :
    (S.filter (fun f => f.1 = u ∧ f.2 ≠ v)).card +
    (S.filter (fun f => f.1 ≠ u ∧ f.2 = v)).card
    ≤ (S.filter (fun f => ¬ edge_indep (u, v) f ∧ f ≠ (u, v))).card := by
  rw [dep_neighbors_card_decomp S u v]; omega

end EdgeIndependence
