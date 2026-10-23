/-
  MonnaiesEndogene/WeightedAutomaton.lean
  Automate fini valué dans un dioïde K (Weighted Finite Automaton).

  Structure générique sur [Dioid K]. Les instanciations naturelles :
  - K = Bool      → NFA classique (D4)
  - K = Z_max     → valuation max-plus (D1)
  - K = Z_min     → valuation min-plus (D2)

  D3 (Sign) N'EST PAS un dioïde → pas d'instance WFA pour Sign.
  La contrainte transverse utilise CumulativeNonNegative (Signe.lean).
-/

import ThesePlanetaire.Basic
import ThesePlanetaire.Dioid

open Dioid

/-! ### Chemin dans un automate -/

inductive WFAPath (σ α : Type _) : Type _ where
  | mk (s : σ) : WFAPath σ α
  | extend (p : WFAPath σ α) (a : α) (t : σ) : WFAPath σ α
  deriving Repr

namespace WFAPath

variable {σ α : Type _}

def last : WFAPath σ α → σ
  | mk s => s
  | extend _ _ t => t

end WFAPath

/-! ### Automate fini valué pondéré -/

structure WeightedAutomaton (K : Type _) [Semiring K] (α : Type _) (σ : Type _) where
  init : σ → K
  trans : σ → α → σ → K
  final : σ → K

namespace WeightedAutomaton

variable {K : Type _} [Semiring K] {α σ : Type _}

/-- Poids d'un chemin = init(start) × (∏ trans) × final(last). -/
def path_weight (wfa : WeightedAutomaton K α σ) : WFAPath σ α → K
  | WFAPath.mk s => wfa.init s * wfa.final s
  | WFAPath.extend p a t => path_weight wfa p * wfa.trans (WFAPath.last p) a t * wfa.final t

section Fintype

variable [Fintype σ] [DecidableEq σ]

/-- Poids d'un mot par programmation dynamique.
    On maintient un vecteur `state_weight : σ → K` donnant le poids
    de tous les chemins aboutissant à chaque état après lecture du préfixe.

    Complexité O(|σ|²·|w|), évite l'énumération exponentielle des chemins. -/
def word_weight (wfa : WeightedAutomaton K α σ) (w : List α) : K :=
  -- poids initial : init(s) pour chaque état s
  let start_weights : σ → K := wfa.init
  -- Après lecture de w, poids accumulé par état
  let final_weights : σ → K :=
    List.foldl (λ (weights : σ → K) (a : α) =>
      λ (t : σ) =>
        Finset.sum (Finset.univ : Finset σ) (λ (s : σ) =>
          weights s * wfa.trans s a t))
      start_weights
      w
  -- Somme finale : pondérer par final(t)
  Finset.sum (Finset.univ : Finset σ) (λ (t : σ) => final_weights t * wfa.final t)

/-- Un mot est accepté si son poids est ≠ 0. -/
def accepts (wfa : WeightedAutomaton K α σ) (w : List α) : Prop :=
  word_weight wfa w ≠ 0

end Fintype

/-! ### Construction canonique : WFA booléen d'un graphe -/

/-- WFA booléen d'un graphe (V, E). Tout sommet est initial et final.
    Les arêtes sont les transitions de poids `true`. -/
def ofGraph (V : Type _) [Fintype V] [DecidableEq V] (E : V → V → Bool) :
    WeightedAutomaton Bool V V where
  init _ := true
  trans u _ v := E u v
  final _ := true

end WeightedAutomaton
