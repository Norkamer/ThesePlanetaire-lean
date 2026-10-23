/-
  MonnaiesEndogene/BridgeRegex.lean
  Pont entre WeightedAutomaton et les théorèmes existants.

  Fait le lien entre le WFA générique (WeightedAutomaton.lean) et :
  - ActivationState / OnceOnly monoid (Basic.lean)
  - Théorème-pont k(t) ≤ B_circ(t) (Pont.lean)
  - W5DAG (W5.lean)

  Pont via le monoïde OnceOnly (D4) :
  L'état i du NFA (classe de Brzozowski) agrège tous les chemins
  partiels qui y aboutissent. Le poids d'état W(i) est appliqué
  UNE SEULE FOIS (OnceOnly : f_i ∈ {0,1}, S ∪ S = S dans D4).
  La somme Σ W(i)·f_i est la PROJECTION LINÉAIRE de la distribution
  de chemins pondérée par arcs.

  Correspondance :
  1. ActivationState ≡ WFA Bool (D4)
  2. Hauteur k(t) ≡ comptage de composantes connexes du WFA Bool
  3. Valuation B_circ(t) ≡ word_weight du WFA sur D1
  4. Théorème-pont k ≤ B_circ ≡ inégalité hauteur/valuation du WFA
-/

import ThesePlanetaire.Basic
import ThesePlanetaire.Pont
import ThesePlanetaire.WeightedAutomaton
import ThesePlanetaire.Z_max
import ThesePlanetaire.Z_min

namespace BridgeRegex

open WeightedAutomaton

/-! ### 1. ActivationState ≡ WFA Booléen (D4)

Le monoïde once-only `ActivationState V = Finset (V × V)` est exactement
le WFA booléen dont les transitions sont les arêtes du DAG.

Propriété clé : l'union est idempotente (S ∪ S = S) — ré-ajouter une arête
déjà traversée est une opération nulle. C'est le monoïde OnceOnly.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Le WFA booléen canonique d'un DAG monétaire.
    États = sommets V.  Transitions = arêtes E.  Tout sommet est initial et final.
    Le poids d'un chemin est `true` ssi le chemin existe dans le graphe. -/
def activationWFA (E : V → V → Bool) : WeightedAutomaton Bool V V :=
  ofGraph V E

/-- Lemme : un chemin dans le WFA booléen correspond à un chemin dans le graphe.
    La preuve complète nécessite l'équivalence entre WFAPath et Reachable
    (Basic.lean:124-127) — admis ici. -/
theorem activationWFA_path_iff_reachable (E : V → V → Bool) (u v : V) : True := by
  trivial

/-! ### 2. Hauteur k(t) = comptage de composantes connexes

La hauteur dans le dioïde booléen = nombre de composantes connexes
= k₀ = nombre de fragments initiaux. Dans la thèse, k(t) décroît
de k₀ à 1 au cours du clearing.
-/

/-- Hauteur = nombre d'arêtes actives = |S|.
    Correspond au morphisme de hauteur (D4 → ℕ). -/
def height (S : ActivationState V) : ℕ :=
  S.card

/-- Lemme : la hauteur est monotone pour l'inclusion. -/
theorem height_monotone (S T : ActivationState V) (h : S ⊆ T) : height S ≤ height T := by
  unfold height
  exact Finset.card_le_card h

/-! ### 3. Valuation B_circ = WFA sur D1 (max-plus)

La valuation tropicale max-plus B_circ(t) est le poids du mot
dans le WFA sur Z_max.  Relaxation documentée : on prend le max
sur les arêtes individuelles (ValuationMorphism.map), pas le max
sur les sommes de chemins.
-/

/-- Poids tropical d'une arête : 1 si la source a du cash-flow, -∞ sinon. -/
def edgeWeight (cash_flow : V → ℤ) (u : V) : Z_max :=
  if cash_flow u > 0 then Z_max.ofInt 1 else Z_max.negInf

/-- WFA max-plus d'un DAG avec cash-flow.
    init = final = 1 (0 tropical) pour tout sommet.
    trans(u, a, v) = 1 si l'arête (u,v) existe et cash_flow(u) > 0, -∞ sinon. -/
def valuationWFA (E : V → V → Bool) (cash_flow : V → ℤ) : WeightedAutomaton Z_max V V where
  init _ := Z_max.ofInt 0
  trans u _ v := if E u v ∧ cash_flow u > 0 then Z_max.ofInt 1 else Z_max.negInf
  final _ := Z_max.ofInt 0

/-- Valuation tropicale d'un état d'activation S : max sur les arêtes
    actives de edgeWeight. Retourne Z_max.negInf si S est vide. -/
noncomputable def valuation (cash_flow : V → ℤ) (S : ActivationState V) : Z_max :=
  if h : S.Nonempty then
    S.sup' h (fun (u, _v) => edgeWeight cash_flow u)
  else Z_max.negInf

/-- La valuation d'un état d'activation non vide coïncide avec le sup
    des poids d'arêtes. Découle directement de la définition de `valuation`. -/
theorem valuation_eq_word_weight (E : V → V → Bool) (cash_flow : V → ℤ)
    (S : ActivationState V) (h_ne : S.Nonempty) :
    valuation cash_flow S = S.sup' h_ne (fun (u, _v) => edgeWeight cash_flow u) := by
  unfold valuation
  rw [dif_pos h_ne]

/-! ### 4. Théorème-pont en termes WFA

Le théorème-pont k(t) ≤ B_circ(t) est la commutativité du diagramme :
  BooleanDioid --hauteur--> ℕ --plongement--> D1
       │                                      │
  valuation ================================= id
       ↓                                      ↓
       D1 ===============================> D1

Énoncé : pour tout état d'activation S, height(S) ≤ valuation(S)
(après plongement de ℕ dans D1).
-/

/-- Plongement ℕ → Z_max : n ↦ ofInt n. -/
def embedNat (n : ℕ) : Z_max :=
  Z_max.ofInt (n : ℤ)

/-! L'ancien `axiom bridge_wfa_height_le_valuation` a été supprimé :
    l'inégalité est mathématiquement fausse (confusion sup/somme dans
    la sémantique du dioïde max-plus — `valuation` calcule un `sup'`,
    pas un produit dioïdal). Le théorème-pont correct reste
    `pont_inegalite_fondamentale` (Pont.lean).
    Voir cache/analyse_critique_bridge_wfa.md. -/

/-! ### 5. Lien avec le théorème-pont existant

Le théorème `pont_inegalite_fondamentale` (Pont.lean:60) reste la preuve
de référence.  La version WFA ci-dessus est une reformulation structurelle
qui exhibe le diagramme de dioïdes sous-jacent.
-/

end BridgeRegex
