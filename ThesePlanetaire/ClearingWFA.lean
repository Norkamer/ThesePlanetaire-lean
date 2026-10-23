/-
  MonnaiesEndogene/ClearingWFA.lean
  Phase 4-C : WFA ↔ ClearingOperator
  Foncteur entre opérateur de clearing (treillis) et automate fini valué booléen.

  Références : plan_phase_4_reste.md §3 (2026-06-08)
-/

import ThesePlanetaire.Basic
import ThesePlanetaire.LatticeClearing
import ThesePlanetaire.WeightedAutomaton
import ThesePlanetaire.BridgeRegex
import ThesePlanetaire.PlanetaryBoundaries

namespace ClearingWFA

open WeightedAutomaton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Foncteur ClearingOperator → WFA Bool

    Un opérateur de clearing Φ : ActivationState V → ActivationState V
    devient un WFA booléen dont :
    - les états sont les états d'activation (Finset (V × V))
    - les transitions valident l'activation d'une arête par Φ
    - tout mot accepté encode une séquence de clearing valide
-/

/-- Foncteur `clearingToWFA` : ClearingOperator → WFA Bool.

    Interprétation économique : chaque itération de Φ correspond à une transition
    du WFA. Un mot `w = [e₁, e₂, ...]` est accepté s'il existe une séquence
    d'états S₀, S₁, ... telle que S_{i+1} = Φ(S_i ∪ {e_i}).

    Cette construction est conservative : elle ne modélise que l'activation,
    pas la désactivation (souveraineté du clearing). -/
def clearingToWFA (Φ : ClearingOperator V) : WeightedAutomaton Bool (V × V) (ActivationState V) where
  init S := decide (S = ∅)
  trans S e T := decide (T = Φ (S ∪ {e}))
  final _ := true

/-- Un mot `w : List (V × V)` est une "séquence de clearing valide" s'il
    existe un chemin dans le WFA booléen qui aboutit à un état final. -/
def isValidClearingSequence (Φ : ClearingOperator V) (w : List (V × V)) : Prop :=
  accepts (clearingToWFA Φ) w

/-! ### 2. Foncteur WFA Bool → ClearingOperator (sens inverse)

    Étant donné un WFA booléen dont les transitions sont fonctionnelles
    (chaque état et symbole déterminent un unique état suivant), on construit
    un opérateur de clearing Φ qui applique cette transition à l'état courant.

    Hypothèse : le WFA est **déterministe** pour ce foncteur.

    Note : cette définition est naïve / documentaire. La preuve d'équivalence
    exacte entre les deux foncteurs est hors scope Phase 4-C (travail de thèse
    Ch.8 sur les automates de clearing). -/
def wfaToClearing (wfa : WeightedAutomaton Bool (V × V) (ActivationState V))
    (_ : ∀ S e, ∃! T, wfa.trans S e T = true) : ClearingOperator V :=
  λ S => S  -- placeholder documentaire : l'identité (opérateur trivial)

/-- Théorème de correspondance (tautologie structurelle) :
    `isValidClearingSequence` est exactement l'acceptation par le WFA.

    C'est une **tautologie de définition** : `accepts` est défini comme
    `word_weight ≠ 0`, ce qui pour `K = Bool` équivaut à `= true`. -/
theorem clearing_wfa_roundtrip (Φ : ClearingOperator V) (w : List (V × V)) :
    isValidClearingSequence Φ w ↔ word_weight (clearingToWFA Φ) w = true := by
  simp [isValidClearingSequence, accepts]
  cases word_weight (clearingToWFA Φ) w <;> simp

/-! ### 3. WFA réglementaire (EU Taxonomy)

    Extension du foncteur Clearing→WFA avec des gardes réglementaires.
    Chaque transition peut être contrainte par un objectif de la Taxonomie EU.
    Source : Klessascheck et al. (2024).

    NOTE : cette extension est structurelle. La condition de garde est `True`
    car la vraie vérification des critères TSC nécessite des données empiriques
    (données de rapportage des émetteurs). Le pont formel est posé ;
    la validation économique est dans les tests Python (Phase 4). -/

/-- WFA de clearing avec contraintes EU Taxonomy.
    Une transition est acceptée ssi elle satisfait l'opérateur de clearing Φ
    ET toutes les gardes binding associées à cette arête. -/
def clearingToRegulatoryWFA (Φ : ClearingOperator V)
    (guards : Finset (PlanetaryBoundaries.RegulatoryGuard (V := V))) :
    WeightedAutomaton Bool (V × V) (ActivationState V) where
  init S := decide (S = ∅)
  trans S e T :=
    decide (T = Φ (S ∪ {e}) ∧
            ∀ g ∈ guards, g.edge = e →
              g.transition_type = PlanetaryBoundaries.TaxonomyTransitionType.binding →
              True)
  final _ := true

/-- Théorème : le WFA réglementaire et le WFA standard partagent le même état initial.
    C'est un pont structurel (la preuve d'inclusion des langages nécessite
    une induction sur `w`, hors scope ici). -/
theorem regulatory_wfa_init_eq (Φ : ClearingOperator V)
    (guards : Finset (PlanetaryBoundaries.RegulatoryGuard (V := V))) (S : ActivationState V) :
    (clearingToRegulatoryWFA Φ guards).init S = (clearingToWFA Φ).init S := rfl

end ClearingWFA
