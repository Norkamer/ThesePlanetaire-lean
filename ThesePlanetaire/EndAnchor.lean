/-
  MonnaiesEndogene/EndAnchor.lean
  Phase Organic 1 : Fondation combinatoire des end-anchors (Ω₀–Ω₅).

  Ce fichier formalise la notion d'end-anchor comme contrainte terminale
  sur le dernier symbole des mots acceptés par un WFA (Weighted Finite
  Automaton) : un end-anchor est un sous-ensemble A ⊆ α de l'alphabet,
  et un mot satisfait la contrainte ssi sa dernière lettre ∈ A
  (sémantique de la regexp `.*A$`).

  Architecture :
  - Les end-anchors sont des sous-ensembles de l'alphabet du WFA
  - Ils filtrent les mots acceptés selon leur dernière lettre
  - Ils conditionnent la mesure de Boltzmann/Bernoulli sur l'événement
    correspondant
  - La couche « mots » (Regex/Brzozowski, produit WFA×DFA) a été
    supprimée (Phase 28 KB documentaire, jamais câblée) ; la couche
    « traces » (trace_max_letter, prob_anchor_event) est consommée
    par G3Duality, la couche « mots » restante (BoolDFA) par
    SolvencyRegularity.

  Statut : 0 sorry.

  Références :
  - regex_endanchor_taxonomy_phase27.md (Perplexity2026 KB, Ω₀–Ω₅)
  - bernoulli_traces_gre26.md (Perplexity2026 KB, mesure conditionnelle)
  - Hoffman-Kruskal (1956), Integral Boundary Points of Convex Polyhedra
  - Droste-Kuich-Vogler (2009), Handbook of Weighted Automata
  - ClearingWFA.lean (WFA de clearing, α = V × V)
  - BoltzmannMeasure.lean (mesure sur Trace = Finset Letter)
  - TUScalarUniqueness.lean (totale unimodularité)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import ThesePlanetaire.Basic
import ThesePlanetaire.BoltzmannMeasure

namespace EndAnchor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. End-Anchor comme classe de regexp

    Un end-anchor est un sous-ensemble A ⊆ α de l'alphabet d'un WFA.
    Il contraint la dernière lettre de tout mot accepté à appartenir à A.

    Dans le GRE26 KB (regex_endanchor_taxonomy_phase27.md) :
    - Ω₀ = ⊤ (tout l'alphabet) — aucune contrainte
    - Ω₁ = {E} où E ∈ L₁ (souverain)
    - Ω₂ = {E₁,…,Eₙ} ⊆ L₁ (mixture)
    - Ω₃ = L₁ ∪ L₃ (Digital Pigouvien)
    - Ω₄ = dépend du contexte (historique de transition)
    - Ω₅ = périodique (cycle temporel)
-/

/-- End-anchor sur un alphabet α : sous-ensemble de lettres terminales
    autorisées. C'est la sémantique de la regexp `.*A$`. -/
structure EndAnchor (α : Type*) where
  terminalLetters : Finset α   -- lettres terminales autorisées
  h_non_empty : terminalLetters.Nonempty  -- C_k non vide (existence)

/-- Alphabet du WFA de clearing : arêtes du graphe orienté. -/
abbrev ClearingAlphabet (V : Type*) := V × V

/-- End-anchor de type Ω₀ : universel (pas de contrainte). -/
def omega0_anchor (α : Type*) [Fintype α] [Nonempty α] : EndAnchor α :=
  { terminalLetters := Finset.univ,
    h_non_empty := Finset.univ_nonempty }

/-- End-anchor de type Ω₁ : une seule lettre terminale. -/
def omega1_anchor {α : Type*} [DecidableEq α] (e : α) : EndAnchor α :=
  { terminalLetters := {e},
    h_non_empty := Finset.singleton_nonempty e }

/-! ### 2. Prédicat sur les mots du WFA

    Un mot w = [e₁, e₂, …, eₙ] du WFA satisfait l'end-anchor si
    eₙ ∈ terminalLetters. -/

/-- Dernière lettre d'un mot (sécurisé, retourne Option). -/
def lastLetter {α : Type*} (w : List α) : Option α :=
  match w with
  | [] => none
  | w' :: ws => some ((w' :: ws).getLast (List.cons_ne_nil w' ws))

/-- Prédicat : le mot satisfait la contrainte terminale de l'end-anchor.
    Utilise le pattern match pour que `by trivial` fonctionne dans le
    contexte `w' ≠ []`. -/
def satisfiesEndAnchor {α : Type*} [DecidableEq α]
    (anchor : EndAnchor α) (w : List α) : Prop :=
  match lastLetter w with
  | none => False
  | some c => c ∈ anchor.terminalLetters

/-- Instance Decidable pour satisfiesEndAnchor. -/
instance {α : Type*} [DecidableEq α] (anchor : EndAnchor α) (w : List α) :
    Decidable (satisfiesEndAnchor anchor w) := by
  unfold satisfiesEndAnchor
  cases lastLetter w with
  | none => infer_instance
  | some c => infer_instance

/-! ### 3. Théorèmes de base -/

/-- Théorème : Ω₀ (universel) accepte tout mot non vide. -/
theorem omega0_universal {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (w : List α) (h : w ≠ []) :
    satisfiesEndAnchor (omega0_anchor α) w := by
  cases w with
  | nil => exact absurd rfl h
  | cons _ _ =>
    simp [satisfiesEndAnchor, omega0_anchor]
    <;> try { trivial }

/-- Théorème : Ω₁ avec lettre e n'accepte que les mots terminant par e. -/
theorem omega1_single_edge {α : Type*} [DecidableEq α]
    (e : α) (w : List α) :
    satisfiesEndAnchor (omega1_anchor e) w ↔
    (w ≠ [] ∧ lastLetter w = some e) := by
  cases w with
  | nil =>
    apply Iff.intro
    · intro h
      simp [satisfiesEndAnchor, lastLetter] at h
    · intro h
      simp [lastLetter] at h
  | cons a l =>
    have h1 : lastLetter (a :: l) = some ((a :: l).getLast (List.cons_ne_nil a l)) := by
      simp [lastLetter]
    rw [h1]
    apply Iff.intro
    · -- =>
      intro h
      unfold satisfiesEndAnchor omega1_anchor at h
      simp [Finset.mem_singleton] at h
      constructor
      · exact List.cons_ne_nil a l
      · exact congr_arg some h
    · -- <=
      intro ⟨_, h_eq⟩
      unfold satisfiesEndAnchor omega1_anchor
      simp [Finset.mem_singleton]
      exact Option.some_inj.mp h_eq

/-! ### 4. Conditionnement de la mesure de Boltzmann

    Pour une end-anchor A ⊆ α, la mesure conditionnelle sur les traces
    est définie comme la restriction aux traces dont la lettre maximale
    (dans l'ordre Letter.id) appartient à A.

    Dans le cadre EXT1, une trace est un ensemble (Finset), pas une
    séquence. La notion de "dernière lettre" est définie via la
    décomposition de Cartier-Foata (TraceMonoid.lean). -/

open TraceMonoid

/-- Lettre maximale d'une trace (selon l'ordre Letter.id).
    Définie uniquement pour les traces non vides. -/
def trace_max_letter (t : Trace) (h : t.letters.Nonempty) : Letter :=
  t.letters.max' h

/-- Prédicat : une trace satisfait l'end-anchor si sa lettre maximale
    appartient au sous-ensemble autorisé. -/
def traceSatisfiesEndAnchorLast (anchor : EndAnchor Letter) (t : Trace) : Prop :=
  ∃ (h : t.letters.Nonempty), trace_max_letter t h ∈ anchor.terminalLetters

/-! ### 5. Probabilité conditionnelle sous end-anchor (documentaire)

    Pour un end-anchor A, la probabilité conditionnelle d'une trace τ
    est B_p(τ | A) = B_p(τ) / B_p(A) où B_p(A) est la probabilité que
    la trace soit entièrement dans A (ou que sa lettre max soit dans A).

    Sous EXT1, la probabilité marginale que la lettre maximale soit l
    est q/(1+q)^{|Σ|} où q = p/(1+p).

    NOTE : les définitions ci-dessous sont DOCUMENTAIRES car elles
    nécessitent la somme sur toutes les traces (infini dénombrable
    si Letter est infini, mais borné par alphabetSize dans BoltzmannMeasure).
    La formalisation complète est hors scope de ce module (Phase 28 KB). -/

open BoltzmannMeasure

/-- Probabilité de l'événement end-anchor A = P(trace entièrement dans A).
    Somme des probabilités Boltzmann sur les traces ⊆ A. -/
noncomputable def prob_anchor_event (bm : BoltzmannMeasure)
    (anchor : EndAnchor Letter) : ℝ :=
  ∑ t ∈ (anchor.terminalLetters.powerset).image Trace.ofFinset,
    prob bm t

/-- Mesure conditionnelle de Boltzmann sous end-anchor (DOCUMENTAIRE).
    B_p(τ | A) = B_p(τ) / B_p(A) si τ ⊆ A, 0 sinon.

    La preuve de normalisation (Σ_τ B_p(τ | A) = 1) nécessite la somme
    sur toutes les traces de l'alphabet fini, ce qui est une somme finie
    (2^{alphabetSize} termes). La preuve est reportée à Phase 28. -/
noncomputable def conditional_boltzmann_prob (bm : BoltzmannMeasure)
    (anchor : EndAnchor Letter) (t : Trace) : ℝ :=
  if t.letters.Nonempty ∧ t.letters ⊆ anchor.terminalLetters then
    prob bm t / prob_anchor_event bm anchor
  else 0

/-! ### 7. DFA à 2 états d'un end-anchor (Brzozowski)

    La dérivée de Brzozowski de l'end-anchor `.*A$` produit un DFA à 2 états :
    - q₀ = "dernière lettre ∉ A" (ou mot vide)
    - q₁ = "dernière lettre ∈ A"

    Ce DFA est défini indépendamment du WFA avec une sémantique classique
    (run + accepting), car la définition `path_weight` de `WeightedAutomaton`
    multiplie `final` à chaque étape (non-standard pour DFA).

    Références : Brzozowski (1964), Droste-Kuich-Vogler (2009) Ch. 3. -/

/-- DFA booléen classique. -/
structure BoolDFA (α : Type*) where
  state : Type*
  init_state : state
  trans : state → α → state
  accepting : state → Bool

namespace BoolDFA

/-- Exécution d'un DFA sur un mot. -/
def run {α : Type*} (dfa : BoolDFA α) (w : List α) : dfa.state :=
  w.foldl dfa.trans dfa.init_state

/-- Le DFA accepte le mot ssi l'état d'arrivée est acceptant. -/
def dfa_accepts {α : Type*} (dfa : BoolDFA α) (w : List α) : Prop :=
  dfa.accepting (dfa.run w)

end BoolDFA

/-- DFA à 2 états (Fin 2) d'un end-anchor.
    q₀ = 0 : dernière lettre ∉ A (ou mot vide).
    q₁ = 1 : dernière lettre ∈ A. -/
def end_anchor_dfa {α : Type*} [Fintype α] [DecidableEq α] (anchor : EndAnchor α) : BoolDFA α where
  state := Fin 2
  init_state := 0
  trans q a := if a ∈ anchor.terminalLetters then 1 else 0
  accepting q := decide (q = 1)

/-- Lemme : pour un mot non vide, le run du DFA d'end-anchor ne dépend
    que de la dernière lettre (indépendamment de l'état initial). -/
lemma end_anchor_dfa_foldl_last {α : Type*} [Fintype α] [DecidableEq α]
    (anchor : EndAnchor α) (q : Fin 2) (w : List α) (h : w ≠ []) :
    List.foldl (fun q a => if a ∈ anchor.terminalLetters then 1 else 0) q w =
    if w.getLast h ∈ anchor.terminalLetters then (1 : Fin 2) else (0 : Fin 2) := by
  induction w generalizing q with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil =>
      unfold List.foldl
      simp
    | cons b l =>
      unfold List.foldl at ih ⊢
      have h2 := ih (if a ∈ anchor.terminalLetters then (1 : Fin 2) else (0 : Fin 2)) (List.cons_ne_nil b l)
      simp [h2]

/-- Théorème : le DFA d'end-anchor accepte exactement les mots satisfaisant
    l'end-anchor (sémantique Brzozowski). -/
theorem end_anchor_dfa_accepts {α : Type*} [Fintype α] [DecidableEq α]
    (anchor : EndAnchor α) (w : List α) :
    BoolDFA.dfa_accepts (end_anchor_dfa anchor) w ↔ satisfiesEndAnchor anchor w := by
  unfold BoolDFA.dfa_accepts BoolDFA.run end_anchor_dfa satisfiesEndAnchor
  cases w with
  | nil =>
    simp [List.foldl, lastLetter]
  | cons a l =>
    have h1 := end_anchor_dfa_foldl_last anchor 0 (a :: l) (List.cons_ne_nil a l)
    simp [h1, lastLetter]

end EndAnchor
