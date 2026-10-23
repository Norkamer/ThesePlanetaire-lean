/-
  MonnaiesEndogene/ConditionalBernoulli.lean
  Phase 3 : Mesure uniforme conditionnelle sur les chemins du WFA.

  Architecture :
  - Mesure uniforme sur un ensemble fini de chemins (List (V × V))
  - Conditionnement par end-anchor (restriction + renormalisation)
  - 0 sorry, imports minimaux (pas de BoltzmannMeasure, BernoulliMeasure,
    TraceMonoid, InfiniteTraceSpace en import direct)

  Références :
  - Arratia & Tavaré (1994), Independent Process Approximations
  - Siegrist (LibreTexts), Conditional Probability
  - Stanley (1973), Enumerative Combinatorics §4.7
  - Ong, Ma, Kozen (2025), Probabilistic Kleene Algebra
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import ThesePlanetaire.EndAnchor
import ThesePlanetaire.WeightedAutomaton

namespace ConditionalBernoulli

open EndAnchor WeightedAutomaton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Mesure uniforme sur les chemins d'un WFA -/

/-- Mesure uniforme sur un ensemble fini de chemins élémentaires.
    La probabilité est la mesure de comptage normalisée. -/
structure UniformPathMeasure (V : Type*) [Fintype V] [DecidableEq V] where
  wfa : WeightedAutomaton Bool (V × V) V
  all_paths : Finset (List (V × V))
  h_all_paths_accepted : ∀ w ∈ all_paths, accepts wfa w
  -- C3 : `all_paths` contient TOUS les chemins acceptés par le WFA.
  -- Cette hypothèse structurelle lie `all_paths` au WFA : la mesure
  -- uniforme est définie sur l'ensemble COMPLET des chemins acceptés
  -- (dans le cadre fini du TEG organique, où le graphe est contraint
  -- par `guard.allowedEdges` et `end_anchor`).
  -- Hors scope : WFA avec infinité de mots acceptés (cycles non contraints).
  h_all_paths_complete : ∀ w, accepts wfa w → w ∈ all_paths
  h_all_paths_nonempty : all_paths.Nonempty
  h_all_paths_nonempty_words : ∀ w ∈ all_paths, w ≠ []

/-- Probabilité uniforme d'un chemin. -/
noncomputable def prob_path (m : UniformPathMeasure V) (w : List (V × V)) : ℝ :=
  if w ∈ m.all_paths then 1 / (m.all_paths.card : ℝ) else 0

/-- Probabilité de l'événement end-anchor sous la mesure uniforme. -/
noncomputable def prob_anchor (m : UniformPathMeasure V)
    (anchor : EndAnchor (V × V)) : ℝ :=
  let accept_paths := m.all_paths.filter (satisfiesEndAnchor anchor)
  (accept_paths.card : ℝ) / (m.all_paths.card : ℝ)

/-- Mesure conditionnelle uniforme sous end-anchor. -/
noncomputable def conditional_prob (m : UniformPathMeasure V)
    (anchor : EndAnchor (V × V)) (w : List (V × V)) : ℝ :=
  if w ∈ m.all_paths ∧ satisfiesEndAnchor anchor w then
    1 / ((m.all_paths.filter (satisfiesEndAnchor anchor)).card : ℝ)
  else 0

/-! ### 2. Théorèmes de base -/

/-- Théorème : la probabilité uniforme est non-négative. -/
theorem uniform_prob_nonneg (m : UniformPathMeasure V) (w : List (V × V)) :
    prob_path m w ≥ 0 := by
  unfold prob_path
  split_ifs <;> simp

/-- Théorème : la probabilité uniforme est ≤ 1. -/
theorem uniform_prob_le_one (m : UniformPathMeasure V) (w : List (V × V)) :
    prob_path m w ≤ 1 := by
  unfold prob_path
  split_ifs
  · have h_pos : (m.all_paths.card : ℝ) ≥ 1 := by
      have h : m.all_paths.Nonempty := m.h_all_paths_nonempty
      have h2 : m.all_paths.card ≥ 1 := Finset.Nonempty.card_pos h
      exact_mod_cast h2
    have h1 : (1 : ℝ) / (m.all_paths.card : ℝ) ≤ 1 := by
      have h2 : (1 : ℝ) ≤ (m.all_paths.card : ℝ) := by exact_mod_cast h_pos
      have h3 : (1 : ℝ) / (m.all_paths.card : ℝ) ≤ (m.all_paths.card : ℝ) / (m.all_paths.card : ℝ) := by
        apply div_le_div_of_nonneg_right h2 (by positivity)
      rw [div_self (by positivity)] at h3
      exact h3
    exact h1
  · simp

/-- Théorème : la somme des probabilités uniformes sur all_paths vaut 1. -/
theorem uniform_prob_sum_one (m : UniformPathMeasure V) :
    ∑ w ∈ m.all_paths, prob_path m w = 1 := by
  unfold prob_path
  have h_eq : ∀ w ∈ m.all_paths,
    (if w ∈ m.all_paths then 1 / (m.all_paths.card : ℝ) else 0)
      = 1 / (m.all_paths.card : ℝ) := by
    intro w hw
    simp [hw]
  rw [Finset.sum_congr rfl h_eq]
  rw [Finset.sum_const]
  have h_pos : (m.all_paths.card : ℝ) > 0 := by
    exact_mod_cast Finset.card_pos.mpr m.h_all_paths_nonempty
  simp only [nsmul_eq_mul]
  rw [mul_one_div_cancel (by linarith)]

/-- Théorème : la probabilité de l'end-anchor est le cardinal relatif. -/
theorem prob_anchor_def (m : UniformPathMeasure V) (anchor : EndAnchor (V × V)) :
    prob_anchor m anchor =
    (m.all_paths.filter (satisfiesEndAnchor anchor)).card / m.all_paths.card := by
  unfold prob_anchor
  simp

/-- Théorème : la probabilité conditionnelle est 1/|A∩all_paths| sur l'intersection. -/
theorem conditional_prob_def (m : UniformPathMeasure V)
    (anchor : EndAnchor (V × V)) (w : List (V × V)) :
    conditional_prob m anchor w =
    if w ∈ m.all_paths ∧ satisfiesEndAnchor anchor w then
      1 / ((m.all_paths.filter (satisfiesEndAnchor anchor)).card : ℝ)
    else 0 := by
  unfold conditional_prob
  simp

/-- Théorème : la somme des probabilités conditionnelles sur l'intersection vaut 1.
    Hypothèse : l'end-anchor est compatible (au moins un chemin satisfait l'ancre). -/
theorem conditional_prob_sum_one (m : UniformPathMeasure V) (anchor : EndAnchor (V × V))
    (h_compat : ∃ w ∈ m.all_paths, satisfiesEndAnchor anchor w) :
    ∑ w ∈ m.all_paths.filter (satisfiesEndAnchor anchor),
      conditional_prob m anchor w = 1 := by
  have h_term : ∀ w ∈ m.all_paths.filter (satisfiesEndAnchor anchor),
      conditional_prob m anchor w = 1 / ((m.all_paths.filter (satisfiesEndAnchor anchor)).card : ℝ) := by
    intro w hw
    rw [conditional_prob_def]
    have h : w ∈ m.all_paths ∧ satisfiesEndAnchor anchor w := by
      simpa using hw
    rw [if_pos h]
  rw [Finset.sum_congr rfl h_term]
  rw [Finset.sum_const]
  have h_pos : (m.all_paths.filter (satisfiesEndAnchor anchor)).card > 0 := by
    obtain ⟨w, hw, hanchor⟩ := h_compat
    apply Finset.card_pos.mpr
    use w
    exact Finset.mem_filter.mpr ⟨hw, hanchor⟩
  have h_pos' : ((m.all_paths.filter (satisfiesEndAnchor anchor)).card : ℝ) > 0 := by
    exact_mod_cast h_pos
  simp only [nsmul_eq_mul]
  rw [mul_one_div_cancel (by linarith)]

/-- Théorème : le conditionnement par Ω₀ (universel) est l'identité.
    Tous les chemins dans all_paths sont non vides, donc satisfient Ω₀. -/
theorem omega0_identity (m : UniformPathMeasure V) [Nonempty V] (w : List (V × V)) :
    conditional_prob m (omega0_anchor (V × V)) w = prob_path m w := by
  unfold conditional_prob prob_path
  have h_omega0 : ∀ w' ∈ m.all_paths, satisfiesEndAnchor (omega0_anchor (V × V)) w' := by
    intro w' hw'
    apply omega0_universal
    exact m.h_all_paths_nonempty_words w' hw'
  have h_filter : m.all_paths.filter (satisfiesEndAnchor (omega0_anchor (V × V))) = m.all_paths := by
    ext w'
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, h_omega0 w' h⟩
  rw [h_filter]
  by_cases hw : w ∈ m.all_paths
  · simp [hw, h_omega0 w hw]
  · simp [hw]

/-- Théorème : si un chemin terminant par e existe, P(Ω₁) > 0. -/
theorem omega1_conditional_positive (m : UniformPathMeasure V) (e : V × V)
    (h : ∃ w ∈ m.all_paths, lastLetter w = some e) :
    prob_anchor m (omega1_anchor e) > 0 := by
  unfold prob_anchor
  have h' : ∃ w ∈ m.all_paths, satisfiesEndAnchor (omega1_anchor e) w := by
    obtain ⟨w, hw, hlast⟩ := h
    use w, hw
    rw [omega1_single_edge]
    exact ⟨m.h_all_paths_nonempty_words w hw, hlast⟩
  have h_pos : (m.all_paths.filter (satisfiesEndAnchor (omega1_anchor e))).card > 0 := by
    obtain ⟨w, hw, hanchor⟩ := h'
    apply Finset.card_pos.mpr
    use w
    exact Finset.mem_filter.mpr ⟨hw, hanchor⟩
  have h_pos2 : (m.all_paths.card : ℝ) > 0 := by
    exact_mod_cast Finset.card_pos.mpr m.h_all_paths_nonempty
  have h_pos3 : ((m.all_paths.filter (satisfiesEndAnchor (omega1_anchor e))).card : ℝ) > 0 := by
    exact_mod_cast h_pos
  apply div_pos
  · exact h_pos3
  · exact h_pos2

/-! ### 3. Complétude de `all_paths` (C3)

  Le pont entre `UniformPathMeasure` et le WFA est maintenant structurel :
  `all_paths` n'est plus un paramètre libre, mais l'ensemble exact des
  chemins acceptés par le WFA (dans le cadre fini du TEG organique). -/

/-- Théorème : équivalence structurale — `w ∈ all_paths` ↔ `accepts wfa w`.
    C'est la conséquence directe de `h_all_paths_accepted` (→) et
    `h_all_paths_complete` (←). -/
theorem all_paths_iff_accepted (m : UniformPathMeasure V) (w : List (V × V)) :
    w ∈ m.all_paths ↔ accepts m.wfa w := by
  constructor
  · intro h
    exact m.h_all_paths_accepted w h
  · intro h
    exact m.h_all_paths_complete w h

end ConditionalBernoulli
