/-
  ThesePlanetaire/AutomatonRegularity.lean
  Phase 2b (2026-10-01) : régularité au sens de Mathlib (`Language.IsRegular`) pour les plis à
  invariant fini, pont depuis `EndAnchor.BoolDFA`, et le huit comptable de l'autre côté.

  Développé d'abord en `AutomatonRegularity_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 2b, étape 3) ; analyse :
  `cache/analyse_forte_connexite_graphe_transactions_2026-10-01.md` (§12).

  1. ★ `isRegular_of_finite_invariant` : un pli `w ↦ w.foldl δ s₀` dont les états atteints
     restent dans un ensemble FINI stable par `δ` reconnaît, pour toute condition d'acceptation
     `acc`, un langage régulier. L'automate est `invariantDFA`, restriction de `δ` à
     l'invariant ; son exécution est le pli (`invariantDFA_evalFrom_val`). Corollaire
     `isRegular_of_finite_states` (espace d'états fini) ;
  2. pont : `BoolDFA.toDFA`, et `isRegular_iff_boolDFA` — un langage est régulier ssi un
     `BoolDFA` à états finis le reconnaît ;
  3. ★ `huit_not_isRegular` : transport de `SolvencyRegularity.no_finite_verifier` — le langage
     d'auto-financement du huit comptable n'est pas régulier ; `ne_huit_of_isRegular` ;
  4. `endAnchor_isRegular` : le langage `.*A$` d'`end_anchor_dfa` est régulier.

  Regexp au sens strict : le théorème de Kleene (`RegularExpression` ↔ `IsRegular`) n'est pas
  dans le Mathlib local ; on n'énonce rien sur `RegularExpression`.
-/

import Mathlib.Computability.DFA
import ThesePlanetaire.SolvencyRegularity

namespace AutomatonRegularity

open EndAnchor (BoolDFA satisfiesEndAnchor end_anchor_dfa end_anchor_dfa_accepts)
open OrganicLP (isSelfFinancing)
open SolvencyRegularity (huitTEG no_finite_verifier)

universe u v

variable {α : Type u} {σ : Type v}

/-! ### 1. Plis à invariant fini -/

/-- Restriction du pli `δ` à un invariant stable `Inv` contenant `s₀`. -/
def invariantDFA (δ : σ → α → σ) (s₀ : σ) (Inv : σ → Prop) (h0 : Inv s₀)
    (hδ : ∀ s a, Inv s → Inv (δ s a)) (acc : σ → Bool) : DFA α {s // Inv s} where
  step s a := ⟨δ s.1 a, hδ s.1 a s.2⟩
  start := ⟨s₀, h0⟩
  accept := {s | acc s.1 = true}

/-- L'exécution de `invariantDFA` est le pli. -/
theorem invariantDFA_evalFrom_val (δ : σ → α → σ) (s₀ : σ) (Inv : σ → Prop) (h0 : Inv s₀)
    (hδ : ∀ s a, Inv s → Inv (δ s a)) (acc : σ → Bool) (s : {s // Inv s}) (w : List α) :
    ((invariantDFA δ s₀ Inv h0 hδ acc).evalFrom s w).1 = w.foldl δ s.1 := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih _

/-- ★ Un pli dont les états atteints restent dans un ensemble fini stable reconnaît un langage
    régulier, pour toute condition d'acceptation. -/
theorem isRegular_of_finite_invariant (δ : σ → α → σ) (s₀ : σ) {Inv : σ → Prop}
    (hfin : {s | Inv s}.Finite) (h0 : Inv s₀) (hδ : ∀ s a, Inv s → Inv (δ s a))
    (acc : σ → Bool) :
    Language.IsRegular ({w | acc (w.foldl δ s₀) = true} : Language α) := by
  letI : Fintype {s // Inv s} := hfin.fintype
  rw [Language.isRegular_iff.{u, v}]
  refine ⟨{s // Inv s}, inferInstance, invariantDFA δ s₀ Inv h0 hδ acc, ?_⟩
  ext w
  rw [DFA.mem_accepts]
  show acc ((invariantDFA δ s₀ Inv h0 hδ acc).evalFrom ⟨s₀, h0⟩ w).1 = true ↔ _
  rw [invariantDFA_evalFrom_val]
  rfl

/-- Espace d'états fini : tout pli reconnaît un langage régulier. -/
theorem isRegular_of_finite_states [Finite σ] (δ : σ → α → σ) (s₀ : σ) (acc : σ → Bool) :
    Language.IsRegular ({w | acc (w.foldl δ s₀) = true} : Language α) :=
  isRegular_of_finite_invariant δ s₀ (Inv := fun _ => True) (Set.toFinite _) trivial
    (fun _ _ _ => trivial) acc

/-! ### 2. Pont `BoolDFA` ↔ `DFA` -/

/-- Un `BoolDFA` du dépôt comme DFA de Mathlib. -/
def _root_.EndAnchor.BoolDFA.toDFA (dfa : BoolDFA.{u, v} α) : DFA α dfa.state :=
  ⟨dfa.trans, dfa.init_state, {s | dfa.accepting s = true}⟩

theorem _root_.EndAnchor.BoolDFA.mem_toDFA_accepts (dfa : BoolDFA.{u, v} α) (w : List α) :
    w ∈ dfa.toDFA.accepts ↔ dfa.dfa_accepts w :=
  Iff.rfl

/-- Un langage est régulier ssi un `BoolDFA` à états finis le reconnaît. -/
theorem isRegular_iff_boolDFA {L : Language α} :
    L.IsRegular ↔
      ∃ (dfa : BoolDFA.{u, v} α) (_ : Fintype dfa.state), ∀ w, w ∈ L ↔ dfa.dfa_accepts w := by
  classical
  rw [Language.isRegular_iff.{u, v}]
  constructor
  · rintro ⟨σ', inst, M, rfl⟩
    refine ⟨⟨σ', M.start, M.step, fun s => decide (s ∈ M.accept)⟩, inst, fun w => ?_⟩
    rw [DFA.mem_accepts]
    exact decide_eq_true_iff.symm
  · rintro ⟨dfa, inst, h⟩
    exact ⟨dfa.state, inst, dfa.toDFA, Set.ext fun w => (h w).symm⟩

/-! ### 3. Le huit comptable n'est pas régulier -/

/-- ★ Le langage d'auto-financement du huit comptable n'est pas régulier
    (`SolvencyRegularity.no_finite_verifier`, transporté). -/
theorem huit_not_isRegular :
    ¬ Language.IsRegular ({w | isSelfFinancing huitTEG w} : Language (Fin 3 × Fin 3)) := by
  intro h
  obtain ⟨dfa, inst, hdfa⟩ := isRegular_iff_boolDFA.{0, 0}.mp h
  exact no_finite_verifier dfa (fun w => (hdfa w).symm)

/-- Aucun langage régulier n'est le langage du huit. -/
theorem ne_huit_of_isRegular {L : Language (Fin 3 × Fin 3)} (h : L.IsRegular) :
    L ≠ {w | isSelfFinancing huitTEG w} :=
  fun heq => huit_not_isRegular (heq ▸ h)

/-! ### 4. L'unique « regexp » du dépôt : `.*A$` -/

/-- Le langage `.*A$` d'un end-anchor est régulier (DFA à deux états). -/
theorem endAnchor_isRegular [Fintype α] [DecidableEq α] (anchor : EndAnchor.EndAnchor α) :
    Language.IsRegular ({w | satisfiesEndAnchor anchor w} : Language α) :=
  isRegular_iff_boolDFA.{u, 0}.mpr ⟨end_anchor_dfa anchor, (inferInstance : Fintype (Fin 2)),
    fun w => (end_anchor_dfa_accepts anchor w).symm⟩

end AutomatonRegularity
