/-
  ThesePlanetaire/PivotWFA.lean
  Pivot d'admission, phase 1 : l'admission pivot est l'exécution d'un WFA.

  Provenance : scratch PivotWFA_scratch, porté verbatim (2026-10-01). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md`.

  `FlowAdmission.futureGatedWFA` (FlowAdmission.lean:86) et son pont
  `admissionFold_wfa_terminal` n'utilisent de `isAdmissible` que sa décidabilité et la
  forme test-and-keep. On les généralise ici, comme code neuf (FlowAdmission.lean non
  modifié), à tout prédicat décidable `P` (`gatedWFA`), on vérifie que `futureGatedWFA` en
  est l'instance `P := isAdmissible` (`futureGatedWFA_eq_gatedWFA`, par `rfl`), puis on
  instancie sur `pivotAdmissible`. On ajoute l'unicité de l'exécution
  (`gatedWFA_reaches_iff`), que FlowAdmission énonce en commentaire sans la prouver.
-/

import Mathlib.Tactic
import ThesePlanetaire.FlowAdmission
import ThesePlanetaire.PivotPotential

namespace PivotWFA

open DualDAG (FuturePool isAdmissible admissionFoldP admissionFold)
open FlowAdmission (WFAReaches futureGatedWFA)
open PivotPotential

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. WFA test-and-keep paramétrique -/

/-- WFA booléen test-and-keep pour un prédicat d'admission décidable quelconque. -/
def gatedWFA (P : ActivationState V → V × V → Prop) [∀ S e, Decidable (P S e)] :
    WeightedAutomaton Bool (V × V) (ActivationState V) where
  init S := decide (S = ∅)
  trans S e T := decide (T = if P S e then S ∪ {e} else S)
  final _ := true

/-- `futureGatedWFA` est l'instance `P := isAdmissible` de `gatedWFA`. -/
theorem futureGatedWFA_eq_gatedWFA (pool : FuturePool V) (demands : V × V → ℤ) :
    futureGatedWFA pool demands = gatedWFA (isAdmissible pool demands) := rfl

omit [Fintype V] in
theorem gatedWFA_trans_iff (P : ActivationState V → V × V → Prop) [∀ S e, Decidable (P S e)]
    (S : ActivationState V) (e : V × V) (T : ActivationState V) :
    (gatedWFA P).trans S e T = true ↔ T = if P S e then S ∪ {e} else S := by
  simp [gatedWFA]

omit [Fintype V] in
theorem gatedWFA_deterministic (P : ActivationState V → V × V → Prop)
    [∀ S e, Decidable (P S e)] (S : ActivationState V) (e : V × V) :
    ∃! T, (gatedWFA P).trans S e T = true :=
  ⟨_, (gatedWFA_trans_iff P S e _).mpr rfl, fun _ hT => (gatedWFA_trans_iff P S e _).mp hT⟩

/-! ### 2. Pont mot ↔ fold, avec unicité -/

omit [Fintype V] in
/-- L'exécution du WFA depuis `S` sur `w` atteint `T` SSI `T` est le fold test-and-keep :
    existence (le fold est une exécution) ET unicité (c'est la seule). -/
theorem gatedWFA_reaches_iff (P : ActivationState V → V × V → Prop)
    [∀ S e, Decidable (P S e)] (w : List (V × V)) (S T : ActivationState V) :
    WFAReaches (gatedWFA P) S w T ↔
      T = w.foldl (fun cur e => if P cur e then cur ∪ {e} else cur) S := by
  induction w generalizing S with
  | nil =>
    constructor
    · intro h; cases h; rfl
    · intro hT; rw [hT]; exact WFAReaches.nil _
  | cons e es ih =>
    simp only [List.foldl_cons]
    constructor
    · intro h
      cases h with
      | step _ _ T' _ _ h_trans h_rest =>
        rw [(gatedWFA_trans_iff P S e T').mp h_trans] at h_rest
        exact (ih _).mp h_rest
    · intro hT
      exact WFAReaches.step S e _ es T ((gatedWFA_trans_iff P S e _).mpr rfl) ((ih _).mpr hT)

omit [Fintype V] in
/-- Généralisation d'`admissionFold_wfa_terminal` à tout `P` : `admissionFoldP P w` est
    L'UNIQUE état atteint par `gatedWFA P` depuis ∅. -/
theorem admissionFoldP_wfa_terminal (P : ActivationState V → V × V → Prop)
    [∀ S e, Decidable (P S e)] (w : List (V × V)) :
    (gatedWFA P).init ∅ = true ∧ WFAReaches (gatedWFA P) ∅ w (admissionFoldP P w) ∧
      ∀ T, WFAReaches (gatedWFA P) ∅ w T → T = admissionFoldP P w :=
  ⟨by simp [gatedWFA], (gatedWFA_reaches_iff P w ∅ _).mpr rfl,
    fun T h => (gatedWFA_reaches_iff P w ∅ T).mp h⟩

/-! ### 3. Instances : admission classique et admission pivot -/

/-- Cohérence : on retrouve `admissionFold_wfa_terminal`, avec unicité en plus. -/
theorem admissionFold_wfa_unique (pool : FuturePool V) (demands : V × V → ℤ)
    (w : List (V × V)) (T : ActivationState V)
    (h : WFAReaches (futureGatedWFA pool demands) ∅ w T) :
    T = admissionFold pool demands w := by
  rw [futureGatedWFA_eq_gatedWFA] at h
  exact (admissionFoldP_wfa_terminal (isAdmissible pool demands) w).2.2 T h

/-- WFA de l'admission pivot (lecture crédit). -/
def pivotGatedWFA (pool : FuturePool V) (demands : V × V → ℤ) :
    WeightedAutomaton Bool (V × V) (ActivationState V) :=
  gatedWFA (pivotAdmissible pool demands)

/-- ★ L'admission pivot est l'unique exécution de `pivotGatedWFA` depuis ∅. -/
theorem pivotAdmissionFold_wfa_terminal (pool : FuturePool V) (demands : V × V → ℤ)
    (w : List (V × V)) :
    (pivotGatedWFA pool demands).init ∅ = true ∧
    WFAReaches (pivotGatedWFA pool demands) ∅ w (pivotAdmissionFold pool demands w) ∧
      ∀ T, WFAReaches (pivotGatedWFA pool demands) ∅ w T → T = pivotAdmissionFold pool demands w :=
  admissionFoldP_wfa_terminal (pivotAdmissible pool demands) w

end PivotWFA
