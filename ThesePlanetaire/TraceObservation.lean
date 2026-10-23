/-
  ThesePlanetaire/TraceObservation.lean
  Phase 1b (2026-10-01) : observations locales sur M(V × V, I_loc) et fibres SCE non
  dégénérées (P1 réorienté, plan `~/.claude/plans/witty-dazzling-manatee.md`).

  Développé d'abord en `TraceObservation_scratch.lean` (workflow du dépôt).

  Ce qu'un agent `i` observe d'une histoire de paiements :
  - `sentBy i` : ses émissions, dans l'ordre — descend aux traces (`sentObs`), car deux
    lettres `I_loc`-indépendantes ont des sources distinctes ;
  - `recvBag i` : le multi-ensemble de ses recettes — descend (`recvBagObs`) ;
  - `recvSeq i` : la SUITE ordonnée de ses recettes — NE descend PAS
    (`recvSeq_not_descends`) : deux paiements entrants commutent toujours sous `I_loc` ;
  - `localView i` : les lettres qui le touchent, dans l'ordre ; descend comme TRACE
    (`localObs`, projection de Zielonka : `LocTrace.filter`), pas comme mot.

  ★ `sce_fiber_nondegenerate` : sur le témoin de blocage (`LocalCommutation.Gridlock`),
  l'agent `2` a exactement la même vue locale ordonnée dans `[g, f, a]` et `[f, g, a]`, mais
  ses transactions admises diffèrent (`{f, a}` contre `∅`). Ce que l'agent observe ne
  détermine pas ce qui lui arrive : la fibre des conjectures compatibles avec ses
  observations (équilibre auto-confirmé, Fudenberg-Levine 1993) contient des histoires aux
  issues différentes — et cela sur un espace de traces non dégénéré sur tout graphe.

  (D5) `sceConsistent obs μ P := μ.map obs = P.map obs` (`PMF.map`) : définitions et
  propriétés de base seulement ; aucune mesure n'est encore construite sur `LocTrace V`.
-/

import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ThesePlanetaire.LocalCommutation

namespace TraceObservation

open DualDAG (FuturePool)
open LocalCommutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Observations sur les mots -/

/-- Émissions de `i`, dans l'ordre. -/
def sentBy (i : V) (l : List (V × V)) : List (V × V) := l.filter (fun e => e.1 = i)

/-- Recettes de `i`, dans l'ordre. -/
def recvSeq (i : V) (l : List (V × V)) : List (V × V) := l.filter (fun e => e.2 = i)

/-- Recettes de `i`, sans l'ordre. -/
def recvBag (i : V) (l : List (V × V)) : Multiset (V × V) := (recvSeq i l : Multiset (V × V))

/-- La lettre `e` touche l'agent `i`. -/
def touches (i : V) (e : V × V) : Bool := decide (e.1 = i ∨ e.2 = i)

/-- Vue locale de `i` : les lettres qui le touchent, dans l'ordre. -/
def localView (i : V) (l : List (V × V)) : List (V × V) := l.filter (touches i)

/-! ### 2. Descente aux traces -/

omit [Fintype V] in
lemma sentBy_swap (i : V) (u w : List (V × V)) {a b : V × V} (h : I_loc a b) :
    sentBy i (u ++ a :: b :: w) = sentBy i (u ++ b :: a :: w) := by
  unfold sentBy
  simp only [List.filter_append, List.filter_cons]
  by_cases ha : a.1 = i
  · have hb : ¬ b.1 = i := fun hb => h.1 (ha.trans hb.symm)
    simp [ha, hb]
  · by_cases hb : b.1 = i <;> simp [ha, hb]

/-- Les émissions de `i` sont bien définies sur les traces. -/
def sentObs (i : V) : LocTrace V → List (V × V) :=
  Quot.lift (sentBy i) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact sentBy_swap i u w hI)

omit [Fintype V] in
lemma recvBag_swap (i : V) (u w : List (V × V)) (a b : V × V) :
    recvBag i (u ++ a :: b :: w) = recvBag i (u ++ b :: a :: w) := by
  unfold recvBag recvSeq
  exact Multiset.coe_eq_coe.mpr (((List.Perm.swap b a w).append_left u).filter _)

/-- Le multi-ensemble des recettes de `i` est bien défini sur les traces. -/
def recvBagObs (i : V) : LocTrace V → Multiset (V × V) :=
  Quot.lift (recvBag i) (by
    intro _ _ h
    obtain ⟨u, w, a, b, -⟩ := h
    exact recvBag_swap i u w a b)

omit [Fintype V] [DecidableEq V] in
/-- Filtrer par un prédicat de lettre envoie un échange `I_loc` sur un échange `I_loc` ou sur
    une égalité. -/
lemma mk_filter_swap (p : V × V → Bool) (u w : List (V × V)) {a b : V × V} (h : I_loc a b) :
    LocTrace.mk ((u ++ a :: b :: w).filter p) = LocTrace.mk ((u ++ b :: a :: w).filter p) := by
  simp only [List.filter_append, List.filter_cons]
  cases ha : p a <;> cases hb : p b <;> simp only [Bool.false_eq_true, if_false, if_true]
  exact LocTrace.mk_swap _ _ h

/-- Projection sur un sous-alphabet (Zielonka) : endomorphisme de M(V × V, I_loc). -/
def LocTrace.filter (p : V × V → Bool) : LocTrace V → LocTrace V :=
  Quot.lift (fun l => LocTrace.mk (l.filter p)) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact mk_filter_swap p u w hI)

/-- Vue locale de `i`, comme trace : bien définie. -/
def localObs (i : V) : LocTrace V → LocTrace V := LocTrace.filter (touches i)

omit [Fintype V] in
theorem localObs_mk (i : V) (l : List (V × V)) :
    localObs i (LocTrace.mk l) = LocTrace.mk (localView i l) := rfl

omit [Fintype V] in
/-- La SUITE des recettes ne descend pas : deux paiements entrants commutent sous `I_loc`. -/
theorem recvSeq_not_descends {x y i : V} (hxy : x ≠ y) (hxi : x ≠ i) (hyi : y ≠ i) :
    ¬ ∃ F : LocTrace V → List (V × V), ∀ l, F (LocTrace.mk l) = recvSeq i l := by
  rintro ⟨F, hF⟩
  have hswap := LocTrace.mk_swap [] [] (I_loc_shared_receiver hxy hxi hyi)
  have h := (hF _).symm.trans ((congrArg F hswap).trans (hF _))
  simp [recvSeq] at h
  exact hxy h.1

/-! ### 3. Issue privée : les transactions admises qui touchent `i` -/

/-- Transactions admises (pli RTGS) qui touchent `i` : bien défini sur les traces, comme
    composée de `rtgsFoldTrace`. -/
def ownAdmitted (pool : FuturePool V) (demands : V × V → ℤ) (i : V) (t : LocTrace V) :
    Finset (V × V) :=
  (rtgsFoldTrace pool demands t).filter (fun e => touches i e)

theorem ownAdmitted_mk (pool : FuturePool V) (demands : V × V → ℤ) (i : V) (l : List (V × V)) :
    ownAdmitted pool demands i (LocTrace.mk l) =
      (rtgsFold pool demands l).filter (fun e => touches i e) := rfl

/-! ### 4. Fibre non dégénérée (témoin de blocage) -/

section Witness

open LocalCommutation.Gridlock

/-- ★ L'agent `2` a la même vue locale ordonnée (`[f, a]`), donc mêmes émissions et mêmes
    recettes, dans `[g, f, a]` et `[f, g, a]` ; ses transactions admises diffèrent
    (`{f, a}` contre `∅`). Témoin à marges strictes (D1). -/
theorem sce_fiber_nondegenerate :
    sentObs (2 : Fin 4) (LocTrace.mk [g, f, a]) = sentObs 2 (LocTrace.mk [f, g, a]) ∧
    recvBagObs (2 : Fin 4) (LocTrace.mk [g, f, a]) = recvBagObs 2 (LocTrace.mk [f, g, a]) ∧
    localView (2 : Fin 4) [g, f, a] = localView 2 [f, g, a] ∧
    localObs (2 : Fin 4) (LocTrace.mk [g, f, a]) = localObs 2 (LocTrace.mk [f, g, a]) ∧
    ownAdmitted pool demands 2 (LocTrace.mk [g, f, a]) ≠
      ownAdmitted pool demands 2 (LocTrace.mk [f, g, a]) := by
  have hview : localView (2 : Fin 4) [g, f, a] = localView 2 [f, g, a] := by decide
  refine ⟨by decide, ?_, hview, ?_, ?_⟩
  · show (recvSeq (2 : Fin 4) [g, f, a] : Multiset (Fin 4 × Fin 4)) = recvSeq 2 [f, g, a]
    rw [show recvSeq (2 : Fin 4) [g, f, a] = recvSeq 2 [f, g, a] by decide]
  · rw [localObs_mk, localObs_mk, hview]
  · rw [ownAdmitted_mk, ownAdmitted_mk, fold_gfa, fold_fga]
    decide

end Witness

/-! ### 5. (D5) Cohérence SCE : égalité des lois des observations -/

section SCE

variable {Ω O O' : Type*}

/-- Une conjecture `μ` est compatible avec la loi vraie `P` pour l'observation `obs` si elles
    induisent la même loi des observations. -/
def sceConsistent (obs : Ω → O) (μ P : PMF Ω) : Prop := μ.map obs = P.map obs

/-- Fibre des conjectures compatibles. -/
def sceFiber (obs : Ω → O) (P : PMF Ω) : Set (PMF Ω) := {μ | sceConsistent obs μ P}

/-- La mesure vraie est toujours dans sa fibre. -/
theorem sceConsistent_refl (obs : Ω → O) (P : PMF Ω) : sceConsistent obs P P := rfl

theorem sceConsistent_symm {obs : Ω → O} {μ P : PMF Ω} (h : sceConsistent obs μ P) :
    sceConsistent obs P μ := h.symm

theorem sceConsistent_trans {obs : Ω → O} {μ ν P : PMF Ω} (h₁ : sceConsistent obs μ ν)
    (h₂ : sceConsistent obs ν P) : sceConsistent obs μ P := h₁.trans h₂

/-- Une observation plus grossière a une fibre plus grosse. -/
theorem sceConsistent_coarsen {obs : Ω → O} (f : O → O') {μ P : PMF Ω}
    (h : sceConsistent obs μ P) : sceConsistent (f ∘ obs) μ P := by
  unfold sceConsistent at *
  rw [← PMF.map_comp, ← PMF.map_comp, h]

end SCE

section WitnessPMF

open LocalCommutation.Gridlock

/-- ★ Version mesurée : les conjectures de Dirac sur `[g, f, a]` et `[f, g, a]` sont
    compatibles pour la vue locale de l'agent `2`, mais induisent des lois différentes de son
    issue. -/
theorem sce_fiber_nondegenerate_pmf :
    sceConsistent (localObs (2 : Fin 4)) (PMF.pure (LocTrace.mk [g, f, a]))
      (PMF.pure (LocTrace.mk [f, g, a])) ∧
    (PMF.pure (LocTrace.mk [g, f, a])).map (ownAdmitted pool demands 2) ≠
      (PMF.pure (LocTrace.mk [f, g, a])).map (ownAdmitted pool demands 2) := by
  obtain ⟨-, -, -, hloc, hown⟩ := sce_fiber_nondegenerate
  refine ⟨?_, ?_⟩
  · unfold sceConsistent
    rw [PMF.pure_map, PMF.pure_map, hloc]
  · rw [PMF.pure_map, PMF.pure_map]
    intro h
    apply hown
    have hs := congrArg PMF.support h
    rw [PMF.support_pure, PMF.support_pure] at hs
    exact Set.singleton_injective hs

end WitnessPMF

end TraceObservation
