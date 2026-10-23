/-
  ThesePlanetaire/GatedStep.lean
  Phase 2b (2026-10-01) : le pas « tester puis garder » et sa commutation, une fois pour toutes.

  Développé d'abord en `GatedStep_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 2b, étape 1) ; analyse :
  `cache/analyse_forte_connexite_graphe_transactions_2026-10-01.md` (§12).

  Quatre plis du dépôt ont la même forme : un pas `s ↦ if P s a then upd s a else s`
  (`BudgetGatedIndep.admitStep`, `PivotCommutation.pivotStep`, `LocalCommutation.rtgsStep`,
  `LedgerCirculation.ledgerStep`). Leurs preuves de commutation répétaient la même analyse à
  quatre cas ; ce module la fait une fois.
  1. `gatedStep_comm` : si les mises à jour commutent et si chaque test est stable par la mise
     à jour de l'autre lettre, les deux pas commutent. Les hypothèses portent sur l'état
     courant (le pivot en a besoin : ses hypothèses d'atteignabilité dépendent de l'état) ;
  2. `insertStep_comm` : cas `upd = (· ∪ {·})` sur `Finset`, où la commutation des mises à
     jour est `union_singleton_comm` — il ne reste que les deux stabilités ;
  3. `foldl_swap_of_step_comm` / `foldl_swap_of_diamond` : du pas au pli en contexte ;
  4. `Diamond δ I` : la propriété de losange relativement à une indépendance `I` ;
     `isCommutativeUpdate_iff_diamond` : `CommutativeClassification.IsCommutativeUpdate` en est
     le cas `I = ⊤`.
  5. Phase 3 (2026-10-01) : quotient de Mazurkiewicz générique `TraceQ I` (échanges
     `I`-indépendants en contexte), descente `TraceQ.liftFold` de tout pli à losange,
     invariance de la longueur (`TraceQ.length_eq`) et `TraceQ.coarsen` (une indépendance plus petite donne un monoïde plus fin). `LocTrace`
     (`LocalCommutation`) en est l'instance `I_loc`, conservée telle quelle.

  Mathlib seul (plus `CommutativeClassification`, Mathlib seul) : module bas.
-/

import Mathlib.Tactic
import ThesePlanetaire.CommutativeClassification

namespace GatedStep

variable {σ α : Type*}

/-! ### 1. Le pas « tester puis garder » -/

/-- Pas « tester puis garder » : si le test `P` passe, appliquer `upd`, sinon ne rien faire. -/
def gatedStep (P : σ → α → Prop) [∀ s a, Decidable (P s a)] (upd : σ → α → σ) (s : σ)
    (a : α) : σ :=
  if P s a then upd s a else s

/-- ★ Commutation du pas « tester puis garder » depuis l'état `s` : les mises à jour commutent
    et chaque test est stable par la mise à jour de l'autre lettre. -/
theorem gatedStep_comm {P : σ → α → Prop} [∀ s a, Decidable (P s a)] {upd : σ → α → σ}
    {s : σ} {a b : α} (h_upd : upd (upd s a) b = upd (upd s b) a)
    (h_ab : P (upd s b) a ↔ P s a) (h_ba : P (upd s a) b ↔ P s b) :
    gatedStep P upd (gatedStep P upd s a) b = gatedStep P upd (gatedStep P upd s b) a := by
  unfold gatedStep
  by_cases hPa : P s a
  · by_cases hPb : P s b
    · simp only [if_pos hPa, if_pos hPb, if_pos (h_ba.mpr hPb), if_pos (h_ab.mpr hPa), h_upd]
    · simp only [if_pos hPa, if_neg hPb, if_neg (fun h => hPb (h_ba.mp h))]
  · by_cases hPb : P s b
    · simp only [if_neg hPa, if_pos hPb, if_neg (fun h => hPa (h_ab.mp h))]
    · simp only [if_neg hPa, if_neg hPb]

/-! ### 2. Cas de l'insertion dans un `Finset` -/

/-- Deux insertions commutent. -/
theorem union_singleton_comm [DecidableEq α] (S : Finset α) (a b : α) :
    (S ∪ {a}) ∪ {b} = (S ∪ {b}) ∪ {a} :=
  Finset.union_right_comm S {a} {b}

/-- ★ Pas d'admission dans un `Finset` : seules les deux stabilités du test restent à montrer. -/
theorem insertStep_comm [DecidableEq α] {P : Finset α → α → Prop} [∀ s a, Decidable (P s a)]
    {S : Finset α} {a b : α} (h_ab : P (S ∪ {b}) a ↔ P S a) (h_ba : P (S ∪ {a}) b ↔ P S b) :
    gatedStep P (fun T e => T ∪ {e}) (gatedStep P (fun T e => T ∪ {e}) S a) b =
    gatedStep P (fun T e => T ∪ {e}) (gatedStep P (fun T e => T ∪ {e}) S b) a :=
  gatedStep_comm (union_singleton_comm S a b) h_ab h_ba

/-! ### 3. Du pas au pli en contexte -/

/-- Si les deux pas commutent à l'état atteint après le préfixe `u`, l'échange en contexte
    laisse le pli invariant. -/
theorem foldl_swap_of_step_comm (δ : σ → α → σ) (s₀ : σ) (u w : List α) {a b : α}
    (h : δ (δ (u.foldl δ s₀) a) b = δ (δ (u.foldl δ s₀) b) a) :
    (u ++ a :: b :: w).foldl δ s₀ = (u ++ b :: a :: w).foldl δ s₀ := by
  simp only [List.foldl_append, List.foldl_cons, h]

/-- Propriété de losange de `δ` relativement à l'indépendance `I` : depuis tout état, deux
    lettres indépendantes commutent. -/
def Diamond (δ : σ → α → σ) (I : α → α → Prop) : Prop :=
  ∀ s a b, I a b → δ (δ s a) b = δ (δ s b) a

/-- ★ Losange ⟹ commutation du pli en contexte, depuis tout état initial. -/
theorem foldl_swap_of_diamond {δ : σ → α → σ} {I : α → α → Prop} (hD : Diamond δ I) (s₀ : σ)
    (u w : List α) {a b : α} (h : I a b) :
    (u ++ a :: b :: w).foldl δ s₀ = (u ++ b :: a :: w).foldl δ s₀ :=
  foldl_swap_of_step_comm δ s₀ u w (hD _ a b h)

/-- `IsCommutativeUpdate` est le losange pour l'indépendance totale. -/
theorem isCommutativeUpdate_iff_diamond (δ : σ → α → σ) :
    CommutativeClassification.IsCommutativeUpdate δ ↔ Diamond δ (fun _ _ => True) :=
  ⟨fun h s a b _ => h s a b, fun h s a b => h s a b trivial⟩

/-! ### 4. Monoïde de traces générique -/

/-- Générateurs de la congruence de Mazurkiewicz pour `I` (échange en contexte). -/
inductive SwapRel (I : α → α → Prop) : List α → List α → Prop
  | swap (u w : List α) (a b : α) (h : I a b) : SwapRel I (u ++ a :: b :: w) (u ++ b :: a :: w)

/-- Monoïde de traces M(α, I) : mots modulo la clôture d'équivalence des échanges `I`. -/
def TraceQ (I : α → α → Prop) := Quot (SwapRel I)

/-- Classe d'un mot. -/
def TraceQ.mk (I : α → α → Prop) (l : List α) : TraceQ I := Quot.mk _ l

theorem TraceQ.mk_swap {I : α → α → Prop} (u w : List α) {a b : α} (h : I a b) :
    TraceQ.mk I (u ++ a :: b :: w) = TraceQ.mk I (u ++ b :: a :: w) :=
  Quot.sound (SwapRel.swap u w a b h)

/-- Descente sur M(α, I) de tout pli à losange pour `I`. -/
def TraceQ.liftFold {I : α → α → Prop} (δ : σ → α → σ) (s₀ : σ) (hD : Diamond δ I) :
    TraceQ I → σ :=
  Quot.lift (fun l => l.foldl δ s₀) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact foldl_swap_of_diamond hD s₀ u w hI)

theorem TraceQ.liftFold_mk {I : α → α → Prop} (δ : σ → α → σ) (s₀ : σ) (hD : Diamond δ I)
    (l : List α) : TraceQ.liftFold δ s₀ hD (TraceQ.mk I l) = l.foldl δ s₀ := rfl

/-- La longueur est un invariant de trace. -/
theorem TraceQ.length_eq {I : α → α → Prop} {w w' : List α}
    (h : TraceQ.mk I w = TraceQ.mk I w') : w.length = w'.length :=
  congrArg (Quot.lift List.length (by
    intro _ _ h
    obtain ⟨u, w, a, b, _⟩ := h
    simp)) h

/-- `I ⊆ J` : l'identité des mots induit un morphisme M(α, I) → M(α, J). -/
def TraceQ.coarsen {I J : α → α → Prop} (hIJ : ∀ a b, I a b → J a b) : TraceQ I → TraceQ J :=
  Quot.lift (TraceQ.mk J) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact TraceQ.mk_swap u w (hIJ a b hI))

theorem TraceQ.coarsen_mk {I J : α → α → Prop} (hIJ : ∀ a b, I a b → J a b) (l : List α) :
    TraceQ.coarsen hIJ (TraceQ.mk I l) = TraceQ.mk J l := rfl

end GatedStep
