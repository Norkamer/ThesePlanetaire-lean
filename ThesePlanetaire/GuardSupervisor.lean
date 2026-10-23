/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/GuardSupervisor.lean
  Phase 9 (2026-10-02) : sûreté minimale — la garde est le superviseur maximal ; réserve pour
  lettres incontrôlables selon la mémoire ; pont avec la dynamique des mesures (budget `stock`).

  Développé d'abord en `GuardSupervisor_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase9_2026-10-02/plan_phase9.md` ; analyse :
  `cache/analyse_phase9_mesures_prix_etat_surete_2026-10-02.md` ; sondes S1-S4, S8a, S12
  (`cache/phase9_2026-10-02/outils/`).
-/

import ThesePlanetaire.LedgerClock
import ThesePlanetaire.MeasureFibration

/-!
# La garde comme superviseur maximal, la réserve pour incontrôlables

Théorie du contrôle supervisé (Ramadge–Wonham) sur le modèle de charge des Phases 6-8 : une
charge `L : ℕ`, des émissions `e a` contrôlables, un top de période `tick` incontrôlable
(toujours tirable).

1. ★ `guard_safe`, `guard_maximal`, `guard_is_canonPA` : la garde `L + e a ≤ cap` est sûre dès
   que le top ne fait pas monter la charge (`tickOp_le`, les trois mémoires), et **maximale** :
   tout superviseur sûr n'autorise, sur ses états atteignables, que ce que la garde autorise.
   Sa boucle fermée est le modèle canonique gardé `LedgerClock.canonPA` ; le relèvement au grand
   livre passe par `LedgerClock.clockP_projectsOn`.
2. ★ `reserve_maximal`, `reserve_ci_iff`, `stock_unc_empty`, `regen_unc_empty`,
   `regen_reserve_iff`, `flow_reserve_iff` : avec une lettre **incontrôlable** (émission `eu`,
   au plus `m` fois par période), le plus grand ensemble contrôlé-invariant est contenu dans la
   réserve `X_res = {(L, j) | L + eu·(m − j) ≤ cap}` ; elle est invariante ssi le top la
   restaure (`TopOK`), soit `eu·m ≤ cap` (flow), `eu·m ≤ min r cap` (regen), `eu·m = 0` (stock).
   En `stock` (et en `regen` si `r < eu·m`), aucun état n'est viable.
3. ★ `stock_guard_necessary` : sous la demande minimale atteignable cumulée
   (`MeasureFibration.stock_infeasible_iff`), laisser passer toutes les lettres d'une dynamique
   des mesures pure n'est **pas** sûr, alors que la garde l'est. La mesure ne peut pas ; la
   garde peut, et elle ne refuse que le nécessaire (`guard_maximal`).
-/

namespace GuardSupervisor

open LocalTraceLang (PAut run run_append run_singleton)
open FeedbackClass (Memory Governance tickOp)
open LedgerClock (fits canonPA canonPA_some)
open MeasureFibration (MGInst Box load minLoad stock_measure_cannot)

/-! ## §1. La garde est le superviseur maximal -/

section Guard

variable {α : Type*}

/-- Un superviseur autorise ou non l'émission `a` à la charge `L` ; le top n'est pas
contrôlable. -/
abbrev Supervisor (α : Type*) := ℕ → α → Prop

/-- Boucle fermée en sémantique partielle : le top est toujours tirable, une émission ne l'est
que si le superviseur l'autorise. -/
def closedLoop (tick : ℕ → ℕ) (e : α → ℕ) (S : Supervisor α) [∀ L a, Decidable (S L a)] :
    PAut ℕ (Option α)
  | L, none => some (tick L)
  | L, some a => if S L a then some (L + e a) else none

/-- Charges atteignables depuis `L₀` en boucle fermée. -/
inductive Reach (tick : ℕ → ℕ) (e : α → ℕ) (S : Supervisor α) (L₀ : ℕ) : ℕ → Prop
  | init : Reach tick e S L₀ L₀
  | top {L : ℕ} : Reach tick e S L₀ L → Reach tick e S L₀ (tick L)
  | emit {L : ℕ} {a : α} : Reach tick e S L₀ L → S L a → Reach tick e S L₀ (L + e a)

variable {tick : ℕ → ℕ} {e : α → ℕ} {S : Supervisor α} {L₀ cap : ℕ}

/-- `Reach` est exactement l'ensemble des charges lues par les mots de la boucle fermée. -/
theorem reach_iff_run [∀ L a, Decidable (S L a)] (L : ℕ) :
    Reach tick e S L₀ L ↔ ∃ w, run (closedLoop tick e S) L₀ w = some L := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨[], rfl⟩
    | @top L _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨w ++ [none], by rw [run_append, hw]; rfl⟩
    | @emit L a _ hS ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨w ++ [some a], ?_⟩
      rw [run_append, hw]
      simp [closedLoop, hS]
  · rintro ⟨w, hw⟩
    induction w using List.reverseRecOn generalizing L with
    | nil =>
      cases hw
      exact Reach.init
    | append_singleton w x ih =>
      rw [run_append] at hw
      cases hr : run (closedLoop tick e S) L₀ w with
      | none => rw [hr] at hw; cases hw
      | some L' =>
        rw [hr] at hw
        have hL' := ih L' hr
        cases x with
        | none =>
          simp only [Option.bind_some, run_singleton, closedLoop] at hw
          cases hw
          exact Reach.top hL'
        | some a =>
          simp only [Option.bind_some, run_singleton, closedLoop] at hw
          split_ifs at hw with hS
          cases hw
          exact Reach.emit hL' hS

/-- Sûreté : toute charge atteignable reste sous le plafond. -/
def SafeSup (tick : ℕ → ℕ) (e : α → ℕ) (cap L₀ : ℕ) (S : Supervisor α) : Prop :=
  ∀ L, Reach tick e S L₀ L → L ≤ cap

/-- La garde « premier arrivé » : autoriser `a` ssi la charge reste sous le plafond. -/
def guard (cap : ℕ) (e : α → ℕ) : Supervisor α := fun L a => L + e a ≤ cap

instance (cap : ℕ) (e : α → ℕ) (L : ℕ) (a : α) : Decidable (guard cap e L a) :=
  inferInstanceAs (Decidable (L + e a ≤ cap))

theorem guard_iff_fits (L : ℕ) (a : α) : guard cap e L a ↔ fits .gated cap L (e a) := by
  simp [guard, fits]

/-- Le top ne fait jamais monter la charge, quelle que soit la mémoire. -/
theorem tickOp_le (mem : Memory) (r L : ℕ) : tickOp mem r L ≤ L := by
  cases mem
  · exact le_rfl
  · exact Nat.sub_le L r
  · exact Nat.zero_le L

/-- ★ La garde est sûre dès que le top ne fait pas monter la charge. -/
theorem guard_safe (htick : ∀ L, tick L ≤ L) (hL₀ : L₀ ≤ cap) :
    SafeSup tick e cap L₀ (guard cap e) := by
  intro L h
  induction h with
  | init => exact hL₀
  | top _ ih => exact le_trans (htick _) ih
  | emit _ hS _ => exact hS

/-- ★ **Maximalité** : tout superviseur sûr atteint moins de charges que la garde, et n'autorise,
sur ses états atteignables, que ce que la garde autorise. -/
theorem guard_maximal (hS : SafeSup tick e cap L₀ S) :
    (∀ L, Reach tick e S L₀ L → Reach tick e (guard cap e) L₀ L) ∧
      ∀ L a, Reach tick e S L₀ L → S L a → guard cap e L a := by
  have h2 : ∀ L a, Reach tick e S L₀ L → S L a → guard cap e L a :=
    fun L a hL ha => hS _ (Reach.emit hL ha)
  refine ⟨fun L h => ?_, h2⟩
  induction h with
  | init => exact Reach.init
  | top _ ih => exact Reach.top ih
  | emit hL ha ih => exact Reach.emit ih (h2 _ _ hL ha)

/-- ★ La boucle fermée de la garde est le modèle canonique gardé de la Phase 8. -/
theorem guard_is_canonPA (mem : Memory) (r : ℕ) :
    closedLoop (tickOp mem r) e (guard cap e) = canonPA (tickOp mem r) .gated e cap := by
  funext L x
  cases x with
  | none => rfl
  | some a =>
    simp only [closedLoop, canonPA_some]
    by_cases h : L + e a ≤ cap <;> simp [guard, fits, h]

end Guard

/-! ## §2. Réserve pour lettres incontrôlables

État `(L, j)` : charge et nombre de lettres incontrôlables tirées dans la période. Une lettre
incontrôlable émet `eu` et peut survenir tant que `j < m` ; le top applique `tick` et remet `j`
à zéro. Les lettres contrôlables peuvent toujours être refusées : elles ne contraignent pas
l'invariance. -/

section Reserve

/-- Ensemble contrôlé-invariant : sûr, fermé par la lettre incontrôlable et par le top. -/
def ControlledInvariant (tick : ℕ → ℕ) (eu m cap : ℕ) (X : ℕ × ℕ → Prop) : Prop :=
  (∀ L j, X (L, j) → L ≤ cap) ∧
    (∀ L j, X (L, j) → j < m → X (L + eu, j + 1)) ∧
    ∀ L j, X (L, j) → X (tick L, 0)

/-- La réserve : de quoi absorber les lettres incontrôlables restantes de la période. -/
def Xres (eu m cap : ℕ) : ℕ × ℕ → Prop := fun q => q.1 + eu * (m - q.2) ≤ cap

/-- La garde avec réserve : autoriser `a` ssi l'état suivant reste dans la réserve. -/
def reserveGuard {α : Type*} (eu m cap : ℕ) (e : α → ℕ) (q : ℕ × ℕ) (a : α) : Prop :=
  Xres eu m cap (q.1 + e a, q.2)

/-- Le top restaure la réserve : depuis toute charge sûre, la période suivante peut absorber
`m` lettres incontrôlables. -/
def TopOK (tick : ℕ → ℕ) (eu m cap : ℕ) : Prop := ∀ L, L ≤ cap → tick L + eu * m ≤ cap

variable {tick : ℕ → ℕ} {eu m cap : ℕ} {X : ℕ × ℕ → Prop}

theorem ci_unc_iter (hX : ControlledInvariant tick eu m cap X) {L j : ℕ} (h : X (L, j)) :
    ∀ i, j + i ≤ m → X (L + eu * i, j + i) := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
    intro hi
    have := hX.2.1 _ _ (ih (by omega)) (by omega)
    rw [show L + eu * (i + 1) = L + eu * i + eu by ring, show j + (i + 1) = j + i + 1 by omega]
    exact this

/-- ★ Tout ensemble contrôlé-invariant est contenu dans la réserve : depuis `(L, j)` hors de
`X_res`, le mot incontrôlable `u^(m − j)` dépasse le plafond. -/
theorem reserve_maximal (hX : ControlledInvariant tick eu m cap X) :
    ∀ q, X q → Xres eu m cap q := by
  rintro ⟨L, j⟩ h
  show L + eu * (m - j) ≤ cap
  by_cases hj : j ≤ m
  · have := ci_unc_iter hX h (m - j) (by omega)
    rw [show j + (m - j) = m by omega] at this
    exact hX.1 _ _ this
  · rw [show m - j = 0 by omega, mul_zero, add_zero]
    exact hX.1 _ _ h

/-- ★ La réserve est contrôlé-invariante ssi le top la restaure. -/
theorem reserve_ci_iff : ControlledInvariant tick eu m cap (Xres eu m cap) ↔ TopOK tick eu m cap := by
  constructor
  · rintro ⟨_, _, htop⟩ L hL
    have := htop L m (by show L + eu * (m - m) ≤ cap; simpa using hL)
    simpa [Xres] using this
  · intro hT
    refine ⟨fun L j h => ?_, fun L j h hj => ?_, fun L j h => ?_⟩
    · exact le_trans (Nat.le_add_right _ _) h
    · show L + eu + eu * (m - (j + 1)) ≤ cap
      have h' : L + eu * (m - j) ≤ cap := h
      have hs : eu * (m - j) = eu + eu * (m - (j + 1)) := by
        rw [show m - j = (m - (j + 1)) + 1 by omega]
        ring
      calc L + eu + eu * (m - (j + 1)) = L + eu * (m - j) := by rw [hs]; ring
        _ ≤ cap := h'
    · show tick L + eu * (m - 0) ≤ cap
      rw [Nat.sub_zero]
      exact hT L (le_trans (Nat.le_add_right _ _) h)

/-- La garde avec réserve préserve la réserve. -/
theorem reserveGuard_preserves {α : Type*} (e : α → ℕ) (q : ℕ × ℕ) (a : α)
    (h : reserveGuard eu m cap e q a) : Xres eu m cap (q.1 + e a, q.2) := h

theorem topOK_stock_iff (r : ℕ) : TopOK (tickOp .stock r) eu m cap ↔ eu * m = 0 := by
  simp only [TopOK, tickOp]
  generalize eu * m = k
  exact ⟨fun h => by have := h cap le_rfl; omega, fun h L hL => by omega⟩

theorem topOK_flow_iff (r : ℕ) : TopOK (tickOp .flow r) eu m cap ↔ eu * m ≤ cap := by
  simp only [TopOK, tickOp]
  generalize eu * m = k
  exact ⟨fun h => by have := h 0 (Nat.zero_le _); omega, fun h L _ => by omega⟩

theorem topOK_regen_iff (r : ℕ) : TopOK (tickOp .regen r) eu m cap ↔ eu * m ≤ min r cap := by
  simp only [TopOK, tickOp, le_min_iff]
  generalize eu * m = k
  constructor
  · intro h
    have h1 := h cap le_rfl
    have h2 := h 0 (Nat.zero_le _)
    omega
  · rintro ⟨h1, h2⟩ L hL
    omega

/-- ★ `regen` : la réserve est contrôlé-invariante ssi `eu·m ≤ min r cap`. -/
theorem regen_reserve_iff (r : ℕ) :
    ControlledInvariant (tickOp .regen r) eu m cap (Xres eu m cap) ↔ eu * m ≤ min r cap :=
  reserve_ci_iff.trans (topOK_regen_iff r)

/-- ★ `flow` : la réserve est contrôlé-invariante ssi `eu·m ≤ cap`. -/
theorem flow_reserve_iff (r : ℕ) :
    ControlledInvariant (tickOp .flow r) eu m cap (Xres eu m cap) ↔ eu * m ≤ cap :=
  reserve_ci_iff.trans (topOK_flow_iff r)

/-- Si chaque période (top compris) fait monter la charge, aucun état n'est viable. -/
theorem unc_empty_of_growth (hg : ∀ L, L + 1 ≤ tick (L + eu * m))
    (hX : ControlledInvariant tick eu m cap X) : ∀ q, ¬ X q := by
  rintro ⟨L, j⟩ hq
  have key : ∀ k, ∃ L', X (L', 0) ∧ k ≤ L' := by
    intro k
    induction k with
    | zero => exact ⟨tick L, hX.2.2 L j hq, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨L', hL', hk⟩ := ih
      have h1 := ci_unc_iter hX hL' m (by omega)
      rw [Nat.zero_add] at h1
      exact ⟨tick (L' + eu * m), hX.2.2 _ _ h1, by have := hg L'; omega⟩
  obtain ⟨L', hL', hk⟩ := key (cap + 1)
  have := hX.1 L' 0 hL'
  omega

/-- ★ `stock` : avec des lettres incontrôlables effectives, aucun état n'est viable. -/
theorem stock_unc_empty (r : ℕ) (h : 0 < eu * m)
    (hX : ControlledInvariant (tickOp .stock r) eu m cap X) : ∀ q, ¬ X q :=
  unc_empty_of_growth (fun L => by simp only [tickOp]; omega) hX

/-- ★ `regen` : si les incontrôlables d'une période dépassent la régénération, aucun état n'est
viable. -/
theorem regen_unc_empty (r : ℕ) (h : r < eu * m)
    (hX : ControlledInvariant (tickOp .regen r) eu m cap X) : ∀ q, ¬ X q :=
  unc_empty_of_growth (fun L => by simp only [tickOp]; omega) hX

end Reserve

/-! ## §3. Pont avec la dynamique des mesures : la mesure ne peut pas, la garde peut -/

section Bridge

variable {α : Type*}

/-- Sans refus, toute lettre passe : on atteint la somme de tout ensemble de lettres. -/
theorem reach_free_sum (tick : ℕ → ℕ) (e : α → ℕ) (L₀ : ℕ) (s : Finset α) :
    Reach tick e (fun _ _ => True) L₀ (L₀ + ∑ a ∈ s, e a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Reach.init
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, show L₀ + (e a + ∑ x ∈ s, e x) = L₀ + ∑ x ∈ s, e x + e a by ring]
    exact Reach.emit ih trivial

variable {ι B : Type*} [Fintype ι] {T : ℕ}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Instance à charges entières, lue dans 𝕜 (la capacité par fibre ne sert pas ici). -/
def natInst (aP aM : ι → B → ℕ) : MGInst 𝕜 ι B where
  aP := fun i μ => aP i μ
  aM := fun i μ => aM i μ
  L := fun _ => 0

/-- Lettres d'une dynamique des mesures **pure** le long des états visités `s` : la lettre
`(t, i)` émet la charge de la stratégie choisie par `i` au pas `t`. -/
def pureEmit (aP aM : ι → B → ℕ) (s : Fin T → B) (σ : Fin T → ι → Bool) : Fin T × ι → ℕ :=
  fun ti => if σ ti.1 ti.2 then aP ti.2 (s ti.1) else aM ti.2 (s ti.1)

/-- La section `±1` d'un profil pur. -/
def pureSection (σ : Fin T → ι → Bool) (t : Fin T) : ι → 𝕜 := fun i => if σ t i then 1 else -1

theorem cast_pureEmit_sum (aP aM : ι → B → ℕ) (s : Fin T → B) (σ : Fin T → ι → Bool) :
    ((∑ ti, pureEmit aP aM s σ ti : ℕ) : 𝕜) = ∑ t, load (natInst aP aM) (pureSection σ t) (s t) := by
  rw [Nat.cast_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [pureEmit, pureSection, natInst]
  split_ifs <;> ring

/-- ★ **La mesure ne peut pas, la garde peut.** Sous la demande minimale atteignable cumulée,
pour **toute** dynamique des mesures pure `σ`, laisser passer toutes ses lettres (superviseur
trivial) n'est pas sûr en mémoire `stock`, alors que la garde l'est ; et par `guard_maximal`,
tout superviseur sûr refuse au moins ce que la garde refuse. Les sections mixtes sont couvertes
par `MeasureFibration.stock_measure_cannot`. -/
theorem stock_guard_necessary (aP aM : ι → B → ℕ) (s : Fin T → B) (cap r : ℕ)
    (h : (cap : 𝕜) < ∑ t, minLoad (natInst aP aM) (s t)) (σ : Fin T → ι → Bool) :
    ¬ SafeSup (tickOp .stock r) (pureEmit aP aM s σ) cap 0 (fun _ _ => True) ∧
      SafeSup (tickOp .stock r) (pureEmit aP aM s σ) cap 0 (guard cap (pureEmit aP aM s σ)) := by
  refine ⟨fun hS => ?_, guard_safe (fun L => tickOp_le .stock r L) (Nat.zero_le _)⟩
  have hr := hS _ (reach_free_sum (tickOp .stock r) (pureEmit aP aM s σ) 0 Finset.univ)
  have hm : ∀ t, Box (pureSection (𝕜 := 𝕜) σ t) := fun t i => by
    unfold pureSection
    split_ifs <;> norm_num
  have hlt := stock_measure_cannot (natInst aP aM) s h (pureSection σ) hm
  rw [← cast_pureEmit_sum] at hlt
  rw [Nat.zero_add] at hr
  have hc : ((∑ ti, pureEmit aP aM s σ ti : ℕ) : 𝕜) ≤ cap := by exact_mod_cast hr
  linarith

end Bridge

end GuardSupervisor

/-!
## Domaine (généralisation D-13, 2026-10-03)

Les déclarations de la section `Bridge` qui lisent les charges entières dans un corps (`natInst`,
`pureSection`, `cast_pureEmit_sum`, `stock_guard_necessary`) sont énoncées sur un corps ordonné
quelconque `𝕜`. Le reste du module est dans `ℕ` (émissions et capacités entières, hypothèse R5) :
la généralisation n'y touche pas.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration`. `ℚ` et
  `ℝ` en sont des instances ; les énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
