/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/GuardField.lean
  Phase 16 (2026-10-04) : la garde et la réserve sur un corps ordonné (papier 11, théorèmes A
  et B) ; lecture des trois mémoires en seau à jetons ; non-blocage dans la période ; maximum
  sur les fibres ; ponts ℕ → 𝕜.

  Développé d'abord en `GuardField_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase16_2026-10-04/plan.md` ; analyse :
  `cache/phase16_2026-10-04/analyse_droits_echeances_2026-10-04.md` ; comparaison :
  `ThèseNov26/couche3_dynamique/P11_garde/comparaison.md`.
-/

import ThesePlanetaire.ReserveCoverage

/-!
# La garde et la réserve sur un corps ordonné

Les théorèmes A et B du papier 11 (`GuardSupervisor`, `ReserveCoverage`) sont énoncés dans `ℕ`.
Ce module les reprend sur un corps ordonné `𝕜` (décision D-13), et ajoute deux compléments.

1. ★ `guardF_safe`, `guardF_maximal`, `stock_guard_necessaryF` : la garde `L + e a ≤ cap` est
   sûre dès que le top ne sort pas du plafond, et maximale ; laisser passer toutes les lettres
   d'une dynamique des mesures pure n'est pas sûr en `stock` sous la demande minimale cumulée.
2. ★ `tickOpF_tokens` : les trois mémoires sont des seaux à jetons. Les jetons `cap − L`
   deviennent `min (cap − L + ρ) cap` au top, avec un débit `ρ = rhoF mem r cap` (0 en `stock`,
   `min r cap` en `regen`, `cap` en `flow`) ; donc `ρ ≤ cap`.
3. ★ `reserveF_maximal`, `reserveF_ci_iff`, `topOKF_iff`, `viableF_iff`, `coverageF_iff` : la
   réserve pour les lettres incontrôlables, et la condition de couverture `M ≤ ρ`, où `M` est la
   masse incontrôlable d'une période. Les noyaux vides (`stockF_unc_empty`, `regenF_unc_empty`,
   `uncSetF_empty_of_growth`) demandent un corps **archimédien**.
4. ★ `nb_reserve_necessary`, `nbGuard_safe`, `nbGuard_nonblocking`, `nbGuard_maximal` :
   non-blocage dans la période. Des lots essentiels doivent être servis avant la fin de la
   période ; le superviseur sûr non bloquant maximal autorise une émission discrétionnaire `a`
   ssi `L + e a + Σ_P b ≤ cap`. La garde gloutonne bloque (`greedy_blocks`, sonde S4c).
5. ★ `coverage_all_fibers_iff`, `uncMass_perDraw`, `fibers_strict` : couvrir toutes les fibres,
   c'est couvrir le maximum `uncMassMax` ; si la fibre change à chaque tirage, le pire cas est
   `Σ_i max_μ`, strictement plus grand en général.
6. Ponts : `tickOpF_cast`, `xresF_cast_iff`, `uncMassF_natInst`, `reachF_cast`.
-/

namespace GuardField

open LocalTraceLang (PAut run run_append run_singleton)
open FeedbackClass (Memory tickOp)
open MeasureFibration (MGInst Ω ξ Box load minLoad stock_measure_cannot)
open GuardSupervisor (pureSection natInst)
open ReserveCoverage (omegaOf)

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## §1. La garde est le superviseur maximal (théorème A) -/

section Guard

variable {α : Type*}

/-- Un superviseur autorise ou non l'émission `a` à la charge `L` ; le top n'est pas
contrôlable. -/
abbrev SupervisorF (𝕜 α : Type*) := 𝕜 → α → Prop

/-- Boucle fermée en sémantique partielle : le top est toujours tirable, une émission ne l'est
que si le superviseur l'autorise. -/
def closedLoopF (tick : 𝕜 → 𝕜) (e : α → 𝕜) (S : SupervisorF 𝕜 α) [∀ L a, Decidable (S L a)] :
    PAut 𝕜 (Option α)
  | L, none => some (tick L)
  | L, some a => if S L a then some (L + e a) else none

/-- Charges atteignables depuis `L₀` en boucle fermée. -/
inductive ReachF (tick : 𝕜 → 𝕜) (e : α → 𝕜) (S : SupervisorF 𝕜 α) (L₀ : 𝕜) : 𝕜 → Prop
  | init : ReachF tick e S L₀ L₀
  | top {L : 𝕜} : ReachF tick e S L₀ L → ReachF tick e S L₀ (tick L)
  | emit {L : 𝕜} {a : α} : ReachF tick e S L₀ L → S L a → ReachF tick e S L₀ (L + e a)

variable {tick : 𝕜 → 𝕜} {e : α → 𝕜} {S : SupervisorF 𝕜 α} {L₀ cap : 𝕜}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- `ReachF` est exactement l'ensemble des charges lues par les mots de la boucle fermée. -/
theorem reachF_iff_run [∀ L a, Decidable (S L a)] (L : 𝕜) :
    ReachF tick e S L₀ L ↔ ∃ w, run (closedLoopF tick e S) L₀ w = some L := by
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
      simp [closedLoopF, hS]
  · rintro ⟨w, hw⟩
    induction w using List.reverseRecOn generalizing L with
    | nil =>
      cases hw
      exact ReachF.init
    | append_singleton w x ih =>
      rw [run_append] at hw
      cases hr : run (closedLoopF tick e S) L₀ w with
      | none => rw [hr] at hw; cases hw
      | some L' =>
        rw [hr] at hw
        have hL' := ih L' hr
        cases x with
        | none =>
          simp only [Option.bind_some, run_singleton, closedLoopF] at hw
          cases hw
          exact ReachF.top hL'
        | some a =>
          simp only [Option.bind_some, run_singleton, closedLoopF] at hw
          split_ifs at hw with hS
          cases hw
          exact ReachF.emit hL' hS

/-- Sûreté : toute charge atteignable reste sous le plafond. -/
def SafeSupF (tick : 𝕜 → 𝕜) (e : α → 𝕜) (cap L₀ : 𝕜) (S : SupervisorF 𝕜 α) : Prop :=
  ∀ L, ReachF tick e S L₀ L → L ≤ cap

/-- La garde « premier arrivé » : autoriser `a` ssi la charge reste sous le plafond. -/
def guardF (cap : 𝕜) (e : α → 𝕜) : SupervisorF 𝕜 α := fun L a => L + e a ≤ cap

instance (cap : 𝕜) (e : α → 𝕜) (L : 𝕜) (a : α) : Decidable (guardF cap e L a) :=
  inferInstanceAs (Decidable (L + e a ≤ cap))

omit [IsStrictOrderedRing 𝕜] in
/-- ★ La garde est sûre dès que le top ne fait pas sortir du plafond. -/
theorem guardF_safe (htick : ∀ L, L ≤ cap → tick L ≤ cap) (hL₀ : L₀ ≤ cap) :
    SafeSupF tick e cap L₀ (guardF cap e) := by
  intro L h
  induction h with
  | init => exact hL₀
  | top _ ih => exact htick _ ih
  | emit _ hS _ => exact hS

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Maximalité** : tout superviseur sûr atteint moins de charges que la garde, et n'autorise,
sur ses états atteignables, que ce que la garde autorise. -/
theorem guardF_maximal (hS : SafeSupF tick e cap L₀ S) :
    (∀ L, ReachF tick e S L₀ L → ReachF tick e (guardF cap e) L₀ L) ∧
      ∀ L a, ReachF tick e S L₀ L → S L a → guardF cap e L a := by
  have h2 : ∀ L a, ReachF tick e S L₀ L → S L a → guardF cap e L a :=
    fun L a hL ha => hS _ (ReachF.emit hL ha)
  refine ⟨fun L h => ?_, h2⟩
  induction h with
  | init => exact ReachF.init
  | top _ ih => exact ReachF.top ih
  | emit hL ha ih => exact ReachF.emit ih (h2 _ _ hL ha)

end Guard

/-! ### Le top des trois mémoires, et sa lecture en seau à jetons -/

section Tick

/-- Effet du top de période sur la charge `L` (la soustraction tronquée de `ℕ` devient
`max (L − r) 0`). -/
def tickOpF : Memory → 𝕜 → 𝕜 → 𝕜
  | .stock, _, L => L
  | .regen, r, L => max (L - r) 0
  | .flow, _, _ => 0

/-- Débit du seau à jetons de chaque mémoire. -/
def rhoF : Memory → 𝕜 → 𝕜 → 𝕜
  | .stock, _, _ => 0
  | .regen, r, cap => min r cap
  | .flow, _, cap => cap

variable {r cap L : 𝕜}

/-- Le top ne fait jamais monter une charge positive (régénération positive). -/
theorem tickOpF_le (mem : Memory) (hr : 0 ≤ r) (hL : 0 ≤ L) : tickOpF mem r L ≤ L := by
  cases mem
  · exact le_rfl
  · exact max_le (by linarith) hL
  · exact hL

/-- Le top ne fait pas sortir du plafond. -/
theorem tickOpF_le_cap (mem : Memory) (hr : 0 ≤ r) (hcap : 0 ≤ cap) (hL : L ≤ cap) :
    tickOpF mem r L ≤ cap := by
  cases mem
  · exact hL
  · exact max_le (by linarith) hcap
  · exact hcap

omit [IsStrictOrderedRing 𝕜] in
theorem tickOpF_nonneg_of_ne_stock (mem : Memory) (h : mem ≠ .stock) (r L : 𝕜) :
    0 ≤ tickOpF mem r L := by
  cases mem
  · exact absurd rfl h
  · exact le_max_right _ _
  · exact le_rfl

omit [IsStrictOrderedRing 𝕜] in
theorem rhoF_le_cap (mem : Memory) (hcap : 0 ≤ cap) : rhoF mem r cap ≤ cap := by
  cases mem
  · exact hcap
  · exact min_le_right _ _
  · exact le_rfl

omit [IsStrictOrderedRing 𝕜] in
theorem rhoF_nonneg (mem : Memory) (hr : 0 ≤ r) (hcap : 0 ≤ cap) : 0 ≤ rhoF mem r cap := by
  cases mem
  · exact le_rfl
  · exact le_min hr hcap
  · exact hcap

/-- ★ **Seau à jetons.** Les jetons `cap − L` deviennent `min (cap − L + ρ) cap` au top, avec
le débit `ρ = rhoF mem r cap` : 0 en `stock`, `min r cap` en `regen`, `cap` en `flow`. -/
theorem tickOpF_tokens (mem : Memory) (hL : 0 ≤ L) (hLc : L ≤ cap) :
    cap - tickOpF mem r L = min (cap - L + rhoF mem r cap) cap := by
  cases mem
  · simp only [tickOpF, rhoF, add_zero]
    rw [min_eq_left (by linarith)]
  · simp only [tickOpF, rhoF]
    rcases le_total r cap with h | h
    · rw [min_eq_left h]
      rcases le_total (L - r) 0 with h' | h'
      · rw [max_eq_right h', min_eq_right (by linarith)]
        ring
      · rw [max_eq_left h', min_eq_left (by linarith)]
        ring
    · rw [min_eq_right h, min_eq_right (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
  · simp only [tickOpF, rhoF]
    rw [min_eq_right (by linarith)]
    ring

end Tick

/-! ### La mesure ne peut pas, la garde peut -/

section Bridge

variable {α : Type*}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Sans refus, toute lettre passe : on atteint la somme de tout ensemble de lettres. -/
theorem reachF_free_sum (tick : 𝕜 → 𝕜) (e : α → 𝕜) (L₀ : 𝕜) (s : Finset α) :
    ReachF tick e (fun _ _ => True) L₀ (L₀ + ∑ a ∈ s, e a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ReachF.init
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, show L₀ + (e a + ∑ x ∈ s, e x) = L₀ + ∑ x ∈ s, e x + e a by ring]
    exact ReachF.emit ih trivial

variable {ι B : Type*} [Fintype ι] {T : ℕ}

/-- Lettres d'une dynamique des mesures **pure** le long des états visités `s` : la lettre
`(t, i)` émet la charge de la stratégie choisie par `i` au pas `t`. -/
def pureEmitF (G : MGInst 𝕜 ι B) (s : Fin T → B) (σ : Fin T → ι → Bool) : Fin T × ι → 𝕜 :=
  fun ti => if σ ti.1 ti.2 then G.aP ti.2 (s ti.1) else G.aM ti.2 (s ti.1)

theorem sum_pureEmitF (G : MGInst 𝕜 ι B) (s : Fin T → B) (σ : Fin T → ι → Bool) :
    ∑ ti, pureEmitF G s σ ti = ∑ t, load G (pureSection σ t) (s t) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [pureEmitF, pureSection]
  split_ifs <;> ring

/-- ★ **La mesure ne peut pas, la garde peut** (sur un corps). Sous la demande minimale
atteignable cumulée, laisser passer toutes les lettres d'une dynamique des mesures pure n'est pas
sûr en `stock`, alors que la garde l'est ; par `guardF_maximal`, tout superviseur sûr refuse au
moins ce que la garde refuse. -/
theorem stock_guard_necessaryF (G : MGInst 𝕜 ι B) (s : Fin T → B) (cap r : 𝕜) (hcap : 0 ≤ cap)
    (h : cap < ∑ t, minLoad G (s t)) (σ : Fin T → ι → Bool) :
    ¬ SafeSupF (tickOpF .stock r) (pureEmitF G s σ) cap 0 (fun _ _ => True) ∧
      SafeSupF (tickOpF .stock r) (pureEmitF G s σ) cap 0 (guardF cap (pureEmitF G s σ)) := by
  refine ⟨fun hS => ?_, guardF_safe (fun L hL => hL) hcap⟩
  have hr := hS _ (reachF_free_sum (tickOpF .stock r) (pureEmitF G s σ) 0 Finset.univ)
  have hm : ∀ t, Box (pureSection (𝕜 := 𝕜) σ t) := fun t i => by
    unfold pureSection
    split_ifs <;> norm_num
  have hlt := stock_measure_cannot G s h (pureSection σ) hm
  rw [← sum_pureEmitF, ← zero_add (∑ ti, pureEmitF G s σ ti)] at hlt
  linarith

end Bridge

/-! ## §2. Réserve pour lettres incontrôlables (théorème B)

État `(L, j)` : charge et nombre de lettres incontrôlables tirées dans la période (`eu` chacune,
au plus `m` par période) ; puis sources multiples `U`, chacune au plus une fois par période. -/

section Reserve

/-- Ensemble contrôlé-invariant : sûr, fermé par la lettre incontrôlable et par le top. -/
def ControlledInvariantF (tick : 𝕜 → 𝕜) (eu : 𝕜) (m : ℕ) (cap : 𝕜) (X : 𝕜 × ℕ → Prop) : Prop :=
  (∀ L j, X (L, j) → L ≤ cap) ∧
    (∀ L j, X (L, j) → j < m → X (L + eu, j + 1)) ∧
    ∀ L j, X (L, j) → X (tick L, 0)

/-- La réserve : de quoi absorber les lettres incontrôlables restantes de la période. -/
def XresF (eu : 𝕜) (m : ℕ) (cap : 𝕜) : 𝕜 × ℕ → Prop := fun q => q.1 + eu * ((m - q.2 : ℕ) : 𝕜) ≤ cap

/-- Le top restaure la réserve. -/
def TopOKF (tick : 𝕜 → 𝕜) (eu : 𝕜) (m : ℕ) (cap : 𝕜) : Prop :=
  ∀ L, L ≤ cap → tick L + eu * m ≤ cap

variable {tick : 𝕜 → 𝕜} {eu cap : 𝕜} {m : ℕ} {X : 𝕜 × ℕ → Prop}

theorem ciF_unc_iter (hX : ControlledInvariantF tick eu m cap X) {L : 𝕜} {j : ℕ} (h : X (L, j)) :
    ∀ i : ℕ, j + i ≤ m → X (L + eu * i, j + i) := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
    intro hi
    have := hX.2.1 _ _ (ih (by omega)) (by omega)
    rw [show L + eu * ((i + 1 : ℕ) : 𝕜) = L + eu * i + eu by push_cast; ring,
      show j + (i + 1) = j + i + 1 by omega]
    exact this

/-- ★ Tout ensemble contrôlé-invariant est contenu dans la réserve. -/
theorem reserveF_maximal (hX : ControlledInvariantF tick eu m cap X) :
    ∀ q, X q → XresF eu m cap q := by
  rintro ⟨L, j⟩ h
  show L + eu * ((m - j : ℕ) : 𝕜) ≤ cap
  by_cases hj : j ≤ m
  · have := ciF_unc_iter hX h (m - j) (by omega)
    rw [show j + (m - j) = m by omega] at this
    exact hX.1 _ _ this
  · rw [show m - j = 0 by omega, Nat.cast_zero, mul_zero, add_zero]
    exact hX.1 _ _ h

/-- ★ La réserve est contrôlé-invariante ssi le top la restaure (émissions incontrôlables
positives). -/
theorem reserveF_ci_iff (heu : 0 ≤ eu) :
    ControlledInvariantF tick eu m cap (XresF eu m cap) ↔ TopOKF tick eu m cap := by
  constructor
  · rintro ⟨_, _, htop⟩ L hL
    have := htop L m (by show L + eu * ((m - m : ℕ) : 𝕜) ≤ cap; simpa using hL)
    simpa [XresF] using this
  · intro hT
    refine ⟨fun L j h => ?_, fun L j h hj => ?_, fun L j h => ?_⟩
    · have : (0 : 𝕜) ≤ eu * ((m - j : ℕ) : 𝕜) := mul_nonneg heu (Nat.cast_nonneg _)
      have h' : L + eu * ((m - j : ℕ) : 𝕜) ≤ cap := h
      linarith
    · show L + eu + eu * ((m - (j + 1) : ℕ) : 𝕜) ≤ cap
      have h' : L + eu * ((m - j : ℕ) : 𝕜) ≤ cap := h
      have hs : ((m - j : ℕ) : 𝕜) = ((m - (j + 1) : ℕ) : 𝕜) + 1 := by
        rw [show m - j = (m - (j + 1)) + 1 by omega]
        push_cast
        ring
      rw [hs] at h'
      linarith
    · show tick L + eu * ((m - 0 : ℕ) : 𝕜) ≤ cap
      have : (0 : 𝕜) ≤ eu * ((m - j : ℕ) : 𝕜) := mul_nonneg heu (Nat.cast_nonneg _)
      have h' : L + eu * ((m - j : ℕ) : 𝕜) ≤ cap := h
      rw [Nat.sub_zero]
      exact hT L (by linarith)

/-- ★ **Une seule condition pour les trois mémoires** : le top restaure la réserve ssi la masse
incontrôlable d'une période est sous le débit du seau, `eu·m ≤ ρ`. -/
theorem topOKF_iff (mem : Memory) (r : 𝕜) :
    TopOKF (tickOpF mem r) eu m cap ↔ eu * m ≤ rhoF mem r cap := by
  cases mem
  · simp only [TopOKF, tickOpF, rhoF]
    exact ⟨fun h => by have := h cap le_rfl; linarith, fun h L hL => by linarith⟩
  · simp only [TopOKF, tickOpF, rhoF, le_min_iff]
    constructor
    · intro h
      have h1 := h cap le_rfl
      constructor <;> linarith [le_max_left (cap - r) 0, le_max_right (cap - r) 0]
    · rintro ⟨h1, h2⟩ L hL
      rcases le_total (L - r) 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
  · simp only [TopOKF, tickOpF, rhoF]
    exact ⟨fun h => by have := h cap le_rfl; linarith, fun h L _ => by linarith⟩

/-- ★ Réserve et mémoire : la réserve est contrôlé-invariante ssi `eu·m ≤ ρ`. -/
theorem reserveF_iff (mem : Memory) (r : 𝕜) (heu : 0 ≤ eu) :
    ControlledInvariantF (tickOpF mem r) eu m cap (XresF eu m cap) ↔ eu * m ≤ rhoF mem r cap :=
  (reserveF_ci_iff heu).trans (topOKF_iff mem r)

/-- Si chaque période (top compris) fait monter la charge d'au moins `δ > 0`, aucun état n'est
viable (corps archimédien). -/
theorem uncF_empty_of_growth [Archimedean 𝕜] {δ : 𝕜} (hδ : 0 < δ)
    (hg : ∀ L, L + δ ≤ tick (L + eu * m)) (hX : ControlledInvariantF tick eu m cap X) :
    ∀ q, ¬ X q := by
  rintro ⟨L, j⟩ hq
  have key : ∀ k : ℕ, ∃ L', X (L', 0) ∧ tick L + k * δ ≤ L' := by
    intro k
    induction k with
    | zero => exact ⟨tick L, hX.2.2 L j hq, by simp⟩
    | succ k ih =>
      obtain ⟨L', hL', hk⟩ := ih
      have h1 := ciF_unc_iter hX hL' m (by omega)
      rw [Nat.zero_add] at h1
      refine ⟨tick (L' + eu * m), hX.2.2 _ _ h1, ?_⟩
      have := hg L'
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((cap - tick L) / δ)
  obtain ⟨L', hL', hkL⟩ := key k
  have h1 := hX.1 L' 0 hL'
  have h2 : cap - tick L < k * δ := (div_lt_iff₀ hδ).mp hk
  linarith

/-- ★ `stock` : avec des lettres incontrôlables effectives, aucun état n'est viable. -/
theorem stockF_unc_empty [Archimedean 𝕜] (r : 𝕜) (h : 0 < eu * m)
    (hX : ControlledInvariantF (tickOpF .stock r) eu m cap X) : ∀ q, ¬ X q :=
  uncF_empty_of_growth h (fun _ => le_rfl) hX

/-- ★ `regen` : si les incontrôlables d'une période dépassent la régénération, aucun état n'est
viable. -/
theorem regenF_unc_empty [Archimedean 𝕜] (r : 𝕜) (h : r < eu * m)
    (hX : ControlledInvariantF (tickOpF .regen r) eu m cap X) : ∀ q, ¬ X q :=
  uncF_empty_of_growth (δ := eu * m - r) (by linarith)
    (fun L => by simp only [tickOpF]; linarith [le_max_left (L + eu * m - r) 0]) hX

/-! ### Sources multiples -/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Ensemble contrôlé-invariant à sources multiples : une source `u ∉ J` peut toujours survenir ;
le top remet `J` à `∅`. -/
def ControlledInvariantSetF (tick : 𝕜 → 𝕜) (eu : U → 𝕜) (cap : 𝕜) (X : 𝕜 × Finset U → Prop) :
    Prop :=
  (∀ L J, X (L, J) → L ≤ cap) ∧
    (∀ L J u, X (L, J) → u ∉ J → X (L + eu u, insert u J)) ∧
    ∀ L J, X (L, J) → X (tick L, ∅)

/-- La réserve : de quoi absorber les sources restantes de la période. -/
def XresSetF (eu : U → 𝕜) (cap : 𝕜) : 𝕜 × Finset U → Prop :=
  fun q => q.1 + ∑ u ∈ q.2ᶜ, eu u ≤ cap

variable {eus : U → 𝕜} {Y : 𝕜 × Finset U → Prop}

omit [Fintype U] [IsStrictOrderedRing 𝕜] in
/-- Tirer d'un coup un ensemble de sources encore disponibles. -/
theorem ciSetF_draw (hY : ControlledInvariantSetF tick eus cap Y) {L : 𝕜} {J : Finset U}
    (h : Y (L, J)) : ∀ K : Finset U, Disjoint K J → Y (L + ∑ u ∈ K, eus u, J ∪ K) := by
  intro K
  induction K using Finset.induction_on with
  | empty => intro _; simpa using h
  | insert u K hu ih =>
    intro hd
    have hd' : Disjoint K J := Finset.disjoint_of_subset_left (Finset.subset_insert u K) hd
    have huJ : u ∉ J ∪ K := by
      simp only [Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_left.mp hd (Finset.mem_insert_self u K), hu⟩
    have := hY.2.1 _ _ u (ih hd') huJ
    rw [Finset.sum_insert hu, Finset.union_insert,
      show L + (eus u + ∑ x ∈ K, eus x) = L + ∑ x ∈ K, eus x + eus u by ring]
    exact this

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Tout ensemble contrôlé-invariant est contenu dans la réserve. -/
theorem reserveSetF_maximal (hY : ControlledInvariantSetF tick eus cap Y) :
    ∀ q, Y q → XresSetF eus cap q := by
  rintro ⟨L, J⟩ h
  exact hY.1 _ _ (ciSetF_draw hY h Jᶜ disjoint_compl_left)

/-- ★ La réserve est contrôlé-invariante ssi le top la restaure, pour la masse totale `Σ_u eu u`
tirée au plus une fois par période. -/
theorem reserveSetF_ci_iff (heu : ∀ u, 0 ≤ eus u) :
    ControlledInvariantSetF tick eus cap (XresSetF eus cap) ↔ TopOKF tick (∑ u, eus u) 1 cap := by
  have hpos : ∀ J : Finset U, (0 : 𝕜) ≤ ∑ u ∈ J, eus u := fun J => Finset.sum_nonneg fun u _ => heu u
  constructor
  · rintro ⟨_, _, htop⟩ L hL
    have := htop L Finset.univ (by simpa [XresSetF] using hL)
    simpa [XresSetF] using this
  · intro hT
    refine ⟨fun L J h => ?_, fun L J u h hu => ?_, fun L J h => ?_⟩
    · have h' : L + ∑ u ∈ Jᶜ, eus u ≤ cap := h
      linarith [hpos Jᶜ]
    · show L + eus u + ∑ x ∈ (insert u J)ᶜ, eus x ≤ cap
      have hs := Finset.add_sum_erase Jᶜ eus (Finset.mem_compl.mpr hu)
      rw [Finset.compl_insert, add_assoc, hs]
      exact h
    · show tick L + ∑ x ∈ (∅ : Finset U)ᶜ, eus x ≤ cap
      have h' : L + ∑ u ∈ Jᶜ, eus u ≤ cap := h
      rw [Finset.compl_empty]
      simpa using hT L (by linarith [hpos Jᶜ])

/-- Si chaque période (top compris) fait monter la charge d'au moins `δ > 0`, aucun état n'est
viable (corps archimédien). -/
theorem uncSetF_empty_of_growth [Archimedean 𝕜] {δ : 𝕜} (hδ : 0 < δ)
    (hg : ∀ L, L + δ ≤ tick (L + ∑ u, eus u)) (hY : ControlledInvariantSetF tick eus cap Y) :
    ∀ q, ¬ Y q := by
  rintro ⟨L, J⟩ hq
  have key : ∀ k : ℕ, ∃ L', Y (L', ∅) ∧ tick L + k * δ ≤ L' := by
    intro k
    induction k with
    | zero => exact ⟨tick L, hY.2.2 L J hq, by simp⟩
    | succ k ih =>
      obtain ⟨L', hL', hk⟩ := ih
      have h1 := ciSetF_draw hY hL' Finset.univ (Finset.disjoint_empty_right _)
      rw [Finset.empty_union] at h1
      refine ⟨tick (L' + ∑ u, eus u), hY.2.2 _ _ h1, ?_⟩
      have := hg L'
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((cap - tick L) / δ)
  obtain ⟨L', hL', hkL⟩ := key k
  have h1 := hY.1 L' ∅ hL'
  have h2 : cap - tick L < k * δ := (div_lt_iff₀ hδ).mp hk
  linarith

/-- Viabilité : il existe un ensemble contrôlé-invariant non vide. -/
def ViableF (tick : 𝕜 → 𝕜) (eu : U → 𝕜) (cap : 𝕜) : Prop :=
  ∃ X, ControlledInvariantSetF tick eu cap X ∧ ∃ q, X q

/-- ★ **Viabilité par mémoire** (corps archimédien) : un état viable existe ssi la masse
incontrôlable d'une période est sous le débit du seau, `Σ_u eu u ≤ ρ`. -/
theorem viableF_iff [Archimedean 𝕜] (mem : Memory) (r : 𝕜) (heu : ∀ u, 0 ≤ eus u) :
    ViableF (tickOpF mem r) eus cap ↔ ∑ u, eus u ≤ rhoF mem r cap := by
  constructor
  · rintro ⟨Y, hY, ⟨L, J⟩, hq⟩
    have hres := reserveSetF_maximal hY _ (hY.2.2 L J hq)
    simp only [XresSetF, Finset.compl_empty] at hres
    by_contra hlt
    replace hlt := not_le.mp hlt
    cases mem
    · exact uncSetF_empty_of_growth (δ := ∑ u, eus u) (by simpa [rhoF] using hlt)
        (fun L => by simp [tickOpF]) hY _ hq
    · simp only [rhoF, min_lt_iff] at hlt
      rcases hlt with hlt | hlt
      · exact uncSetF_empty_of_growth (δ := ∑ u, eus u - r) (by linarith)
          (fun L => by simp only [tickOpF]; linarith [le_max_left (L + ∑ u, eus u - r) 0])
          hY _ hq
      · have := le_max_right (L - r) 0
        simp only [tickOpF] at hres
        linarith
    · simp only [tickOpF, rhoF] at hres hlt
      linarith
  · intro h
    refine ⟨_, (reserveSetF_ci_iff heu).mpr ((topOKF_iff mem r).mpr (by simpa using h)),
      (cap - ∑ u, eus u, ∅), ?_⟩
    simp [XresSetF]

end Reserve

/-! ### Couverture : partition de Ω et masse incontrôlable -/

section Coverage

variable {ι B Un : Type*} [Fintype ι] [DecidableEq ι] [Fintype Un] [DecidableEq Un]

/-- Masse incontrôlable : pire cas des agents hors de l'ensemble couvert `A`, sur la fibre `μ`. -/
def uncMassF (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) : 𝕜 :=
  ∑ i ∈ Aᶜ, max (G.aP i μ) (G.aM i μ)

theorem max_eq_omega_abs (a b : 𝕜) : max a b = (a + b) / 2 + |(a - b) / 2| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    ring

/-- ★ La masse incontrôlable est `Σ_{i ∉ A} (Ω_i + |ξ_i|)`. -/
theorem uncMassF_eq (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) :
    uncMassF G A μ = ∑ i ∈ Aᶜ, (omegaOf G i μ + |ξ G i μ|) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [max_eq_omega_abs]
  rfl

/-- ★ Pire cas : toute section de la boîte charge les agents non couverts d'au plus la masse
incontrôlable. -/
theorem uncLoadF_le_uncMassF (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) {m : ι → 𝕜} (hm : Box m) :
    ∑ i ∈ Aᶜ, ((1 + m i) / 2 * G.aP i μ + (1 - m i) / 2 * G.aM i μ) ≤ uncMassF G A μ := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : G.aP i μ ≤ max (G.aP i μ) (G.aM i μ) := le_max_left _ _
  have h2 : G.aM i μ ≤ max (G.aP i μ) (G.aM i μ) := le_max_right _ _
  obtain ⟨hl, hu⟩ := hm i
  have := mul_le_mul_of_nonneg_left h1 (show (0 : 𝕜) ≤ (1 + m i) / 2 by linarith)
  have := mul_le_mul_of_nonneg_left h2 (show (0 : 𝕜) ≤ (1 - m i) / 2 by linarith)
  nlinarith

/-- ★ … et ce pire cas est atteint par une section pure. -/
theorem uncMassF_attained (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) :
    ∃ m : ι → 𝕜, Box m ∧
      ∑ i ∈ Aᶜ, ((1 + m i) / 2 * G.aP i μ + (1 - m i) / 2 * G.aM i μ) = uncMassF G A μ := by
  refine ⟨fun i => if G.aM i μ ≤ G.aP i μ then 1 else -1,
    fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  split_ifs with h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right (le_of_not_ge h)]; ring

/-- Émission des sources incontrôlables : nature (`enat`) et agents non couverts. -/
def srcEmitF (enat : Un → 𝕜) (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) : Un ⊕ ι → 𝕜
  | .inl n => enat n
  | .inr i => if i ∈ A then 0 else max (G.aP i μ) (G.aM i μ)

omit [DecidableEq Un] [IsStrictOrderedRing 𝕜] in
theorem sum_srcEmitF (enat : Un → 𝕜) (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) :
    ∑ u, srcEmitF enat G A μ u = ∑ n, enat n + uncMassF G A μ := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [uncMassF, ← Finset.sum_compl_add_sum A]
  simp only [srcEmitF]
  rw [Finset.sum_ite_of_true (fun i hi => hi), Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i hi => if_neg (Finset.mem_compl.mp hi)

/-- ★ **Couverture par mémoire** (corps archimédien) : avec `M = E_nat + uncMass`, un état viable
existe ssi `M ≤ ρ` — soit `M = 0` en `stock`, `M ≤ min r cap` en `regen`, `M ≤ cap` en
`flow`. -/
theorem coverageF_iff [Archimedean 𝕜] (mem : Memory) (r cap : 𝕜) {enat : Un → 𝕜}
    {G : MGInst 𝕜 ι B} {A : Finset ι} {μ : B} (henat : ∀ n, 0 ≤ enat n)
    (hG : ∀ i, 0 ≤ G.aP i μ ∧ 0 ≤ G.aM i μ) :
    ViableF (tickOpF mem r) (srcEmitF enat G A μ) cap ↔
      ∑ n, enat n + uncMassF G A μ ≤ rhoF mem r cap := by
  rw [viableF_iff mem r, sum_srcEmitF]
  rintro (n | i)
  · exact henat n
  · simp only [srcEmitF]
    split_ifs
    · exact le_rfl
    · exact le_trans (hG i).1 (le_max_left _ _)

omit [IsStrictOrderedRing 𝕜] in
/-- Couverture totale : sans agent non couvert, seule l'émission naturelle reste. -/
theorem uncMassF_univ (G : MGInst 𝕜 ι B) (μ : B) : uncMassF G Finset.univ μ = 0 := by
  simp [uncMassF]

end Coverage

/-! ## §3. Non-blocage : des lots essentiels à servir dans la période

État `(L, P)` : charge et lots essentiels encore en attente. Une émission discrétionnaire `a`
(charge `e a`) est toujours tirable ; le service d'un lot `k ∈ P` (charge `b k`) le retire de
`P`. Le superviseur peut refuser les deux. L'état est **marqué** quand `P = ∅` : tous les lots
essentiels de la période ont été servis. Les lots sont indivisibles. -/

section NonBlocking

variable {α κ : Type*} [DecidableEq κ]

/-- Un pas : émission discrétionnaire ou service d'un lot essentiel. -/
def stepNB (e : α → 𝕜) (b : κ → 𝕜) (q : 𝕜 × Finset κ) : α ⊕ κ → 𝕜 × Finset κ
  | .inl a => (q.1 + e a, q.2)
  | .inr k => (q.1 + b k, q.2.erase k)

/-- Une lettre est tirable : toute émission discrétionnaire, et le service d'un lot en attente. -/
def Fires (q : 𝕜 × Finset κ) : α ⊕ κ → Prop
  | .inl _ => True
  | .inr k => k ∈ q.2

/-- États atteignables en boucle fermée depuis `q₀`. -/
inductive ReachNB (e : α → 𝕜) (b : κ → 𝕜) (S : 𝕜 × Finset κ → α ⊕ κ → Prop)
    (q₀ : 𝕜 × Finset κ) : 𝕜 × Finset κ → Prop
  | init : ReachNB e b S q₀ q₀
  | step {q : 𝕜 × Finset κ} {x : α ⊕ κ} :
      ReachNB e b S q₀ q → Fires q x → S q x → ReachNB e b S q₀ (stepNB e b q x)

/-- Sûreté : toute charge atteignable reste sous le plafond. -/
def SafeNB (e : α → 𝕜) (b : κ → 𝕜) (S : 𝕜 × Finset κ → α ⊕ κ → Prop) (cap : 𝕜)
    (q₀ : 𝕜 × Finset κ) : Prop :=
  ∀ q, ReachNB e b S q₀ q → q.1 ≤ cap

/-- Non-blocage : depuis tout état atteignable, un état marqué reste atteignable. -/
def NonBlocking (e : α → 𝕜) (b : κ → 𝕜) (S : 𝕜 × Finset κ → α ⊕ κ → Prop)
    (q₀ : 𝕜 × Finset κ) : Prop :=
  ∀ q, ReachNB e b S q₀ q → ∃ L, ReachNB e b S q (L, ∅)

/-- La réserve de non-blocage : de quoi servir les lots essentiels en attente. -/
def ResNB (b : κ → 𝕜) (cap : 𝕜) (q : 𝕜 × Finset κ) : Prop := q.1 + ∑ k ∈ q.2, b k ≤ cap

/-- La garde de non-blocage : autoriser une lettre ssi l'état suivant reste dans la réserve ;
pour une émission discrétionnaire, ssi `L + e a + Σ_P b ≤ cap`. -/
def nbGuard (e : α → 𝕜) (b : κ → 𝕜) (cap : 𝕜) : 𝕜 × Finset κ → α ⊕ κ → Prop :=
  fun q x => ResNB b cap (stepNB e b q x)

/-- La garde gloutonne : autoriser une lettre ssi la charge suivante reste sous le plafond. -/
def greedyNB (e : α → 𝕜) (b : κ → 𝕜) (cap : 𝕜) : 𝕜 × Finset κ → α ⊕ κ → Prop :=
  fun q x => (stepNB e b q x).1 ≤ cap

variable {e : α → 𝕜} {b : κ → 𝕜} {S : 𝕜 × Finset κ → α ⊕ κ → Prop} {cap : 𝕜}
  {q₀ : 𝕜 × Finset κ}

omit [IsStrictOrderedRing 𝕜] in
theorem nbGuard_inl (q : 𝕜 × Finset κ) (a : α) :
    nbGuard e b cap q (.inl a) ↔ q.1 + e a + ∑ k ∈ q.2, b k ≤ cap := Iff.rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem reachNB_trans {q q' : 𝕜 × Finset κ} (h : ReachNB e b S q₀ q) (h' : ReachNB e b S q q') :
    ReachNB e b S q₀ q' := by
  induction h' with
  | init => exact h
  | step _ hf hs ih => exact ReachNB.step ih hf hs

/-- Le potentiel `L + Σ_P b` ne décroît pas le long d'un déroulé (émissions positives). -/
theorem reachNB_pot (he : ∀ a, 0 ≤ e a) {q q' : 𝕜 × Finset κ} (h : ReachNB e b S q q') :
    q.1 + ∑ k ∈ q.2, b k ≤ q'.1 + ∑ k ∈ q'.2, b k := by
  induction h with
  | init => exact le_rfl
  | @step q x _ hf _ ih =>
    cases x with
    | inl a =>
      simp only [stepNB]
      linarith [he a]
    | inr k =>
      simp only [stepNB]
      have hs := Finset.add_sum_erase q.2 b hf
      linarith

/-- ★ **La réserve est nécessaire** : tout superviseur sûr et non bloquant garde, sur ses états
atteignables, de quoi servir les lots essentiels en attente. -/
theorem nb_reserve_necessary (he : ∀ a, 0 ≤ e a) (hS : SafeNB e b S cap q₀)
    (hN : NonBlocking e b S q₀) : ∀ q, ReachNB e b S q₀ q → ResNB b cap q := by
  intro q hq
  obtain ⟨L, hL⟩ := hN q hq
  have h1 := reachNB_pot he hL
  have h2 := hS _ (reachNB_trans hq hL)
  simp only [Finset.sum_empty, add_zero] at h1 h2
  exact le_trans h1 h2

omit [IsStrictOrderedRing 𝕜] in
theorem nbGuard_inv (h₀ : ResNB b cap q₀) {q : 𝕜 × Finset κ}
    (hq : ReachNB e b (nbGuard e b cap) q₀ q) : ResNB b cap q := by
  induction hq with
  | init => exact h₀
  | step _ _ hs _ => exact hs

/-- ★ La garde de non-blocage est sûre. -/
theorem nbGuard_safe (hb : ∀ k, 0 ≤ b k) (h₀ : ResNB b cap q₀) :
    SafeNB e b (nbGuard e b cap) cap q₀ := by
  intro q hq
  have h := nbGuard_inv h₀ hq
  have : (0 : 𝕜) ≤ ∑ k ∈ q.2, b k := Finset.sum_nonneg fun k _ => hb k
  unfold ResNB at h
  linarith

omit [IsStrictOrderedRing 𝕜] in
/-- Depuis un état de la réserve, la garde laisse servir tous les lots en attente. -/
theorem nbGuard_serve_all (P : Finset κ) :
    ∀ L, ResNB b cap (L, P) → ReachNB e b (nbGuard e b cap) (L, P) (L + ∑ k ∈ P, b k, ∅) := by
  induction P using Finset.induction_on with
  | empty => intro L _; simpa using ReachNB.init
  | insert k P hk ih =>
    intro L hL
    have hst : stepNB e b (L, insert k P) (.inr k) = (L + b k, P) := by
      simp [stepNB, Finset.erase_insert hk]
    have hres : ResNB b cap (L + b k, P) := by
      unfold ResNB at hL ⊢
      rw [Finset.sum_insert hk] at hL
      simpa [add_assoc] using hL
    have h1 : ReachNB e b (nbGuard e b cap) (L, insert k P) (L + b k, P) := by
      rw [← hst]
      exact ReachNB.step ReachNB.init (Finset.mem_insert_self k P) (by rw [nbGuard, hst]; exact hres)
    have h2 := ih (L + b k) hres
    rw [Finset.sum_insert hk, ← add_assoc]
    exact reachNB_trans h1 h2

omit [IsStrictOrderedRing 𝕜] in
/-- ★ La garde de non-blocage est non bloquante. -/
theorem nbGuard_nonblocking (h₀ : ResNB b cap q₀) : NonBlocking e b (nbGuard e b cap) q₀ :=
  fun q hq => ⟨_, nbGuard_serve_all q.2 q.1 (nbGuard_inv h₀ hq)⟩

/-- ★ **Maximalité** : tout superviseur sûr et non bloquant atteint moins d'états que la garde de
non-blocage, et n'autorise, sur ses états atteignables, que ce qu'elle autorise. -/
theorem nbGuard_maximal (he : ∀ a, 0 ≤ e a) (hS : SafeNB e b S cap q₀)
    (hN : NonBlocking e b S q₀) :
    (∀ q, ReachNB e b S q₀ q → ReachNB e b (nbGuard e b cap) q₀ q) ∧
      ∀ q x, ReachNB e b S q₀ q → Fires q x → S q x → nbGuard e b cap q x := by
  have h2 : ∀ q x, ReachNB e b S q₀ q → Fires q x → S q x → nbGuard e b cap q x :=
    fun q x hq hf hs => nb_reserve_necessary he hS hN _ (ReachNB.step hq hf hs)
  refine ⟨fun q h => ?_, h2⟩
  induction h with
  | init => exact ReachNB.init
  | step hq hf hs ih => exact ReachNB.step ih hf (h2 _ _ hq hf hs)

omit [IsStrictOrderedRing 𝕜] in
/-- La garde gloutonne est sûre. -/
theorem greedyNB_safe (h₀ : q₀.1 ≤ cap) : SafeNB e b (greedyNB e b cap) cap q₀ := by
  intro q hq
  induction hq with
  | init => exact h₀
  | step _ _ hs _ => exact hs

/-- ★ **Témoin (sonde S4c)** : émission discrétionnaire 2, lot essentiel 3, plafond 7. La garde
gloutonne est sûre mais bloquante : elle atteint `(6, {()})`, où plus rien ne passe. La garde de
non-blocage refuse déjà en `(4, {()})`. -/
theorem greedy_blocks :
    SafeNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
        (greedyNB (fun _ => 2) (fun _ => 3) 7) 7 (0, {()}) ∧
      ¬ NonBlocking (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
        (greedyNB (fun _ => 2) (fun _ => 3) 7) (0, {()}) ∧
      ¬ nbGuard (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ)) 7 (4, {()}) (.inl ()) := by
  refine ⟨greedyNB_safe (by norm_num), fun hN => ?_, by simp [nbGuard_inl]; norm_num⟩
  -- trois émissions discrétionnaires mènent à `(6, {()})`
  have h2 : ReachNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
      (greedyNB (fun _ => 2) (fun _ => 3) 7) (0, {()}) (6, {()}) := by
    have e1 := ReachNB.step (e := fun _ : Unit => (2 : ℚ)) (b := fun _ : Unit => (3 : ℚ))
      (x := .inl ()) ReachNB.init trivial
      (show greedyNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ)) 7 (0, {()}) (.inl ()) by
        simp [greedyNB, stepNB]; norm_num)
    have e2 := ReachNB.step (x := .inl ()) e1 trivial
      (show greedyNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ)) 7 _ (.inl ()) by
        simp [greedyNB, stepNB]; norm_num)
    have e3 := ReachNB.step (x := .inl ()) e2 trivial
      (show greedyNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ)) 7 _ (.inl ()) by
        simp [greedyNB, stepNB]; norm_num)
    convert e3 using 1
    simp [stepNB]
    norm_num
  obtain ⟨L, hL⟩ := hN _ h2
  -- depuis `(6, {()})`, aucune lettre ne passe
  have stuck : ∀ q, ReachNB (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
      (greedyNB (fun _ => 2) (fun _ => 3) 7) (6, {()}) q → q = (6, {()}) := by
    intro q hq
    induction hq with
    | init => rfl
    | @step q x _ _ hs ih =>
      subst ih
      cases x <;> simp [greedyNB, stepNB] at hs <;> norm_num at hs
  have := stuck _ hL
  simp at this

end NonBlocking

/-! ## §4. Maximum sur les fibres

La garde ne connaît pas la fibre `μ`. Si la fibre est fixée pour tout le déroulé, couvrir toutes
les fibres, c'est couvrir le maximum `uncMassMax`. Si elle change à chaque tirage, le pire cas
par agent est `Σ_i max_μ`, plus grand en général (`fibers_strict`). -/

section Fibers

variable {ι B Un : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [Nonempty B] [Fintype Un]
  [DecidableEq Un]

/-- Masse incontrôlable au pire des fibres. -/
def uncMassMax (G : MGInst 𝕜 ι B) (A : Finset ι) : 𝕜 :=
  Finset.univ.sup' Finset.univ_nonempty (uncMassF G A)

/-- Masse incontrôlable quand la fibre change à chaque tirage : pire cas par agent. -/
def uncMassDraw (G : MGInst 𝕜 ι B) (A : Finset ι) : 𝕜 :=
  ∑ i ∈ Aᶜ, Finset.univ.sup' Finset.univ_nonempty (fun μ => max (G.aP i μ) (G.aM i μ))

omit [IsStrictOrderedRing 𝕜] in
theorem uncMassF_le_max (G : MGInst 𝕜 ι B) (A : Finset ι) (μ : B) :
    uncMassF G A μ ≤ uncMassMax G A :=
  Finset.le_sup' _ (Finset.mem_univ μ)

omit [IsStrictOrderedRing 𝕜] in
theorem uncMassMax_attained (G : MGInst 𝕜 ι B) (A : Finset ι) :
    ∃ μ, uncMassF G A μ = uncMassMax G A := by
  obtain ⟨μ, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (uncMassF G A)
  exact ⟨μ, h.symm⟩

/-- ★ **Toutes les fibres** (corps archimédien) : la garde est viable sur chaque fibre ssi
`E_nat + uncMassMax ≤ ρ`. -/
theorem coverage_all_fibers_iff [Archimedean 𝕜] (mem : Memory) (r cap : 𝕜) {enat : Un → 𝕜}
    {G : MGInst 𝕜 ι B} {A : Finset ι} (henat : ∀ n, 0 ≤ enat n)
    (hG : ∀ i μ, 0 ≤ G.aP i μ ∧ 0 ≤ G.aM i μ) :
    (∀ μ, ViableF (tickOpF mem r) (srcEmitF enat G A μ) cap) ↔
      ∑ n, enat n + uncMassMax G A ≤ rhoF mem r cap := by
  have key : ∀ μ, ViableF (tickOpF mem r) (srcEmitF enat G A μ) cap ↔
      ∑ n, enat n + uncMassF G A μ ≤ rhoF mem r cap :=
    fun μ => coverageF_iff mem r cap henat (fun i => hG i μ)
  simp only [key]
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := uncMassMax_attained G A
    rw [← hμ]
    exact h μ
  · intro h μ
    linarith [uncMassF_le_max G A μ]

/-- ★ Si la fibre change à chaque tirage, le pire cas par agent majore le pire cas par fibre. -/
theorem uncMass_perDraw (G : MGInst 𝕜 ι B) (A : Finset ι) : uncMassMax G A ≤ uncMassDraw G A := by
  refine Finset.sup'_le _ _ fun μ _ => Finset.sum_le_sum fun i _ => ?_
  exact Finset.le_sup' (fun μ => max (G.aP i μ) (G.aM i μ)) (Finset.mem_univ μ)

/-- Témoin : deux agents, deux fibres ; l'agent `i` émet 1 sur la fibre `i`, 0 sinon. -/
def fibInst : MGInst ℚ (Fin 2) (Fin 2) where
  aP := fun i μ => if i = μ then 1 else 0
  aM := fun _ _ => 0
  L := fun _ => 0

/-- ★ **Témoin strict** : sans couverture, le pire cas par fibre vaut 1, le pire cas par tirage
vaut 2. -/
theorem fibers_strict : uncMassMax fibInst ∅ = 1 ∧ uncMassDraw fibInst ∅ = 2 := by
  have hf : ∀ μ : Fin 2, uncMassF fibInst ∅ μ = 1 := by
    intro μ
    fin_cases μ <;> simp [uncMassF, fibInst, Fin.sum_univ_two]
  have hd : ∀ i : Fin 2,
      Finset.univ.sup' Finset.univ_nonempty (fun μ => max (fibInst.aP i μ) (fibInst.aM i μ)) = 1 := by
    intro i
    refine le_antisymm (Finset.sup'_le _ _ fun μ _ => ?_) ?_
    · simp only [fibInst]
      split_ifs <;> norm_num
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ i))
      simp [fibInst]
  refine ⟨le_antisymm (Finset.sup'_le _ _ fun μ _ => le_of_eq (hf μ)) ?_, ?_⟩
  · exact le_trans (le_of_eq (hf 0).symm) (uncMassF_le_max fibInst ∅ 0)
  · simp only [uncMassDraw, hd, Finset.compl_empty, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num

end Fibers

/-! ## §5. Ponts `ℕ → 𝕜` -/

section Cast

/-- Le top de `ℕ` (soustraction tronquée) est le top de `𝕜` lu sur des entiers. -/
theorem tickOpF_cast (mem : Memory) (r L : ℕ) :
    ((tickOp mem r L : ℕ) : 𝕜) = tickOpF mem (r : 𝕜) (L : 𝕜) := by
  cases mem
  · rfl
  · simp only [tickOp, tickOpF]
    rcases le_total r L with h | h
    · have h' : (r : 𝕜) ≤ L := by exact_mod_cast h
      rw [Nat.cast_sub h, max_eq_left (by linarith)]
    · have h' : (L : 𝕜) ≤ r := by exact_mod_cast h
      rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right (by linarith)]
  · simp [tickOp, tickOpF]

/-- La réserve de `ℕ` est la réserve de `𝕜` lue sur des entiers. -/
theorem xresF_cast_iff (eu m cap L j : ℕ) :
    XresF (eu : 𝕜) m (cap : 𝕜) ((L : 𝕜), j) ↔ GuardSupervisor.Xres eu m cap (L, j) := by
  simp only [XresF, GuardSupervisor.Xres]
  norm_cast

/-- La masse incontrôlable de `ℕ` est celle de `𝕜` lue sur une instance entière. -/
theorem uncMassF_natInst {ι B : Type*} [Fintype ι] [DecidableEq ι] (aP aM : ι → B → ℕ)
    (A : Finset ι) (μ : B) :
    uncMassF (natInst (𝕜 := 𝕜) aP aM) A μ = (ReserveCoverage.uncMass aP aM A μ : 𝕜) := by
  simp only [uncMassF, ReserveCoverage.uncMass, natInst, Nat.cast_sum, Nat.cast_max]

/-- ★ Les charges atteintes par la garde de `ℕ` sont, lues dans `𝕜`, exactement celles de la
garde de `𝕜` depuis la même charge initiale. -/
theorem reachF_cast_iff {α : Type*} (mem : Memory) (r cap L₀ : ℕ) (e : α → ℕ) (x : 𝕜) :
    ReachF (tickOpF mem (r : 𝕜)) (fun a => (e a : 𝕜)) (guardF (cap : 𝕜) (fun a => (e a : 𝕜)))
        (L₀ : 𝕜) x ↔
      ∃ L, GuardSupervisor.Reach (tickOp mem r) e (GuardSupervisor.guard cap e) L₀ L ∧
        (L : 𝕜) = x := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨L₀, GuardSupervisor.Reach.init, rfl⟩
    | top _ ih =>
      obtain ⟨L, hL, rfl⟩ := ih
      exact ⟨_, GuardSupervisor.Reach.top hL, tickOpF_cast mem r L⟩
    | @emit _ a _ hS ih =>
      obtain ⟨L, hL, rfl⟩ := ih
      have hS' : (L : 𝕜) + e a ≤ cap := hS
      refine ⟨_, GuardSupervisor.Reach.emit hL (show L + e a ≤ cap by exact_mod_cast hS'), ?_⟩
      push_cast
      rfl
  · rintro ⟨L, hL, rfl⟩
    induction hL with
    | init => exact ReachF.init
    | @top L _ ih =>
      rw [tickOpF_cast]
      exact ReachF.top ih
    | @emit L a _ hS ih =>
      push_cast
      exact ReachF.emit ih (show (L : 𝕜) + e a ≤ cap by exact_mod_cast hS)

end Cast

end GuardField

/-!
## Domaine (Phase 16, 2026-10-04 ; décisions D-13 et D-21)

- Tout le module est énoncé sur un corps ordonné quelconque `𝕜` (`[Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration`) ; les énoncés précédés de `omit … in` en
  demandent moins. `ℚ` et `ℝ` en sont des instances ; les énoncés valent donc dans `ℝ` sans autre
  argument.
- **Corps archimédien** (`[Archimedean 𝕜]`) : les noyaux vides (`uncF_empty_of_growth`,
  `stockF_unc_empty`, `regenF_unc_empty`, `uncSetF_empty_of_growth`) et ce qui en dépend
  (`viableF_iff`, `coverageF_iff`, `coverage_all_fibers_iff`). Remarque non formalisée : sur un
  corps non archimédien, une croissance infinitésimale par période ne franchit jamais le plafond,
  et l'hypothèse ne peut pas être levée.
- Hypothèses de signe, explicites ici (dans `ℕ` elles étaient incorporées au type) : émissions
  incontrôlables positives (`reserveF_ci_iff`, `reserveSetF_ci_iff`, `viableF_iff`), régénération
  positive (`tickOpF_le`, `tickOpF_le_cap`), émissions discrétionnaires et lots positifs (§3).
- Le non-blocage (§3) admet des lots indivisibles : dans la période, l'ordre ne joue pas. Les lots
  reportables sont traités dans `DeadlineGuard` (`lumps_gap`).
- Le §4 compare deux lectures de la fibre inconnue (fixe, ou tirée à chaque fois). Une garde qui
  apprend la fibre en observant (observation partielle) est hors du module.
- Les témoins sont dans `ℚ` : ce sont des exemples rationnels, pas des restrictions.
- `GuardSupervisor` et `ReserveCoverage` restent dans `ℕ`, signatures inchangées ; le §5 les relie
  à ce module.
-/
