/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/SupplyPropagation.lean
  Phase 10 (2026-10-02), étape 10d : propagation de l'adhésion sur un réseau de production en
  couches — l'aval seul n'atteint jamais les émetteurs, les émetteurs entraînent tout le réseau,
  la faisabilité ne suffit pas ; chaîne vers la couverture.

  Développé d'abord en `SupplyPropagation_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase10_2026-10-02/plan_phase10.md` ; analyse :
  `cache/analyse_phase10_garde_repartie_2026-10-02.md` ; sonde S10
  (`cache/phase9_2026-10-02/outils/sonde_propagation.py`).
-/

import ThesePlanetaire.ReserveCoverage

/-!
# Propagation de la devise exigée : qui doit adhérer ?

Réseau : `sup v` (fournisseurs de `v`), `w c s` (volume que `c` achète à `s`). Les émetteurs
primaires sont les nœuds sans fournisseur. Deux canaux :
- **aval** (devise exigée) : un client d'un fournisseur adhérent doit payer en droits, donc
  adhère (`forced` : un fournisseur adhérent suffit ; `subst` : il peut se fournir ailleurs tant
  qu'un fournisseur n'adhère pas, il n'adhère que si tous adhèrent) ;
- **amont** (pression des clients) : un fournisseur adhère si la part de ses recettes venant de
  clients adhérents atteint `q`.

L'adhésion est la plus petite clôture `OrderHom.lfp` de l'opérateur monotone
graine ∪ aval ∪ amont.

1. ★ `down_only_emitters` : en aval seul, un émetteur adhère ssi il est dans la graine.
2. ★ `emitters_forced_all` : si la graine contient les émetteurs, l'aval (forcé ou substituable)
   entraîne **tout** le réseau (récurrence sur le rang).
3. ★ `feasible_not_propagated` : l'adhésion totale est cohérente mais, depuis les finals, l'aval
   seul ne l'atteint pas ; ★ `upstream_reaches_emitter` : l'amont, lui, remonte.
4. ★ `finals_down_only_stock_unviable`, `emitters_seed_unc_eq_nat` : chaîne vers
   `ReserveCoverage` — en `stock`, une graine sans émetteur effectif en aval seul n'a aucun état
   viable ; une graine d'émetteurs ramène la masse incontrôlable à l'émission naturelle.
-/

namespace SupplyPropagation

open FeedbackClass (tickOp)
open ReserveCoverage (Viable srcEmit uncMass coverage_stock_iff uncMass_univ)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Réseau de production : fournisseurs, et volume `w c s` que le client `c` achète à `s`. -/
structure Net (V : Type*) where
  sup : V → Finset V
  w : V → V → ℕ

/-- Mode du canal aval. -/
inductive Down
  | forced
  | subst
  deriving DecidableEq

/-- Clients de `v`. -/
def clients (N : Net V) (v : V) : Finset V := Finset.univ.filter fun c => v ∈ N.sup c

/-- Le canal aval fait adhérer `v` étant donné l'ensemble adhérent `X`. -/
def downOK (N : Net V) : Down → Set V → V → Prop
  | .forced, X, v => ∃ s ∈ N.sup v, s ∈ X
  | .subst, X, v => (N.sup v).Nonempty ∧ ∀ s ∈ N.sup v, s ∈ X

open Classical in
/-- Recettes de `v` venant de clients de `X`. -/
noncomputable def revenue (N : Net V) (X : Set V) (v : V) : 𝕜 :=
  ∑ c ∈ (clients N v).filter (· ∈ X), (N.w c v : 𝕜)

/-- Le canal amont fait adhérer `v` : part des recettes venant d'adhérents `≥ q`. -/
def upOK (N : Net V) (q : 𝕜) (X : Set V) (v : V) : Prop :=
  (clients N v).Nonempty ∧ q * revenue N Set.univ v ≤ revenue N X v

omit [Fintype V] [DecidableEq V] in
theorem downOK_mono (N : Net V) (d : Down) {X Y : Set V} (h : X ⊆ Y) {v : V}
    (hv : downOK N d X v) : downOK N d Y v := by
  cases d with
  | forced => obtain ⟨s, hs, hX⟩ := hv; exact ⟨s, hs, h hX⟩
  | subst => exact ⟨hv.1, fun s hs => h (hv.2 s hs)⟩

theorem revenue_mono (N : Net V) {X Y : Set V} (h : X ⊆ Y) (v : V) :
    revenue (𝕜 := 𝕜) N X v ≤ revenue N Y v := by
  classical
  unfold revenue
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  convert And.intro hc.1 (h hc.2)

/-- L'opérateur d'adhésion : graine ∪ aval ∪ amont (canaux optionnels). -/
def step (N : Net V) (seed : Set V) (down : Option Down) (up : Option 𝕜) : Set V →o Set V where
  toFun X := seed ∪ {v | ∃ d, down = some d ∧ downOK N d X v} ∪
    {v | ∃ q, up = some q ∧ upOK N q X v}
  monotone' X Y h v hv := by
    rcases hv with (hs | ⟨d, hd, hv⟩) | ⟨q, hq, hc, hv⟩
    · exact Or.inl (Or.inl hs)
    · exact Or.inl (Or.inr ⟨d, hd, downOK_mono N d h hv⟩)
    · exact Or.inr ⟨q, hq, hc, le_trans hv (revenue_mono N h v)⟩

/-- L'adhésion : la plus petite clôture. -/
def adh (N : Net V) (seed : Set V) (down : Option Down) (up : Option 𝕜) : Set V :=
  OrderHom.lfp (step N seed down up)

variable {N : Net V} {seed : Set V} {down : Option Down} {up : Option 𝕜}

theorem adh_fixed : step N seed down up (adh N seed down up) = adh N seed down up :=
  OrderHom.map_lfp _

theorem seed_subset_adh : seed ⊆ adh N seed down up := fun v hv => by
  rw [← adh_fixed]
  exact Or.inl (Or.inl hv)

theorem down_mem_adh {d : Down} (hd : down = some d) {v : V}
    (hv : downOK N d (adh N seed down up) v) : v ∈ adh N seed down up := by
  rw [← adh_fixed]
  exact Or.inl (Or.inr ⟨d, hd, hv⟩)

theorem up_mem_adh {q : 𝕜} (hq : up = some q) {v : V} (hv : upOK N q (adh N seed down up) v) :
    v ∈ adh N seed down up := by
  rw [← adh_fixed]
  exact Or.inr ⟨q, hq, hv⟩

theorem adh_subset {Y : Set V} (h : step N seed down up Y ⊆ Y) : adh N seed down up ⊆ Y :=
  OrderHom.lfp_le _ h

/-- ★ (b) **L'aval seul n'atteint pas les émetteurs** : un émetteur adhère ssi il est dans la
graine. -/
theorem down_only_emitters (d : Down) {v : V} (hv : N.sup v = ∅) :
    v ∈ adh N seed (some d) (none : Option 𝕜) ↔ v ∈ seed := by
  refine ⟨fun h => ?_, fun h => seed_subset_adh h⟩
  have hY : adh N seed (some d) (none : Option 𝕜) ⊆ seed ∪ {v | (N.sup v).Nonempty} := by
    refine adh_subset ?_
    rintro u ((hs | ⟨d', -, hu⟩) | ⟨q, hq, -⟩)
    · exact Or.inl hs
    · right
      cases d' with
      | forced => obtain ⟨s, hs, -⟩ := hu; exact ⟨s, hs⟩
      | subst => exact hu.1
    · cases hq
  rcases hY h with h | h
  · exact h
  · exact absurd hv (Finset.nonempty_iff_ne_empty.mp h)

/-- ★ (c) **Les émetteurs entraînent tout** : si la graine contient les émetteurs et que le
réseau est en couches (`rank` croît vers l'aval), l'aval forcé ou substituable fait adhérer
tous les nœuds. -/
theorem emitters_forced_all (rank : V → ℕ) (hrank : ∀ v s, s ∈ N.sup v → rank s < rank v)
    (hseed : ∀ v, N.sup v = ∅ → v ∈ seed) (d : Down) (up : Option 𝕜) :
    ∀ v, v ∈ adh N seed (some d) up := by
  suffices h : ∀ n v, rank v = n → v ∈ adh N seed (some d) up from fun v => h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    by_cases he : N.sup v = ∅
    · exact seed_subset_adh (hseed v he)
    · have hall : ∀ s ∈ N.sup v, s ∈ adh N seed (some d) up :=
        fun s hs => ih _ (hv ▸ hrank v s hs) s rfl
      have hne := Finset.nonempty_iff_ne_empty.mpr he
      refine down_mem_adh rfl ?_
      cases d with
      | forced => obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, hall s hs⟩
      | subst => exact ⟨hne, hall⟩

/-- ★ **L'amont remonte** : si tous les clients d'un nœud adhèrent et `q ≤ 1`, il adhère. -/
theorem upstream_reaches_emitter {q : 𝕜} (hq : q ≤ 1) {v : V} (hne : (clients N v).Nonempty)
    (hall : ∀ c ∈ clients N v, c ∈ adh N seed down (some q)) : v ∈ adh N seed down (some q) := by
  classical
  refine up_mem_adh rfl ⟨hne, ?_⟩
  have h0 : (0 : 𝕜) ≤ revenue N Set.univ v :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have heq : revenue (𝕜 := 𝕜) N (adh N seed down (some q)) v = revenue N Set.univ v := by
    unfold revenue
    congr 1
    ext c
    simp only [Finset.mem_filter, Set.mem_univ, and_true, and_iff_left_iff_imp]
    exact hall c
  rw [heq]
  nlinarith

/-- L'adhésion totale est cohérente : avec l'amont (`q ≤ 1`), si chaque émetteur a un client,
`univ` est un point fixe de l'opérateur, quelle que soit la graine. -/
theorem univ_fixed (d : Down) {q : 𝕜} (hq : q ≤ 1)
    (hcl : ∀ v, N.sup v = ∅ → (clients N v).Nonempty) :
    step N seed (some d) (some q) Set.univ = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ?_
  by_cases he : N.sup v = ∅
  · refine Or.inr ⟨q, rfl, hcl v he, ?_⟩
    have h0 : (0 : 𝕜) ≤ revenue N Set.univ v :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    nlinarith
  · have hne := Finset.nonempty_iff_ne_empty.mpr he
    refine Or.inl (Or.inr ⟨d, rfl, ?_⟩)
    cases d with
    | forced => obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, trivial⟩
    | subst => exact ⟨hne, fun _ _ => trivial⟩

/-! ### Le témoin (d) : chaîne P (0) → I (1) → F (2, 3) -/

/-- Émetteur `0`, intermédiaire `1` (fournisseur `0`), finals `2` et `3` (fournisseur `1`). -/
def wN : Net (Fin 4) where
  sup := ![∅, {0}, {1}, {1}]
  w := fun _ _ => 1

theorem wN_clients0 : clients wN 0 = {1} := by decide

theorem wN_clients1 : clients wN 1 = {2, 3} := by decide

/-- ★ (d) **La faisabilité ne suffit pas** : l'adhésion totale est un point fixe (cohérente),
mais depuis les finals, l'aval seul n'atteint pas l'émetteur ; l'amont (`q = 1`) l'atteint. -/
theorem feasible_not_propagated :
    step wN {2, 3} (some .forced) (some (1 : ℚ)) Set.univ = Set.univ ∧
      (0 : Fin 4) ∉ adh wN {2, 3} (some .forced) (none : Option ℚ) ∧
        (0 : Fin 4) ∈ adh wN {2, 3} (some .forced) (some (1 : ℚ)) := by
  refine ⟨univ_fixed _ le_rfl fun v hv => ?_, ?_, ?_⟩
  · fin_cases v
    · exact ⟨1, by decide⟩
    all_goals simp [wN] at hv
  · rw [down_only_emitters _ (by rfl)]
    simp
  · have h1 : (1 : Fin 4) ∈ adh wN {2, 3} (some .forced) (some (1 : ℚ)) := by
      refine upstream_reaches_emitter le_rfl (by rw [wN_clients1]; simp) fun c hc => ?_
      rw [wN_clients1] at hc
      exact seed_subset_adh (by simpa using hc)
    refine upstream_reaches_emitter le_rfl (by rw [wN_clients0]; simp) fun c hc => ?_
    rw [wN_clients0, Finset.mem_singleton] at hc
    exact hc ▸ h1

/-! ### Chaîne vers la couverture -/

open Classical in
/-- L'ensemble adhérent comme ensemble couvert (`ReserveCoverage`). -/
noncomputable def adhF (N : Net V) (seed : Set V) (down : Option Down) (up : Option 𝕜) :
    Finset V :=
  Finset.univ.filter (· ∈ adh N seed down up)

theorem mem_adhF {v : V} : v ∈ adhF N seed down up ↔ v ∈ adh N seed down up := by
  simp [adhF]

variable {B Un : Type*} [Fintype Un] [DecidableEq Un]

/-- ★ **Graine sans émetteur, aval seul, `stock` : aucun état viable.** Un émetteur hors de la
graine, d'émission effective sur la fibre `μ`, reste non couvert ; sa masse incontrôlable
interdit toute viabilité (`ReserveCoverage.coverage_stock_iff`). -/
theorem finals_down_only_stock_unviable (d : Down) (enat : Un → ℕ) (aP aM : V → B → ℕ) (μ : B)
    (r cap : ℕ) {v : V} (hv : N.sup v = ∅) (hvs : v ∉ seed) (hpos : 0 < max (aP v μ) (aM v μ)) :
    ¬ Viable (tickOp .stock r)
      (srcEmit enat aP aM (adhF N seed (some d) (none : Option 𝕜)) μ) cap := by
  rw [coverage_stock_iff]
  have hvA : v ∈ (adhF N seed (some d) (none : Option 𝕜))ᶜ := by
    rw [Finset.mem_compl, mem_adhF, down_only_emitters d hv]
    exact hvs
  have : max (aP v μ) (aM v μ) ≤ uncMass aP aM (adhF N seed (some d) (none : Option 𝕜)) μ :=
    Finset.single_le_sum (f := fun i => max (aP i μ) (aM i μ)) (fun _ _ => Nat.zero_le _) hvA
  omega

/-- ★ **Graine d'émetteurs, aval : la masse incontrôlable se réduit à l'émission naturelle.** -/
theorem emitters_seed_unc_eq_nat (rank : V → ℕ) (hrank : ∀ v s, s ∈ N.sup v → rank s < rank v)
    (hseed : ∀ v, N.sup v = ∅ → v ∈ seed) (d : Down) (up : Option 𝕜) (aP aM : V → B → ℕ)
    (μ : B) : uncMass aP aM (adhF N seed (some d) up) μ = 0 := by
  have : adhF N seed (some d) up = Finset.univ :=
    Finset.eq_univ_of_forall fun v => mem_adhF.mpr (emitters_forced_all rank hrank hseed d up v)
  rw [this, uncMass_univ]

end SupplyPropagation

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf le témoin (d)
(`wN`, `wN_clients0`, `wN_clients1`, `feasible_not_propagated`), qui reste dans `ℚ`. Les poids du
réseau sont dans `ℕ`, comme avant.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration`. `ℚ` et
  `ℝ` en sont des instances ; les énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
