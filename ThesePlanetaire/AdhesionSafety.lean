/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/AdhesionSafety.lean
  Phase 11 (2026-10-02), étape 11c : sûreté ∩ stabilité — une coalition stable et sûre existe
  ssi le plus grand équilibre est sûr ; un amorçage temporaire y conduit ; masse critique en
  émissions ; ensembles bloquants de Morris et verrouillage par l'amont.

  Développé d'abord en `AdhesionSafety_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase11_2026-10-02/plan_phase11.md` ; analyse :
  `cache/analyse_phase11_adhesion_emetteurs_2026-10-02.md` §3-4 ; sonde G4-G5
  (`cache/phase11_2026-10-02/outils/sonde_adhesion.py`).
-/

import ThesePlanetaire.AdhesionGame
import ThesePlanetaire.SupplyPropagation

/-!
# Sûreté ∩ stabilité

Une coalition `X` d'émetteurs adhérents est **sûre** (`Safe`) si la garde à réserve de
`ReserveCoverage` tient le plafond quand seuls les émetteurs hors de `X` (et la nature) échappent
à la couverture. Par `coverage_*_iff`, c'est une condition de masse :
`Σ enat + uncMass ≤ memBound` (★ `safe_iff`), et elle est **croissante** en `X` (★ `safe_mono`).

1. ★ `exists_fixed_safe_iff`, `exists_stable_safe_iff` : pour une propriété croissante, une
   coalition stable qui la vérifie existe ssi le plus grand équilibre la vérifie.
2. ★ `seeding_safe_iff` (résultat central de la Phase 11) : un amorçage **temporaire** (champ
   `H ≥ 0`, puis retrait) conduit la dynamique myope à une coalition stable et sûre ssi le plus
   grand équilibre est sûr. Sinon, aucun amorçage temporaire ne suffit : il faut modifier
   durablement les gains (`AdhesionGame.drain_enlarges`, `AdhesionGame.mandate_enlarges`).
3. ★ `safety_gap_stock` : l'écart entre équilibres extrêmes est un écart de sûreté ;
   ★ `holdout_stock_regen` : un réfractaire de petite émission rend toute coalition stable non
   sûre en `stock`, pas en `regen` ; ★ `regen_minority_safe_majority_unsafe` : la masse critique
   se compte en émissions, pas en nombre.
4. Réseaux (`SupplyPropagation`) : ★ `step_compl_subset_iff`, `not_mem_adh_iff` (un nœud
   n'adhère pas ssi il est dans un ensemble cohésif bloquant, au sens de Morris 2000),
   ★ `not_upOK_iff_cohesive` (cohésion en recettes), ★ `stock_safe_adh_iff`,
   ★ `supply_lock_in` (une obligation temporaire des émetteurs est retenue par l'amont).
-/

namespace AdhesionSafety

open AdhesionGame
open FeedbackClass (Memory tickOp)
open ReserveCoverage (Viable srcEmit uncMass coverage_stock_iff coverage_regen_iff
  coverage_flow_iff uncMass_univ)
open SupplyPropagation (Net Down downOK upOK revenue clients step adh adh_fixed adh_subset
  univ_fixed emitters_forced_all wN)

/-! ### §2a. Le lemme générique -/

/-- ★ Pour une propriété croissante `P`, un point fixe de `F` vérifiant `P` existe ssi le plus
grand point fixe la vérifie. -/
theorem exists_fixed_safe_iff {V : Type*} {P : Set V → Prop} (hP : ∀ ⦃X Y⦄, X ⊆ Y → P X → P Y)
    (F : Set V →o Set V) : (∃ X, F X = X ∧ P X) ↔ P F.gfp :=
  ⟨fun ⟨_, hX, hPX⟩ => hP (F.le_gfp hX.ge) hPX, fun h => ⟨_, F.map_gfp, h⟩⟩

/-! ### §1. Sûreté d'une coalition -/

variable {V : Type*} [Fintype V]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

open Classical in
/-- La coalition comme ensemble couvert. -/
noncomputable def finOf (X : Set V) : Finset V := Finset.univ.filter (· ∈ X)

theorem mem_finOf {X : Set V} {i : V} : i ∈ finOf X ↔ i ∈ X := by simp [finOf]

theorem finOf_mono {X Y : Set V} (h : X ⊆ Y) : finOf X ⊆ finOf Y :=
  fun _ hi => mem_finOf.mpr (h (mem_finOf.mp hi))

theorem finOf_coe [DecidableEq V] (A : Finset V) : finOf (A : Set V) = A := by
  ext i
  simp [finOf]

variable [DecidableEq V] {B Un : Type*} [Fintype Un] [DecidableEq Un]

/-- Coalition sûre : la garde à réserve tient le plafond quand nature et non-adhérents échappent à
la couverture. -/
def Safe (m : Memory) (r cap : ℕ) (enat : Un → ℕ) (aP aM : V → B → ℕ) (μ : B) (X : Set V) :
    Prop :=
  Viable (tickOp m r) (srcEmit enat aP aM (finOf X) μ) cap

/-- Masse incontrôlable admissible par mémoire. -/
def memBound : Memory → ℕ → ℕ → ℕ
  | .stock, _, _ => 0
  | .regen, r, cap => min r cap
  | .flow, _, cap => cap

variable {m : Memory} {r cap : ℕ} {enat : Un → ℕ} {aP aM : V → B → ℕ} {μ : B}

/-- ★ Sûreté = condition de masse. -/
theorem safe_iff {X : Set V} :
    Safe m r cap enat aP aM μ X ↔ ∑ n, enat n + uncMass aP aM (finOf X) μ ≤ memBound m r cap := by
  cases m with
  | stock => rw [Safe, coverage_stock_iff, memBound, Nat.le_zero]
  | regen => exact coverage_regen_iff
  | flow => exact coverage_flow_iff

omit [Fintype Un] [DecidableEq Un] in
/-- ★ Couvrir plus réduit la masse incontrôlable. -/
theorem uncMass_anti (aP aM : V → B → ℕ) (μ : B) {A A' : Finset V} (h : A ⊆ A') :
    uncMass aP aM A' μ ≤ uncMass aP aM A μ :=
  Finset.sum_le_sum_of_subset (Finset.compl_subset_compl.mpr h)

/-- ★ La sûreté est croissante : un ensemble supérieur. -/
theorem safe_mono {X Y : Set V} (h : X ⊆ Y) (hX : Safe m r cap enat aP aM μ X) :
    Safe m r cap enat aP aM μ Y := by
  rw [safe_iff] at hX ⊢
  exact le_trans (Nat.add_le_add_left (uncMass_anti aP aM μ (finOf_mono h)) _) hX

/-! ### §2b. Sûreté ∩ stabilité -/

variable {g : V → Set V → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
/-- ★ (E6) Une coalition stable et sûre existe ssi le plus grand équilibre est sûr. -/
theorem exists_stable_safe_iff (hg : Supermodular g) :
    (∃ X, IsNash g X ∧ Safe m r cap enat aP aM μ X) ↔
      Safe m r cap enat aP aM μ (br g hg).gfp :=
  (exists_congr fun _ => and_congr_left' isNash_iff_fixed).trans
    (exists_fixed_safe_iff (fun _ _ h hX => safe_mono h hX) (br g hg))

/-- ★ **Résultat central** : un amorçage temporaire (champ `H ≥ 0`, puis retrait) laisse une
coalition stable et sûre ssi le plus grand équilibre est sûr. Dans le sens direct, l'amorçage
`H = Σ_i |g i ∅|` allume tout, et le retrait laisse le plus grand équilibre. -/
theorem seeding_safe_iff (hg : Supermodular g) :
    (∃ H, 0 ≤ H ∧ Safe m r cap enat aP aM μ (afterSeed g hg H)) ↔
      Safe m r cap enat aP aM μ (br g hg).gfp := by
  constructor
  · rintro ⟨H, hH, hS⟩
    exact safe_mono (afterSeed_subset_gfp hg hH) hS
  · intro h
    refine ⟨∑ i, |g i ∅|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
    have hall : ∀ i, 0 ≤ g i ∅ + ∑ j, |g j ∅| := fun i => by
      have h1 : |g i ∅| ≤ ∑ j, |g j ∅| :=
        Finset.single_le_sum (f := fun j => |g j ∅|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h2 := neg_abs_le (g i ∅)
      linarith
    rw [afterSeed_full hg (ignition_all hg hall)]
    exact h

/-! ### Témoins -/

/-- Émission unitaire. -/
def eOne : Fin 2 → Unit → ℕ := fun _ _ => 1

/-- ★ **L'écart lfp/gfp est un écart de sûreté** : dans le jeu de coordination bistable, le plus
grand équilibre est sûr en `stock`, le plus petit ne l'est pas. -/
theorem safety_gap_stock :
    Safe .stock 0 0 (fun _ : Empty => 0) eOne eOne () (br coordGain coordGain_super).gfp ∧
      ¬ Safe .stock 0 0 (fun _ : Empty => 0) eOne eOne () (br coordGain coordGain_super).lfp := by
  obtain ⟨h1, h2, -⟩ := bistable_witness
  rw [safe_iff, safe_iff, h1, h2, ← Finset.coe_univ, ← Finset.coe_empty, finOf_coe, finOf_coe,
    uncMass_univ]
  decide

/-- Un gros émetteur (`0`) qui veut adhérer, un petit (`1`) qui refuse toujours. -/
def holdGain : Fin 2 → Set (Fin 2) → ℚ := fun i _ => if i = 0 then 1 else -1

theorem holdGain_super : Supermodular holdGain := fun _ _ _ _ => le_rfl

/-- Émissions : `5` pour l'émetteur `0`, `1` pour le réfractaire. -/
def eHold : Fin 2 → Unit → ℕ := fun i _ => if i = 0 then 5 else 1

theorem holdGain_br (X : Set (Fin 2)) : brSet holdGain X = {0} := by
  ext i
  fin_cases i <;> simp [brSet, holdGain]

theorem holdGain_gfp : (br holdGain holdGain_super).gfp = ({0} : Finset (Fin 2)) := by
  rw [← (br holdGain holdGain_super).map_gfp]
  show brSet holdGain _ = _
  rw [holdGain_br]
  simp

/-- ★ **Le réfractaire de petite émission** : aucune coalition stable n'est sûre en `stock`, une
l'est en `regen` (`r = cap = 1`). -/
theorem holdout_stock_regen :
    (¬ ∃ X, IsNash holdGain X ∧ Safe .stock 1 1 (fun _ : Empty => 0) eHold eHold () X) ∧
      ∃ X, IsNash holdGain X ∧ Safe .regen 1 1 (fun _ : Empty => 0) eHold eHold () X := by
  rw [exists_stable_safe_iff holdGain_super, exists_stable_safe_iff holdGain_super, safe_iff,
    safe_iff, holdGain_gfp, finOf_coe]
  decide

/-- Émissions `(8, 1, 1, 1, 1)`. -/
def eCrit : Fin 5 → Unit → ℕ := fun i _ => if i = 0 then 8 else 1

/-- ★ (E2, S8a) **La masse critique se compte en émissions** : en `regen` (`r = cap = 4`), la
majorité `{1, 2, 3, 4}` n'est pas sûre, la minorité `{0}` l'est. -/
theorem regen_minority_safe_majority_unsafe :
    ¬ Safe .regen 4 4 (fun _ : Empty => 0) eCrit eCrit () (({1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) ∧
      Safe .regen 4 4 (fun _ : Empty => 0) eCrit eCrit () (({0} : Finset (Fin 5)) : Set (Fin 5)) := by
  rw [safe_iff, safe_iff, finOf_coe, finOf_coe]
  decide

/-! ### §4. Réseaux : ensembles cohésifs bloquants (Morris 2000) -/

variable {N : Net V} {seed : Set V} {down : Option Down} {up : Option 𝕜}

/-- `Y` bloque l'adhésion : hors de la graine, et aucun de ses nœuds n'est entraîné par le
complément, ni par l'aval ni par l'amont. -/
def Blocking (N : Net V) (seed : Set V) (down : Option Down) (up : Option 𝕜) (Y : Set V) :
    Prop :=
  ∀ u ∈ Y, u ∉ seed ∧ (∀ d, down = some d → ¬ downOK N d Yᶜ u) ∧
    ∀ q, up = some q → ¬ upOK N q Yᶜ u

/-- ★ `Y` bloque ssi son complément est stable par l'opérateur d'adhésion. -/
theorem step_compl_subset_iff {Y : Set V} :
    step N seed down up Yᶜ ⊆ Yᶜ ↔ Blocking N seed down up Y := by
  constructor
  · intro h u hu
    exact ⟨fun hs => h (Or.inl (Or.inl hs)) hu, fun d hd hdo => h (Or.inl (Or.inr ⟨d, hd, hdo⟩)) hu,
      fun q hq hup => h (Or.inr ⟨q, hq, hup⟩) hu⟩
  · rintro h u hu huY
    obtain ⟨h1, h2, h3⟩ := h u huY
    rcases hu with (hs | ⟨d, hd, hdo⟩) | ⟨q, hq, hup⟩
    · exact h1 hs
    · exact h2 d hd hdo
    · exact h3 q hq hup

/-- ★ Le complément de l'adhésion bloque. -/
theorem adh_compl_blocking : Blocking N seed down up (adh N seed down up)ᶜ :=
  step_compl_subset_iff.mp (by rw [compl_compl]; exact adh_fixed.le)

/-- ★ … et c'est le plus grand ensemble bloquant. -/
theorem blocking_subset_compl_adh {Y : Set V} (h : Blocking N seed down up Y) :
    Y ⊆ (adh N seed down up)ᶜ :=
  fun _ hv hA => adh_subset (step_compl_subset_iff.mpr h) hA hv

/-- ★ **Morris** : un nœud n'adhère pas ssi il appartient à un ensemble bloquant. -/
theorem not_mem_adh_iff {v : V} :
    v ∉ adh N seed down up ↔ ∃ Y, v ∈ Y ∧ Blocking N seed down up Y :=
  ⟨fun hv => ⟨_, hv, adh_compl_blocking⟩, fun ⟨_, hvY, hB⟩ => blocking_subset_compl_adh hB hvY⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Les recettes se partagent entre `Y` et son complément. -/
theorem revenue_compl_add (N : Net V) (Y : Set V) (v : V) :
    revenue (𝕜 := 𝕜) N Yᶜ v + revenue N Y v = revenue N Set.univ v := by
  classical
  have hu : revenue N Set.univ v = ∑ c ∈ clients N v, (N.w c v : 𝕜) := by
    unfold revenue
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext c
    simp
  rw [hu, ← Finset.sum_filter_not_add_sum_filter (clients N v) (· ∈ Y)]
  unfold revenue
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp

/-- ★ **Cohésion en recettes** : l'amont n'entraîne pas `v` depuis `Yᶜ` ssi plus d'une part
`1 − q` de ses recettes vient de `Y`. -/
theorem not_upOK_iff_cohesive {q : 𝕜} {Y : Set V} {v : V} :
    ¬ upOK N q Yᶜ v ↔
      ((clients N v).Nonempty → (1 - q) * revenue N Set.univ v < revenue N Y v) := by
  have h := revenue_compl_add (𝕜 := 𝕜) N Y v
  have hr : (1 - q) * revenue N Set.univ v = revenue N Set.univ v - q * revenue N Set.univ v := by
    ring
  unfold upOK
  constructor
  · intro hn hne
    by_contra hc
    exact hn ⟨hne, by linarith⟩
  · rintro hc ⟨hne, hle⟩
    have := hc hne
    linarith

/-- ★ **Sûreté `stock` d'un réseau** : l'adhésion est sûre ssi la nature n'émet pas et aucun
émetteur effectif n'appartient à un ensemble bloquant. -/
theorem stock_safe_adh_iff :
    Safe .stock r cap enat aP aM μ (adh N seed down up) ↔
      ∑ n, enat n = 0 ∧
        ∀ v, 0 < max (aP v μ) (aM v μ) → ∀ Y, v ∈ Y → ¬ Blocking N seed down up Y := by
  rw [safe_iff, memBound, Nat.le_zero, Nat.add_eq_zero_iff]
  refine and_congr_right' ?_
  rw [uncMass, Finset.sum_eq_zero_iff]
  constructor
  · intro h v hv Y hvY hB
    have := h v (by rw [Finset.mem_compl, mem_finOf]; exact not_mem_adh_iff.mpr ⟨Y, hvY, hB⟩)
    omega
  · intro h v hv
    rw [Finset.mem_compl, mem_finOf] at hv
    obtain ⟨Y, hvY, hB⟩ := not_mem_adh_iff.mp hv
    by_contra hne
    exact h v (Nat.pos_of_ne_zero hne) Y hvY hB

/-- ★ **Verrouillage par l'amont (voie 3)** : sur un réseau en couches où chaque émetteur a un
client, une obligation **temporaire** des émetteurs (graine) fait tout adhérer
(`emitters_forced_all`) ; l'état atteint est un point fixe de l'opérateur **sans graine**, qui
en est le plus grand point fixe : le retrait de l'obligation ne défait rien. -/
theorem supply_lock_in (rank : V → ℕ) (hrank : ∀ v s, s ∈ N.sup v → rank s < rank v)
    (hseed : ∀ v, N.sup v = ∅ → v ∈ seed) (d : Down) {q : 𝕜} (hq : q ≤ 1)
    (hcl : ∀ v, N.sup v = ∅ → (clients N v).Nonempty) :
    adh N seed (some d) (some q) = Set.univ ∧
      step N ∅ (some d) (some q) (adh N seed (some d) (some q)) = adh N seed (some d) (some q) ∧
        (step N ∅ (some d) (some q)).gfp = Set.univ := by
  have h1 : adh N seed (some d) (some q) = Set.univ :=
    Set.eq_univ_of_forall (emitters_forced_all rank hrank hseed d (some q))
  have hu : step N ∅ (some d) (some q) Set.univ = Set.univ := univ_fixed d hq hcl
  refine ⟨h1, by rw [h1, hu], ?_⟩
  exact Set.eq_univ_of_univ_subset ((step N ∅ (some d) (some q)).le_gfp hu.ge)

/-- ★ **Hystérésis sur réseau** : sur la chaîne `wN` (`SupplyPropagation`), sans graine, la plus
petite adhésion est vide, la plus grande est totale. -/
theorem supply_bistable_witness :
    adh wN ∅ (some .forced) (some (1 : ℚ)) = ∅ ∧
      (step wN ∅ (some .forced) (some (1 : ℚ))).gfp = Set.univ := by
  refine ⟨Set.subset_empty_iff.mp (adh_subset ?_), ?_⟩
  · rintro u ((hs | ⟨d, hd, hdo⟩) | ⟨q, hq, hne, hle⟩)
    · exact hs
    · cases hd
      obtain ⟨s, -, hs⟩ := hdo
      exact hs
    · cases hq
      have h0 : revenue (𝕜 := ℚ) wN ∅ u = 0 := by simp [revenue]
      have hpos : 0 < revenue (𝕜 := ℚ) wN Set.univ u := by
        unfold revenue
        refine Finset.sum_pos (fun _ _ => by simp [wN]) ?_
        simpa using hne
      rw [h0] at hle
      linarith
  · refine Set.eq_univ_of_univ_subset ((step wN ∅ (some .forced) (some (1 : ℚ))).le_gfp
      (univ_fixed _ le_rfl fun v hv => ?_).ge)
    fin_cases v
    · exact ⟨1, by decide⟩
    all_goals simp [wN] at hv

end AdhesionSafety

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf les témoins
(`holdGain` et ses conséquences, `supply_bistable_witness`), qui restent dans `ℚ`. Les émissions
des témoins (`eOne`, `eHold`, `eCrit`) sont dans `ℕ`, comme avant.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
