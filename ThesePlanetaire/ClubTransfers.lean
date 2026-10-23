/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/ClubTransfers.lean
  Phase 12 (2026-10-03) : E7 complet — qui finance la prime à pleine adhésion, toutes sources
  internes comprises ? Financement interne ⟺ PIS ; symétrique : rien d'interne ; barème plafonné
  (budget à chaque coalition, plein = plus grand équilibre, allumage non renchéri) ; rayon de
  robustesse = marge moyenne ; caisse perpétuelle ⟺ dotation `≥ P/r`.

  Développé d'abord en `ClubTransfers_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase12_2026-10-03/plan_phase12.md` ; analyse :
  `cache/analyse_phase12_E7_financement_club_2026-10-03.md` §4 ; sondes F1-F6
  (`cache/phase12_2026-10-03/outils/sonde_financement.py`) et F1', F3', F7 (`sonde_bareme.py`).
-/

import ThesePlanetaire.ClubFinancing
import ThesePlanetaire.RobustIgnition

/-!
# Le financement interne de la prime

`ClubFinancing` traite la prime financée par la frontière : elle s'annule au plein. Ici, les
transferts `t i S` (indexés comme les gains, sur les **autres** adhérents `S`) sont de signe
quelconque : une cotisation est un `t < 0`. Le gain de base `g` est `intr + drain` (prime exclue) ;
`margin g i = g i (univ \ {i})` est la marge de pleine adhésion, gain du membre au plein moins
gain du passager clandestin. `Budget drain t` : à **chaque** coalition `X`, les transferts nets
versés aux membres sont couverts par les drains des non-membres (`BorderFinanced` sans
l'hypothèse `prem ≥ 0`, `borderFinanced_iff_budget`).

Le critère `λ*(D) ≤ 0` du corpus n'est pas le bon : il teste les cycles (circulation), alors que
le financement est un bilan aux nœuds (analyse, §3). Le bon critère est connu : la stabilité
interne potentielle (PIS, Eyckmans et Finus, déf. 5 ; Carraro, Eyckmans et Finus 2006).

1. ★ `internal_financing_iff` (connu, cité) : un transfert budgété rend le plein stable ssi
   `Σ_i margin g i ≥ 0` (PIS). Noyau scalaire : `exists_balanced_iff`.
2. ★ `sym_internal_useless` : à marges égales, le financement interne n'apporte rien ;
   ★ `premium_gap_internal` prolonge `premium_gap_witness` à toute source interne. Le modèle
   symétrique de Renn (arXiv 2608.12143 v3) instancie ce cas : une prime au plein y est
   extérieure ou absente.
3. ★ Barème plafonné `capped g e` (cible `e i` = gain visé au plein) : supermodularité conservée
   (`capped_super`), gain au plein `= e` (`capped_full`), budget à chaque coalition sous
   `Σ e ≤ Σ margin` (`capped_budget`), plein = plus grand équilibre (`capped_gfp`), meilleure
   réponse élargie pour tout amorçage `H ≥ 0` (`capped_br_widens`, `capped_lfp_widens`) ;
   ★ `financed_seeding_safe` : sous PIS, « amorcer puis retirer » finit au plein sans source
   extérieure.
4. ★ `robust_financed_iff` : le rayon de robustesse du plein financé est la marge **moyenne**
   (`card V · x ≤ Σ margin`), contre la marge minimale sans transfert. ★ `aggregate_threshold` :
   variante multiplicative, `x ≤ 1 − ΣGap/ΣP`.
5. ★ `fund_perpetuity_iff` : une caisse `F (t+1) = (1+r) F t − P` reste positive ssi
   `P ≤ r · F 0` (dotation `≥ P/r`) ; ★ `fund_exhausted_zero_rate` : à taux nul, elle s'épuise.
   C'est le seul sens classique de « No-Ponzi » ici : une condition de limite, pas de cycle.
-/

namespace ClubTransfers

open AdhesionGame
open AdhesionSafety (finOf mem_finOf Safe seeding_safe_iff)
open ClubFinancing (Club BorderFinanced extClub)
open RobustIgnition (Robust robust_iff_margin)

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §0. Marge de pleine adhésion, gain d'un club -/

/-- Marge de pleine adhésion : gain d'adhérer face à tous les autres. -/
def margin (g : V → Set V → 𝕜) (i : V) : 𝕜 := g i (Set.univ \ {i})

variable {g : V → Set V → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
/-- L'adhésion totale est un équilibre ssi toutes les marges sont positives. -/
theorem full_nash_iff_margin : IsNash g Set.univ ↔ ∀ i, 0 ≤ margin g i :=
  ⟨fun h i => h.1 i (Set.mem_univ i),
    fun h => ⟨fun i _ => h i, fun i hi => absurd (Set.mem_univ i) hi⟩⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Le gain d'un club est le gain de base `intr + drain` plus un transfert : la prime, indexée
sur les autres adhérents. -/
theorem club_gain_eq (C : Club 𝕜 V) :
    C.gain = addGain (fun i S => C.intr i S + C.drain i S) (fun i S => C.prem i (insert i S)) := by
  funext i S
  simp only [Club.gain, addGain]
  ring

/-! ### §1. Le barème plafonné -/

open Classical in
/-- Barème plafonné de cible `e` : le gain d'un membre est plafonné à `e i` (cotisation au-delà),
et un bénéficiaire (`margin g i < e i`) reçoit l'écart, seulement face à tous les autres. -/
noncomputable def capped (g : V → Set V → 𝕜) (e : V → 𝕜) : V → Set V → 𝕜 :=
  fun i S => min 0 (e i - g i S) + if Set.univ \ {i} ⊆ S then max 0 (e i - margin g i) else 0

open Classical in
theorem capped_gain_eq (g : V → Set V → 𝕜) (e : V → 𝕜) (i : V) (S : Set V) :
    addGain g (capped g e) i S =
      min (g i S) (e i) + if Set.univ \ {i} ⊆ S then max 0 (e i - margin g i) else 0 := by
  have h : g i S + min 0 (e i - g i S) = min (g i S) (e i) := by
    rcases le_total (g i S) (e i) with h | h
    · rw [min_eq_left (sub_nonneg.mpr h), min_eq_left h]
      ring
    · rw [min_eq_right (sub_nonpos.mpr h), min_eq_right h]
      ring
  simp only [addGain, capped]
  rw [← add_assoc, h]

/-- ★ Le barème plafonné conserve la supermodularité. -/
theorem capped_super (hg : Supermodular g) (e : V → 𝕜) : Supermodular (addGain g (capped g e)) := by
  intro i S T hST
  rw [capped_gain_eq, capped_gain_eq]
  refine add_le_add (min_le_min_right _ (hg i hST)) ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hST) h2
  · exact le_max_left _ _
  · exact le_rfl

/-- ★ Au plein, le gain financé vaut la cible. -/
theorem capped_full (g : V → Set V → 𝕜) (e : V → 𝕜) (i : V) :
    addGain g (capped g e) i (Set.univ \ {i}) = e i := by
  rw [capped_gain_eq, if_pos subset_rfl]
  show min (margin g i) (e i) + max 0 (e i - margin g i) = e i
  rcases le_total (margin g i) (e i) with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]
    ring

/-- ★ À cible positive, l'adhésion totale est un équilibre du jeu financé. -/
theorem capped_nash {e : V → 𝕜} (he0 : ∀ i, 0 ≤ e i) :
    IsNash (addGain g (capped g e)) Set.univ :=
  full_nash_iff_margin.mpr fun i => by
    show 0 ≤ addGain g (capped g e) i (Set.univ \ {i})
    rw [capped_full]
    exact he0 i

/-- ★ … donc le plus grand équilibre du jeu financé est le plein. -/
theorem capped_gfp (hg : Supermodular g) {e : V → 𝕜} (he0 : ∀ i, 0 ≤ e i) :
    (br _ (capped_super hg e)).gfp = Set.univ :=
  Set.eq_univ_of_univ_subset ((gfp_greatest_nash _).2 (capped_nash he0))

open Classical in
/-- ★ **Allumage non renchéri** : pour tout amorçage `H ≥ 0`, le barème plafonné élargit la
meilleure réponse. Un cotisant n'est plafonné qu'à `e i ≥ 0`, ce qui ne décide jamais du signe. -/
theorem capped_br_widens {e : V → 𝕜} (he0 : ∀ i, 0 ≤ e i) {H : 𝕜} (hH : 0 ≤ H) (X : Set V) :
    brSet (shift g H) X ⊆ brSet (shift (addGain g (capped g e)) H) X := by
  intro i hi
  have hi' : 0 ≤ g i (X \ {i}) + H := hi
  show 0 ≤ addGain g (capped g e) i (X \ {i}) + H
  rw [capped_gain_eq]
  have h1 : 0 ≤ min (g i (X \ {i})) (e i) + H := by
    rcases le_total (g i (X \ {i})) (e i) with h | h
    · rw [min_eq_left h]
      exact hi'
    · rw [min_eq_right h]
      linarith [he0 i]
  have h2 : (0 : 𝕜) ≤ if Set.univ \ {i} ⊆ X \ {i} then max 0 (e i - margin g i) else 0 := by
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  linarith

/-- ★ … donc le plus petit équilibre amorcé : le seuil d'allumage n'est pas accru. -/
theorem capped_lfp_widens (hg : Supermodular g) {e : V → 𝕜} (he0 : ∀ i, 0 ≤ e i) {H : 𝕜}
    (hH : 0 ≤ H) :
    (br (shift g H) (hg.shift H)).lfp ⊆
      (br (shift (addGain g (capped g e)) H) ((capped_super hg e).shift H)).lfp :=
  (br (shift g H) (hg.shift H)).lfp_le fun _ hi =>
    (br (shift (addGain g (capped g e)) H) ((capped_super hg e).shift H)).map_lfp.le
      (capped_br_widens he0 hH _ hi)

/-- ★ Un amorçage qui allume le jeu de base, puis retiré, laisse le plein dans le jeu financé. -/
theorem capped_after_seed (hg : Supermodular g) {e : V → 𝕜} (he0 : ∀ i, 0 ≤ e i) {H : 𝕜}
    (hH : 0 ≤ H) (hign : (br (shift g H) (hg.shift H)).lfp = Set.univ) :
    afterSeed (addGain g (capped g e)) (capped_super hg e) H = Set.univ := by
  have h := capped_lfp_widens hg he0 hH
  rw [hign] at h
  rw [afterSeed_full _ (Set.eq_univ_of_univ_subset h), capped_gfp hg he0]

variable [Fintype V]

/-! ### §2. Noyau scalaire de la PIS, budget, pont avec la Phase 11 -/

/-- Noyau scalaire de la PIS : des transferts de somme négative rendent toutes les marges
positives ssi leur somme l'est. -/
theorem exists_balanced_iff (a : V → 𝕜) :
    (∃ t : V → 𝕜, ∑ i, t i ≤ 0 ∧ ∀ i, 0 ≤ a i + t i) ↔ 0 ≤ ∑ i, a i := by
  constructor
  · rintro ⟨t, ht, h⟩
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => h i
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro h
    refine ⟨fun i => -a i, ?_, fun i => by simp⟩
    rw [Finset.sum_neg_distrib]
    linarith

theorem finOf_univ : finOf (Set.univ : Set V) = Finset.univ :=
  Finset.eq_univ_of_forall fun _ => mem_finOf.mpr trivial

/-- ★ **Variante multiplicative** : si l'érosion `x` porte sur les canaux de rétention `P i` et
non sur les transferts, des transferts de somme négative tiennent le plein ssi
`x ≤ 1 − ΣGap / ΣP`. Le seuil `x̄_int(n) = 1 − Gap(n)/P(n)` que le modèle de Renn instancie en
est le cas symétrique. -/
theorem aggregate_threshold (P Gap : V → 𝕜) (hP : 0 < ∑ i, P i) (x : 𝕜) :
    (∃ t : V → 𝕜, ∑ i, t i ≤ 0 ∧ ∀ i, 0 ≤ P i * (1 - x) - Gap i + t i) ↔
      x ≤ 1 - (∑ i, Gap i) / ∑ i, P i := by
  rw [exists_balanced_iff fun i => P i * (1 - x) - Gap i, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  have key : 1 - (∑ i, Gap i) / (∑ i, P i) - x =
      ((∑ i, P i) * (1 - x) - ∑ i, Gap i) / ∑ i, P i := by
    field_simp
    ring
  rw [← sub_nonneg (b := x), key, le_div_iff₀ hP, zero_mul]

variable [DecidableEq V]

/-- Budget à chaque coalition : les transferts versés aux membres de `X` (face aux autres
membres) sont couverts par les drains des non-membres. -/
def Budget (drain t : V → Set V → 𝕜) : Prop :=
  ∀ X : Set V, ∑ i ∈ finOf X, t i (X \ {i}) ≤ ∑ j ∈ (finOf X)ᶜ, drain j X

omit [IsStrictOrderedRing 𝕜] in
/-- Au plein, il n'y a plus de non-membre : les transferts y sont de somme négative. -/
theorem budget_univ {drain t : V → Set V → 𝕜} (hB : Budget drain t) :
    ∑ i, t i (Set.univ \ {i}) ≤ 0 := by
  have h := hB Set.univ
  rwa [finOf_univ, Finset.compl_univ, Finset.sum_empty] at h

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Pont** : le financement frontalier de la Phase 11 est le budget des transferts positifs
`prem i (insert i S)`. -/
theorem borderFinanced_iff_budget (C : Club 𝕜 V) :
    BorderFinanced C ↔ Budget C.drain (fun i S => C.prem i (insert i S)) := by
  refine forall_congr' fun X => ?_
  have : ∑ i ∈ finOf X, C.prem i (insert i (X \ {i})) = ∑ i ∈ finOf X, C.prem i X :=
    Finset.sum_congr rfl fun i hi => by
      rw [Set.insert_diff_singleton, Set.insert_eq_of_mem (mem_finOf.mp hi)]
  show _ ≤ _ ↔ ∑ i ∈ finOf X, C.prem i (insert i (X \ {i})) ≤ _
  rw [this]

/-- ★ **Budget à chaque coalition** : hors du plein, le barème ne fait que prélever ; au plein,
le solde est `Σ (e − margin) ≤ 0`. -/
theorem capped_budget {drain : V → Set V → 𝕜} (hD : ∀ j X, 0 ≤ drain j X) {e : V → 𝕜}
    (he : ∑ i, e i ≤ ∑ i, margin g i) : Budget drain (capped g e) := by
  intro X
  by_cases hX : X = Set.univ
  · subst hX
    rw [finOf_univ, Finset.compl_univ, Finset.sum_empty]
    have h : ∀ i, capped g e i (Set.univ \ {i}) = e i - margin g i := fun i => by
      have := capped_full g e i
      simp only [addGain] at this
      show _ = e i - g i (Set.univ \ {i})
      linarith
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib]
    linarith
  · refine le_trans (Finset.sum_nonpos fun i hi => ?_) (Finset.sum_nonneg fun j _ => hD j X)
    have hiX := mem_finOf.mp hi
    obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem X).mp hX
    have hji : j ≠ i := fun h => hj (h ▸ hiX)
    have hnot : ¬ (Set.univ \ {i} ⊆ X \ {i}) := fun h => hj (h ⟨Set.mem_univ j, hji⟩).1
    simp only [capped, hnot, if_false, add_zero]
    exact min_le_left _ _

/-! ### §3. E7a — financement interne ⟺ PIS -/

/-- ★ **Financement interne ⟺ PIS** (Eyckmans et Finus, déf. 5 — résultat connu, cité) : un
transfert budgété à chaque coalition rend l'adhésion totale stable ssi la somme des marges de
pleine adhésion est positive. -/
theorem internal_financing_iff {drain : V → Set V → 𝕜} (hD : ∀ j X, 0 ≤ drain j X) :
    (∃ t, Budget drain t ∧ IsNash (addGain g t) Set.univ) ↔ 0 ≤ ∑ i, margin g i := by
  constructor
  · rintro ⟨t, hB, hN⟩
    have h1 := budget_univ hB
    have h2 : ∀ i, 0 ≤ margin g i + t i (Set.univ \ {i}) := full_nash_iff_margin.mp hN
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => h2 i
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro h
    refine ⟨capped g fun _ => 0, capped_budget hD ?_, capped_nash fun _ => le_rfl⟩
    simpa using h

/-! ### §4. E7a-sym — le cas symétrique : rien d'interne -/

/-- ★ **Symétrique : le financement interne n'apporte rien.** À marges égales, un transfert
budgété rend le plein stable ssi il l'est déjà sans transfert. -/
theorem sym_internal_useless {drain : V → Set V → 𝕜} (hD : ∀ j X, 0 ≤ drain j X)
    (hsym : ∀ i j, margin g i = margin g j) :
    (∃ t, Budget drain t ∧ IsNash (addGain g t) Set.univ) ↔ IsNash g Set.univ := by
  rw [internal_financing_iff hD, full_nash_iff_margin]
  constructor
  · intro h i
    have hs : ∑ j, margin g j = (Fintype.card V : 𝕜) * margin g i := by
      rw [Finset.sum_congr rfl fun j _ => hsym j i, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have hc : (0 : 𝕜) < Fintype.card V := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    rw [hs] at h
    by_contra hneg
    have := mul_neg_of_pos_of_neg hc (not_le.mp hneg)
    linarith
  · intro h
    exact Finset.sum_nonneg fun i _ => h i

/-- ★ **L'écart de la prime, toutes sources internes comprises** : le club témoin de la Phase 11
tient le plein avec sa prime extérieure, mais aucun transfert budgété ne le tient. -/
theorem premium_gap_internal :
    IsNash extClub.gain Set.univ ∧
      ¬ ∃ t, Budget extClub.drain t ∧
        IsNash (addGain (fun i S => extClub.intr i S + extClub.drain i S) t) Set.univ := by
  refine ⟨ClubFinancing.premium_gap_witness.1, ?_⟩
  rw [internal_financing_iff (drain := extClub.drain) fun _ _ => le_rfl]
  simp [margin, extClub]

/-! ### §5. Le barème plafonné finance « amorcer puis retirer » -/

variable {B Un : Type*} [Fintype Un] [DecidableEq Un]
variable {m : FeedbackClass.Memory} {r cap : ℕ} {enat : Un → ℕ} {aP aM : V → B → ℕ} {μ : B}

/-- ★ **Amorcer puis retirer, financé en interne** : sous PIS, il existe un transfert budgété à
chaque coalition, qui conserve la supermodularité, fait du plein le plus grand équilibre, laisse
le plein après tout amorçage qui allume le jeu de base puis est retiré, et pour lequel un
amorçage temporaire sûr existe ssi le plein est sûr. -/
theorem financed_seeding_safe (hg : Supermodular g) {drain : V → Set V → 𝕜}
    (hD : ∀ j X, 0 ≤ drain j X) (hPIS : 0 ≤ ∑ i, margin g i) :
    ∃ t, Budget drain t ∧ ∃ ht : Supermodular (addGain g t),
      (br _ ht).gfp = Set.univ ∧
      (∀ H, 0 ≤ H → (br (shift g H) (hg.shift H)).lfp = Set.univ →
        afterSeed _ ht H = Set.univ) ∧
      ((∃ H, 0 ≤ H ∧ Safe m r cap enat aP aM μ (afterSeed _ ht H)) ↔
        Safe m r cap enat aP aM μ Set.univ) := by
  have he0 : ∀ i : V, (0 : 𝕜) ≤ (fun _ => 0) i := fun _ => le_rfl
  refine ⟨capped g fun _ => 0, capped_budget hD (by simpa using hPIS), capped_super hg _,
    capped_gfp hg he0, fun H hH hign => capped_after_seed hg he0 hH hign, ?_⟩
  rw [seeding_safe_iff, capped_gfp hg he0]

/-! ### §6. E7c — rayon de robustesse du plein financé = marge moyenne -/

/-- ★ **Rayon = marge moyenne** : il existe un transfert supermodulaire, budgété à chaque
coalition, qui rend le plein robuste aux érosions de niveau `x` ssi `card V · x ≤ Σ margin`. Sans
transfert, le rayon est la marge minimale (`robust_iff_margin`). -/
theorem robust_financed_iff (hg : Supermodular g) {drain : V → Set V → 𝕜}
    (hD : ∀ j X, 0 ≤ drain j X) {x : 𝕜} :
    (∃ t, Supermodular (addGain g t) ∧ Budget drain t ∧ Robust (addGain g t) x Set.univ) ↔
      (Fintype.card V : 𝕜) * x ≤ ∑ i, margin g i := by
  constructor
  · rintro ⟨t, ht, hB, hR⟩
    have h1 := budget_univ hB
    have h2 := (robust_iff_margin ht).mp hR
    have h3 : ∀ i, x ≤ margin g i + t i (Set.univ \ {i}) := fun i => h2 i (Set.mem_univ i)
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib] at this
    linarith
  · intro h
    refine ⟨capped g fun _ => x, capped_super hg _, capped_budget hD ?_, ?_⟩
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact h
    · rw [robust_iff_margin (capped_super hg _)]
      intro i _
      exact (capped_full g (fun _ => x) i).ge

/-! ### §7. E7d — la caisse : dotation `≥ P/r` -/

/-- Forme close de la caisse, sans division : `r · F t − P = (1+r)^t · (r · F 0 − P)`. -/
theorem fund_closed {r P : 𝕜} {F : ℕ → 𝕜} (hF : ∀ t, F (t + 1) = (1 + r) * F t - P) :
    ∀ t, r * F t - P = (1 + r) ^ t * (r * F 0 - P)
  | 0 => by simp
  | t + 1 => by
    have ih := fund_closed hF t
    rw [hF, pow_succ]
    linear_combination (1 + r) * ih

/-- ★ **Une prime perpétuelle exige une dotation `≥ P/r`** : à taux `r > 0`, la caisse reste
positive à toute date ssi `P ≤ r · F 0`. Condition de limite (O'Connell et Zeldes 1988), pas de
cycle. -/
theorem fund_perpetuity_iff [Archimedean 𝕜] {r P : 𝕜} {F : ℕ → 𝕜} (hr : 0 < r) (hP : 0 ≤ P)
    (hF : ∀ t, F (t + 1) = (1 + r) * F t - P) : (∀ t, 0 ≤ F t) ↔ P ≤ r * F 0 := by
  constructor
  · intro h
    by_contra hlt
    have hd : 0 < P - r * F 0 := by linarith [not_le.mp hlt]
    obtain ⟨n, hn⟩ := exists_nat_gt (P / (r * (P - r * F 0)))
    have hn' : P < n * (r * (P - r * F 0)) := (div_lt_iff₀ (mul_pos hr hd)).mp hn
    have hb : 1 + (n : 𝕜) * r ≤ (1 + r) ^ n := one_add_mul_le_pow (by linarith) n
    have hm : (1 + (n : 𝕜) * r) * (P - r * F 0) ≤ (1 + r) ^ n * (P - r * F 0) :=
      mul_le_mul_of_nonneg_right hb hd.le
    have hc := fund_closed hF n
    have hFn : r * F n < 0 := by nlinarith
    have := h n
    nlinarith
  · intro h t
    have hc := fund_closed hF t
    have h0 : 0 ≤ (1 + r) ^ t * (r * F 0 - P) :=
      mul_nonneg (pow_nonneg (by linarith) t) (by linarith)
    have : 0 ≤ r * F t := by linarith
    exact (mul_nonneg_iff_of_pos_left hr).mp this

/-- ★ À taux nul, une prime positive épuise toute caisse finie. -/
theorem fund_exhausted_zero_rate [Archimedean 𝕜] {P : 𝕜} {F : ℕ → 𝕜} (hP : 0 < P)
    (hF : ∀ t, F (t + 1) = F t - P) : ∃ t, F t < 0 := by
  have hc : ∀ t : ℕ, F t = F 0 - t * P := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hF, ih]
      push_cast
      ring
  obtain ⟨n, hn⟩ := exists_nat_gt (F 0 / P)
  refine ⟨n, ?_⟩
  rw [hc]
  have := (div_lt_iff₀ hP).mp hn
  linarith

end ClubTransfers

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf
`premium_gap_internal`, qui porte sur le club témoin `ClubFinancing.extClub` et reste dans `ℚ`.
`fund_perpetuity_iff` et `fund_exhausted_zero_rate` demandent en plus un corps archimédien
(`[Archimedean 𝕜]`, pour `exists_nat_gt`) ; `ℝ` l'est. Aucune preuve n'utilise la complétude.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
