/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/DeadlineGuard.lean
  Phase 16 (2026-10-04) : la garde à échéances (papier 11, option γ) — des droits divisibles,
  chacun avec son échéance, validés par la faisabilité d'un plan de service dans le seau à
  jetons de la mémoire.

  Développé d'abord en `DeadlineGuard_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase16_2026-10-04/plan.md` ; analyse :
  `cache/phase16_2026-10-04/analyse_droits_echeances_2026-10-04.md` (§2-§4) ; sonde :
  `cache/phase16_2026-10-04/outils/sonde_echeances.py`.
-/

import ThesePlanetaire.GuardField

/-!
# La garde à échéances

Modèle **par période**. Dans une période, la charge est monotone : l'ordre des événements n'y joue
pas, seul compte le total consommé (`GuardField`, §2-§3). Les jetons `T = cap − L` suivent le seau
de la mémoire (`GuardField.tickOpF_tokens`) : `T ↦ min (T − c + ρ) C` après une consommation `c`.

- `M` : charge obligatoire par période, au pire cas (incontrôlables, émissions essentielles
  récurrentes ; `GuardField.uncMassMax`).
- Droits en attente : `b i ≥ 0` (divisibles), à servir au plus tard à la période `d i`
  (0 = la période courante).
- Un plan sert chaque droit avant son échéance, et tient chaque période dans les jetons, la
  charge obligatoire comprise. La garde admet une émission discrétionnaire `a` ssi un tel plan
  existe depuis `T − a` (`dlGuard`).

1. ★ `feasible_mono`, `dlGuard_safe` : la faisabilité est monotone en jetons ; une émission
   admise laisse un service de la période tel que, pour toute charge réalisée `u ≤ M`, l'état
   suivant (échéances décalées) reste faisable. Sur tout corps ordonné.
2. ★ `stationary_viable`, `stationary_necessary`, `dlGuard_maximal`, `dlGuard_iff` : la charge
   obligatoire doit tenir dans le débit, `M ≤ min ρ C` (nécessaire sur un corps archimédien) ; la
   garde admet exactement les émissions qui ouvrent un déroulé infini sûr.
3. ★ Formes closes : `dl_k0_iff` (toutes les échéances à 0 : la réserve additive
   `Σ b + M ≤ T`, pont `nbReserve_eq_dl_k0` avec `GuardField.ResNB`) ; `dl_k1_iff` (échéances
   `≤ 1` : `B₀ + M ≤ T` et `B₀ + B₁ + 2M ≤ T + min ρ C`).
4. ★ Témoins : `deferral_strict` (le report admet ce que la réserve additive refuse) ;
   `lumps_gap` (des lots indivisibles reportables : la fenêtre passe, aucun plan n'existe).
-/

namespace DeadlineGuard

open FeedbackClass (Memory)
open GuardField (tickOpF rhoF tickOpF_tokens ResNB)

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## §1. Seau à jetons, plans, faisabilité -/

section Defs

variable (C ρ M : 𝕜) {ι : Type*} [Fintype ι] (b : ι → 𝕜) (d : ι → ℕ)

/-- Jetons après une période de consommation `c` : `min (T − c + ρ) C`. -/
def tokNext (T c : 𝕜) : 𝕜 := min (T - c + ρ) C

/-- Jetons au début de chaque période, pour les consommations `c`. -/
def toks (T : 𝕜) (c : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => T
  | t + 1 => tokNext C ρ (toks T c t) (c t)

/-- Un service respecte les droits : positif, nul après l'échéance, de somme `b i`. -/
def Serves (x : ι → ℕ → 𝕜) : Prop :=
  (∀ i t, 0 ≤ x i t) ∧ (∀ i t, d i < t → x i t = 0) ∧
    ∀ i, ∑ t ∈ Finset.range (d i + 1), x i t = b i

/-- Consommation d'une période sous un plan : charge obligatoire et service. -/
def planLoad (x : ι → ℕ → 𝕜) (t : ℕ) : 𝕜 := M + ∑ i, x i t

/-- Un plan sert les droits et tient chaque période dans les jetons. -/
def PlanOK (T : 𝕜) (x : ι → ℕ → 𝕜) : Prop :=
  Serves b d x ∧ ∀ t, planLoad M x t ≤ toks C ρ T (planLoad M x) t

/-- Faisabilité : la charge obligatoire tient dans le débit, et un plan existe. -/
def Feasible (T : 𝕜) : Prop := M ≤ min ρ C ∧ ∃ x, PlanOK C ρ M b d T x

/-- La garde à échéances : admettre l'émission discrétionnaire `a` ssi l'état reste faisable. -/
def dlGuard (T a : 𝕜) : Prop := Feasible C ρ M b d (T - a)

/-- Consommation d'une période d'un déroulé : charge obligatoire (au pire cas), émission
discrétionnaire `a t`, service. -/
def runLoad (a : ℕ → 𝕜) (y : ι → ℕ → 𝕜) (t : ℕ) : 𝕜 := M + (a t + ∑ i, y i t)

/-- Un déroulé infini est sûr contre la charge `M` : émissions discrétionnaires positives, et
chaque période tient dans les jetons. -/
def SafeRun (T : 𝕜) (a : ℕ → 𝕜) (y : ι → ℕ → 𝕜) : Prop :=
  (∀ t, 0 ≤ a t) ∧ ∀ t, runLoad M a y t ≤ toks C ρ T (runLoad M a y) t

end Defs

variable {C ρ M : 𝕜} {ι : Type*} [Fintype ι] {b : ι → 𝕜} {d : ι → ℕ}

/-- Le seau de `DeadlineGuard` est celui de la mémoire : jetons `cap − L`, débit `rhoF`. -/
theorem tokNext_tickOpF (mem : Memory) {r cap L c : 𝕜} (hL : 0 ≤ L + c) (hLc : L + c ≤ cap) :
    tokNext cap (rhoF mem r cap) (cap - L) c = cap - tickOpF mem r (L + c) := by
  rw [tickOpF_tokens mem hL hLc, tokNext]
  ring_nf

/-! ## §2. Monotonie, sûreté de la garde -/

section Safety

theorem tokNext_mono {T T' c c' : 𝕜} (hT : T ≤ T') (hc : c' ≤ c) :
    tokNext C ρ T c ≤ tokNext C ρ T' c' :=
  min_le_min_right _ (by linarith)

theorem toks_mono {T T' : 𝕜} {c c' : ℕ → 𝕜} (hT : T ≤ T') (hc : ∀ t, c' t ≤ c t) :
    ∀ t, toks C ρ T c t ≤ toks C ρ T' c' t
  | 0 => hT
  | t + 1 => tokNext_mono (toks_mono hT hc t) (hc t)

/-- ★ **Dominance** : plus de jetons ne rend jamais infaisable. -/
theorem feasible_mono {T T' : 𝕜} (hT : T ≤ T') (h : Feasible C ρ M b d T) :
    Feasible C ρ M b d T' := by
  obtain ⟨hM, x, hx, hp⟩ := h
  exact ⟨hM, x, hx, fun t => le_trans (hp t) (toks_mono hT (fun _ => le_rfl) t)⟩

/-- ★ **Stationnaire** : si `M ≤ min ρ C`, une période à charge `M` seule garde les jetons
au-dessus de `M`. -/
theorem stationary_viable {T : 𝕜} (hM : M ≤ min ρ C) (hT : M ≤ T) : M ≤ tokNext C ρ T M := by
  rw [le_min_iff] at hM
  exact le_min (by linarith) hM.2

omit [IsStrictOrderedRing 𝕜] in
theorem toks_shift (T : 𝕜) (c : ℕ → 𝕜) :
    ∀ t, toks C ρ (toks C ρ T c 1) (fun t => c (t + 1)) t = toks C ρ T c (t + 1)
  | 0 => rfl
  | t + 1 => by
    show tokNext C ρ (toks C ρ (toks C ρ T c 1) (fun t => c (t + 1)) t) (c (t + 1)) = _
    rw [toks_shift T c t]
    rfl

omit [Fintype ι] in
theorem serves_le (hx : Serves b d x) (i : ι) : x i 0 ≤ b i := by
  rw [← hx.2.2 i]
  exact Finset.single_le_sum (fun t _ => hx.1 i t) (Finset.mem_range.mpr (Nat.succ_pos _))

/-- Après une période, le plan décalé sert les droits restants (échéances décalées). -/
theorem planOK_shift {T : 𝕜} {x : ι → ℕ → 𝕜} (h : PlanOK C ρ M b d T x) :
    PlanOK C ρ M (fun i => b i - x i 0) (fun i => d i - 1) (toks C ρ T (planLoad M x) 1)
      (fun i t => x i (t + 1)) := by
  obtain ⟨⟨h0, hz, hs⟩, hp⟩ := h
  refine ⟨⟨fun i t => h0 i (t + 1), fun i t ht => hz i (t + 1) (by dsimp only at ht; omega),
    fun i => ?_⟩, fun t => ?_⟩
  · dsimp only
    have := hs i
    rcases Nat.eq_zero_or_pos (d i) with hd | hd
    · rw [hd, zero_add, Finset.sum_range_one] at this
      rw [hd, Nat.zero_sub, zero_add, Finset.sum_range_one, hz i 1 (by omega), this, sub_self]
    · rw [Finset.sum_range_succ'] at this
      rw [show d i - 1 + 1 = d i by omega]
      linarith
  · have := hp (t + 1)
    rw [← toks_shift] at this
    exact this

/-- ★ **Sûreté de la garde** : si l'émission `a` est admise, il existe un service `s` de la
période (les droits échus servis en entier) tel que la période tient dans les jetons, et que,
pour toute charge obligatoire réalisée `u ≤ M`, l'état suivant reste faisable. -/
theorem dlGuard_safe {T a : 𝕜} (h : dlGuard C ρ M b d T a) :
    ∃ s : ι → 𝕜, (∀ i, 0 ≤ s i ∧ s i ≤ b i) ∧ (∀ i, d i = 0 → s i = b i) ∧
      a + M + ∑ i, s i ≤ T ∧
      ∀ u, u ≤ M → Feasible C ρ M (fun i => b i - s i) (fun i => d i - 1)
        (tokNext C ρ (T - a) (u + ∑ i, s i)) := by
  obtain ⟨hM, x, hx, hp⟩ := h
  refine ⟨fun i => x i 0, fun i => ⟨hx.1 i 0, serves_le hx i⟩, fun i hd => ?_, ?_, fun u hu => ?_⟩
  · have := hx.2.2 i
    rwa [hd, zero_add, Finset.sum_range_one] at this
  · have := hp 0
    simp only [planLoad, toks] at this
    linarith
  · refine feasible_mono ?_ ⟨hM, _, planOK_shift ⟨hx, hp⟩⟩
    exact tokNext_mono le_rfl (by simp only [planLoad]; linarith)

end Safety

/-! ## §3. Nécessité stationnaire et maximalité (corps archimédien) -/

section Maximal

/-- ★ **Nécessité stationnaire** (corps archimédien) : si `M > min ρ C`, aucun déroulé infini
ne tient la charge `M` — le pendant de `GuardField.stockF_unc_empty` et
`GuardField.regenF_unc_empty`. -/
theorem stationary_necessary [Archimedean 𝕜] {T : 𝕜} {c : ℕ → 𝕜} (hc : ∀ t, 0 ≤ c t)
    (h : ∀ t, M + c t ≤ toks C ρ T (fun t => M + c t) t) : M ≤ min ρ C := by
  by_contra hlt
  rcases min_lt_iff.mp (not_le.mp hlt) with hρ | hC
  · -- chaque période retire au moins `δ = M − ρ` jetons
    have key : ∀ t : ℕ, toks C ρ T (fun t => M + c t) t ≤ T - t * (M - ρ) := by
      intro t
      induction t with
      | zero => simp [toks]
      | succ t ih =>
        show min (toks C ρ T (fun t => M + c t) t - (M + c t) + ρ) C ≤ _
        have := hc t
        push_cast
        linarith [min_le_left (toks C ρ T (fun t => M + c t) t - (M + c t) + ρ) C]
    obtain ⟨k, hk⟩ := exists_nat_gt ((T - M) / (M - ρ))
    have h1 := (div_lt_iff₀ (by linarith : (0 : 𝕜) < M - ρ)).mp hk
    have h2 := h k
    have h3 := key k
    linarith [hc k]
  · have h1 := h 1
    have h2 : toks C ρ T (fun t => M + c t) 1 ≤ C := min_le_right _ _
    linarith [hc 1]

theorem toks_run_le {T : 𝕜} {a : ℕ → 𝕜} {y : ι → ℕ → 𝕜} (ha : ∀ t, 0 ≤ a t) :
    ∀ t, toks C ρ T (runLoad M a y) t - a t ≤ toks C ρ (T - a 0) (planLoad M y) t
  | 0 => le_rfl
  | t + 1 => by
    have ih := toks_run_le (T := T) (a := a) (y := y) ha t
    have h : toks C ρ T (runLoad M a y) (t + 1) ≤ toks C ρ (T - a 0) (planLoad M y) (t + 1) := by
      show min (_ - runLoad M a y t + ρ) C ≤ min (_ - planLoad M y t + ρ) C
      refine min_le_min_right _ ?_
      simp only [runLoad, planLoad]
      linarith
    linarith [ha (t + 1)]

/-- ★ **Maximalité** (corps archimédien) : tout déroulé infini sûr contre la charge `M`, qui sert
les droits avant leurs échéances, a son émission discrétionnaire initiale admise par la garde. -/
theorem dlGuard_maximal [Archimedean 𝕜] {T : 𝕜} {a : ℕ → 𝕜} {y : ι → ℕ → 𝕜}
    (hy : Serves b d y) (hrun : SafeRun C ρ M T a y) : dlGuard C ρ M b d T (a 0) := by
  obtain ⟨ha, hr⟩ := hrun
  refine ⟨stationary_necessary (c := fun t => a t + ∑ i, y i t) (T := T)
    (fun t => add_nonneg (ha t) (Finset.sum_nonneg fun i _ => hy.1 i t)) hr, y, hy, fun t => ?_⟩
  have h1 := hr t
  have h2 := toks_run_le (y := y) (T := T) (C := C) (ρ := ρ) (M := M) ha t
  simp only [runLoad, planLoad] at h1 ⊢
  linarith

/-- ★ **La garde admet exactement ce qui ouvre un déroulé infini sûr** (corps archimédien). -/
theorem dlGuard_iff [Archimedean 𝕜] {T a : 𝕜} (ha : 0 ≤ a) :
    dlGuard C ρ M b d T a ↔ ∃ a' y, a' 0 = a ∧ Serves b d y ∧ SafeRun C ρ M T a' y := by
  constructor
  · rintro ⟨-, x, hx, hp⟩
    let a' : ℕ → 𝕜 := fun t => if t = 0 then a else 0
    have key : ∀ t, toks C ρ T (runLoad M a' x) t = toks C ρ (T - a) (planLoad M x) t + a' t := by
      intro t
      induction t with
      | zero => simp [toks, a']
      | succ t ih =>
        show min (_ - runLoad M a' x t + ρ) C = min (_ - planLoad M x t + ρ) C + a' (t + 1)
        rw [ih]
        simp only [runLoad, planLoad, a', if_neg (Nat.succ_ne_zero t), add_zero]
        ring_nf
    refine ⟨a', x, by simp [a'], hx, fun t => by simp only [a']; split_ifs <;> linarith, fun t => ?_⟩
    rw [key]
    have := hp t
    simp only [runLoad, planLoad] at this ⊢
    linarith
  · rintro ⟨a', y, rfl, hy, hrun⟩
    exact dlGuard_maximal hy hrun

end Maximal

/-! ## §4. Formes closes -/

section Closed

/-- Toutes les périodes après la première : la charge obligatoire seule tient. -/
theorem toks_tail {T : 𝕜} {c : ℕ → 𝕜} (hM : M ≤ min ρ C) (n : ℕ) (hc : ∀ t, n ≤ t → c t = M)
    (hn : M ≤ toks C ρ T c n) : ∀ t, n ≤ t → M ≤ toks C ρ T c t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hn
  | succ t ht ih =>
    show M ≤ tokNext C ρ (toks C ρ T c t) (c t)
    rw [hc t ht]
    exact stationary_viable hM ih

/-- ★ **Échéances toutes à 0 : la réserve additive.** -/
theorem dl_k0_iff {T : 𝕜} (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, d i = 0) :
    Feasible C ρ M b d T ↔ M ≤ min ρ C ∧ ∑ i, b i + M ≤ T := by
  constructor
  · rintro ⟨hM, x, hx, hp⟩
    have h0 : ∀ i, x i 0 = b i := fun i => by
      have := hx.2.2 i
      rwa [hd i, zero_add, Finset.sum_range_one] at this
    have := hp 0
    simp only [planLoad, toks, h0] at this
    exact ⟨hM, by linarith⟩
  · rintro ⟨hM, hT⟩
    let x : ι → ℕ → 𝕜 := fun i t => if t = 0 then b i else 0
    have hx : Serves b d x := by
      refine ⟨fun i t => ?_, fun i t ht => ?_, fun i => ?_⟩
      · simp only [x]; split_ifs <;> simp [hb i]
      · simp only [x]; rw [if_neg (by omega)]
      · simp [x, hd i]
    have hl0 : planLoad M x 0 = M + ∑ i, b i := by simp [planLoad, x]
    have hl : ∀ t, 1 ≤ t → planLoad M x t = M := fun t ht => by
      simp [planLoad, x, show t ≠ 0 by omega]
    refine ⟨hM, x, hx, fun t => ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hl0]; simp only [toks]; linarith
    · rw [hl t ht]
      refine toks_tail hM 1 hl ?_ t ht
      show M ≤ min (T - planLoad M x 0 + ρ) C
      rw [hl0]
      rw [le_min_iff] at hM
      exact le_min (by linarith) hM.2

/-- ★ **Pont avec le non-blocage** (`GuardField`, §3) : sans charge obligatoire, avec des
échéances toutes à 0 et les jetons `cap − L`, la faisabilité est la réserve de non-blocage. -/
theorem nbReserve_eq_dl_k0 [DecidableEq ι] {L cap : 𝕜} (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, d i = 0)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) :
    Feasible C ρ 0 b d (cap - L) ↔ ResNB b cap (L, Finset.univ) := by
  rw [dl_k0_iff hb hd]
  simp only [ResNB, le_min_iff, hρ, hC, true_and]
  constructor <;> intro h <;> linarith

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Les droits d'échéance `≤ 1` se partagent en échus (0) et reportables d'une période (1). -/
theorem sum_split01 (hd : ∀ i, d i ≤ 1) (f : ι → 𝕜) :
    ∑ i, f i = ∑ i ∈ Finset.univ.filter (fun i => d i = 0), f i +
      ∑ i ∈ Finset.univ.filter (fun i => d i = 1), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i = 0)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  have := hd i
  omega

/-- ★ **Échéances `≤ 1` : forme close.** Avec `B₀` les droits échus et `B₁` les droits
reportables d'une période, un plan existe ssi `B₀ + M ≤ T` et `B₀ + B₁ + 2M ≤ T + min ρ C`.
Le plan avance `y = max 0 (B₁ + M − C)` de `B₁` en période 0. -/
theorem dl_k1_iff {T : 𝕜} (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, d i ≤ 1) :
    Feasible C ρ M b d T ↔
      M ≤ min ρ C ∧ ∑ i ∈ Finset.univ.filter (fun i => d i = 0), b i + M ≤ T ∧
        ∑ i ∈ Finset.univ.filter (fun i => d i = 0), b i +
          ∑ i ∈ Finset.univ.filter (fun i => d i = 1), b i + 2 * M ≤ T + min ρ C := by
  set F0 := Finset.univ.filter (fun i => d i = 0)
  set F1 := Finset.univ.filter (fun i => d i = 1)
  have mem0 : ∀ i, i ∈ F0 ↔ d i = 0 := fun i => by simp [F0]
  have mem1 : ∀ i, i ∈ F1 ↔ d i = 1 := fun i => by simp [F1]
  constructor
  · rintro ⟨hM, x, ⟨h0, hz, hs⟩, hp⟩
    have hx0 : ∀ i ∈ F0, x i 0 = b i := fun i hi => by
      have := hs i
      rwa [(mem0 i).mp hi, zero_add, Finset.sum_range_one] at this
    have hx1 : ∀ i ∈ F0, x i 1 = 0 := fun i hi => hz i 1 (by rw [(mem0 i).mp hi]; omega)
    have hy1 : ∀ i ∈ F1, x i 1 = b i - x i 0 := fun i hi => by
      have := hs i
      rw [(mem1 i).mp hi, Finset.sum_range_succ, Finset.sum_range_one] at this
      linarith
    set y := ∑ i ∈ F1, x i 0
    have hy : 0 ≤ y := Finset.sum_nonneg fun i _ => h0 i 0
    have hl0 : planLoad M x 0 = M + (∑ i ∈ F0, b i + y) := by
      rw [planLoad, sum_split01 hd, Finset.sum_congr rfl hx0]
    have hl1 : planLoad M x 1 = M + (∑ i ∈ F1, b i - y) := by
      rw [planLoad, sum_split01 hd, Finset.sum_congr rfl hx1, Finset.sum_congr rfl hy1,
        Finset.sum_const_zero, zero_add, Finset.sum_sub_distrib]
    have p0 := hp 0
    have p1 := hp 1
    simp only [toks, tokNext] at p0 p1
    rw [hl0] at p0
    rw [hl1, hl0, le_min_iff] at p1
    have : ∑ i ∈ F0, b i + ∑ i ∈ F1, b i + 2 * M - T ≤ min ρ C :=
      le_min (by linarith [p1.1]) (by linarith [p1.2])
    exact ⟨hM, by linarith, by linarith⟩
  · rintro ⟨hM, h0, h1⟩
    have hM' := le_min_iff.mp hM
    have h1' := le_min_iff.mp (show ∑ i ∈ F0, b i + ∑ i ∈ F1, b i + 2 * M - T ≤ min ρ C by
      linarith)
    set B0 := ∑ i ∈ F0, b i
    set B1 := ∑ i ∈ F1, b i
    have hB1 : 0 ≤ B1 := Finset.sum_nonneg fun i _ => hb i
    obtain ⟨y, hy_eq⟩ : ∃ y, y = max 0 (B1 + M - C) := ⟨_, rfl⟩
    have hy0 : 0 ≤ y := hy_eq ▸ le_max_left _ _
    have hyC : B1 + M - C ≤ y := hy_eq ▸ le_max_right _ _
    have hyB : y ≤ B1 := hy_eq ▸ max_le hB1 (by linarith [hM'.2])
    -- la part avancée `θ = y / B₁`
    set θ := y / B1
    have hθ : 0 ≤ θ ∧ θ ≤ 1 ∧ θ * B1 = y := by
      rcases hB1.lt_or_eq with hpos | hzero
      · exact ⟨div_nonneg hy0 hB1, (div_le_one hpos).mpr hyB, div_mul_cancel₀ y hpos.ne'⟩
      · have : y = 0 := le_antisymm (hzero ▸ hyB) hy0
        simp [θ, ← hzero, this]
    obtain ⟨hθ0, hθ1, hθB⟩ := hθ
    let x : ι → ℕ → 𝕜 := fun i t =>
      if d i = 0 then (if t = 0 then b i else 0)
      else if t = 0 then θ * b i else if t = 1 then (1 - θ) * b i else 0
    have hx : Serves b d x := by
      refine ⟨fun i t => ?_, fun i t ht => ?_, fun i => ?_⟩
      · have := hb i
        simp only [x]
        split_ifs
        · exact this
        · exact le_rfl
        · exact mul_nonneg hθ0 this
        · exact mul_nonneg (by linarith) this
        · exact le_rfl
      · simp only [x]
        have := hd i
        split_ifs <;> first | rfl | omega
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i) with h | h
        · simp [x, h]
        · simp only [x, h, one_ne_zero, if_false, Finset.sum_range_succ]
          simp
          ring
    have hl0 : planLoad M x 0 = M + (B0 + y) := by
      rw [planLoad, sum_split01 hd, ← hθB, Finset.mul_sum]
      congr 2
      · exact Finset.sum_congr rfl fun i hi => by simp [x, (mem0 i).mp hi]
      · exact Finset.sum_congr rfl fun i hi => by simp [x, (mem1 i).mp hi]
    have hl1 : planLoad M x 1 = M + (B1 - y) := by
      rw [planLoad, sum_split01 hd, ← hθB,
        show B1 - θ * B1 = ∑ i ∈ F1, (1 - θ) * b i by rw [← Finset.mul_sum]; ring]
      congr 1
      rw [Finset.sum_eq_zero fun i hi => by simp [x, (mem0 i).mp hi], zero_add]
      exact Finset.sum_congr rfl fun i hi => by simp [x, (mem1 i).mp hi]
    have hl : ∀ t, 2 ≤ t → planLoad M x t = M := fun t ht => by
      simp [planLoad, x, show t ≠ 0 by omega, show t ≠ 1 by omega]
    have p0 : planLoad M x 0 ≤ toks C ρ T (planLoad M x) 0 := by
      rw [hl0]
      show M + (B0 + y) ≤ T
      rcases max_choice 0 (B1 + M - C) with h | h <;> rw [← hy_eq] at h <;> linarith
    have p1 : planLoad M x 1 ≤ toks C ρ T (planLoad M x) 1 := by
      show planLoad M x 1 ≤ min (T - planLoad M x 0 + ρ) C
      rw [hl1, hl0]
      exact le_min (by linarith) (by linarith)
    refine ⟨hM, x, hx, fun t => ?_⟩
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t
      · exact p0
      · exact p1
    · rw [hl t ht]
      refine toks_tail hM 2 hl ?_ t ht
      show M ≤ min (toks C ρ T (planLoad M x) 1 - planLoad M x 1 + ρ) C
      exact le_min (by linarith [hM'.1]) hM'.2

end Closed

/-! ## §5. Témoins -/

/-- ★ **Le report admet ce que la réserve additive refuse** (`C = 7`, `ρ = 3`, `M = 0`, jetons
`T = 7`, un droit `b = 4`). Échu (`d = 0`), il interdit l'émission `a = 6` ; reportable d'une
période (`d = 1`), il l'admet ; `a = 7` reste refusée. -/
theorem deferral_strict :
    ¬ dlGuard (7 : ℚ) 3 0 (fun _ : Unit => 4) (fun _ => 0) 7 6 ∧
      dlGuard (7 : ℚ) 3 0 (fun _ : Unit => 4) (fun _ => 1) 7 6 ∧
      ¬ dlGuard (7 : ℚ) 3 0 (fun _ : Unit => 4) (fun _ => 1) 7 7 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dlGuard, dl_k0_iff (fun _ => by norm_num) (fun _ => rfl)]
    norm_num
  · rw [dlGuard, dl_k1_iff (fun _ => by norm_num) (fun _ => le_rfl)]
    norm_num
  · rw [dlGuard, dl_k1_iff (fun _ => by norm_num) (fun _ => le_rfl)]
    norm_num

/-- ★ **Lots indivisibles reportables** : trois lots de 3, deux périodes de capacité 5
(`C = ρ = T = 5`, `M = 0`). Divisibles, ils sont servables (`9 ≤ 10`) ; indivisibles, aucune
affectation des lots aux périodes ne tient. -/
theorem lumps_gap :
    Feasible (5 : ℚ) 5 0 (fun _ : Fin 3 => 3) (fun _ => 1) 5 ∧
      ¬ ∃ f : Fin 3 → Fin 2, ∀ p : Fin 2, 3 * (Finset.univ.filter (fun k => f k = p)).card ≤ 5 := by
  refine ⟨?_, by decide⟩
  rw [dl_k1_iff (fun _ => by norm_num) (fun _ => le_rfl)]
  norm_num

end DeadlineGuard

/-!
## Domaine (Phase 16, 2026-10-04 ; décision D-21)

- **Corps ordonné quelconque** : les définitions, `feasible_mono`, `stationary_viable`,
  `dlGuard_safe`, les formes closes `dl_k0_iff` et `dl_k1_iff`, le pont `nbReserve_eq_dl_k0`.
- **Corps archimédien** : `stationary_necessary`, `dlGuard_maximal`, `dlGuard_iff` (la nécessité
  de `M ≤ min ρ C`). Remarque non formalisée : sans l'hypothèse, une perte infinitésimale par
  période ne vide jamais le seau.
- **Droits divisibles** : le service `x i t` prend des valeurs dans `𝕜`. Les lots indivisibles ne
  sont admis que dans la période (`GuardField`, §3). Reportables, ils rendent la condition de
  fenêtre insuffisante (`lumps_gap`) ; leur validation exacte n'est pas traitée.
- **Forme close jusqu'à une période de report** (`dl_k1_iff`). Au-delà, existence et maximalité
  seulement (`dlGuard_safe`, `dlGuard_iff`).
- **Modèle par période**, charge obligatoire `M` au pire cas : un plan faisable au pire cas le
  reste pour toute charge réalisée inférieure (`feasible_mono`, et `dlGuard_safe` pour tout
  `u ≤ M`). La maximalité est relative à une garde qui ne révise pas `M` au vu des réalisations.
- Débit quelconque : `min ρ C` couvre le cas `ρ > C` (correctif K31 du registre des écarts) ; pour
  les trois mémoires, `ρ = GuardField.rhoF mem r cap ≤ cap` (`GuardField.rhoF_le_cap`), et le
  seau est celui de la mémoire (`tokNext_tickOpF`).
- Témoins : `deferral_strict` dans `ℚ` ; `lumps_gap` dans `ℚ` (partie divisible) et dans `ℕ`
  (affectation des lots, `decide`).
-/
