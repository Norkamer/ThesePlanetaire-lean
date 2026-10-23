/-
  ViabilityKernel.lean — Noyau de viabilité comme plus grand point fixe.

  Brique formelle autonome (ne greffe pas sur `ClearingOperator` de
  `LatticeClearing.lean`, dont les axiomes sont spécifiques) mais imite ses
  schémas de preuve : chaîne descendante depuis un ensemble de départ,
  stabilisation par pigeonhole en cadre fini, plus grand point fixe.

  Cadre (viability theory, Aubin 1991) : un ensemble de contraintes `K`
  (les états admissibles) et une dynamique `step : S → Finset S` (les
  successeurs possibles d'un état). Le noyau de viabilité est l'ensemble des
  états de `K` d'où l'on peut rester indéfiniment dans `K` en suivant `step`.

  Version finitaire : `viableN x n` = il existe un chemin de longueur `n`
  issu de `x` restant dans `K` à chaque étape. C'est la version prouvable
  sans axiome de choix ; l'équivalence avec les trajectoires infinies sur un
  ensemble fini se commente en prose, ne se prouve pas ici (cf. plan macro
  P1, décisions tranchées).

  Théorème cible : `viability_kernel_eq_gfp` — le noyau (plus grand point
  fixe de l'opérateur de pré-image admissible) coïncide exactement avec
  l'ensemble des états viables à TOUT horizon fini.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace ViabilityKernel

variable {S : Type*} [DecidableEq S] [Fintype S]

/-! ### 1. L'opérateur de pré-image admissible -/

/-- Pré-image admissible restreinte à `K` : états de `K` ayant au moins un
    successeur dans `A`. -/
def preK (K : Finset S) (step : S → Finset S) (A : Finset S) : Finset S :=
  K.filter (fun x => (step x ∩ A).Nonempty)

lemma preK_subset_K (K : Finset S) (step : S → Finset S) (A : Finset S) :
    preK K step A ⊆ K :=
  Finset.filter_subset _ _

/-- `preK K step` est monotone en son argument `A`. -/
lemma preK_mono {K : Finset S} {step : S → Finset S} {A B : Finset S}
    (h : A ⊆ B) : preK K step A ⊆ preK K step B := by
  intro x hx
  rw [preK, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  obtain ⟨y, hy⟩ := hx.2
  rw [Finset.mem_inter] at hy
  exact ⟨y, Finset.mem_inter.mpr ⟨hy.1, h hy.2⟩⟩

/-! ### 2. Chaîne descendante depuis K (analogue de bw_gfp_chain) -/

/-- Chaîne descendante : `kernelChain K step 0 = K`,
    `kernelChain K step (n+1) = preK K step (kernelChain K step n)`. -/
def kernelChain (K : Finset S) (step : S → Finset S) : ℕ → Finset S
  | 0 => K
  | n + 1 => preK K step (kernelChain K step n)

/-- La chaîne est décroissante (adjacente) : chaque étape est incluse dans
    la précédente. -/
lemma kernelChain_antitone (K : Finset S) (step : S → Finset S) :
    ∀ n, kernelChain K step (n + 1) ⊆ kernelChain K step n := by
  intro n
  induction n with
  | zero =>
    show preK K step K ⊆ K
    exact preK_subset_K K step K
  | succ n ih =>
    show preK K step (kernelChain K step (n + 1)) ⊆ preK K step (kernelChain K step n)
    exact preK_mono ih

/-- Antitonie de la chaîne pour des indices quelconques (pas seulement
    adjacents). -/
lemma kernelChain_le_antitone {K : Finset S} {step : S → Finset S} {n m : ℕ}
    (h : n ≤ m) : kernelChain K step m ⊆ kernelChain K step n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  clear h
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    have heq : n + (k + 1) = (n + k) + 1 := by omega
    rw [heq]
    exact (kernelChain_antitone K step (n + k)).trans ih

/-! ### 3. Stabilisation finie (pigeonhole) -/

/-- Dans un cadre fini, la chaîne descendante stabilise en au plus
    `Fintype.card S` étapes. Même schéma de preuve que
    `bw_gfp_finite_stabilization` (LatticeClearing.lean), avec `K` en point
    de départ au lieu de `univ` (K est aussi borné par `Fintype.card S`, ce
    qui suffit — pas besoin que K soit tout l'espace). -/
theorem kernelChain_finite_stabilization (K : Finset S) (step : S → Finset S) :
    ∃ n, n ≤ Fintype.card S ∧ kernelChain K step n = kernelChain K step (n + 1) := by
  by_contra h
  push Not at h
  have h_strict : ∀ n, n ≤ Fintype.card S →
      kernelChain K step (n + 1) ⊂ kernelChain K step n := by
    intro n hn
    have h_sub := kernelChain_antitone K step n
    have h_ne : kernelChain K step (n + 1) ≠ kernelChain K step n := (h n hn).symm
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨h_sub, h_ne⟩
  have h_card_strict : ∀ n, n ≤ Fintype.card S →
      (kernelChain K step (n + 1)).card < (kernelChain K step n).card :=
    fun n hn => Finset.card_lt_card (h_strict n hn)
  have h_ind : ∀ m, m ≤ Fintype.card S →
      (kernelChain K step m).card ≤ Fintype.card S - m := by
    intro m hm
    induction m with
    | zero => simpa using Finset.card_le_univ K
    | succ m ih =>
      have hm' : m ≤ Fintype.card S := by omega
      have h_lt := h_card_strict m hm'
      have h_ih := ih hm'
      omega
  have h_card_N : (kernelChain K step (Fintype.card S)).card = 0 := by
    have := h_ind (Fintype.card S) (le_refl _)
    omega
  have h_empty : kernelChain K step (Fintype.card S) = ∅ :=
    Finset.card_eq_zero.mp h_card_N
  have h_strict_N : kernelChain K step (Fintype.card S + 1) ⊂ kernelChain K step (Fintype.card S) :=
    h_strict (Fintype.card S) (le_refl _)
  rw [h_empty] at h_strict_N
  have h_sub_empty : kernelChain K step (Fintype.card S + 1) ⊆ ∅ :=
    (Finset.ssubset_iff_subset_ne.mp h_strict_N).1
  have h_eq_empty : kernelChain K step (Fintype.card S + 1) = ∅ :=
    Finset.subset_empty.mp h_sub_empty
  have h_ne_empty : kernelChain K step (Fintype.card S + 1) ≠ ∅ :=
    (Finset.ssubset_iff_subset_ne.mp h_strict_N).2
  contradiction

/-- Si la chaîne stabilise à l'étape `n`, l'état atteint est un point fixe
    de `preK K step`. -/
theorem kernelChain_fixed_point (K : Finset S) (step : S → Finset S) (n : ℕ)
    (h_stab : kernelChain K step n = kernelChain K step (n + 1)) :
    preK K step (kernelChain K step n) = kernelChain K step n := by
  have h_unfold : kernelChain K step (n + 1) = preK K step (kernelChain K step n) := rfl
  rw [h_unfold] at h_stab
  exact h_stab.symm

/-- Une fois stabilisée, la chaîne reste constante à tous les indices
    ultérieurs. -/
lemma kernelChain_stable_forall_ge (K : Finset S) (step : S → Finset S) (n0 : ℕ)
    (h : kernelChain K step n0 = kernelChain K step (n0 + 1)) :
    ∀ k, kernelChain K step (n0 + k) = kernelChain K step n0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have heq : n0 + (k + 1) = (n0 + k) + 1 := by omega
    rw [heq]
    show preK K step (kernelChain K step (n0 + k)) = kernelChain K step n0
    rw [ih]
    exact kernelChain_fixed_point K step n0 h

/-- La chaîne est déjà stabilisée à l'indice `Fintype.card S` précisément
    (pas seulement « il existe un indice ≤ card S où elle stabilise »). -/
theorem kernelChain_stabilized_at_card (K : Finset S) (step : S → Finset S) :
    kernelChain K step (Fintype.card S) = kernelChain K step (Fintype.card S + 1) := by
  obtain ⟨n0, hn0, heq⟩ := kernelChain_finite_stabilization K step
  obtain ⟨k, hk⟩ := Nat.le.dest hn0
  have h1 : kernelChain K step (Fintype.card S) = kernelChain K step n0 := by
    rw [← hk]; exact kernelChain_stable_forall_ge K step n0 heq k
  have h2 : kernelChain K step (Fintype.card S + 1) = kernelChain K step n0 := by
    have heq' : Fintype.card S + 1 = n0 + (k + 1) := by omega
    rw [heq']
    exact kernelChain_stable_forall_ge K step n0 heq (k + 1)
  rw [h1, h2]

/-! ### 4. Le noyau de viabilité comme plus grand point fixe -/

/-- Le noyau de viabilité : l'état stabilisé de la chaîne descendante à
    l'indice `Fintype.card S`. -/
def viabilityKernel (K : Finset S) (step : S → Finset S) : Finset S :=
  kernelChain K step (Fintype.card S)

/-- **THÉORÈME (Knaster–Tarski, cadre fini) : le noyau de viabilité est le
    PLUS GRAND point fixe de `preK K step`.** Mêmes ingrédients que
    `KnasterTarski_gfp_exists` (LatticeClearing.lean) : point fixe par
    stabilisation, maximalité par récurrence sur la monotonie. -/
theorem viabilityKernel_is_gfp (K : Finset S) (step : S → Finset S) :
    preK K step (viabilityKernel K step) = viabilityKernel K step ∧
      ∀ T : Finset S, preK K step T = T → T ⊆ viabilityKernel K step := by
  refine ⟨kernelChain_fixed_point K step (Fintype.card S)
    (kernelChain_stabilized_at_card K step), ?_⟩
  intro T hT
  have h_sub_n : ∀ m, T ⊆ kernelChain K step m := by
    intro m
    induction m with
    | zero =>
      show T ⊆ K
      rw [← hT]; exact preK_subset_K K step T
    | succ m ih =>
      have h_ΦT_sub : preK K step T ⊆ preK K step (kernelChain K step m) := preK_mono ih
      rw [hT] at h_ΦT_sub
      exact h_ΦT_sub
  exact h_sub_n (Fintype.card S)

/-! ### 5. Viabilité finitaire et coïncidence avec le noyau -/

/-- `viableN K step x n` : il existe un chemin de longueur `n` issu de `x`,
    restant dans `K` à chaque étape (y compris `x` lui-même). -/
def viableN (K : Finset S) (step : S → Finset S) (x : S) : ℕ → Prop
  | 0 => x ∈ K
  | n + 1 => x ∈ K ∧ ∃ y ∈ step x, viableN K step y n

/-- Pont structurel : appartenir à la chaîne à l'étape `n` équivaut à être
    viable sur un horizon de `n` pas. -/
lemma kernelChain_eq_viableN (K : Finset S) (step : S → Finset S) :
    ∀ n x, x ∈ kernelChain K step n ↔ viableN K step x n := by
  intro n
  induction n with
  | zero =>
    intro x
    exact Iff.rfl
  | succ n ih =>
    intro x
    show x ∈ preK K step (kernelChain K step n) ↔
      (x ∈ K ∧ ∃ y ∈ step x, viableN K step y n)
    rw [preK, Finset.mem_filter]
    constructor
    · rintro ⟨hxK, y, hy⟩
      rw [Finset.mem_inter] at hy
      exact ⟨hxK, y, hy.1, (ih y).mp hy.2⟩
    · rintro ⟨hxK, y, hyStep, hyViable⟩
      exact ⟨hxK, y, Finset.mem_inter.mpr ⟨hyStep, (ih y).mpr hyViable⟩⟩

/-- Membre du noyau ⟹ membre de la chaîne à TOUT indice (pas seulement
    `Fintype.card S`) : en dessous, par antitonie ; au-dessus, la chaîne
    est déjà stable. -/
lemma mem_viabilityKernel_imp_mem_kernelChain (K : Finset S) (step : S → Finset S)
    (x : S) (hx : x ∈ viabilityKernel K step) (m : ℕ) :
    x ∈ kernelChain K step m := by
  by_cases hm : m ≤ Fintype.card S
  · exact kernelChain_le_antitone hm hx
  · have hm' : Fintype.card S ≤ m := by omega
    obtain ⟨k, hk⟩ := Nat.le.dest hm'
    have hstab := kernelChain_stabilized_at_card K step
    have heq := kernelChain_stable_forall_ge K step (Fintype.card S) hstab k
    have hm_eq : kernelChain K step m = kernelChain K step (Fintype.card S) := by
      rw [← hk]; exact heq
    rw [hm_eq]; exact hx

/-- **THÉORÈME CIBLE.** Le noyau de viabilité (plus grand point fixe de
    l'opérateur de pré-image admissible, `viabilityKernel_is_gfp`) coïncide
    exactement avec l'ensemble des états viables à TOUT horizon fini `n`. -/
theorem viability_kernel_eq_gfp (K : Finset S) (step : S → Finset S) (x : S) :
    x ∈ viabilityKernel K step ↔ ∀ n, viableN K step x n := by
  constructor
  · intro hx n
    exact (kernelChain_eq_viableN K step n x).mp
      (mem_viabilityKernel_imp_mem_kernelChain K step x hx n)
  · intro h
    exact (kernelChain_eq_viableN K step (Fintype.card S) x).mpr (h (Fintype.card S))

end ViabilityKernel
