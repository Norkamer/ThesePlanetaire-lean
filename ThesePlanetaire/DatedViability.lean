/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/DatedViability.lean
  Viabilité datée, à horizon fini (2026-10-14, SP-3, D-45) — papier 11 : le théorème 2 à horizon
  fini, avec des plafonds et des sources qui dépendent de la date. Développé d'abord en
  `DatedViability_scratch.lean` (workflow du dépôt). Trace : `cache/sp3_viabilite_datee_2026-10-14/`.

  Module neuf (D-30) : aucun module existant n'est modifié. Il importe `GuardField` (papier 11).

  Portée.
  - §1, la récurrence datée générale (le tube cible de Bertsekas et Rhodes, 1971) : états,
    actions et chocs quelconques, contraintes `K t`, actions admissibles `Adm t x`, chocs
    `W t x a`, dynamique `F t x a z`. Un état est dans `V n t` ssi une politique en boucle fermée
    tient `K` aux dates `t, …, t + n` contre toute suite de chocs (`mem_V_iff`) ; une politique
    qui tient ne choisit que des actions viables (`holds_action_mem`) ; toute famille qui tient
    d'une date à la suivante est dans la récurrence (`tube_subset_V`). Observer le choc avant
    d'agir élargit la récurrence (`V_subset_Vae`), strictement en général (`ae_strict`). Cas
    stationnaire : tout ensemble robuste contrôlé-invariant est dans la récurrence
    (`ci_subset_V`) ; sur un espace fini, le noyau `⋂ n, V n 0` est robuste contrôlé-invariant,
    donc le plus grand (`kernel_ci`, `ci_subset_kernel`).
  - §2, l'instance du papier 11 : états `(L, J)` du théorème 2, plafonds `C t` et tailles
    `e t u` datés, fin de période `τ`. (d)(i) toute famille tenable jusqu'à `T` est contenue dans
    la réserve datée, calculée à rebours (`tenableD_subset_res`) ; (d)(ii) si `τ` est croissante
    et les sources positives, la réserve datée est tenable (`res_tenableD`, `mem_tenableD_iff`) ;
    (d)(iii) en mémoire `stock`, c'est un budget cumulé à chaque date (`resD_stock_iff`) ; (d)(iv)
    à données constantes, `L + M + n · max (M − ρ) 0 ≤ C` (`resD_const_iff`) ; (d)(v) sur un corps
    archimédien, tenable à tout horizon fini ssi `L + M ≤ C` et `M ≤ ρ`, ssi dans un ensemble
    tenable du théorème 2(b) (`forall_horizon_iff`, `forall_horizon_iff_tenable`).
  - §3, témoins dans ℚ : `m3a_two_periods` (le plafond 2 tient deux périodes contre une source
    de 1, pas trois) ; `effective_date` (un plafond abaissé à la seconde date : la règle en
    vigueur à la première admet une charge que plus rien ne ramène sous le nouveau plafond en
    mémoire `stock` ; la réserve datée, en vigueur dès la première date, ne l'admet pas).
  - §4, préparation de SP-7, non exportée : deux systèmes séparés ont pour récurrence le produit
    des récurrences (`V_prod`) ; tenir deux contraintes ensemble demande au moins chacune
    (`V_inter_subset`), et le témoin couplé `joint_strict` montre que cela ne suffit pas.
  Nature : §1 et (d)(i)-(ii) sont des instances de la récurrence du tube cible ; les formes
  closes (d)(iii)-(v) et les témoins sont élémentaires.
  Hors : plusieurs plafonds datés (`JointReserve`) ; les échéances (`DeadlineGuard`) sous des
  plafonds datés ; un horizon non borné à plafonds variables ; la variante « choc observé
  d'abord » en politique (seule la récurrence est énoncée).
-/
import ThesePlanetaire.GuardField

namespace DatedViability

open FeedbackClass (Memory)
open GuardField (tickOpF rhoF)

/-! ## §1. La récurrence datée générale -/

section General

variable {S A Z : Type*}
variable (K : ℕ → Set S) (Adm : ℕ → S → Set A) (W : ℕ → S → A → Set Z)
  (F : ℕ → S → A → Z → S) (W' : ℕ → S → Set Z)

/-- Récurrence datée : `V n t` est l'ensemble des états d'où l'on peut tenir `K` aux dates
`t, …, t + n`, une action admissible étant choisie avant le choc. -/
def V : ℕ → ℕ → Set S
  | 0, t => K t
  | n + 1, t => {x | x ∈ K t ∧ ∃ a ∈ Adm t x, ∀ z ∈ W t x a, F t x a z ∈ V n (t + 1)}

/-- Variante où le choc est observé avant l'action. -/
def Vae : ℕ → ℕ → Set S
  | 0, t => K t
  | n + 1, t => {x | x ∈ K t ∧ ∀ z ∈ W' t x, ∃ a ∈ Adm t x, F t x a z ∈ Vae n (t + 1)}

/-- Trajectoire depuis `x` à la date `t`, sous la politique `π` et les chocs `ζ`. -/
def traj (π : ℕ → S → A) (ζ : ℕ → Z) (t : ℕ) (x : S) : ℕ → S
  | 0 => x
  | k + 1 => F (t + k) (traj π ζ t x k) (π (t + k) (traj π ζ t x k)) (ζ (t + k))

/-- La politique en boucle fermée `π` tient depuis `x` à la date `t` pendant `n` pas : pour toute
suite de chocs, admissible jusqu'au pas `k`, l'état du pas `k` est dans `K` et, avant le dernier
pas, l'action choisie est admissible. -/
def Holds (π : ℕ → S → A) (n t : ℕ) (x : S) : Prop :=
  ∀ ζ : ℕ → Z, ∀ k ≤ n,
    (∀ j < k, ζ (t + j) ∈ W (t + j) (traj F π ζ t x j) (π (t + j) (traj F π ζ t x j))) →
      traj F π ζ t x k ∈ K (t + k) ∧
        (k < n → π (t + k) (traj F π ζ t x k) ∈ Adm (t + k) (traj F π ζ t x k))

variable {K Adm W F W'}

@[simp] theorem traj_zero (π : ℕ → S → A) (ζ : ℕ → Z) (t : ℕ) (x : S) :
    traj F π ζ t x 0 = x := rfl

theorem traj_succ (π : ℕ → S → A) (ζ : ℕ → Z) (t : ℕ) (x : S) (k : ℕ) :
    traj F π ζ t x (k + 1) =
      F (t + k) (traj F π ζ t x k) (π (t + k) (traj F π ζ t x k)) (ζ (t + k)) := rfl

theorem traj_shift (π : ℕ → S → A) (ζ : ℕ → Z) (t : ℕ) (x : S) (k : ℕ) :
    traj F π ζ t x (k + 1) = traj F π ζ (t + 1) (F t x (π t x) (ζ t)) k := by
  induction k with
  | zero => simp [traj_succ]
  | succ k ih =>
    rw [traj_succ, ih, traj_succ, show t + (k + 1) = t + 1 + k by omega]

theorem traj_congr {π : ℕ → S → A} {ζ ζ' : ℕ → Z} {t : ℕ} {x : S}
    (h : ∀ s, t ≤ s → ζ s = ζ' s) : ∀ k, traj F π ζ t x k = traj F π ζ' t x k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [traj_succ, traj_succ, ih, h (t + k) (by omega)]

theorem V_subset_K {n t : ℕ} : V K Adm W F n t ⊆ K t := by
  cases n with
  | zero => exact fun _ h => h
  | succ n => exact fun _ h => h.1

/-- Un horizon plus long demande plus. -/
theorem V_succ_subset : ∀ n t, V K Adm W F (n + 1) t ⊆ V K Adm W F n t
  | 0, _ => fun _ h => h.1
  | n + 1, t => fun _ h => ⟨h.1, by
      obtain ⟨a, ha, hz⟩ := h.2
      exact ⟨a, ha, fun z hz' => V_succ_subset n (t + 1) (hz z hz')⟩⟩

theorem V_antitone (t : ℕ) : Antitone fun n => V K Adm W F n t :=
  antitone_nat_of_succ_le fun n => V_succ_subset n t

/-- Sous une politique qui tient `n + 1` pas, chaque successeur tient `n` pas. -/
theorem holds_succ {π : ℕ → S → A} {n t : ℕ} {x : S} (h : Holds K Adm W F π (n + 1) t x)
    {z : Z} (hz : z ∈ W t x (π t x)) : Holds K Adm W F π n (t + 1) (F t x (π t x) z) := by
  intro ζ k hk hpre
  let ζ' : ℕ → Z := fun s => if s = t then z else ζ s
  have hagree : ∀ s, t + 1 ≤ s → ζ' s = ζ s := fun s hs => if_neg (by omega)
  have hζt : ζ' t = z := if_pos rfl
  have hshift : ∀ j, traj F π ζ' t x (j + 1) = traj F π ζ (t + 1) (F t x (π t x) z) j := by
    intro j
    rw [traj_shift, hζt, traj_congr hagree]
  have := h ζ' (k + 1) (by omega) ?_
  · rw [hshift, show t + (k + 1) = t + 1 + k by omega] at this
    exact ⟨this.1, fun hk' => this.2 (by omega)⟩
  · intro j hj
    cases j with
    | zero => simpa [hζt] using hz
    | succ j =>
      rw [hshift, show t + (j + 1) = t + 1 + j by omega, hagree _ (by omega)]
      exact hpre j (by omega)

/-- Une politique qui tient part d'un état de la récurrence. -/
theorem V_of_holds [Nonempty Z] {π : ℕ → S → A} :
    ∀ {n t : ℕ} {x : S}, Holds K Adm W F π n t x → x ∈ V K Adm W F n t
  | 0, t, x, h => by
    have := (h (Classical.arbitrary _) 0 le_rfl (fun j hj => absurd hj (Nat.not_lt_zero _))).1
    show x ∈ K t
    simpa using this
  | n + 1, t, x, h => by
    have h0 := h (Classical.arbitrary _) 0 (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
    simp only [traj_zero, Nat.add_zero] at h0
    exact ⟨h0.1, π t x, h0.2 (by omega), fun z hz => V_of_holds (holds_succ h hz)⟩

/-- Depuis un état de la récurrence, une politique qui choisit une action viable tient. -/
theorem holds_of_V [Nonempty A] {n t : ℕ} {x : S} (hx : x ∈ V K Adm W F n t) :
    ∃ π, Holds K Adm W F π n t x := by
  classical
  let H := t + n
  let π : ℕ → S → A := fun s y =>
    if h : ∃ a ∈ Adm s y, ∀ z ∈ W s y a, F s y a z ∈ V K Adm W F (H - (s + 1)) (s + 1) then
      h.choose
    else Classical.arbitrary A
  have hπdef : ∀ s y, π s y = if h : ∃ a ∈ Adm s y, ∀ z ∈ W s y a,
      F s y a z ∈ V K Adm W F (H - (s + 1)) (s + 1) then h.choose else Classical.arbitrary A :=
    fun _ _ => rfl
  have hπ : ∀ s y, s < H → y ∈ V K Adm W F (H - s) s →
      π s y ∈ Adm s y ∧
        ∀ z ∈ W s y (π s y), F s y (π s y) z ∈ V K Adm W F (H - (s + 1)) (s + 1) := by
    intro s y hs hy
    rw [show H - s = (H - (s + 1)) + 1 by omega] at hy
    have h : ∃ a ∈ Adm s y, ∀ z ∈ W s y a, F s y a z ∈ V K Adm W F (H - (s + 1)) (s + 1) :=
      hy.2
    rw [hπdef s y, dif_pos h]
    exact h.choose_spec
  refine ⟨π, fun ζ k hk hpre => ?_⟩
  have key : ∀ k ≤ n,
      (∀ j < k, ζ (t + j) ∈ W (t + j) (traj F π ζ t x j) (π (t + j) (traj F π ζ t x j))) →
        traj F π ζ t x k ∈ V K Adm W F (H - (t + k)) (t + k) := by
    intro k
    induction k with
    | zero => intro _ _; simpa [H] using hx
    | succ k ih =>
      intro hk hpre
      have hprev := ih (by omega) (fun j hj => hpre j (by omega))
      have := (hπ (t + k) _ (by omega) hprev).2 _ (hpre k (by omega))
      rw [traj_succ, show t + (k + 1) = t + k + 1 by omega]
      exact this
  have hk' := key k hk hpre
  exact ⟨V_subset_K hk', fun hlt => (hπ (t + k) _ (by omega) hk').1⟩

/-- ★ **Récurrence datée** (tube cible) : un état est dans `V n t` si et seulement si une
politique en boucle fermée tient `K` aux dates `t, …, t + n` contre toute suite de chocs. -/
theorem mem_V_iff [Nonempty A] [Nonempty Z] {n t : ℕ} {x : S} :
    x ∈ V K Adm W F n t ↔ ∃ π, Holds K Adm W F π n t x :=
  ⟨holds_of_V, fun ⟨_, h⟩ => V_of_holds h⟩

/-- ★ **La garde datée est la plus permissive** : une politique qui tient ne choisit que des
actions viables, celles qui gardent chaque successeur dans la récurrence. -/
theorem holds_action_mem [Nonempty Z] {π : ℕ → S → A} {n t : ℕ} {x : S}
    (h : Holds K Adm W F π (n + 1) t x) :
    π t x ∈ Adm t x ∧ ∀ z ∈ W t x (π t x), F t x (π t x) z ∈ V K Adm W F n (t + 1) := by
  have h0 := h (Classical.arbitrary _) 0 (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
  simp only [traj_zero, Nat.add_zero] at h0
  exact ⟨h0.2 (by omega), fun z hz => V_of_holds (holds_succ h hz)⟩

/-- ★ Observer le choc avant d'agir ne peut qu'élargir la récurrence. -/
theorem V_subset_Vae : ∀ n t, V K Adm (fun t x _ => W' t x) F n t ⊆ Vae K Adm F W' n t
  | 0, _ => fun _ h => h
  | n + 1, t => fun _ h => ⟨h.1, by
      obtain ⟨a, ha, hz⟩ := h.2
      exact fun z hz' => ⟨a, ha, V_subset_Vae n (t + 1) (hz z hz')⟩⟩

/-- ★ **Maximalité** : toute famille d'ensembles qui tient d'une date à la suivante est contenue
dans la récurrence, à tout horizon. -/
theorem tube_subset_V {X : ℕ → Set S} (hK : ∀ t, X t ⊆ K t)
    (hX : ∀ t, ∀ x ∈ X t, ∃ a ∈ Adm t x, ∀ z ∈ W t x a, F t x a z ∈ X (t + 1)) :
    ∀ n t, X t ⊆ V K Adm W F n t
  | 0, t => hK t
  | n + 1, t => fun x hx => ⟨hK t hx, by
      obtain ⟨a, ha, hz⟩ := hX t x hx
      exact ⟨a, ha, fun z hz' => tube_subset_V hK hX n (t + 1) (hz z hz')⟩⟩

end General

/-- ★ Témoin : quand seule l'action égale au choc tient, choisir avant le choc ne tient pas,
choisir après tient. -/
theorem ae_strict :
    V (fun t => if t = 0 then Set.univ else {true}) (fun _ _ => Set.univ)
        (fun _ _ _ => Set.univ) (fun _ _ (a z : Bool) => decide (a = z)) 1 0 = ∅ ∧
      Vae (fun t => if t = 0 then Set.univ else {true}) (fun _ _ => Set.univ)
        (fun _ _ (a z : Bool) => decide (a = z)) (fun _ _ => Set.univ) 1 0 = Set.univ := by
  constructor
  · ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, a, -, h⟩
    have := h (!a) (Set.mem_univ _)
    cases a <;> simp [V] at this
  · ext x
    simp only [Set.mem_univ, iff_true]
    refine ⟨Set.mem_univ _, fun z _ => ⟨z, Set.mem_univ _, ?_⟩⟩
    show decide (z = z) ∈ (if 0 + 1 = 0 then Set.univ else {true})
    simp

/-! ### Cas stationnaire : le noyau -/

section Stationary

variable {S A Z : Type*} (K₀ : Set S) (Adm₀ : S → Set A) (W₀ : S → A → Set Z)
  (F₀ : S → A → Z → S)

/-- Ensemble robuste contrôlé-invariant : dans `K₀`, et une action admissible y garde l'état
contre tout choc. -/
def RobustCI (X : Set S) : Prop :=
  X ⊆ K₀ ∧ ∀ x ∈ X, ∃ a ∈ Adm₀ x, ∀ z ∈ W₀ x a, F₀ x a z ∈ X

/-- Le noyau : les états qui sont dans la récurrence à tout horizon. -/
def kernel : Set S :=
  ⋂ n, V (fun _ => K₀) (fun _ => Adm₀) (fun _ => W₀) (fun _ => F₀) n 0

variable {K₀ Adm₀ W₀ F₀}

theorem V_stat (n t s : ℕ) :
    V (fun _ => K₀) (fun _ => Adm₀) (fun _ => W₀) (fun _ => F₀) n t =
      V (fun _ => K₀) (fun _ => Adm₀) (fun _ => W₀) (fun _ => F₀) n s := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [V, Set.mem_setOf_eq, ih (t + 1) (s + 1)]

/-- ★ Tout ensemble robuste contrôlé-invariant est dans la récurrence à tout horizon, donc dans
le noyau. -/
theorem ci_subset_V {X : Set S} (hX : RobustCI K₀ Adm₀ W₀ F₀ X) (n t : ℕ) :
    X ⊆ V (fun _ => K₀) (fun _ => Adm₀) (fun _ => W₀) (fun _ => F₀) n t :=
  tube_subset_V (X := fun _ => X) (fun _ => hX.1) (fun _ => hX.2) n t

theorem ci_subset_kernel {X : Set S} (hX : RobustCI K₀ Adm₀ W₀ F₀ X) :
    X ⊆ kernel K₀ Adm₀ W₀ F₀ :=
  Set.subset_iInter fun n => ci_subset_V hX n 0

/-- ★ **Noyau sur un espace fini** : la récurrence se stabilise ; le noyau est robuste
contrôlé-invariant, donc le plus grand. -/
theorem kernel_ci [Finite S] : RobustCI K₀ Adm₀ W₀ F₀ (kernel K₀ Adm₀ W₀ F₀) := by
  set Vs : ℕ → Set S := fun n => V (fun _ => K₀) (fun _ => Adm₀) (fun _ => W₀) (fun _ => F₀) n 0
    with hVs
  have hanti : Antitone Vs := V_antitone 0
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    (Set.range fun n => (Vs n).ncard) ⟨_, 0, rfl⟩
  have hstab : ∀ m, N ≤ m → Vs m = Vs N := fun m hm =>
    Set.eq_of_subset_of_ncard_le (hanti hm)
      (not_lt.mp (hmin _ ⟨m, rfl⟩)) (Set.toFinite _)
  have hker : kernel K₀ Adm₀ W₀ F₀ = Vs N := by
    apply Set.Subset.antisymm (Set.iInter_subset _ N)
    refine Set.subset_iInter fun n => ?_
    rcases le_total n N with h | h
    · exact hanti h
    · exact (hstab n h).ge
  rw [hker]
  refine ⟨V_subset_K, fun x hx => ?_⟩
  have hx' : x ∈ Vs (N + 1) := by rw [hstab _ (by omega)]; exact hx
  obtain ⟨-, a, ha, hz⟩ := hx'
  exact ⟨a, ha, fun z hz' => by
    have := hz z hz'
    rw [V_stat N 1 0] at this
    exact this⟩

end Stationary

/-! ## §2. Instance du papier 11 : la réserve datée -/

section Dated

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Masse des sources de la période `t`. -/
def periodMass (e : ℕ → U → 𝕜) (t : ℕ) : 𝕜 := ∑ u, e t u

/-- Pointe de la période : la charge plus les sources encore possibles dans la période. -/
def peak (e : ℕ → U → 𝕜) (t : ℕ) (q : 𝕜 × Finset U) : 𝕜 := q.1 + ∑ u ∈ q.2ᶜ, e t u

/-- Tenabilité d'une pointe `p` à la date `t`, avec `n` fins de période restantes. -/
def resP (τ : 𝕜 → 𝕜) (e : ℕ → U → 𝕜) (C : ℕ → 𝕜) : ℕ → ℕ → 𝕜 → Prop
  | 0, t, p => p ≤ C t
  | n + 1, t, p => p ≤ C t ∧ resP τ e C n (t + 1) (τ p + periodMass e (t + 1))

/-- Réserve datée : `resD τ e C n t q`, avec `n` fins de période restantes (horizon `t + n`). -/
def resD (τ : 𝕜 → 𝕜) (e : ℕ → U → 𝕜) (C : ℕ → 𝕜) (n t : ℕ) (q : 𝕜 × Finset U) : Prop :=
  resP τ e C n t (peak e t q)

/-- Famille tenable jusqu'à l'horizon `T` : plafond `C t` aux dates `t ≤ T`, fermée par chaque
source non encore survenue dans la période (taille `e t u`), et par la fin de période `τ` avant
`T`. -/
def TenableD (τ : 𝕜 → 𝕜) (e : ℕ → U → 𝕜) (C : ℕ → 𝕜) (T : ℕ)
    (X : ℕ → 𝕜 × Finset U → Prop) : Prop :=
  (∀ t L J, t ≤ T → X t (L, J) → L ≤ C t) ∧
    (∀ t L J u, t ≤ T → X t (L, J) → u ∉ J → X t (L + e t u, insert u J)) ∧
    ∀ t L J, t < T → X t (L, J) → X (t + 1) (τ L, ∅)

variable {τ : 𝕜 → 𝕜} {e : ℕ → U → 𝕜} {C : ℕ → 𝕜} {T : ℕ} {X : ℕ → 𝕜 × Finset U → Prop}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem peak_empty (t : ℕ) (L : 𝕜) : peak e t (L, ∅) = L + periodMass e t := by
  simp [peak, periodMass]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem peak_insert {t : ℕ} {L : 𝕜} {J : Finset U} {u : U} (hu : u ∉ J) :
    peak e t (L + e t u, insert u J) = peak e t (L, J) := by
  show L + e t u + ∑ x ∈ (insert u J)ᶜ, e t x = L + ∑ x ∈ Jᶜ, e t x
  rw [Finset.compl_insert, add_assoc, Finset.add_sum_erase Jᶜ (e t) (Finset.mem_compl.mpr hu)]

theorem le_peak (he : ∀ t u, 0 ≤ e t u) (t : ℕ) (q : 𝕜 × Finset U) : q.1 ≤ peak e t q := by
  have := Finset.sum_nonneg fun u (_ : u ∈ q.2ᶜ) => he t u
  simp only [peak]
  linarith

omit [IsStrictOrderedRing 𝕜] [DecidableEq U] in
theorem resP_head {n t : ℕ} {p : 𝕜} (h : resP τ e C n t p) : p ≤ C t := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

omit [DecidableEq U] in
theorem resP_anti (hτ : Monotone τ) :
    ∀ n t {p p' : 𝕜}, p' ≤ p → resP τ e C n t p → resP τ e C n t p'
  | 0, _, _, _, hp, h => le_trans hp h
  | n + 1, t, _, _, hp, h => ⟨le_trans hp h.1, resP_anti hτ n (t + 1)
      (add_le_add (hτ hp) le_rfl) h.2⟩

omit [IsStrictOrderedRing 𝕜] [Fintype U] in
/-- Tirer d'un coup des sources encore disponibles. -/
theorem tenableD_draw (hX : TenableD τ e C T X) {t : ℕ} (ht : t ≤ T) {L : 𝕜} {J : Finset U}
    (h : X t (L, J)) : ∀ K : Finset U, Disjoint K J → X t (L + ∑ u ∈ K, e t u, J ∪ K) := by
  intro K
  induction K using Finset.induction_on with
  | empty => intro _; simpa using h
  | insert u K hu ih =>
    intro hd
    have hd' : Disjoint K J := Finset.disjoint_of_subset_left (Finset.subset_insert u K) hd
    have huJ : u ∉ J ∪ K := by
      simp only [Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_left.mp hd (Finset.mem_insert_self u K), hu⟩
    have := hX.2.1 _ _ _ u ht (ih hd') huJ
    rw [Finset.sum_insert hu, Finset.union_insert,
      show L + (e t u + ∑ x ∈ K, e t x) = L + ∑ x ∈ K, e t x + e t u by ring]
    exact this

omit [IsStrictOrderedRing 𝕜] in
theorem tenableD_subset_res_aux (hX : TenableD τ e C T X) :
    ∀ n t (q : 𝕜 × Finset U), t + n = T → X t q → resD τ e C n t q := by
  intro n
  induction n with
  | zero =>
    rintro t ⟨L, J⟩ ht h
    have := hX.1 _ _ _ (by omega) (tenableD_draw hX (by omega) h Jᶜ disjoint_compl_left)
    simpa [resD, resP, peak] using this
  | succ n ih =>
    rintro t ⟨L, J⟩ ht h
    have hdraw := tenableD_draw hX (by omega) h Jᶜ disjoint_compl_left
    rw [Finset.union_compl] at hdraw
    refine ⟨hX.1 _ _ _ (by omega) hdraw, ?_⟩
    have := ih (t + 1) _ (by omega) (hX.2.2 _ _ _ (by omega) hdraw)
    simpa [resD, peak_empty] using this

omit [IsStrictOrderedRing 𝕜] in
/-- ★ (d)(i) Toute famille tenable jusqu'à `T` est contenue dans la réserve datée. -/
theorem tenableD_subset_res (hX : TenableD τ e C T X) {t : ℕ} (ht : t ≤ T)
    (q : 𝕜 × Finset U) (h : X t q) : resD τ e C (T - t) t q :=
  tenableD_subset_res_aux hX _ _ q (by omega) h

/-- ★ (d)(ii) Si la fin de période est croissante et les sources positives, la réserve datée est
tenable jusqu'à `T`. -/
theorem res_tenableD (hτ : Monotone τ) (he : ∀ t u, 0 ≤ e t u) :
    TenableD τ e C T (fun t q => t ≤ T ∧ resD τ e C (T - t) t q) := by
  refine ⟨fun t L J _ h => ?_, fun t L J u _ h hu => ?_, fun t L J ht h => ?_⟩
  · exact le_trans (le_peak he t (L, J)) (resP_head h.2)
  · refine ⟨h.1, ?_⟩
    show resP τ e C (T - t) t (peak e t (L + e t u, insert u J))
    rw [peak_insert hu]
    exact h.2
  · refine ⟨ht, ?_⟩
    have h2 := h.2
    show resP τ e C (T - (t + 1)) (t + 1) (peak e (t + 1) (τ L, ∅))
    rw [peak_empty]
    unfold resD at h2
    rw [show T - t = T - (t + 1) + 1 by omega] at h2
    exact resP_anti hτ _ _ (add_le_add (hτ (le_peak he t (L, J))) le_rfl) h2.2

/-- ★ (d)(ii) Un état est dans une famille tenable jusqu'à `T` si et seulement s'il est dans la
réserve datée. -/
theorem mem_tenableD_iff (hτ : Monotone τ) (he : ∀ t u, 0 ≤ e t u) {t : ℕ} (ht : t ≤ T)
    (q : 𝕜 × Finset U) : (∃ X, TenableD τ e C T X ∧ X t q) ↔ resD τ e C (T - t) t q :=
  ⟨fun ⟨_, hX, h⟩ => tenableD_subset_res hX ht q h,
    fun h => ⟨_, res_tenableD hτ he, ht, h⟩⟩

/-- La fin de période de chacune des trois mémoires est croissante. -/
theorem tickOpF_monotone (mem : Memory) (r : 𝕜) : Monotone (tickOpF mem r) := by
  intro a b hab
  cases mem
  · exact hab
  · exact max_le_max (by linarith) le_rfl
  · exact le_rfl

omit [DecidableEq U] in
/-- ★ (d)(iii) **Budget à chaque date** (mémoire `stock`) : depuis la charge `L` au début de la
période `t`, la réserve datée à `n` fins de période demande que la charge plus toutes les sources
possibles jusqu'à chaque date tienne sous le plafond de cette date. -/
theorem resP_stock (r : 𝕜) : ∀ n t (p : 𝕜),
    resP (tickOpF .stock r) e C n t p ↔
      ∀ k ≤ n, p + ∑ i ∈ Finset.range k, periodMass e (t + 1 + i) ≤ C (t + k)
  | 0, t, p => by
    constructor
    · intro h k hk
      obtain rfl : k = 0 := by omega
      simpa using h
    · intro h
      simpa using h 0 le_rfl
  | n + 1, t, p => by
    have hs : ∀ k, ∑ i ∈ Finset.range k, periodMass e (t + 1 + (i + 1)) =
        ∑ i ∈ Finset.range k, periodMass e (t + 1 + 1 + i) := fun k =>
      Finset.sum_congr rfl fun i _ => by rw [show t + 1 + (i + 1) = t + 1 + 1 + i by omega]
    show (p ≤ C t ∧ resP (tickOpF .stock r) e C n (t + 1) (p + periodMass e (t + 1))) ↔ _
    rw [resP_stock r n (t + 1)]
    constructor
    · rintro ⟨h0, h⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k =>
        have := h k (by omega)
        rw [Finset.sum_range_succ', hs, Nat.add_zero, show t + (k + 1) = t + 1 + k by omega]
        linarith
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      have := h (k + 1) (by omega)
      rw [Finset.sum_range_succ', hs, Nat.add_zero, show t + (k + 1) = t + 1 + k by omega] at this
      linarith

/-- ★ (d)(iii) en charge de début de période. -/
theorem resD_stock_iff (r : 𝕜) (n t : ℕ) (L : 𝕜) :
    resD (tickOpF .stock r) e C n t (L, ∅) ↔
      ∀ k ≤ n, L + ∑ i ∈ Finset.range (k + 1), periodMass e (t + i) ≤ C (t + k) := by
  have hs : ∀ k, ∑ i ∈ Finset.range (k + 1), periodMass e (t + i) =
      periodMass e t + ∑ i ∈ Finset.range k, periodMass e (t + 1 + i) := by
    intro k
    rw [Finset.sum_range_succ', add_comm, Nat.add_zero]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [show t + (i + 1) = t + 1 + i by omega]
  unfold resD
  rw [peak_empty, resP_stock]
  simp only [hs, ← add_assoc]

section Const

variable {eus : U → 𝕜} {cap r M p : 𝕜}

omit [Fintype U] [DecidableEq U] in
/-- Un pas de la récurrence à données constantes, mémoire par mémoire. -/
theorem step_const (mem : Memory) (hM : 0 ≤ M) (hp : M ≤ p)
    (n : ℕ) :
    M ≤ tickOpF mem r p + M ∧
      ((p ≤ cap ∧ tickOpF mem r p + M + n * max (M - rhoF mem r cap) 0 ≤ cap) ↔
        p + (n + 1) * max (M - rhoF mem r cap) 0 ≤ cap) := by
  have hn : (0 : 𝕜) ≤ n := Nat.cast_nonneg n
  cases mem with
  | stock =>
    simp only [tickOpF, rhoF, sub_zero, max_eq_left hM]
    refine ⟨by linarith, ⟨fun ⟨_, h⟩ => by linarith, fun h => ⟨?_, by linarith⟩⟩⟩
    nlinarith
  | flow =>
    simp only [tickOpF, rhoF, zero_add]
    refine ⟨le_rfl, ?_⟩
    rcases le_total M cap with h | h
    · rw [max_eq_right (by linarith)]
      simp only [mul_zero, add_zero]
      exact ⟨fun ⟨h1, _⟩ => h1, fun h1 => ⟨h1, h⟩⟩
    · rw [max_eq_left (by linarith)]
      have : 0 ≤ (n + 1 : 𝕜) * (M - cap) := mul_nonneg (by linarith) (by linarith)
      constructor
      · rintro ⟨h1, -⟩
        rcases eq_or_lt_of_le h with h' | h'
        · nlinarith
        · linarith
      · intro h1
        have : 0 ≤ (n : 𝕜) * (M - cap) := mul_nonneg hn (by linarith)
        refine ⟨by nlinarith, by nlinarith⟩
  | regen =>
    simp only [tickOpF, rhoF]
    refine ⟨by linarith [le_max_right (p - r) 0], ?_⟩
    rcases le_total M (min r cap) with h | h
    · rw [max_eq_right (show M - min r cap ≤ 0 by linarith)]
      simp only [mul_zero, add_zero]
      have hMr : M ≤ r := le_trans h (min_le_left _ _)
      refine ⟨fun h' => h'.1, fun h1 => ⟨h1, ?_⟩⟩
      rcases le_total (p - r) 0 with h' | h'
      · rw [max_eq_right h']
        linarith [min_le_right r cap]
      · rw [max_eq_left h']
        linarith
    · rw [max_eq_left (show 0 ≤ M - min r cap by linarith)]
      rcases le_total r cap with hrc | hrc
      · rw [min_eq_left hrc] at h ⊢
        rw [max_eq_left (show 0 ≤ p - r by linarith)]
        have e : p - r + M + n * (M - r) = p + (n + 1) * (M - r) := by ring
        have h0 : 0 ≤ ((n : 𝕜) + 1) * (M - r) := mul_nonneg (by linarith) (by linarith)
        rw [e]
        exact ⟨fun h' => h'.2, fun h' => ⟨by linarith, h'⟩⟩
      · rw [min_eq_right hrc] at h ⊢
        have h0 : 0 ≤ ((n : 𝕜) + 1) * (M - cap) := mul_nonneg (by linarith) (by linarith)
        constructor
        · rintro ⟨h1, -⟩
          have hMc : M = cap := le_antisymm (by linarith) h
          rw [hMc, sub_self, mul_zero, add_zero]
          exact h1
        · intro h1
          have hpc : p ≤ cap := by linarith
          have hMc : M = cap := le_antisymm (by linarith) h
          refine ⟨hpc, ?_⟩
          rw [max_eq_right (show p - r ≤ 0 by linarith), hMc, sub_self, mul_zero]
          linarith

omit [DecidableEq U] in
/-- La récurrence à données constantes : `p + n · max (M − ρ) 0 ≤ C`, pour une pointe `p ≥ M`. -/
theorem resP_const (mem : Memory) (heu : ∀ u, 0 ≤ eus u) :
    ∀ n t (p : 𝕜), ∑ u, eus u ≤ p →
      (resP (tickOpF mem r) (fun _ => eus) (fun _ => cap) n t p ↔
        p + n * max (∑ u, eus u - rhoF mem r cap) 0 ≤ cap) := by
  have hM : 0 ≤ ∑ u, eus u := Finset.sum_nonneg fun u _ => heu u
  intro n
  induction n with
  | zero => intro t p _; simp [resP]
  | succ n ih =>
    intro t p hp
    obtain ⟨hnext, hiff⟩ := step_const mem hM hp n
    show (p ≤ cap ∧ resP (tickOpF mem r) (fun _ => eus) (fun _ => cap) n (t + 1)
      (tickOpF mem r p + ∑ u, eus u)) ↔ _
    rw [ih (t + 1) _ hnext, Nat.cast_succ]
    exact hiff

/-- ★ (d)(iv) **Données constantes** : depuis une charge `L ≥ 0` au début d'une période, le
plafond tient `n` fins de période de plus si et seulement si `L + M + n · max (M − ρ) 0 ≤ C`. -/
theorem resD_const_iff (mem : Memory) (heu : ∀ u, 0 ≤ eus u)
    {L : 𝕜} (hL : 0 ≤ L) (n t : ℕ) :
    resD (tickOpF mem r) (fun _ => eus) (fun _ => cap) n t (L, ∅) ↔
      L + ∑ u, eus u + n * max (∑ u, eus u - rhoF mem r cap) 0 ≤ cap := by
  unfold resD
  rw [peak_empty]
  exact resP_const mem heu n t _ (by simp only [periodMass]; linarith)

/-- ★ (d)(v) **Tous les horizons** (corps archimédien) : `L + M ≤ C` et `M ≤ ρ`. -/
theorem forall_horizon_iff [Archimedean 𝕜] (mem : Memory) (heu : ∀ u, 0 ≤ eus u) {L : 𝕜} (hL : 0 ≤ L) (t : ℕ) :
    (∀ n, resD (tickOpF mem r) (fun _ => eus) (fun _ => cap) n t (L, ∅)) ↔
      L + ∑ u, eus u ≤ cap ∧ ∑ u, eus u ≤ rhoF mem r cap := by
  simp only [resD_const_iff mem heu hL]
  constructor
  · intro h
    have h0 := h 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h0
    refine ⟨h0, ?_⟩
    by_contra hlt
    have hd : 0 < ∑ u, eus u - rhoF mem r cap := by linarith [not_le.mp hlt]
    obtain ⟨n, hn⟩ := exists_nat_gt ((cap - (L + ∑ u, eus u)) / (∑ u, eus u - rhoF mem r cap))
    have h1 := h n
    rw [max_eq_left hd.le] at h1
    have h2 := (div_lt_iff₀ hd).mp hn
    linarith
  · rintro ⟨h1, h2⟩ n
    rw [max_eq_right (by linarith)]
    simpa using h1

/-- ★ (d)(v) Tenable à tout horizon fini si et seulement si dans un ensemble tenable du
théorème 2(b) (corps archimédien). -/
theorem forall_horizon_iff_tenable [Archimedean 𝕜] (mem : Memory) (heu : ∀ u, 0 ≤ eus u) {L : 𝕜} (hL : 0 ≤ L) :
    (∀ n, resD (tickOpF mem r) (fun _ => eus) (fun _ => cap) n 0 (L, ∅)) ↔
      ∃ Y, GuardField.ControlledInvariantSetF (tickOpF mem r) eus cap Y ∧ Y (L, ∅) := by
  rw [forall_horizon_iff mem heu hL]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨GuardField.XresSetF eus cap,
      (GuardField.reserveSetF_ci_iff heu).2 ((GuardField.topOKF_iff mem r).2 (by simpa using h2)),
      ?_⟩
    simpa [GuardField.XresSetF] using h1
  · rintro ⟨Y, hY, hq⟩
    have hres := GuardField.reserveSetF_maximal hY _ hq
    simp only [GuardField.XresSetF, Finset.compl_empty] at hres
    exact ⟨hres, (GuardField.viableF_iff mem r heu).1 ⟨Y, hY, _, hq⟩⟩

end Const

end Dated

/-! ## §3. Témoins -/

/-- ★ **Témoin de M3a** : mémoire `stock`, plafond 2, une source de taille 1. Depuis une charge
nulle, le plafond tient deux périodes, pas trois, alors que `M = 1 > ρ = 0`. -/
theorem m3a_two_periods :
    resD (tickOpF .stock (0 : ℚ)) (fun _ (_ : Unit) => (1 : ℚ)) (fun _ => 2) 1 0 (0, ∅) ∧
      ¬ resD (tickOpF .stock (0 : ℚ)) (fun _ (_ : Unit) => (1 : ℚ)) (fun _ => 2) 2 0 (0, ∅) := by
  have h := fun n => resD_const_iff (𝕜 := ℚ) (U := Unit) (eus := fun _ => 1) (cap := 2) (r := 0)
    .stock (fun _ => by norm_num) le_rfl n 0
  rw [h 1, h 2]
  norm_num [rhoF]

/-- ★ **Témoin de la date d'entrée en vigueur** : mémoire `stock`, aucune source, plafond 3 à la
première date et 2 à la seconde. La règle du plafond en vigueur à la première date admet la
charge 3 ; depuis la charge 3, aucune famille ne tient le plafond de la seconde date. La réserve
datée, en vigueur dès la première date, admet jusqu'à 2 ; en mémoire `flow`, jusqu'à 3. -/
theorem effective_date :
    GuardField.guardF (3 : ℚ) (fun _ : Unit => (3 : ℚ)) 0 () ∧
      (¬ ∃ X, TenableD (tickOpF .stock (0 : ℚ)) (fun _ (_ : Empty) => (0 : ℚ))
          (fun t => if t = 0 then 3 else 2) 1 X ∧ X 1 (3, ∅)) ∧
      (∀ L : ℚ, resD (tickOpF .stock 0) (fun _ (_ : Empty) => (0 : ℚ))
          (fun t => if t = 0 then 3 else 2) 1 0 (L, ∅) ↔ L ≤ 2) ∧
      (∀ L : ℚ, resD (tickOpF .flow 0) (fun _ (_ : Empty) => (0 : ℚ))
          (fun t => if t = 0 then 3 else 2) 1 0 (L, ∅) ↔ L ≤ 3) := by
  refine ⟨by norm_num [GuardField.guardF], ?_, fun L => ?_, fun L => ?_⟩
  · rintro ⟨X, hX, h⟩
    have := tenableD_subset_res hX le_rfl _ h
    norm_num [resD, resP, peak] at this
  · simp only [resD, resP, peak, periodMass, tickOpF]
    norm_num
    exact fun h => by linarith
  · simp only [resD, resP, peak, periodMass, tickOpF]
    norm_num

/-! ## §4. Viabilité conjointe : préparation de SP-7 (non exportée) -/

section Product

variable {S₁ S₂ A₁ A₂ Z₁ Z₂ : Type*} {K₁ : ℕ → Set S₁} {Adm₁ : ℕ → S₁ → Set A₁}
  {W₁ : ℕ → S₁ → A₁ → Set Z₁} {F₁ : ℕ → S₁ → A₁ → Z₁ → S₁} {K₂ : ℕ → Set S₂}
  {Adm₂ : ℕ → S₂ → Set A₂} {W₂ : ℕ → S₂ → A₂ → Set Z₂} {F₂ : ℕ → S₂ → A₂ → Z₂ → S₂}

/-- Deux systèmes séparés (chocs toujours possibles) : la récurrence du produit est le produit des
récurrences. -/
theorem V_prod (hW₁ : ∀ t x a, (W₁ t x a).Nonempty) (hW₂ : ∀ t x a, (W₂ t x a).Nonempty) :
    ∀ n t, V (fun t => K₁ t ×ˢ K₂ t) (fun t x => Adm₁ t x.1 ×ˢ Adm₂ t x.2)
        (fun t x a => W₁ t x.1 a.1 ×ˢ W₂ t x.2 a.2)
        (fun t x a z => (F₁ t x.1 a.1 z.1, F₂ t x.2 a.2 z.2)) n t =
      V K₁ Adm₁ W₁ F₁ n t ×ˢ V K₂ Adm₂ W₂ F₂ n t
  | 0, _ => rfl
  | n + 1, t => by
    ext ⟨x₁, x₂⟩
    simp only [V, Set.mem_setOf_eq, Set.mem_prod, V_prod hW₁ hW₂ n (t + 1)]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, ⟨a₁, a₂⟩, ⟨ha₁, ha₂⟩, hz⟩
      obtain ⟨z₁, hz₁⟩ := hW₁ t x₁ a₁
      obtain ⟨z₂, hz₂⟩ := hW₂ t x₂ a₂
      exact ⟨⟨h₁, a₁, ha₁, fun z hz' => (hz (z, z₂) ⟨hz', hz₂⟩).1⟩,
        ⟨h₂, a₂, ha₂, fun z hz' => (hz (z₁, z) ⟨hz₁, hz'⟩).2⟩⟩
    · rintro ⟨⟨h₁, a₁, ha₁, hz₁⟩, ⟨h₂, a₂, ha₂, hz₂⟩⟩
      exact ⟨⟨h₁, h₂⟩, (a₁, a₂), ⟨ha₁, ha₂⟩, fun z hz => ⟨hz₁ z.1 hz.1, hz₂ z.2 hz.2⟩⟩

end Product

/-- Tenir deux contraintes ensemble demande au moins de tenir chacune. -/
theorem V_inter_subset {S A Z : Type*} {K K' : ℕ → Set S} {Adm : ℕ → S → Set A}
    {W : ℕ → S → A → Set Z} {F : ℕ → S → A → Z → S} :
    ∀ n t, V (fun t => K t ∩ K' t) Adm W F n t ⊆ V K Adm W F n t ∩ V K' Adm W F n t
  | 0, _ => fun _ h => h
  | n + 1, t => fun _ ⟨⟨h, h'⟩, a, ha, hz⟩ =>
    ⟨⟨h, a, ha, fun z hz' => (V_inter_subset n (t + 1) (hz z hz')).1⟩,
      ⟨h', a, ha, fun z hz' => (V_inter_subset n (t + 1) (hz z hz')).2⟩⟩

/-- Actions du témoin couplé : vendre (`1`) ou non (`0`). -/
def jAdm : ℕ → ℤ × ℤ → Set ℤ := fun _ _ => {0, 1}

/-- Chocs du témoin couplé : aucun. -/
def jW : ℕ → ℤ × ℤ → ℤ → Set Unit := fun _ _ _ => Set.univ

/-- Dynamique du témoin couplé : vendre émet 1 et rapporte 1 ; une dépense de 1 est due. -/
def jF : ℕ → ℤ × ℤ → ℤ → Unit → ℤ × ℤ := fun _ x a _ => (x.1 + a, x.2 + a - 1)

/-- Témoin couplé : viable pour le plafond seul et pour la solvabilité seule, pas pour les
deux, quand le paiement nécessaire porte une émission. -/
theorem joint_strict :
    ((0 : ℤ), (0 : ℤ)) ∈ V (fun _ => {x : ℤ × ℤ | x.1 ≤ 0}) jAdm jW jF 1 0 ∧
      ((0 : ℤ), (0 : ℤ)) ∈ V (fun _ => {x : ℤ × ℤ | 0 ≤ x.2}) jAdm jW jF 1 0 ∧
      ((0 : ℤ), (0 : ℤ)) ∉
        V (fun _ => {x : ℤ × ℤ | x.1 ≤ 0} ∩ {x | 0 ≤ x.2}) jAdm jW jF 1 0 := by
  refine ⟨⟨by simp, 0, by simp [jAdm], fun _ _ => ?_⟩, ⟨by simp, 1, by simp [jAdm], fun _ _ => ?_⟩,
    ?_⟩
  · show (0 : ℤ) + 0 ≤ 0
    norm_num
  · show (0 : ℤ) ≤ 0 + 1 - 1
    norm_num
  · rintro ⟨-, a, ha, h⟩
    have := h () (Set.mem_univ _)
    rcases ha with rfl | rfl
    · norm_num [jF, V] at this
    · norm_num [jF, V] at this

end DatedViability
