/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/EssentialService.lean
  Service des lots essentiels (2026-10-13, SP-2, D-44) — papier 11 : le service, et non sa seule
  possibilité, sous une hypothèse énoncée sur les demandes ; le théorème 3 à plusieurs plafonds.
  Développé d'abord en `EssentialService_scratch.lean` (workflow du dépôt). Trace :
  `cache/sp2_service_lots_2026-10-13/`.

  Module neuf (D-30) : aucun module existant n'est modifié. Il importe `GuardField` (papier 11).

  Portée. Une période, sans événement de fin ; l'état `(L, P)` porte la charge et les lots
  essentiels encore en attente, fixés au départ. La charge vit dans un monoïde additif commutatif
  ordonné `M` quelconque : ℕ, ℤ, un corps ordonné, ou leurs produits finis `B → 𝕜`, ordonnés
  coordonnée par coordonnée (un plafond par coordonnée : plusieurs plafonds). Les lettres sont
  proposées par l'environnement, en une suite infinie de demandes `w` ; la règle ne fait
  qu'admettre ou refuser (`runV` : une demande refusée, ou celle d'un lot qui n'attend pas, laisse
  l'état inchangé).
  - §1, le théorème 3 de P11 sur `M` (`resV_necessary`, `nbGuardV_safe`, `nbGuardV_nonblocking`,
    `nbGuardV_maximal`), et le pont avec `GuardField` pour un seul plafond sur un corps ordonné
    (`reachV_iff`, `nbGuardV_eq`).
  - §2, le service sous des demandes. (a) Quelle que soit la règle, un lot jamais demandé reste en
    attente (`unrequested_pending`) ; avec une émission de charge nulle demandée sans fin, la
    garde à réserve admet tout, reste non bloquante, et ne sert rien (`starvation`). (b) Si chaque
    lot en attente est demandé parmi les `k` premières demandes (`FairWithin`), la garde à réserve
    les sert tous dans les `k` premières demandes, sûrement (`nbGuardV_serves`) ; servir ainsi
    depuis chaque état atteint (`ServesWithin`) rend non bloquant
    (`servesWithin_nonblocking`), d'où : la garde à réserve reste la plus permissive des règles
    sûres qui servent en `k` demandes (`nbGuardV_maximal_serving`). (c) Une fin de période qui
    vient après au moins `k` demandes vient après tous les services (`nbGuardV_serves`, `n ≥ k`).
  - §3, témoin (`greedy_starves_fair`) : sur les données de `GuardField.greedy_blocks`, avec des
    demandes équitables en 4, la garde gloutonne, sûre, ne sert jamais le lot ; la garde à réserve
    le sert à la quatrième demande.
  Nature : le §1 reprend les preuves du théorème 3 de P11, coordonnée par coordonnée ; le §2 est
  élémentaire : la garde à réserve admet toute demande d'un lot en attente, puisque servir garde le
  potentiel `L + Σ_P b` (`nbGuardV_admits_service`).
  Hors : les événements forçables (un ordonnanceur qui sert de lui-même) ; les lots qui arrivent
  pendant la période ; l'enchaînement des périodes (seau à jetons, `DeadlineGuard`) ; l'équité
  sans borne (« tout lot finit par être servi »), qui n'est pas énoncée ici.
  Les `example` de la fin sont des témoins de non-vacuité, dans `Fin 2 → ℚ` et dans ℕ.
-/
import ThesePlanetaire.GuardField

namespace EssentialService

/-! ## §1. Le modèle générique : plusieurs plafonds -/

section Defs

variable {M : Type*} [AddCommMonoid M] {α κ : Type*} [DecidableEq κ]

/-- Un pas : émission discrétionnaire ou service d'un lot essentiel. -/
def stepV (e : α → M) (b : κ → M) (q : M × Finset κ) : α ⊕ κ → M × Finset κ
  | .inl a => (q.1 + e a, q.2)
  | .inr k => (q.1 + b k, q.2.erase k)

/-- Une lettre est tirable : toute émission discrétionnaire, et le service d'un lot en attente. -/
def FiresV (q : M × Finset κ) : α ⊕ κ → Prop
  | .inl _ => True
  | .inr k => k ∈ q.2

/-- États atteignables en boucle fermée depuis `q₀`. -/
inductive ReachV (e : α → M) (b : κ → M) (S : M × Finset κ → α ⊕ κ → Prop)
    (q₀ : M × Finset κ) : M × Finset κ → Prop
  | init : ReachV e b S q₀ q₀
  | step {q : M × Finset κ} {x : α ⊕ κ} :
      ReachV e b S q₀ q → FiresV q x → S q x → ReachV e b S q₀ (stepV e b q x)

/-- Non-blocage : depuis tout état atteignable, un état sans lot en attente reste atteignable. -/
def NonBlockingV (e : α → M) (b : κ → M) (S : M × Finset κ → α ⊕ κ → Prop)
    (q₀ : M × Finset κ) : Prop :=
  ∀ q, ReachV e b S q₀ q → ∃ L, ReachV e b S q (L, ∅)

variable [PartialOrder M]

/-- Sûreté : toute charge atteignable reste sous le plafond (dans l'ordre de `M`). -/
def SafeV (e : α → M) (b : κ → M) (S : M × Finset κ → α ⊕ κ → Prop) (cap : M)
    (q₀ : M × Finset κ) : Prop :=
  ∀ q, ReachV e b S q₀ q → q.1 ≤ cap

/-- La réserve : de quoi servir les lots en attente. -/
def ResV (b : κ → M) (cap : M) (q : M × Finset κ) : Prop := q.1 + ∑ k ∈ q.2, b k ≤ cap

/-- La garde à réserve : admettre une lettre ssi l'état suivant reste dans la réserve. -/
def nbGuardV (e : α → M) (b : κ → M) (cap : M) : M × Finset κ → α ⊕ κ → Prop :=
  fun q x => ResV b cap (stepV e b q x)

/-- La garde gloutonne : admettre une lettre ssi la charge suivante reste sous le plafond. -/
def greedyV (e : α → M) (b : κ → M) (cap : M) : M × Finset κ → α ⊕ κ → Prop :=
  fun q x => (stepV e b q x).1 ≤ cap

end Defs

section Reserve

variable {M : Type*} [AddCommMonoid M] {α κ : Type*} [DecidableEq κ]
variable {e : α → M} {b : κ → M} {S : M × Finset κ → α ⊕ κ → Prop} {q₀ : M × Finset κ}

theorem reachV_trans {q q' : M × Finset κ} (h : ReachV e b S q₀ q) (h' : ReachV e b S q q') :
    ReachV e b S q₀ q' := by
  induction h' with
  | init => exact h
  | step _ hf hs ih => exact ReachV.step ih hf hs

/-- Le potentiel d'un service est inchangé. -/
theorem stepV_inr_pot (q : M × Finset κ) {k : κ} (hk : k ∈ q.2) :
    (stepV e b q (.inr k)).1 + ∑ j ∈ (stepV e b q (.inr k)).2, b j = q.1 + ∑ j ∈ q.2, b j := by
  simp only [stepV]
  rw [add_assoc, Finset.add_sum_erase _ _ hk]

/-- Les lots en attente ne font que décroître le long d'un déroulé. -/
theorem reachV_pending {q q' : M × Finset κ} (h : ReachV e b S q q') : q'.2 ⊆ q.2 := by
  induction h with
  | init => exact subset_rfl
  | @step q x _ _ _ ih =>
    cases x with
    | inl a => exact ih
    | inr k => exact (Finset.erase_subset _ _).trans ih

variable [PartialOrder M] [IsOrderedAddMonoid M] {cap : M}

/-- Le potentiel `L + Σ_P b` ne décroît pas le long d'un déroulé (émissions positives). -/
theorem reachV_pot (he : ∀ a, 0 ≤ e a) {q q' : M × Finset κ} (h : ReachV e b S q q') :
    q.1 + ∑ k ∈ q.2, b k ≤ q'.1 + ∑ k ∈ q'.2, b k := by
  induction h with
  | init => exact le_rfl
  | @step q x _ hf _ ih =>
    cases x with
    | inl a =>
      refine ih.trans ?_
      simp only [stepV]
      exact add_le_add (le_add_of_nonneg_right (he a)) le_rfl
    | inr k => exact ih.trans (stepV_inr_pot q hf).ge

/-- ★ **La réserve est nécessaire** (plusieurs plafonds) : tout superviseur sûr et non bloquant
garde, sur ses états atteignables, de quoi servir les lots en attente. -/
theorem resV_necessary (he : ∀ a, 0 ≤ e a) (hS : SafeV e b S cap q₀)
    (hN : NonBlockingV e b S q₀) : ∀ q, ReachV e b S q₀ q → ResV b cap q := by
  intro q hq
  obtain ⟨L, hL⟩ := hN q hq
  have h1 := reachV_pot he hL
  have h2 := hS _ (reachV_trans hq hL)
  simp only [Finset.sum_empty, add_zero] at h1 h2
  exact h1.trans h2

omit [IsOrderedAddMonoid M] in
theorem nbGuardV_inv (h₀ : ResV b cap q₀) {q : M × Finset κ}
    (hq : ReachV e b (nbGuardV e b cap) q₀ q) : ResV b cap q := by
  induction hq with
  | init => exact h₀
  | step _ _ hs _ => exact hs

/-- ★ La garde à réserve est sûre (plusieurs plafonds). -/
theorem nbGuardV_safe (hb : ∀ k, 0 ≤ b k) (h₀ : ResV b cap q₀) :
    SafeV e b (nbGuardV e b cap) cap q₀ := by
  intro q hq
  exact (le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hb k)).trans (nbGuardV_inv h₀ hq)

omit [IsOrderedAddMonoid M] in
/-- Depuis un état de la réserve, la garde laisse servir tous les lots en attente. -/
theorem nbGuardV_serve_all (P : Finset κ) :
    ∀ L, ResV b cap (L, P) → ReachV e b (nbGuardV e b cap) (L, P) (L + ∑ k ∈ P, b k, ∅) := by
  induction P using Finset.induction_on with
  | empty => intro L _; simpa using ReachV.init
  | insert k P hk ih =>
    intro L hL
    have hst : stepV e b (L, insert k P) (.inr k) = (L + b k, P) := by
      simp [stepV, Finset.erase_insert hk]
    have hres : ResV b cap (L + b k, P) := by
      unfold ResV at hL ⊢
      rw [Finset.sum_insert hk] at hL
      simpa [add_assoc] using hL
    have h1 : ReachV e b (nbGuardV e b cap) (L, insert k P) (L + b k, P) := by
      rw [← hst]
      exact ReachV.step ReachV.init (Finset.mem_insert_self k P) (by rw [nbGuardV, hst]; exact hres)
    have h2 := ih (L + b k) hres
    rw [Finset.sum_insert hk, ← add_assoc]
    exact reachV_trans h1 h2

omit [IsOrderedAddMonoid M] in
/-- ★ La garde à réserve est non bloquante (plusieurs plafonds). -/
theorem nbGuardV_nonblocking (h₀ : ResV b cap q₀) : NonBlockingV e b (nbGuardV e b cap) q₀ :=
  fun q hq => ⟨_, nbGuardV_serve_all q.2 q.1 (nbGuardV_inv h₀ hq)⟩

/-- ★ **Maximalité** (plusieurs plafonds) : tout superviseur sûr et non bloquant atteint moins
d'états que la garde à réserve, et n'admet, sur ses états atteignables, que ce qu'elle admet. -/
theorem nbGuardV_maximal (he : ∀ a, 0 ≤ e a) (hS : SafeV e b S cap q₀)
    (hN : NonBlockingV e b S q₀) :
    (∀ q, ReachV e b S q₀ q → ReachV e b (nbGuardV e b cap) q₀ q) ∧
      ∀ q x, ReachV e b S q₀ q → FiresV q x → S q x → nbGuardV e b cap q x := by
  have h2 : ∀ q x, ReachV e b S q₀ q → FiresV q x → S q x → nbGuardV e b cap q x :=
    fun q x hq hf hs => resV_necessary he hS hN _ (ReachV.step hq hf hs)
  refine ⟨fun q h => ?_, h2⟩
  induction h with
  | init => exact ReachV.init
  | step hq hf hs ih => exact ReachV.step ih hf (h2 _ _ hq hf hs)

omit [IsOrderedAddMonoid M] in
/-- La garde gloutonne est sûre. -/
theorem greedyV_safe (h₀ : q₀.1 ≤ cap) : SafeV e b (greedyV e b cap) cap q₀ := by
  intro q hq
  induction hq with
  | init => exact h₀
  | step _ _ hs _ => exact hs

end Reserve

/-! ### Pont avec `GuardField` : un seul plafond, sur un corps ordonné -/

section Bridge

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {α κ : Type*} [DecidableEq κ]
variable {e : α → 𝕜} {b : κ → 𝕜} {S : 𝕜 × Finset κ → α ⊕ κ → Prop} {q₀ : 𝕜 × Finset κ}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem stepV_eq (e : α → 𝕜) (b : κ → 𝕜) : stepV e b = GuardField.stepNB e b := by
  funext q x; cases x <;> rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq κ] in
theorem firesV_iff [DecidableEq κ] (q : 𝕜 × Finset κ) (x : α ⊕ κ) : FiresV q x ↔ GuardField.Fires q x := by
  cases x <;> rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- ★ Pont : pour un seul plafond sur un corps ordonné, les états atteints sont ceux de
`GuardField`. -/
theorem reachV_iff {q : 𝕜 × Finset κ} : ReachV e b S q₀ q ↔ GuardField.ReachNB e b S q₀ q := by
  constructor
  · intro h
    induction h with
    | init => exact GuardField.ReachNB.init
    | @step q x _ hf hs ih =>
      rw [stepV_eq]
      exact GuardField.ReachNB.step ih ((firesV_iff q x).mp hf) hs
  · intro h
    induction h with
    | init => exact ReachV.init
    | @step q x _ hf hs ih =>
      rw [← stepV_eq]
      exact ReachV.step ih ((firesV_iff q x).mpr hf) hs

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Pont : pour un seul plafond sur un corps ordonné, la garde à réserve est
`GuardField.nbGuard`. -/
theorem nbGuardV_eq (e : α → 𝕜) (b : κ → 𝕜) (cap : 𝕜) :
    nbGuardV e b cap = GuardField.nbGuard e b cap := by
  funext q x; cases x <;> rfl

end Bridge

/-! ## §2. Le service sous des demandes -/

section Service

variable {M : Type*} [AddCommMonoid M] {α κ : Type*} [DecidableEq κ]
variable {e : α → M} {b : κ → M} {S : M × Finset κ → α ⊕ κ → Prop} {q₀ : M × Finset κ}

open Classical in
/-- Le déroulé sous la suite de demandes `w` : une demande tirable et admise fait un pas ; une
demande refusée, ou celle d'un lot qui n'attend pas, laisse l'état inchangé. -/
noncomputable def runV (e : α → M) (b : κ → M) (S : M × Finset κ → α ⊕ κ → Prop)
    (w : ℕ → α ⊕ κ) (q₀ : M × Finset κ) : ℕ → M × Finset κ
  | 0 => q₀
  | n + 1 =>
    if FiresV (runV e b S w q₀ n) (w n) ∧ S (runV e b S w q₀ n) (w n) then
      stepV e b (runV e b S w q₀ n) (w n)
    else runV e b S w q₀ n

/-- Chaque lot de `P` est demandé parmi les `k` premières demandes. -/
def FairWithin (k : ℕ) (P : Finset κ) (w : ℕ → α ⊕ κ) : Prop :=
  ∀ j ∈ P, ∃ m < k, w m = .inr j

/-- La règle sert en `k` demandes : depuis tout état atteint, toute suite de demandes équitable
en `k` sert tous les lots en attente dans les `k` premières demandes. -/
def ServesWithin (e : α → M) (b : κ → M) (S : M × Finset κ → α ⊕ κ → Prop) (k : ℕ)
    (q₀ : M × Finset κ) : Prop :=
  ∀ q, ReachV e b S q₀ q → ∀ w, FairWithin k q.2 w → (runV e b S w q k).2 = ∅

variable {w : ℕ → α ⊕ κ}

theorem runV_zero : runV e b S w q₀ 0 = q₀ := rfl

theorem runV_succ_of_admit {n : ℕ} (hf : FiresV (runV e b S w q₀ n) (w n))
    (hs : S (runV e b S w q₀ n) (w n)) :
    runV e b S w q₀ (n + 1) = stepV e b (runV e b S w q₀ n) (w n) := by
  rw [runV, if_pos ⟨hf, hs⟩]

theorem runV_succ_of_not {n : ℕ}
    (h : ¬ (FiresV (runV e b S w q₀ n) (w n) ∧ S (runV e b S w q₀ n) (w n))) :
    runV e b S w q₀ (n + 1) = runV e b S w q₀ n := by
  rw [runV, if_neg h]

/-- Chaque état du déroulé est atteint. -/
theorem runV_reach (n : ℕ) : ReachV e b S q₀ (runV e b S w q₀ n) := by
  induction n with
  | zero => exact ReachV.init
  | succ n ih =>
    by_cases h : FiresV (runV e b S w q₀ n) (w n) ∧ S (runV e b S w q₀ n) (w n)
    · rw [runV_succ_of_admit h.1 h.2]
      exact ReachV.step ih h.1 h.2
    · rw [runV_succ_of_not h]
      exact ih

/-- Les lots en attente ne font que décroître le long du déroulé. -/
theorem runV_pending_anti {m n : ℕ} (h : m ≤ n) :
    (runV e b S w q₀ n).2 ⊆ (runV e b S w q₀ m).2 := by
  induction h with
  | refl => exact subset_rfl
  | @step n _ ih =>
    refine Finset.Subset.trans ?_ ih
    by_cases h : FiresV (runV e b S w q₀ n) (w n) ∧ S (runV e b S w q₀ n) (w n)
    · rw [runV_succ_of_admit h.1 h.2]
      cases hw : w n with
      | inl a => exact subset_rfl
      | inr k => exact Finset.erase_subset _ _
    · rw [runV_succ_of_not h]

/-- ★ **(a) Une règle ne fait que refuser** : quelle que soit la règle, un lot qui n'est demandé à
aucun des `n` premiers indices est encore en attente à l'indice `n`. -/
theorem unrequested_pending {j : κ} (hj : j ∈ q₀.2) :
    ∀ n, (∀ m < n, w m ≠ .inr j) → j ∈ (runV e b S w q₀ n).2 := by
  intro n
  induction n with
  | zero => intro _; exact hj
  | succ n ih =>
    intro hw
    have hn := ih fun m hm => hw m (Nat.lt_succ_of_lt hm)
    by_cases h : FiresV (runV e b S w q₀ n) (w n) ∧ S (runV e b S w q₀ n) (w n)
    · rw [runV_succ_of_admit h.1 h.2]
      have hwn := hw n (Nat.lt_succ_self n)
      cases hx : w n with
      | inl a => exact hn
      | inr k =>
        have hkj : j ≠ k := fun h' => hwn (by rw [hx, h'])
        exact Finset.mem_erase.mpr ⟨hkj, hn⟩
    · rw [runV_succ_of_not h]
      exact hn

variable [PartialOrder M] {cap : M}

omit [DecidableEq κ] in
/-- La garde à réserve admet toute demande d'un lot en attente, depuis un état de la réserve. -/
theorem nbGuardV_admits_service [DecidableEq κ] {q : M × Finset κ} (hq : ResV b cap q) {k : κ}
    (hk : k ∈ q.2) : nbGuardV e b cap q (.inr k) := by
  unfold nbGuardV ResV
  rw [stepV_inr_pot q hk]
  exact hq

/-- ★ **(a) Témoin de famine** : une émission discrétionnaire de charge nulle, demandée sans fin.
La garde à réserve admet chaque demande, l'état ne change pas, la garde est non bloquante, et
aucun lot en attente n'est jamais servi. -/
theorem starvation {a : α} (ha : e a = 0) (h₀ : ResV b cap q₀) :
    (∀ n, runV e b (nbGuardV e b cap) (fun _ => .inl a) q₀ n = q₀) ∧
      (∀ n, nbGuardV e b cap (runV e b (nbGuardV e b cap) (fun _ => .inl a) q₀ n) (.inl a)) ∧
      NonBlockingV e b (nbGuardV e b cap) q₀ ∧
      ∀ j ∈ q₀.2, ∀ n, j ∈ (runV e b (nbGuardV e b cap) (fun _ => .inl a) q₀ n).2 := by
  have hst : stepV e b q₀ (.inl a) = q₀ := by simp [stepV, ha]
  have hadm : nbGuardV e b cap q₀ (.inl a) := by
    unfold nbGuardV; rw [hst]; exact h₀
  have hrun : ∀ n, runV e b (nbGuardV e b cap) (fun _ => .inl a) q₀ n = q₀ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [runV_succ_of_admit (by rw [ih]; trivial) (by rw [ih]; exact hadm), ih, hst]
  refine ⟨hrun, fun n => by rw [hrun]; exact hadm, nbGuardV_nonblocking h₀, ?_⟩
  intro j hj n
  rw [hrun]
  exact hj

variable [IsOrderedAddMonoid M]

/-- ★ **(b), (c) Service borné sous des demandes équitables** : depuis un état de la réserve, si
chaque lot en attente est demandé parmi les `k` premières demandes, la garde à réserve les sert
tous dans les `k` premières demandes (donc avant une fin de période qui vient après au moins `k`
demandes) ; si les lots sont positifs, toute charge du déroulé reste sous le plafond. -/
theorem nbGuardV_serves (h₀ : ResV b cap q₀) (hw : FairWithin k q₀.2 w) :
    (∀ n, k ≤ n → (runV e b (nbGuardV e b cap) w q₀ n).2 = ∅) ∧
      ((∀ j, 0 ≤ b j) → ∀ n, (runV e b (nbGuardV e b cap) w q₀ n).1 ≤ cap) := by
  refine ⟨fun n hn => ?_, fun hb n => nbGuardV_safe hb h₀ _ (runV_reach n)⟩
  have hk : ∀ j ∈ q₀.2, j ∉ (runV e b (nbGuardV e b cap) w q₀ k).2 := by
    intro j hj
    obtain ⟨m, hm, hwm⟩ := hw j hj
    by_cases hjm : j ∈ (runV e b (nbGuardV e b cap) w q₀ m).2
    · have hf : FiresV (runV e b (nbGuardV e b cap) w q₀ m) (w m) := by rw [hwm]; exact hjm
      have hs : nbGuardV e b cap (runV e b (nbGuardV e b cap) w q₀ m) (w m) := by
        rw [hwm]
        exact nbGuardV_admits_service (nbGuardV_inv h₀ (runV_reach m)) hjm
      have h1 := runV_succ_of_admit hf hs
      rw [hwm] at h1
      intro hjk
      have := runV_pending_anti (e := e) (b := b) (S := nbGuardV e b cap) (w := w) (q₀ := q₀)
        (Nat.succ_le_of_lt hm) hjk
      rw [h1] at this
      simp [stepV] at this
    · exact fun hjk => hjm (runV_pending_anti hm.le hjk)
  apply Finset.eq_empty_of_forall_notMem
  intro j hjn
  have hj0 : j ∈ q₀.2 := runV_pending_anti (Nat.zero_le n) hjn
  exact hk j hj0 (runV_pending_anti hn hjn)

/-- ★ La garde à réserve sert en `k` demandes, pour tout `k`. -/
theorem nbGuardV_servesWithin (h₀ : ResV b cap q₀) (k : ℕ) :
    ServesWithin e b (nbGuardV e b cap) k q₀ :=
  fun _ hq _ hw => (nbGuardV_serves (nbGuardV_inv h₀ hq) hw).1 k le_rfl

omit [PartialOrder M] [IsOrderedAddMonoid M] in
/-- ★ **Servir en `k` demandes rend non bloquant** quand `k` couvre les lots en attente au
départ. -/
theorem servesWithin_nonblocking (hk : q₀.2.card ≤ k) (hW : ServesWithin e b S k q₀) :
    NonBlockingV e b S q₀ := by
  intro q hq
  by_cases hP : q.2 = ∅
  · refine ⟨q.1, ?_⟩
    have : q = (q.1, ∅) := Prod.ext rfl hP
    rw [← this]
    exact ReachV.init
  obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP
  set l := q.2.toList with hl
  let w : ℕ → α ⊕ κ := fun m => .inr (l.getD m j₀)
  have hcard : q.2.card ≤ k := (Finset.card_le_card (reachV_pending hq)).trans hk
  have hfair : FairWithin k q.2 w := by
    intro j hj
    have hjl : j ∈ l := Finset.mem_toList.mpr hj
    obtain ⟨i, hi, hij⟩ := List.getElem_of_mem hjl
    refine ⟨i, ?_, ?_⟩
    · have : l.length = q.2.card := Finset.length_toList _
      omega
    · simp only [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hij]
  have h := hW q hq w hfair
  refine ⟨(runV e b S w q k).1, ?_⟩
  have hr := runV_reach (e := e) (b := b) (S := S) (w := w) (q₀ := q) k
  rwa [show runV e b S w q k = ((runV e b S w q k).1, ∅) from Prod.ext rfl h] at hr

/-- ★ **(b) Le service borné ne coûte rien en permissivité** : toute règle sûre qui sert en `k`
demandes (avec `k` au moins le nombre de lots en attente au départ) n'atteint que des états que
la garde à réserve atteint, et n'y admet que ce qu'elle admet ; la garde à réserve est elle-même
sûre et sert en `k` demandes (`nbGuardV_safe`, `nbGuardV_servesWithin`). -/
theorem nbGuardV_maximal_serving (he : ∀ a, 0 ≤ e a) (hk : q₀.2.card ≤ k)
    (hS : SafeV e b S cap q₀) (hW : ServesWithin e b S k q₀) :
    (∀ q, ReachV e b S q₀ q → ReachV e b (nbGuardV e b cap) q₀ q) ∧
      ∀ q x, ReachV e b S q₀ q → FiresV q x → S q x → nbGuardV e b cap q x :=
  nbGuardV_maximal he hS (servesWithin_nonblocking hk hW)

end Service

/-! ## §3. Témoins -/

section Witness

/-- Les demandes du témoin : trois émissions discrétionnaires, puis le lot à chaque demande. -/
def wGreedy : ℕ → Unit ⊕ Unit := fun m => if m < 3 then .inl () else .inr ()

/-- ★ **Témoin (glouton sous demandes équitables)** : émission discrétionnaire 2, lot 3,
plafond 7, comme `GuardField.greedy_blocks`. Le lot est demandé parmi les quatre premières
demandes ; la garde gloutonne, sûre, ne le sert jamais ; la garde à réserve refuse la troisième
émission en `(4, {()})` et sert le lot à la quatrième demande. -/
theorem greedy_starves_fair :
    FairWithin 4 {()} wGreedy ∧
      SafeV (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
        (greedyV (fun _ => 2) (fun _ => 3) 7) 7 (0, {()}) ∧
      (∀ n, () ∈ (runV (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
        (greedyV (fun _ => 2) (fun _ => 3) 7) wGreedy (0, {()}) n).2) ∧
      ¬ nbGuardV (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ)) 7 (4, {()}) (.inl ()) ∧
      runV (fun _ : Unit => (2 : ℚ)) (fun _ : Unit => (3 : ℚ))
        (nbGuardV (fun _ => 2) (fun _ => 3) 7) wGreedy (0, {()}) 4 = (7, ∅) := by
  set e : Unit → ℚ := fun _ => 2
  set b : Unit → ℚ := fun _ => 3
  refine ⟨?_, greedyV_safe (by norm_num), ?_, ?_, ?_⟩
  · intro j _
    exact ⟨3, by norm_num, by simp [wGreedy]⟩
  · -- la garde gloutonne : 0 → 2 → 4 → 6, puis le lot est refusé à jamais
    have g1 : runV e b (greedyV e b 7) wGreedy (0, {()}) 1 = (2, {()}) := by
      rw [runV_succ_of_admit (by simp [wGreedy, FiresV])
        (by simp [runV_zero, wGreedy, greedyV, stepV, e]; norm_num)]
      simp [runV_zero, wGreedy, stepV, e]
    have g2 : runV e b (greedyV e b 7) wGreedy (0, {()}) 2 = (4, {()}) := by
      rw [runV_succ_of_admit (by simp [wGreedy, FiresV])
        (by simp [g1, wGreedy, greedyV, stepV, e]; norm_num), g1]
      simp [wGreedy, stepV, e]; norm_num
    have g3 : runV e b (greedyV e b 7) wGreedy (0, {()}) 3 = (6, {()}) := by
      rw [runV_succ_of_admit (by simp [wGreedy, FiresV])
        (by simp [g2, wGreedy, greedyV, stepV, e]; norm_num), g2]
      simp [wGreedy, stepV, e]; norm_num
    have gt : ∀ n, runV e b (greedyV e b 7) wGreedy (0, {()}) (n + 3) = (6, {()}) := by
      intro n
      induction n with
      | zero => exact g3
      | succ n ih =>
        rw [show n + 1 + 3 = (n + 3) + 1 by omega, runV_succ_of_not, ih]
        rw [ih]
        have hw : wGreedy (n + 3) = .inr () := by simp [wGreedy]
        rw [hw]
        simp [greedyV, stepV, b]; norm_num
    intro n
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · simp [runV_zero]
      · rw [g1]; simp
      · rw [g2]; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [gt]; simp
  · simp [nbGuardV, ResV, stepV]; norm_num
  · -- la garde à réserve : 0 → 2 → 4, refus en (4, {()}), puis service : (7, ∅)
    have r1 : runV e b (nbGuardV e b 7) wGreedy (0, {()}) 1 = (2, {()}) := by
      rw [runV_succ_of_admit (by simp [wGreedy, FiresV])
        (by simp [runV_zero, wGreedy, nbGuardV, ResV, stepV, e, b]; norm_num)]
      simp [runV_zero, wGreedy, stepV, e]
    have r2 : runV e b (nbGuardV e b 7) wGreedy (0, {()}) 2 = (4, {()}) := by
      rw [runV_succ_of_admit (by simp [wGreedy, FiresV])
        (by simp [r1, wGreedy, nbGuardV, ResV, stepV, e, b]; norm_num), r1]
      simp [wGreedy, stepV, e]; norm_num
    have r3 : runV e b (nbGuardV e b 7) wGreedy (0, {()}) 3 = (4, {()}) := by
      rw [runV_succ_of_not (by simp [r2, wGreedy, nbGuardV, ResV, stepV, e, b]; norm_num), r2]
    rw [runV_succ_of_admit (by simp [r3, wGreedy, FiresV])
      (by simp [r3, wGreedy, nbGuardV, ResV, stepV, e, b]; norm_num), r3]
    simp [wGreedy, stepV, b]; norm_num

end Witness

/-! ### Non-vacuité -/

-- plusieurs plafonds : deux coordonnées, un lot, une émission discrétionnaire
example : ResV (fun _ : Unit => (![0, 1] : Fin 2 → ℚ)) ![2, 2] (0, {()}) ∧
    ({()} : Finset Unit).card ≤ 1 ∧
    SafeV (fun _ : Unit => (![1, 0] : Fin 2 → ℚ)) (fun _ : Unit => ![0, 1])
      (nbGuardV (fun _ => ![1, 0]) (fun _ => ![0, 1]) ![2, 2]) ![2, 2] (0, {()}) ∧
    ServesWithin (fun _ : Unit => (![1, 0] : Fin 2 → ℚ)) (fun _ : Unit => ![0, 1])
      (nbGuardV (fun _ => ![1, 0]) (fun _ => ![0, 1]) ![2, 2]) 1 (0, {()}) := by
  have h₀ : ResV (fun _ : Unit => (![0, 1] : Fin 2 → ℚ)) ![2, 2] (0, {()}) := by
    intro i; fin_cases i <;> simp
  refine ⟨h₀, by simp, nbGuardV_safe (fun _ i => by fin_cases i <;> simp) h₀,
    nbGuardV_servesWithin h₀ 1⟩

-- dans ℕ
example : NonBlockingV (fun _ : Unit => (1 : ℕ)) (fun _ : Unit => (2 : ℕ))
    (nbGuardV (fun _ => 1) (fun _ => 2) 5) (0, {()}) :=
  nbGuardV_nonblocking (by simp [ResV])

end EssentialService
