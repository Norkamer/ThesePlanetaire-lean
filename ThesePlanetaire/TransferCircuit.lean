/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/TransferCircuit.lean
  Phase 10 (2026-10-02), étape 10c : la devise exigée comme circuit de droits transférés —
  sûreté répartie par conservation, inclusion dans la garde, témoins S9b, fuite et réserve
  d'émission, T-M12-1 pour le transfert (faux en séquentiel, vrai en compensation).

  Développé d'abord en `TransferCircuit_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase10_2026-10-02/plan_phase10.md` ; analyse :
  `cache/analyse_phase10_garde_repartie_2026-10-02.md` ; sonde T1-T6
  (`cache/phase10_2026-10-02/outils/sonde_transfert.py`).
-/

import ThesePlanetaire.ReserveCoverage

/-!
# La devise exigée : une garde répartie

Un fournisseur adhérent exige, avec le paiement, des droits égaux au contenu en émission de sa
vente ; le droit passe du client au fournisseur ; l'émetteur couvert le rend au registre (burn)
quand il émet (circuit des TEQ de Fleming ; P2-15 §8, sonde S9b).

0. ★ `guard_simulates` : tout automate sûr sur un état riche, dont la projection suit
   `L ↦ L + e a` et le top, n'atteint que des charges atteignables sous la garde centrale.
   C'est `GuardSupervisor.guard_maximal` pour les superviseurs à état.
1. ★ `run_spec`, `transfer_conservation`, `transfer_cap` : `Σ ρ + L` est conservé ; la sûreté
   est **répartie** (aucun registre central ne lit `L`) et tient par conservation.
2. ★ `transfer_reach_le_guard` (inclusion dans la garde), ★ `transfer_not_maximal` (S9b : un
   refus que la garde n'aurait pas fait), ★ `transfer_misplaced` (droits mal placés : 0 lettre
   contre 4).
3. ★ `transfer_leak_le`, `issuance_reserve`, `uncovered_emitters_unc` : les émissions non
   couvertes échappent au circuit ; ce sont exactement les lettres qu'il ne peut jamais refuser,
   donc les sources incontrôlables de `ReserveCoverage` §1 ; le registre doit retenir la réserve
   (`S + M ≤ cap`).
4. **T-M12-1 pour le transfert.** ★ `transfer_settles_imp_central` : un règlement intégral par
   transfert implique la porte centrale. ★ `transfer_seq_strict` : la réciproque est **fausse**
   en règlement séquentiel (mot `[y, x]`, `S = 1`). ★ `net_settle_iff`,
   ★ `net_transfer_iff_central` : en compensation par période, une dotation de total `S` existe
   ssi `Σ_v max(0, x_v) ≤ S`, `x_v` = position nette (payé + brûlé − reçu) ; sans droit échoué,
   c'est la porte centrale. ★ `stranded_gap`, `stranded_witness` : l'écart est exactement la
   masse des droits échoués.
-/

namespace TransferCircuit

open LocalTraceLang (PAut run run_cons run_append run_singleton)
open FeedbackClass (Memory tickOp)
open GuardSupervisor (Reach guard closedLoop)

/-! ## §0. L'étalon : la garde simule tout superviseur sûr à état -/

section Simulates

variable {σ α : Type*}

/-- ★ Toute charge atteignable par un automate sûr sur un état riche, dont la projection `π`
suit `π' = π + e a` sur une émission et `π' = tick π` sur le top, est atteignable sous la garde
centrale `L + e a ≤ cap`. -/
theorem guard_simulates (A : PAut σ (Option α)) (π : σ → ℕ) (tick : ℕ → ℕ) (e : α → ℕ)
    (cap : ℕ) (q₀ : σ) (htop : ∀ q q', A q none = some q' → π q' = tick (π q))
    (hemit : ∀ q q' a, A q (some a) = some q' → π q' = π q + e a)
    (hsafe : ∀ w q, run A q₀ w = some q → π q ≤ cap) :
    ∀ w q, run A q₀ w = some q → Reach tick e (guard cap e) (π q₀) (π q) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro q h
    cases h
    exact Reach.init
  | append_singleton w x ih =>
    intro q h
    have hw := h
    rw [run_append] at h
    cases hr : run A q₀ w with
    | none => rw [hr] at h; cases h
    | some q' =>
      rw [hr, Option.bind_some, run_singleton] at h
      cases x with
      | none =>
        rw [htop _ _ h]
        exact Reach.top (ih q' hr)
      | some a =>
        rw [hemit _ _ _ h]
        refine Reach.emit (ih q' hr) ?_
        show π q' + e a ≤ cap
        rw [← hemit _ _ _ h]
        exact hsafe _ _ hw

end Simulates

/-! ## §1. Le circuit -/

section Circuit

variable {V α : Type*} [DecidableEq V]

/-- Un circuit de devise exigée : chaque lettre est un paiement `pay a = (payeur, receveur)`
qui exige `req a` droits (`0` si le receveur n'adhère pas) et porte une émission `em a`,
couverte (`cov a`, brûlée chez le receveur) ou non (fuite). -/
structure Circ (V α : Type*) where
  pay : α → V × V
  req : α → ℕ
  em : α → ℕ
  cov : α → Bool

/-- État : droits par détenteur, charge couverte (brûlée), charge non couverte (fuite). -/
@[ext] structure St (V : Type*) where
  ρ : V → ℕ
  L : ℕ
  Lu : ℕ

instance [Fintype V] : DecidableEq (St V) := fun a b =>
  decidable_of_iff (a.ρ = b.ρ ∧ a.L = b.L ∧ a.Lu = b.Lu) (by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact St.ext h1 h2 h3
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩)

/-- Transfert de `k` droits de `p` à `r` (séquentiel : exact même si `p = r`). -/
def xfer (ρ : V → ℕ) (p r : V) (k : ℕ) : V → ℕ :=
  Function.update (Function.update ρ p (ρ p - k)) r (Function.update ρ p (ρ p - k) r + k)

/-- Émission couverte (lue par la garde) et émission non couverte d'une lettre. -/
def emc (C : Circ V α) (a : α) : ℕ := if C.cov a then C.em a else 0

def lk (C : Circ V α) (a : α) : ℕ := if C.cov a then 0 else C.em a

/-- Un pas : transfert, puis brûlage chez le receveur si l'émission est couverte, sinon fuite.
Admissible ssi le payeur a les droits exigés et, si couverte, le receveur a de quoi brûler. -/
def tstep (C : Circ V α) : PAut (St V) α := fun q a =>
  if C.req a ≤ q.ρ (C.pay a).1 then
    if C.cov a then
      if C.em a ≤ xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a) (C.pay a).2 then
        some ⟨Function.update (xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a)) (C.pay a).2
          (xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a) (C.pay a).2 - C.em a), q.L + C.em a, q.Lu⟩
      else none
    else some ⟨xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a), q.L, q.Lu + C.em a⟩
  else none

/-- Avec le top : en mémoire `stock`, le circuit ne réémet pas de droits ; le top ne change
rien. -/
def circ (C : Circ V α) : PAut (St V) (Option α)
  | q, none => some q
  | q, some a => tstep C q a

/-- Émission couverte cumulée d'un mot (ce que lit la porte centrale) et fuite cumulée. -/
def cumE (C : Circ V α) (w : List α) : ℕ := (w.map (emc C)).sum

def leak (C : Circ V α) (w : List α) : ℕ := (w.map (lk C)).sum

theorem run_circ (C : Circ V α) :
    ∀ (q : St V) (w : List (Option α)), run (circ C) q w = run (tstep C) q (w.filterMap id)
  | q, [] => rfl
  | q, none :: w => run_circ C q w
  | q, some a :: w => by
    show (tstep C q a).bind (fun q' => run (circ C) q' w) =
      (tstep C q a).bind (fun q' => run (tstep C) q' (w.filterMap id))
    cases tstep C q a with
    | none => rfl
    | some q' => exact run_circ C q' w

variable [Fintype V]

theorem sum_update_add (f : V → ℕ) (p : V) (x : ℕ) :
    ∑ v, Function.update f p x v + f p = ∑ v, f v + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ p),
    Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ p) f]
  ring

theorem sum_xfer {ρ : V → ℕ} {p r : V} {k : ℕ} (hk : k ≤ ρ p) :
    ∑ v, xfer ρ p r k v = ∑ v, ρ v := by
  have h1 := sum_update_add ρ p (ρ p - k)
  have h2 := sum_update_add (Function.update ρ p (ρ p - k)) r
    (Function.update ρ p (ρ p - k) r + k)
  unfold xfer
  omega

/-- Spécification d'un pas. -/
theorem tstep_spec {C : Circ V α} {q q' : St V} {a : α} (h : tstep C q a = some q') :
    ∑ v, q'.ρ v + emc C a = ∑ v, q.ρ v ∧ q'.L = q.L + emc C a ∧ q'.Lu = q.Lu + lk C a := by
  unfold tstep at h
  split_ifs at h with h1 h2 h3 <;> cases h
  · have hs := sum_xfer (r := (C.pay a).2) h1
    have hu := sum_update_add (xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a)) (C.pay a).2
      (xfer q.ρ (C.pay a).1 (C.pay a).2 (C.req a) (C.pay a).2 - C.em a)
    simp only [emc, lk, h2, if_true]
    exact ⟨by omega, by simp, by simp⟩
  · have hs := sum_xfer (r := (C.pay a).2) h1
    simp only [emc, lk, h2]
    exact ⟨by simpa using hs, by simp, by simp⟩

/-- ★ Spécification d'une exécution : conservation des droits brûlés, charge couverte = émission
couverte du mot, fuite = émission non couverte du mot. -/
theorem run_spec (C : Circ V α) :
    ∀ (w : List α) (q₀ q : St V), run (tstep C) q₀ w = some q →
      ∑ v, q.ρ v + cumE C w = ∑ v, q₀.ρ v ∧ q.L = q₀.L + cumE C w ∧
        q.Lu = q₀.Lu + leak C w
  | [], q₀, q, h => by cases h; simp [cumE, leak]
  | a :: w, q₀, q, h => by
    rw [run_cons] at h
    cases h1 : tstep C q₀ a with
    | none => rw [h1] at h; cases h
    | some q₁ =>
      rw [h1, Option.bind_some] at h
      obtain ⟨s1, l1, u1⟩ := tstep_spec h1
      obtain ⟨s2, l2, u2⟩ := run_spec C w q₁ q h
      simp only [cumE, leak, List.map_cons, List.sum_cons] at s2 l2 u2 ⊢
      omega

/-- ★ Conservation : `Σ ρ + L` est constant le long des exécutions. -/
theorem transfer_conservation (C : Circ V α) {w : List α} {q₀ q : St V}
    (h : run (tstep C) q₀ w = some q) : ∑ v, q.ρ v + q.L = ∑ v, q₀.ρ v + q₀.L := by
  obtain ⟨h1, h2, -⟩ := run_spec C w q₀ q h
  omega

/-- ★ Sûreté répartie : la charge couverte ne dépasse jamais les droits émis. -/
theorem transfer_cap (C : Circ V α) {w : List α} {q₀ q : St V}
    (h : run (tstep C) q₀ w = some q) : q.L ≤ ∑ v, q₀.ρ v + q₀.L := by
  have := transfer_conservation C h
  omega

/-! ## §2. Inclusion dans la garde, témoins S9b -/

/-- ★ **Inclusion** : toute charge atteinte par le circuit l'est sous la garde centrale de
plafond `S = Σ ρ₀ + L₀`, lisant l'émission couverte (`guard_simulates`). -/
theorem transfer_reach_le_guard (C : Circ V α) (q₀ : St V) (r : ℕ) :
    ∀ w q, run (circ C) q₀ w = some q →
      Reach (tickOp .stock r) (emc C) (guard (∑ v, q₀.ρ v + q₀.L) (emc C)) q₀.L q.L :=
  guard_simulates (circ C) St.L (tickOp .stock r) (emc C) _ q₀
    (fun q q' h => by cases h; rfl)
    (fun q q' a h => (tstep_spec h).2.1)
    (fun w q h => by rw [run_circ] at h; exact transfer_cap C h)

end Circuit

/-! ### Les témoins S9b : chaîne F (0) → R (1) → P (2)

Lettres `x₀, x₁` (`0, 1`) : F paie R, 1 droit exigé ; `y₀, y₁` (`2, 3`) : R paie P, 1 droit
exigé, P émet 1 et le brûle. -/

/-- Le circuit S9b. -/
def s9b : Circ (Fin 3) (Fin 4) where
  pay := fun a => if a.val < 2 then (0, 1) else (1, 2)
  req := fun _ => 1
  em := fun a => if a.val < 2 then 0 else 1
  cov := fun _ => true

/-- ★ **Non maximal** (S9b) : dotation `(2, 0, 0)`, mot `x₀ y₀` puis `y₁` : à la charge `1`, le
circuit refuse `y₁` (R n'a plus de droit), la garde de plafond `2` l'admet. -/
theorem transfer_not_maximal :
    run (tstep s9b) ⟨![2, 0, 0], 0, 0⟩ [0, 2] = some ⟨![1, 0, 0], 1, 0⟩ ∧
      tstep s9b ⟨![1, 0, 0], 1, 0⟩ 3 = none ∧ guard 2 (emc s9b) 1 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- ★ **Droits mal placés** : les mêmes `2` droits chez le producteur P ; le circuit n'admet
aucune lettre, la garde centrale de plafond `2` admet les quatre. -/
theorem transfer_misplaced :
    (∀ a, tstep s9b ⟨![0, 0, 2], 0, 0⟩ a = none) ∧
      run (closedLoop (tickOp .stock 0) (emc s9b) (guard 2 (emc s9b))) 0
        [some 0, some 1, some 2, some 3] = some 2 := by
  refine ⟨by decide, by decide⟩

/-! ## §3. Jonction avec la couverture : fuite et réserve d'émission -/

section Leak

variable {V α : Type*} [DecidableEq V] [Fintype V]

/-- ★ La charge totale (couverte et non couverte) ne dépasse pas les droits émis plus la
fuite. -/
theorem transfer_leak_le (C : Circ V α) {w : List α} {q₀ q : St V}
    (h : run (tstep C) q₀ w = some q) :
    q.L + q.Lu ≤ ∑ v, q₀.ρ v + q₀.L + q₀.Lu + leak C w := by
  obtain ⟨h1, h2, h3⟩ := run_spec C w q₀ q h
  omega

/-- ★ **Réserve d'émission** : si la fuite d'une période est au plus `M` et que le registre
n'émet que `S ≤ cap − M` droits, la charge totale reste sous le plafond. -/
theorem issuance_reserve (C : Circ V α) {w : List α} {ρ₀ : V → ℕ} {q : St V} {M cap : ℕ}
    (h : run (tstep C) ⟨ρ₀, 0, 0⟩ w = some q) (hM : leak C w ≤ M)
    (hcap : ∑ v, ρ₀ v + M ≤ cap) : q.L + q.Lu ≤ cap := by
  have := transfer_leak_le C h
  simp only [add_zero] at this
  omega

omit [Fintype V] in
/-- ★ Les lettres que le circuit ne peut **jamais** refuser sont exactement celles qui
n'exigent rien et dont l'émission n'est pas couverte (ou nulle) : avec `em > 0`, ce sont les
ventes d'émetteurs non adhérents, soit les sources incontrôlables de `ReserveCoverage` §1. -/
theorem uncovered_emitters_unc (C : Circ V α) (a : α) :
    (∀ q, tstep C q a ≠ none) ↔ C.req a = 0 ∧ (C.cov a = false ∨ C.em a = 0) := by
  constructor
  · intro h
    have h0 := h ⟨fun _ => 0, 0, 0⟩
    unfold tstep at h0
    by_cases hr : C.req a ≤ 0
    · refine ⟨by omega, ?_⟩
      by_cases hc : C.cov a = true
      · right
        by_contra hem
        apply h0
        simp only [hr, hc, if_true]
        rw [if_neg]
        simp [xfer, Function.update_apply]
        omega
      · left
        simpa using hc
    · exact absurd (by simp [hr]) h0
  · rintro ⟨hr, hc⟩ q
    unfold tstep
    rw [if_pos (by omega)]
    rcases hc with hc | hc
    · simp [hc]
    · split_ifs <;> simp_all

end Leak

/-! ## §4. T-M12-1 pour le transfert -/

section Settle

variable {V α : Type*} [DecidableEq V] [Fintype V]

/-- ★ Un règlement intégral par transfert depuis une dotation `ρ` implique la porte centrale :
émission couverte cumulée `≤ Σ ρ`. -/
theorem transfer_settles_imp_central (C : Circ V α) {w : List α} {ρ : V → ℕ}
    (h : (run (tstep C) ⟨ρ, 0, 0⟩ w).isSome) : cumE C w ≤ ∑ v, ρ v := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  have := (run_spec C w _ q hq).1
  simp only at this
  omega

omit [Fintype V] in
theorem tstep_req_le {C : Circ V α} {q q' : St V} {a : α} (h : tstep C q a = some q') :
    C.req a ≤ q.ρ (C.pay a).1 := by
  unfold tstep at h
  split_ifs at h with h1 <;> exact h1

omit [Fintype V] in
theorem tstep_other {C : Circ V α} {q q' : St V} {a : α} (h : tstep C q a = some q') {v : V}
    (hp : v ≠ (C.pay a).1) (hr : v ≠ (C.pay a).2) : q'.ρ v = q.ρ v := by
  unfold tstep at h
  split_ifs at h <;> cases h <;> simp [xfer, Function.update_apply, hp, hr]

/-- La chaîne F (0) → R (1) → P (2) : `x` (`0`) = F paie R, `y` (`1`) = R paie P, P brûle 1. -/
def chain : Circ (Fin 3) (Fin 2) where
  pay := fun a => if a = 0 then (0, 1) else (1, 2)
  req := fun _ => 1
  em := fun a => if a = 0 then 0 else 1
  cov := fun _ => true

/-- ★ **T-M12-1 est faux en règlement séquentiel.** Mot `[y, x]`, `S = 1` : la porte centrale
règle (`cumE = 1`), aucune dotation de total `1` ne règle par transfert (R doit payer avant
d'avoir reçu) ; l'ordre `[x, y]` se règle depuis `(1, 0, 0)`. -/
theorem transfer_seq_strict :
    cumE chain [1, 0] ≤ 1 ∧
      (¬ ∃ ρ : Fin 3 → ℕ, ∑ v, ρ v = 1 ∧ (run (tstep chain) ⟨ρ, 0, 0⟩ [1, 0]).isSome) ∧
        (run (tstep chain) ⟨![1, 0, 0], 0, 0⟩ [0, 1]).isSome := by
  refine ⟨by decide, ?_, by decide⟩
  rintro ⟨ρ, hs, h⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  rw [run_cons] at hq
  cases h1 : tstep chain ⟨ρ, 0, 0⟩ 1 with
  | none => rw [h1] at hq; cases hq
  | some q₁ =>
    rw [h1, Option.bind_some, run_singleton] at hq
    have r1 : 1 ≤ ρ 1 := tstep_req_le h1
    have r2 : 1 ≤ q₁.ρ 0 := tstep_req_le hq
    have e0 : q₁.ρ 0 = ρ 0 := tstep_other h1 (by decide) (by decide)
    rw [Fin.sum_univ_three] at hs
    omega

/-- Position nette d'un détenteur sur un mot : payé + brûlé − reçu. -/
def netPos (C : Circ V α) (w : List α) (v : V) : ℤ :=
  (w.map fun a => ((if (C.pay a).1 = v then C.req a else 0 : ℕ) : ℤ) -
    ((if (C.pay a).2 = v then C.req a else 0 : ℕ) : ℤ) +
      ((if (C.pay a).2 = v then emc C a else 0 : ℕ) : ℤ)).sum

/-- ★ Les positions nettes somment à l'émission couverte cumulée. -/
theorem sum_netPos (C : Circ V α) : ∀ w : List α, ∑ v, netPos C w v = cumE C w
  | [] => by simp [netPos, cumE]
  | a :: w => by
    have ih := sum_netPos C w
    simp only [netPos, cumE, List.map_cons, List.sum_cons, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at ih ⊢
    rw [ih]
    push_cast
    simp [Finset.sum_ite_eq]

omit [Fintype V] in
theorem xfer_cast {ρ : V → ℕ} {p r : V} {k : ℕ} (hk : k ≤ ρ p) (v : V) :
    (xfer ρ p r k v : ℤ) = ρ v - (if p = v then k else 0 : ℕ) + (if r = v then k else 0 : ℕ) := by
  unfold xfer
  rcases eq_or_ne v r with rfl | hvr
  · rw [Function.update_self]
    rcases eq_or_ne v p with rfl | hvp
    · simp [Nat.sub_add_cancel hk]
    · rw [Function.update_of_ne hvp]
      simp [Ne.symm hvp]
  · rw [Function.update_of_ne hvr]
    rcases eq_or_ne v p with rfl | hvp
    · simp [Ne.symm hvr, Nat.cast_sub hk]
    · rw [Function.update_of_ne hvp]
      simp [Ne.symm hvr, Ne.symm hvp]

omit [Fintype V] in
/-- Un pas, lu sur les soldes : `ρ' v = ρ v − (payé + brûlé − reçu)`. -/
theorem tstep_cast {C : Circ V α} {q q' : St V} {a : α} (h : tstep C q a = some q') (v : V) :
    (q'.ρ v : ℤ) = q.ρ v - (((if (C.pay a).1 = v then C.req a else 0 : ℕ) : ℤ) -
      ((if (C.pay a).2 = v then C.req a else 0 : ℕ) : ℤ) +
        ((if (C.pay a).2 = v then emc C a else 0 : ℕ) : ℤ)) := by
  unfold tstep at h
  simp only [emc]
  generalize C.pay a = pr at h ⊢
  obtain ⟨p, r⟩ := pr
  dsimp only at h ⊢
  split_ifs at h with h1 h2 h3 <;> cases h <;> dsimp only
  · rcases eq_or_ne r v with rfl | hrv
    · rw [Function.update_self, Nat.cast_sub h3, xfer_cast h1]
      simp only [if_true, h2]
      ring
    · rw [Function.update_of_ne (Ne.symm hrv), xfer_cast h1]
      simp only [hrv, if_false, Nat.cast_zero]
      ring
  · rw [xfer_cast h1]
    simp only [h2, if_false, Bool.false_eq_true, ite_self, Nat.cast_zero]
    ring

omit [Fintype V] in
/-- ★ État final d'un règlement séquentiel : `ρ_fin = ρ₀ − netPos`. -/
theorem run_netPos (C : Circ V α) :
    ∀ (w : List α) (q₀ q : St V), run (tstep C) q₀ w = some q →
      ∀ v, (q.ρ v : ℤ) = q₀.ρ v - netPos C w v
  | [], q₀, q, h, v => by cases h; simp [netPos]
  | a :: w, q₀, q, h, v => by
    rw [run_cons] at h
    cases h1 : tstep C q₀ a with
    | none => rw [h1] at h; cases h
    | some q₁ =>
      rw [h1, Option.bind_some] at h
      rw [run_netPos C w q₁ q h v, tstep_cast h1 v]
      simp only [netPos, List.map_cons, List.sum_cons]
      ring

omit [Fintype V] in
/-- ★ Règlement séquentiel ⇒ compensation : chaque détenteur couvre sa position nette. -/
theorem seq_imp_net (C : Circ V α) {w : List α} {ρ : V → ℕ}
    (h : (run (tstep C) ⟨ρ, 0, 0⟩ w).isSome) (v : V) : netPos C w v ≤ ρ v := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
  have := run_netPos C w _ q hq v
  have : (0 : ℤ) ≤ q.ρ v := Nat.cast_nonneg _
  simp only at *
  omega

omit [DecidableEq V] in
/-- ★ **Compensation par période** : une dotation de total `S` couvre les positions nettes `x`
ssi `Σ_v max(0, x_v) ≤ S`. -/
theorem net_settle_iff [Nonempty V] [DecidableEq V] (x : V → ℤ) (S : ℕ) :
    (∃ ρ : V → ℕ, ∑ v, ρ v = S ∧ ∀ v, x v ≤ ρ v) ↔ ∑ v, max 0 (x v) ≤ S := by
  constructor
  · rintro ⟨ρ, hs, hx⟩
    calc ∑ v, max 0 (x v) ≤ ∑ v, (ρ v : ℤ) :=
          Finset.sum_le_sum fun v _ => max_le (Nat.cast_nonneg _) (hx v)
      _ = S := by rw [← hs, Nat.cast_sum]
  · intro h
    obtain ⟨v₀⟩ := ‹Nonempty V›
    have ht : ((∑ v, (x v).toNat : ℕ) : ℤ) = ∑ v, max 0 (x v) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [Int.toNat_eq_max, max_comm]
    have hle : ∑ v, (x v).toNat ≤ S := by
      have : ((∑ v, (x v).toNat : ℕ) : ℤ) ≤ S := ht ▸ h
      exact_mod_cast this
    refine ⟨fun v => (x v).toNat + if v = v₀ then S - ∑ v, (x v).toNat else 0, ?_, fun v => ?_⟩
    · rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      omega
    · have := Int.self_le_toNat (x v)
      push_cast
      split_ifs <;> omega

/-- ★ **T-M12-1 pour le transfert, forme compensée** : sans droit échoué (positions nettes
`≥ 0`), une dotation de total `S` couvre les positions nettes ssi la porte centrale de plafond
`S` règle. -/
theorem net_transfer_iff_central [Nonempty V] (C : Circ V α) (w : List α) (S : ℕ)
    (h : ∀ v, 0 ≤ netPos C w v) :
    (∃ ρ : V → ℕ, ∑ v, ρ v = S ∧ ∀ v, netPos C w v ≤ ρ v) ↔ cumE C w ≤ S := by
  rw [net_settle_iff, Finset.sum_congr rfl fun v _ => max_eq_right (h v), sum_netPos]
  exact Nat.cast_le

/-- ★ L'écart à la porte centrale est la masse des droits échoués :
`Σ max(0, x) = cumE + Σ max(0, −x)`. -/
theorem stranded_gap (C : Circ V α) (w : List α) :
    ∑ v, max 0 (netPos C w v) = cumE C w + ∑ v, max 0 (-netPos C w v) := by
  rw [← sum_netPos, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases le_total 0 (netPos C w v) with h | h
  · rw [max_eq_right h, max_eq_left (by omega)]; ring
  · rw [max_eq_left h, max_eq_right (by omega)]; ring

end Settle

/-- Le circuit T4 : `0` = F paie 2 droits à R ; `1` = R paie 1 droit à P, P brûle 1. -/
def stranded : Circ (Fin 3) (Fin 2) where
  pay := fun a => if a = 0 then (0, 1) else (1, 2)
  req := fun a => if a = 0 then 2 else 1
  em := fun a => if a = 0 then 0 else 1
  cov := fun _ => true

/-- ★ **Droits échoués** (T4) : positions nettes `(2, −1, 0)`, `cumE = 1` mais
`Σ max(0, x) = 2` ; le règlement exige une dotation de `2` (R garde un droit inutilisé),
la porte centrale `1`. -/
theorem stranded_witness :
    (∀ v, netPos stranded [0, 1] v = ![2, -1, 0] v) ∧ cumE stranded [0, 1] = 1 ∧
      ∑ v, max 0 (netPos stranded [0, 1] v) = 2 ∧
      (run (tstep stranded) ⟨![2, 0, 0], 0, 0⟩ [0, 1]).isSome ∧
      ¬ ∃ ρ : Fin 3 → ℕ, ∑ v, ρ v = 1 ∧ (run (tstep stranded) ⟨ρ, 0, 0⟩ [0, 1]).isSome := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨ρ, hs, h⟩
  have := seq_imp_net stranded h 0
  have h0 : netPos stranded [0, 1] 0 = 2 := by decide
  rw [Fin.sum_univ_three] at hs
  omega

end TransferCircuit
