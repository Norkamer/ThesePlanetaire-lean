/-
  ThesePlanetaire/DualDAG.lean
  DualDAG v2 — Couplage monétaire-physique par budget partagé de futures.

  Le DualDAG v1 (filtre par-arête sans interaction) a échoué : l'opérateur
  de clearing était découplé et physical_capacity était un C_plan renommé.

  DualDAG v2 corrige cela :
  - FuturePool : budget par sommet (futures détenues, acquises par opt-in)
  - coupled_operator : filtre les arêtes par budget PARTAGÉ au sommet source
    (la charge = somme des demandes de TOUTES les arêtes au même sommet)
  - isAdmissible(current, e) : point fixe contextuel depuis current ∪ {e}

  Le test d'admission est un recompute global de faisabilité, pas un
  verrouillage incrémental : current peut aussi être évincé si le budget
  est dépassé.

  Scope v2 : le couplage (budget partagé → rejet émergent + order-dependence)
  est prouvé. L'endogénéité du budget (opt-in → holdings) est différée.

  Résultats principaux :
  - rejection_is_emergent : transaction individuellement OK mais rejetée
    car d'autres au même sommet épuisent le budget partagé
  - admission_is_order_dependent : l'ordre de soumission détermine quelles
    transactions sont admises (Parikh k≥1)

  Références :
  - Eisenberg-Noe 2001 (Management Science 47(2)) — clearing par point fixe
  - Bech & Soramäki 2001 (Bank of Finland DP 9/2001) — validation RTGS
  - Nordhaus 2015 (AER 105(4)) — climate clubs et opt-in
  - Wollmer 1970 (RAND RM-6143-PR) — multicommodity flow / joint capacity
-/

import ThesePlanetaire.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DualDAG

/-! ### 1. FuturePool — budget partagé de futures par sommet

  Budget à chaque sommet v = futures détenues. Pas de paramètre C_plan. -/

/-- Pool de futures planétaires : budget par sommet.
    holdings(v) = futures détenues par v (acquises par opt-in). -/
structure FuturePool (V : Type*) [Fintype V] [DecidableEq V] where
  holdings : V → ℤ
  h_holdings_nonneg : ∀ v, 0 ≤ holdings v

/-! ### 2. Charge et opérateur couplé

  vertex_load = somme des demandes des arêtes sortantes activées depuis v.
  coupled_operator = filtre les arêtes dont la charge cumulée au sommet source
  dépasse le budget. Le couplage : la charge inclut TOUTES les arêtes au même
  sommet, pas seulement l'arête testée. -/

/-- Charge au sommet v : somme des demandes de toutes les arêtes dans S
    ayant v comme source. -/
def vertex_load (demands : V × V → ℤ) (S : ActivationState V) (v : V) : ℤ :=
  (S.filter (fun e => e.1 = v)).sum demands

/-- Dans un graphe à arête sortante unique (graphe fonctionnel), le filtre
    des arêtes de source v est le singleton {(v, σv)} s'il est dans S, sinon ∅.
    Localité de la charge : la charge d'un sommet ne dépend que de la présence
    de son unique arête sortante — cœur structurel du point fixe uniforme (Q9),
    prépare la mise à jour per-agent du chantier rétroaction-regex. -/
lemma filter_src_eq_of_unique_outgoing {V : Type*} [DecidableEq V]
    (ambient : Finset (V × V)) (v : V) (σv : V)
    (h_unique : ∀ {e : V × V}, e ∈ ambient → e.1 = v → e = (v, σv))
    (S : Finset (V × V)) (hS : S ⊆ ambient) :
    S.filter (fun e => e.1 = v) = if (v, σv) ∈ S then {(v, σv)} else ∅ := by
  by_cases h : (v, σv) ∈ S
  · rw [if_pos h]
    apply Finset.ext
    intro e
    constructor
    · intro he
      have heS : e ∈ S := (Finset.mem_filter.mp he).1
      have hev : e.1 = v := (Finset.mem_filter.mp he).2
      have heq := h_unique (hS heS) hev
      exact Finset.mem_singleton.mpr heq
    · intro he
      rw [Finset.mem_singleton.mp he]
      exact Finset.mem_filter.mpr ⟨h, rfl⟩
  · rw [if_neg h]
    rw [Finset.filter_eq_empty_iff]
    intro e heS hev
    have heq := h_unique (hS heS) hev
    exact h (heq ▸ heS)

/-- Variante cible : dans un graphe à arête entrante unique (prédécesseur
    explicite predv), le filtre des arêtes de cible v est le singleton
    {(predv, v)} s'il est dans S, sinon ∅. -/
lemma filter_tgt_eq_of_unique_incoming {V : Type*} [DecidableEq V]
    (ambient : Finset (V × V)) (v : V) (predv : V)
    (h_unique : ∀ {e : V × V}, e ∈ ambient → e.2 = v → e = (predv, v))
    (S : Finset (V × V)) (hS : S ⊆ ambient) :
    S.filter (fun e => e.2 = v) = if (predv, v) ∈ S then {(predv, v)} else ∅ := by
  by_cases h : (predv, v) ∈ S
  · rw [if_pos h]
    apply Finset.ext
    intro e
    constructor
    · intro he
      have heS : e ∈ S := (Finset.mem_filter.mp he).1
      have hev : e.2 = v := (Finset.mem_filter.mp he).2
      have heq := h_unique (hS heS) hev
      exact Finset.mem_singleton.mpr heq
    · intro he
      rw [Finset.mem_singleton.mp he]
      exact Finset.mem_filter.mpr ⟨h, rfl⟩
  · rw [if_neg h]
    rw [Finset.filter_eq_empty_iff]
    intro e heS hev
    have heq := h_unique (hS heS) hev
    exact h (heq ▸ heS)

/-- Test antitone ⟹ filtre idempotent : si le test ne peut que devenir plus
    facile quand l'état décroît, alors Φ(Φ(S)) = Φ(S) (convergence en un pas).
    La famille ANTITONE en r (plus d'entrées reçues ne peut jamais aider)
    garde l'idempotence — la cellule {P3} du trilemme est un théorème
    générique, pas un accident du témoin. -/
lemma filter_operator_idempotent_of_antitone {α : Type*} [DecidableEq α]
    (test : Finset α → α → Prop) [∀ S e, Decidable (test S e)]
    (h_antitone : ∀ {S T : Finset α} {e : α}, T ⊆ S → test S e → test T e)
    (S : Finset α) :
    (S.filter (test S)).filter (test (S.filter (test S))) = S.filter (test S) := by
  apply Finset.Subset.antisymm
  · intro e he
    exact (Finset.mem_filter.mp he).1
  · intro e he
    have h1 := (Finset.mem_filter.mp he).2
    have h2 : test (S.filter (test S)) e :=
      h_antitone (Finset.filter_subset _ S) h1
    exact Finset.mem_filter.mpr ⟨he, h2⟩

/-- Opérateur de clearing couplé : garde les arêtes dont la charge cumulée
    au sommet source ne dépasse pas le budget (holdings). -/
def coupled_operator (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) : ActivationState V :=
  S.filter (fun e => vertex_load demands S e.1 ≤ pool.holdings e.1)

/-- L'opérateur couplé est contractif : Φ(S) ⊆ S. -/
lemma coupled_operator_contractive (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) :
    coupled_operator pool demands S ⊆ S :=
  fun _ he => (mem_filter.mp he).1

/-! ### 3. Chaîne descendante paramétrisée

  Chaîne descendante depuis un état initial arbitraire.
  Stabilise en ≤ |init| pas (pigeonhole). -/

/-- Chaîne descendante depuis un état initial. -/
def descending_chain (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) : ℕ → ActivationState V
  | 0     => init
  | n + 1 => coupled_operator pool demands (descending_chain pool demands init n)

/-- La chaîne descendante est décroissante. -/
lemma descending_chain_antimono (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) (n : ℕ) :
    descending_chain pool demands init (n + 1) ⊆ descending_chain pool demands init n :=
  coupled_operator_contractive pool demands _

/-- La chaîne descendante stabilise en au plus |init| pas (pigeonhole). -/
theorem descending_chain_stabilizes (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    ∃ n, n ≤ init.card ∧
      descending_chain pool demands init n = descending_chain pool demands init (n + 1) := by
  by_contra h
  push Not at h
  let N := init.card
  have h_strict : ∀ n, n ≤ N →
      descending_chain pool demands init (n + 1) ⊂ descending_chain pool demands init n := by
    intro n hn
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨descending_chain_antimono pool demands init n,
           fun h_eq => absurd h_eq.symm (h n hn)⟩
  have h_ind : ∀ m, m ≤ N → (descending_chain pool demands init m).card ≤ N - m := by
    intro m hm
    induction m with
    | zero => simp [descending_chain, N]
    | succ m ih =>
      have h_lt := Finset.card_lt_card (h_strict m (by omega))
      have h_ih := ih (by omega)
      omega
  have h_card_N : (descending_chain pool demands init N).card = 0 := by
    have := h_ind N (le_refl N); omega
  have h_empty := Finset.card_eq_zero.mp h_card_N
  have h_strict_N := h_strict N (le_refl N)
  rw [h_empty] at h_strict_N
  exact absurd (Finset.subset_empty.mp h_strict_N.subset) h_strict_N.ne

/-- Si la chaîne stabilise à l'étape n, c'est un point fixe de Φ. -/
theorem descending_chain_fixed_point (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) (n : ℕ)
    (h_stab : descending_chain pool demands init n = descending_chain pool demands init (n + 1)) :
    coupled_operator pool demands (descending_chain pool demands init n) =
      descending_chain pool demands init n := by
  show descending_chain pool demands init (n + 1) = descending_chain pool demands init n
  exact h_stab.symm

/-- La stabilité se propage : chain(n+k) = chain(n) pour tout k. -/
lemma descending_chain_stable_propagates (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) (n k : ℕ)
    (h_stab : descending_chain pool demands init n = descending_chain pool demands init (n + 1)) :
    descending_chain pool demands init (n + k) = descending_chain pool demands init n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : descending_chain pool demands init (n + (k + 1)) =
      coupled_operator pool demands (descending_chain pool demands init (n + k)) := rfl
    rw [h1, ih]
    exact descending_chain_fixed_point pool demands init n h_stab

/-- La chaîne à l'étape init.card est un point fixe. -/
theorem descending_chain_at_card_fixpoint (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    coupled_operator pool demands (descending_chain pool demands init init.card) =
      descending_chain pool demands init init.card := by
  obtain ⟨n, hn, h_stab⟩ := descending_chain_stabilizes pool demands init
  have h_prop := descending_chain_stable_propagates pool demands init n (init.card - n) h_stab
  rw [Nat.add_sub_cancel' hn] at h_prop
  rw [h_prop]
  exact descending_chain_fixed_point pool demands init n h_stab

/-- Faisabilité conjointe MAX+MIN :
    MAX = budgets planétaires comme plafonds (coupled_operator) ;
    MIN = engagements minimum cross-account (non capturés par coupled_operator).
    La voie intra-compte garantit MAX mais pas MIN en présence d'obligations de flux. -/
def isJointlyFeasible (pool : FuturePool V) (commitments : V → ℤ)
    (demands : V × V → ℤ) (S : ActivationState V) : Prop :=
  (∀ e ∈ S, vertex_load demands S e.1 ≤ pool.holdings e.1) ∧
  (∀ v : V, (S.filter (fun e => e.2 = v)).sum demands ≥ commitments v)

/-! ### 4. Point fixe contextuel et admission

  isAdmissible(current, e) = test de faisabilité globale : si on ajoute e
  à l'état courant, le point fixe du clearing couplé contient-il encore e ?
  C'est un recompute global (pas un verrouillage incrémental de current). -/

/-- Point fixe contextuel : itère Φ depuis current ∪ {e}. -/
def contextual_fixpoint (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V) : ActivationState V :=
  let init := current ∪ {e}
  descending_chain pool demands init init.card

/-- Test d'admission : e est admissible dans l'état current ssi e appartient
    au point fixe contextuel calculé depuis current ∪ {e}. -/
@[reducible] def isAdmissible (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V) : Prop :=
  e ∈ contextual_fixpoint pool demands current e

/-! ### 5. Propriétés du point fixe -/

/-- Au point fixe, chaque arête satisfait la contrainte de budget. -/
lemma fixpoint_satisfies_budget (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V)
    (h_fix : coupled_operator pool demands S = S) :
    ∀ e ∈ S, vertex_load demands S e.1 ≤ pool.holdings e.1 := by
  intro e he
  have : e ∈ coupled_operator pool demands S := by rw [h_fix]; exact he
  exact (mem_filter.mp this).2

/-! ### 6. Rejet émergent

  Le théorème fondamental du couplage : une transaction individuellement
  faisable est rejetée parce que d'autres transactions au même sommet
  épuisent le budget partagé. Ce n'est pas de l'arithmétique sur ℤ — c'est
  une propriété de l'opérateur coupled_operator et du point fixe contextuel.

  Contre-exemple concret sur Fin 3 :
  - Sommets A=0, B=1, C=2. Pool CO₂ : holdings(A)=5.
  - e₁(A→B) demande 3, e₂(A→C) demande 4.
  - isAdmissible ∅ e₂ : Φ({e₂}), load(A)=4≤5, fixpt={e₂}, e₂∈{e₂} ✓
  - isAdmissible {e₁} e₂ : Φ({e₁,e₂}), load(A)=7>5, fixpt=∅, e₂∉∅ ✗ -/

theorem rejection_is_emergent :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (e₁ e₂ : Fin 3 × Fin 3) (current : ActivationState (Fin 3)),
      isAdmissible pool demands current e₂ ∧
      ¬ isAdmissible pool demands (current ∪ {e₁}) e₂ := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    ((0 : Fin 3), (1 : Fin 3)),
    ((0 : Fin 3), (2 : Fin 3)),
    ∅, ?_, ?_⟩
  · decide
  · decide

/-! ### 7. Exclusion mutuelle par contexte

  Même paire de transactions, chacune individuellement admissible,
  mais mutuellement exclusives : la présence de l'une empêche l'autre.
  L'admissibilité de e₂ dépend de si e₁ est déjà dans current.

  Le point fixe de {e₁, e₂} est ∅ (load(A)=7>5 → les deux évincées).
  Le test isAdmissible est un recompute global, pas un verrouillage
  incrémental : ni e₁ ni e₂ ne « reste » dans le point fixe. -/

theorem admission_is_order_dependent :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (e₁ e₂ : Fin 3 × Fin 3),
      isAdmissible pool demands ∅ e₁ ∧
      isAdmissible pool demands ∅ e₂ ∧
      ¬ isAdmissible pool demands {e₁} e₂ ∧
      ¬ isAdmissible pool demands {e₂} e₁ := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    ((0 : Fin 3), (1 : Fin 3)),
    ((0 : Fin 3), (2 : Fin 3)),
    ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-! ### 8. L'ordre de soumission détermine l'ensemble admis

  Sous sémantique test-and-keep (on tente chaque transaction dans l'ordre,
  on l'admet si le recompute global la contient, sinon on passe), deux
  ordres de la même paire produisent des ensembles admis différents :
  - [e₁, e₂] → {e₁} (e₁ admise, e₂ rejetée car 3+4>5)
  - [e₂, e₁] → {e₂} (e₂ admise, e₁ rejetée car 4+3>5)
  C'est la dépendance à l'ordre au sens de Parikh (k≥1). -/

/-- Sémantique test-and-keep : fold séquentiel qui admet e si
    isAdmissible(current, e), sinon passe. -/
def admissionFold (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) : ActivationState V :=
  edges.foldl (fun cur e =>
    if isAdmissible pool demands cur e then cur ∪ {e} else cur) ∅

private lemma admissionFold_subset_aux (pool : FuturePool V) (demands : V × V → ℤ)
    (remaining : List (V × V)) (cur : ActivationState V) (target : Finset (V × V))
    (h_cur : cur ⊆ target) (h_rem : ∀ x ∈ remaining, x ∈ target) :
    remaining.foldl (fun c e =>
      if isAdmissible pool demands c e then c ∪ {e} else c) cur ⊆ target := by
  induction remaining generalizing cur with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd : hd ∈ target := h_rem hd (.head tl)
    have h_tl : ∀ x ∈ tl, x ∈ target := fun x hx => h_rem x (.tail hd hx)
    split
    · exact ih (cur ∪ {hd})
        (Finset.union_subset h_cur (Finset.singleton_subset_iff.mpr h_hd)) h_tl
    · exact ih cur h_cur h_tl

theorem admissionFold_subset (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    admissionFold pool demands edges ⊆ edges.toFinset := by
  exact admissionFold_subset_aux pool demands edges ∅ edges.toFinset
    (Finset.empty_subset _) (fun e he => List.mem_toFinset.mpr he)

/-! ### 8b. admissionFold produces a coupled_operator fixpoint

  The fold result always satisfies the budget constraint at every vertex.
  Proof: induction on the edge list with invariant "cur is a fixpoint of Φ".
  The all-or-nothing vertex-load mechanism is the key: if isAdmissible(cur, e),
  then e survives coupled_operator(cur ∪ {e}), and since all edges at e.1
  share the same vertex_load, existing cur edges at e.1 survive too. -/

private lemma descending_chain_mono_rev (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) {m n : ℕ} (h : n ≤ m) :
    descending_chain pool demands init m ⊆ descending_chain pool demands init n := by
  induction m with
  | zero => have := Nat.le_zero.mp h; subst this; exact Finset.Subset.refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact Finset.Subset.refl _
    · exact (descending_chain_antimono pool demands init k).trans (ih (Nat.lt_succ_iff.mp hlt))

private lemma isAdmissible_implies_in_step1 (pool : FuturePool V) (demands : V × V → ℤ)
    (cur : ActivationState V) (e : V × V) (h : isAdmissible pool demands cur e) :
    e ∈ coupled_operator pool demands (cur ∪ {e}) := by
  unfold isAdmissible contextual_fixpoint at h
  set init := cur ∪ {e} with hinit
  have hcard : 1 ≤ init.card := by
    apply Finset.card_pos.mpr
    exact ⟨e, mem_union_right cur (mem_singleton_self e)⟩
  have : descending_chain pool demands init init.card ⊆
         descending_chain pool demands init 1 :=
    descending_chain_mono_rev pool demands init hcard
  exact this h

omit [Fintype V] in
private lemma vertex_load_union_singleton_ne (demands : V × V → ℤ)
    (cur : ActivationState V) (e : V × V) (v : V) (hne : e.1 ≠ v) :
    vertex_load demands (cur ∪ {e}) v = vertex_load demands cur v := by
  unfold vertex_load
  congr 1
  ext f
  simp only [mem_filter, mem_union, mem_singleton]
  constructor
  · rintro ⟨hf | hf, hfv⟩
    · exact ⟨hf, hfv⟩
    · subst hf; exact absurd hfv hne
  · rintro ⟨hf, hfv⟩
    exact ⟨Or.inl hf, hfv⟩

private lemma fixpoint_union_of_admissible (pool : FuturePool V) (demands : V × V → ℤ)
    (cur : ActivationState V) (e : V × V)
    (hfix : coupled_operator pool demands cur = cur)
    (hadm : isAdmissible pool demands cur e) :
    coupled_operator pool demands (cur ∪ {e}) = cur ∪ {e} := by
  ext f
  simp only [coupled_operator, mem_filter, mem_union, mem_singleton]
  constructor
  · intro ⟨hf, _⟩; exact hf
  · intro hf
    refine ⟨hf, ?_⟩
    have he_load := (mem_filter.mp
      (isAdmissible_implies_in_step1 pool demands cur e hadm)).2
    rcases hf with hf_cur | hf_eq
    · by_cases hv : e.1 = f.1
      · rw [← hv]; exact he_load
      · rw [vertex_load_union_singleton_ne demands cur e f.1 hv]
        have : f ∈ coupled_operator pool demands cur := by rw [hfix]; exact hf_cur
        exact (mem_filter.mp this).2
    · subst hf_eq; exact he_load

private lemma admissionFold_fixpoint_aux (pool : FuturePool V) (demands : V × V → ℤ)
    (remaining : List (V × V)) (cur : ActivationState V)
    (hfix : coupled_operator pool demands cur = cur) :
    coupled_operator pool demands
      (remaining.foldl (fun c e =>
        if isAdmissible pool demands c e then c ∪ {e} else c) cur) =
      remaining.foldl (fun c e =>
        if isAdmissible pool demands c e then c ∪ {e} else c) cur := by
  induction remaining generalizing cur with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    split
    · case isTrue hadm =>
      exact ih (cur ∪ {hd}) (fixpoint_union_of_admissible pool demands cur hd hfix hadm)
    · case isFalse _ =>
      exact ih cur hfix

theorem admissionFold_is_fixpoint (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    coupled_operator pool demands (admissionFold pool demands edges) =
      admissionFold pool demands edges := by
  unfold admissionFold
  exact admissionFold_fixpoint_aux pool demands edges ∅
    (by simp [coupled_operator])

theorem admissionFold_satisfies_budget (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    ∀ e ∈ admissionFold pool demands edges,
      vertex_load demands (admissionFold pool demands edges) e.1 ≤ pool.holdings e.1 :=
  fixpoint_satisfies_budget pool demands _ (admissionFold_is_fixpoint pool demands edges)

theorem admission_final_state_order_dependent :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (e₁ e₂ : Fin 3 × Fin 3),
      admissionFold pool demands [e₁, e₂] ≠
      admissionFold pool demands [e₂, e₁] := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    ((0 : Fin 3), (1 : Fin 3)),
    ((0 : Fin 3), (2 : Fin 3)),
    ?_⟩
  · decide

/-! ### 9. Résultats structurels — caractérisation de l'order-dependence

  Les théorèmes §6-§8 exhibent l'order-dependence sur un exemple concret (Fin 3).
  Les théorèmes ci-dessous la caractérisent pour des données ARBITRAIRES :
  conditions nécessaires et suffisantes sur pool/demands pour que l'admission
  soit order-dependent. Transforme un témoin d'existence en résultat structurel.

  Théorème central : pour deux arêtes e₁, e₂ au même sommet source v,
  l'admission est order-dependent ssi chaque arête est individuellement
  admissible mais leur demande conjointe dépasse le budget.
  C'est une propriété de l'opérateur coupled_operator, pas de l'arithmétique. -/

/-- vertex_load sur un singleton : la charge est exactement la demande. -/
lemma vertex_load_singleton (demands : V × V → ℤ) (e : V × V) :
    vertex_load demands {e} e.1 = demands e := by
  unfold vertex_load
  have : ({e} : Finset (V × V)).filter (fun e' => e'.1 = e.1) = {e} :=
    Finset.filter_true_of_mem (fun x hx => by rw [Finset.mem_singleton.mp hx])
  rw [this, Finset.sum_singleton]

/-- vertex_load sur une paire au même sommet source. -/
lemma vertex_load_pair (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1) :
    vertex_load demands ({e₁, e₂} : Finset (V × V)) e₁.1 =
      demands e₁ + demands e₂ := by
  unfold vertex_load
  have h_filter : ({e₁, e₂} : Finset (V × V)).filter (fun e => e.1 = e₁.1) = {e₁, e₂} :=
    Finset.filter_true_of_mem (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact h_src.symm)
  rw [h_filter]
  rw [Finset.sum_insert (by simp [h_ne]), Finset.sum_singleton]

/-- Si la demande ≤ budget, l'opérateur couplé préserve le singleton. -/
lemma coupled_operator_singleton_of_le (pool : FuturePool V) (demands : V × V → ℤ)
    (e : V × V) (h : demands e ≤ pool.holdings e.1) :
    coupled_operator pool demands {e} = {e} := by
  unfold coupled_operator
  exact Finset.filter_true_of_mem (fun x hx => by
    rw [Finset.mem_singleton.mp hx, vertex_load_singleton]; exact h)

/-- Si la demande conjointe > budget au même sommet, l'opérateur couplé
    vide la paire. -/
lemma coupled_operator_pair_empty (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_over : demands e₁ + demands e₂ > pool.holdings e₁.1) :
    coupled_operator pool demands {e₁, e₂} = ∅ := by
  have h_load := vertex_load_pair demands e₁ e₂ h_ne h_src
  unfold coupled_operator
  have h_not₁ : ¬ (vertex_load demands {e₁, e₂} e₁.1 ≤ pool.holdings e₁.1) := by
    rw [h_load]; omega
  have h_not₂ : ¬ (vertex_load demands {e₁, e₂} e₂.1 ≤ pool.holdings e₂.1) := by
    rw [← h_src, h_load]; omega
  simp only [coupled_operator, Finset.filter_insert, Finset.filter_singleton,
    if_neg h_not₁, if_neg h_not₂, Finset.empty_union]

private lemma descending_chain_one (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    descending_chain pool demands init 1 = coupled_operator pool demands init := rfl

private lemma descending_chain_two (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    descending_chain pool demands init 2 =
      coupled_operator pool demands (coupled_operator pool demands init) := rfl

/-- Une arête est admissible depuis ∅ ssi sa demande ≤ budget. -/
theorem isAdmissible_empty_iff (pool : FuturePool V) (demands : V × V → ℤ)
    (e : V × V) :
    isAdmissible pool demands ∅ e ↔ demands e ≤ pool.holdings e.1 := by
  simp only [isAdmissible, contextual_fixpoint, Finset.empty_union,
    Finset.card_singleton, descending_chain_one]
  constructor
  · intro h_mem
    have := (Finset.mem_filter.mp h_mem).2
    rwa [vertex_load_singleton] at this
  · intro h
    rw [coupled_operator_singleton_of_le pool demands e h]
    exact Finset.mem_singleton_self e

/-- Deux arêtes au même sommet ne sont pas co-admissibles si la demande
    conjointe dépasse le budget. -/
theorem not_isAdmissible_pair (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_over : demands e₁ + demands e₂ > pool.holdings e₁.1) :
    ¬ isAdmissible pool demands {e₁} e₂ := by
  simp only [isAdmissible, contextual_fixpoint, Finset.singleton_union,
    Finset.card_pair h_ne]
  show e₂ ∉ coupled_operator pool demands
    (coupled_operator pool demands {e₁, e₂})
  rw [coupled_operator_pair_empty pool demands e₁ e₂ h_ne h_src h_over]
  simp [coupled_operator]

/-- **Caractérisation structurelle** : pour deux arêtes au même sommet,
    chacune individuellement admissible, l'admission est order-dependent
    ssi la demande conjointe dépasse le budget.

    Direction « budget insuffisant → order-dependent ». -/
theorem order_dependence_sufficient (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h₂ : demands e₂ ≤ pool.holdings e₂.1)
    (h_over : demands e₁ + demands e₂ > pool.holdings e₁.1) :
    admissionFold pool demands [e₁, e₂] ≠
    admissionFold pool demands [e₂, e₁] := by
  simp only [admissionFold, List.foldl_cons, List.foldl_nil]
  have h_adm₁ : isAdmissible pool demands ∅ e₁ :=
    (isAdmissible_empty_iff pool demands e₁).mpr h₁
  have h_adm₂ : isAdmissible pool demands ∅ e₂ :=
    (isAdmissible_empty_iff pool demands e₂).mpr (h_src ▸ h₂)
  have h_rej₂ : ¬ isAdmissible pool demands {e₁} e₂ :=
    not_isAdmissible_pair pool demands e₁ e₂ h_ne h_src h_over
  have h_rej₁ : ¬ isAdmissible pool demands {e₂} e₁ :=
    not_isAdmissible_pair pool demands e₂ e₁ h_ne.symm h_src.symm
      (by rw [add_comm, ← h_src]; exact h_over)
  simp only [h_adm₁, h_adm₂, h_rej₂, h_rej₁, if_true, if_false,
    Finset.empty_union]
  simp [h_ne]

/-- Si la demande conjointe ≤ budget, l'opérateur couplé préserve la paire. -/
lemma coupled_operator_pair_fixed (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_sum : demands e₁ + demands e₂ ≤ pool.holdings e₁.1) :
    coupled_operator pool demands {e₁, e₂} = {e₁, e₂} := by
  have h_load := vertex_load_pair demands e₁ e₂ h_ne h_src
  unfold coupled_operator
  apply Finset.filter_true_of_mem
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  cases hx with
  | inl h => subst h; rw [h_load]; exact h_sum
  | inr h => subst h; rw [← h_src, h_load]; exact h_sum

/-- Direction inverse : si la demande conjointe ≤ budget et chaque arête
    est individuellement admissible, les deux ordres produisent {e₁, e₂}.
    Fonctionne pour des demandes signées (positives = consommation,
    négatives = production/subvention) — pas de restriction 0 ≤ demands. -/
theorem order_independence_sufficient (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_sum : demands e₁ + demands e₂ ≤ pool.holdings e₁.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    admissionFold pool demands [e₁, e₂] = {e₁, e₂} ∧
    admissionFold pool demands [e₂, e₁] = {e₁, e₂} := by
  have hle₁ : demands e₁ ≤ pool.holdings e₁.1 := h₁
  have hle₂ : demands e₂ ≤ pool.holdings e₂.1 := h₂
  have h_adm₁ : isAdmissible pool demands ∅ e₁ :=
    (isAdmissible_empty_iff pool demands e₁).mpr hle₁
  have h_adm₂ : isAdmissible pool demands ∅ e₂ :=
    (isAdmissible_empty_iff pool demands e₂).mpr hle₂
  have h_adm₂₁ : isAdmissible pool demands {e₁} e₂ := by
    simp only [isAdmissible, contextual_fixpoint, Finset.singleton_union,
      Finset.card_pair h_ne]
    show e₂ ∈ coupled_operator pool demands
      (coupled_operator pool demands {e₁, e₂})
    rw [coupled_operator_pair_fixed pool demands e₁ e₂ h_ne h_src h_sum,
      coupled_operator_pair_fixed pool demands e₁ e₂ h_ne h_src h_sum]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₂))
  have h_sum' : demands e₂ + demands e₁ ≤ pool.holdings e₂.1 := by
    rw [add_comm, ← h_src]; exact h_sum
  have h_adm₁₂ : isAdmissible pool demands {e₂} e₁ := by
    simp only [isAdmissible, contextual_fixpoint, Finset.singleton_union,
      Finset.card_pair h_ne.symm]
    show e₁ ∈ coupled_operator pool demands
      (coupled_operator pool demands {e₂, e₁})
    rw [coupled_operator_pair_fixed pool demands e₂ e₁ h_ne.symm h_src.symm h_sum',
      coupled_operator_pair_fixed pool demands e₂ e₁ h_ne.symm h_src.symm h_sum']
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₁))
  simp only [admissionFold, List.foldl_cons, List.foldl_nil]
  simp only [h_adm₁, h_adm₂, h_adm₂₁, h_adm₁₂, if_true, if_false,
    Finset.empty_union]
  exact ⟨rfl, by ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

/-! ### 10. Caractérisation ↔ (consolidation)

  Sur le domaine {e₁ ≠ e₂, même source, demandes non-négatives, chaque
  arête individuellement admissible}, l'order-dependence est équivalente
  au dépassement conjoint du budget. -/

/-- **Caractérisation ↔** : l'admission est order-dependent ssi la demande
    conjointe dépasse le budget (sous admission individuelle de chaque arête).
    Valide pour des demandes signées — pas de restriction 0 ≤ demands.
    Compatible RCF : poids positifs = consommation, négatifs = production. -/
theorem order_dependence_iff (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    (admissionFold pool demands [e₁, e₂] ≠
     admissionFold pool demands [e₂, e₁]) ↔
    demands e₁ + demands e₂ > pool.holdings e₁.1 := by
  constructor
  · intro h_dep
    by_contra h_le
    push_neg at h_le
    have ⟨h_eq₁, _⟩ := order_independence_sufficient pool demands e₁ e₂
      h_ne h_src h_le h₁ h₂
    have ⟨_, h_eq₂⟩ := order_independence_sufficient pool demands e₁ e₂
      h_ne h_src h_le h₁ h₂
    exact h_dep (h_eq₁.trans h_eq₂.symm)
  · exact fun h_over =>
      order_dependence_sufficient pool demands e₁ e₂ h_ne h_src h₁ h₂ h_over

/-! ### 10b. Régime de compensation — hors domaine de `order_dependence_iff`

  `order_dependence_iff` exige h₁ ∧ h₂ (chaque arête individuellement
  admissible depuis ∅) pour caractériser l'order-dependence par un
  dépassement de somme. Le régime économiquement le plus intéressant du
  panier lié (§V30-§V32, GATE G2-B2, test 2b `test_d2b_linked_constraint.py`
  classe m2/m3) est hors de ce domaine : e₂ n'est PAS admissible seule
  depuis ∅ (h₂ faux), mais l'est en combinaison avec sa compensation e₁.
  Ce lemme couvre ce régime directement, sans aucun calcul de somme. -/

/-- **Lemme de compensation** : si e₂ est inadmissible seule depuis ∅ mais
    devient admissible une fois e₁ déjà en place, alors l'ordre détermine
    définitivement le sort de e₂ — admise dans l'ordre [e₁, e₂], rejetée
    dans l'ordre [e₂, e₁]. Preuve directe (pas d'induction, pas de calcul
    de somme) : `admissionFold` ne revient jamais sur une arête déjà
    traitée, donc l'ordre de traitement de e₂ depuis l'état ∅ est
    déterministe et ne dépend que de la position de e₂ dans la liste. -/
theorem compensation_forces_order_dependence (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_adm₁ : isAdmissible pool demands ∅ e₁)
    (h_not_alone : ¬ isAdmissible pool demands ∅ e₂)
    (h_together : isAdmissible pool demands {e₁} e₂) :
    e₂ ∈ admissionFold pool demands [e₁, e₂] ∧
    e₂ ∉ admissionFold pool demands [e₂, e₁] := by
  constructor
  · simp only [admissionFold, List.foldl_cons, List.foldl_nil]
    simp only [h_adm₁, if_true, Finset.empty_union]
    simp only [h_together, if_true]
    rw [Finset.singleton_union]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₂))
  · simp only [admissionFold, List.foldl_cons, List.foldl_nil]
    simp only [h_not_alone, if_false, Finset.empty_union]
    by_cases h_adm₁' : isAdmissible pool demands ∅ e₁
    · simp only [h_adm₁', if_true, Finset.empty_union]
      exact Finset.notMem_singleton.mpr h_ne.symm
    · simp only [h_adm₁', if_false]
      exact Finset.notMem_empty e₂

/-- Corollaire immédiat : sous ces hypothèses, l'admission est
    order-dependent (reformulation en `≠`, pour se brancher directement
    sur le même énoncé que `order_dependence_sufficient`). -/
theorem compensation_order_dependent (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_adm₁ : isAdmissible pool demands ∅ e₁)
    (h_not_alone : ¬ isAdmissible pool demands ∅ e₂)
    (h_together : isAdmissible pool demands {e₁} e₂) :
    admissionFold pool demands [e₁, e₂] ≠
    admissionFold pool demands [e₂, e₁] := by
  have ⟨h_in, h_notin⟩ := compensation_forces_order_dependence pool demands e₁ e₂
    h_ne h_src h_adm₁ h_not_alone h_together
  intro h_eq
  exact h_notin (h_eq ▸ h_in)

/-! ### 10c. Conjonction pairwise de contraintes scalaires (brique 2, plan 3b)

  Généralise `order_independence_sufficient` à une conjonction (ET) de
  plusieurs contraintes scalaires testées sur le même état partagé --
  modélise l'admission simultanée des boîtes par mesure (Layer 1) ET
  d'une ou plusieurs contraintes liées (2b), chaque contrainte liée étant
  réduite à une paire scalaire (demands_i, holdings_i) via la réduction
  algébrique de la brique 1 (cache/analyse_3b_theoreme_restreint_ordre.md
  §2). Chaque contrainte de la liste porte son propre `(pool, demands)` :
  la conjonction n'est PAS une nouvelle structure algébrique, c'est un ET
  de tests `isAdmissible` déjà existants sur un état `current` partagé. -/

/-- Admissibilité conjointe : `e` est admissible ssi elle l'est pour
    TOUTES les contraintes scalaires de la liste, chacune testée sur le
    même état `current` partagé. -/
def admissibleAll (preds : List (FuturePool V × (V × V → ℤ)))
    (current : ActivationState V) (e : V × V) : Prop :=
  ∀ p ∈ preds, isAdmissible p.1 p.2 current e

instance admissibleAll.decidable (preds : List (FuturePool V × (V × V → ℤ)))
    (current : ActivationState V) (e : V × V) :
    Decidable (admissibleAll preds current e) :=
  List.decidableBAll _ preds

/-- Fold d'admission sous conjonction de contraintes scalaires. Généralise
    `admissionFold` : `preds = [(pool, demands)]` en est le cas particulier
    à une seule contrainte. -/
def admissionFoldConj (preds : List (FuturePool V × (V × V → ℤ)))
    (edges : List (V × V)) : ActivationState V :=
  edges.foldl (fun cur e =>
    if admissibleAll preds cur e then cur ∪ {e} else cur) ∅

/-- Hypothèse d'indépendance d'ordre pour une contrainte scalaire, reprise
    telle quelle de `order_independence_sufficient` (h_sum, h₁, h₂). -/
def OrderIndepHyp (p : FuturePool V × (V × V → ℤ)) (e₁ e₂ : V × V) : Prop :=
  p.2 e₁ + p.2 e₂ ≤ p.1.holdings e₁.1 ∧
  p.2 e₁ ≤ p.1.holdings e₁.1 ∧
  p.2 e₂ ≤ p.1.holdings e₂.1

/-- **Brique 2 du plan 3b** : si CHAQUE contrainte de la liste satisfait
    individuellement l'hypothèse h_sum-like de `order_independence_sufficient`,
    la conjonction de toutes est order-indépendante. Preuve : chaque appel
    `isAdmissible` d'une contrainte ne dépend que de son propre
    `(pool, demands)`, jamais des autres contraintes -- `current` est le
    seul point de couplage, et chaque contrainte le voit identiquement
    dans les deux ordres (même argument que `order_independence_sufficient`,
    appliqué contrainte par contrainte). -/
theorem conjunction_order_independence_sufficient
    (preds : List (FuturePool V × (V × V → ℤ)))
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h : ∀ p ∈ preds, OrderIndepHyp p e₁ e₂) :
    admissionFoldConj preds [e₁, e₂] = admissionFoldConj preds [e₂, e₁] := by
  have h_adm₁ : admissibleAll preds ∅ e₁ := fun p hp =>
    (isAdmissible_empty_iff p.1 p.2 e₁).mpr (h p hp).2.1
  have h_adm₂ : admissibleAll preds ∅ e₂ := fun p hp =>
    (isAdmissible_empty_iff p.1 p.2 e₂).mpr (h p hp).2.2
  have h_adm₂₁ : admissibleAll preds {e₁} e₂ := fun p hp => by
    obtain ⟨hsum, _, _⟩ := h p hp
    simp only [isAdmissible, contextual_fixpoint, Finset.singleton_union,
      Finset.card_pair h_ne]
    show e₂ ∈ coupled_operator p.1 p.2
      (coupled_operator p.1 p.2 {e₁, e₂})
    rw [coupled_operator_pair_fixed p.1 p.2 e₁ e₂ h_ne h_src hsum,
      coupled_operator_pair_fixed p.1 p.2 e₁ e₂ h_ne h_src hsum]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₂))
  have h_adm₁₂ : admissibleAll preds {e₂} e₁ := fun p hp => by
    obtain ⟨hsum, _, _⟩ := h p hp
    have hsum' : p.2 e₂ + p.2 e₁ ≤ p.1.holdings e₂.1 := by
      rw [add_comm, ← h_src]; exact hsum
    simp only [isAdmissible, contextual_fixpoint, Finset.singleton_union,
      Finset.card_pair h_ne.symm]
    show e₁ ∈ coupled_operator p.1 p.2
      (coupled_operator p.1 p.2 {e₂, e₁})
    rw [coupled_operator_pair_fixed p.1 p.2 e₂ e₁ h_ne.symm h_src.symm hsum',
      coupled_operator_pair_fixed p.1 p.2 e₂ e₁ h_ne.symm h_src.symm hsum']
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₁))
  simp only [admissionFoldConj, List.foldl_cons, List.foldl_nil]
  simp only [h_adm₁, h_adm₂, h_adm₂₁, h_adm₁₂, if_true, Finset.empty_union]
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton]
  tauto

/-- Cas particulier `preds = [(pool, demands)]` : la conjonction à une
    seule contrainte redonne exactement `order_independence_sufficient`
    (`admissionFoldConj` coïncide avec `admissionFold` sur une liste
    singleton). Confirme que la généralisation n'a rien perdu du cas n=1. -/
theorem admissionFoldConj_singleton (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    admissionFoldConj [(pool, demands)] edges = admissionFold pool demands edges := by
  have hfun : (fun cur e => if admissibleAll [(pool, demands)] cur e then cur ∪ {e} else cur) =
      (fun cur e => if isAdmissible pool demands cur e then cur ∪ ({e} : ActivationState V) else cur) := by
    funext cur e
    have heq : admissibleAll [(pool, demands)] cur e ↔ isAdmissible pool demands cur e := by
      unfold admissibleAll; simp
    exact if_congr heq rfl rfl
  unfold admissionFoldConj admissionFold
  rw [hfun]

/-! ### 10d. Loi de classification — version `P`-abstraite (A1.3)

  Généralise `admissionFoldConj`/`admissibleAll` à un prédicat d'admission
  QUELCONQUE `P : ActivationState V → V × V → Prop`, muni d'une instance de
  décidabilité. La symétrie du test joint (`P {e₁} e₂ ↔ P {e₂} e₁`) est prise
  comme HYPOTHÈSE du théorème abstrait, pas prouvée à ce niveau : il n'existe
  pas d'analogue abstrait d'`isAdmissible_iff_load` pour un `P` quelconque.
  L'instanciation sur `admissibleAll` (ci-dessous) est le seul endroit où
  cette symétrie est effectivement PROUVÉE, via `isAdmissible_iff_load`.
  Cf. `cache/analyse_3b_etape4_forme_theoreme_couverture.md` §2.2 (loi dérivée
  à la main, vérifiée empiriquement 20000 tirages Python) et
  `cache/analyse_voies_alternatives.md` A1.3 (décision de généralité). -/

/-- Fold d'admission générique, paramétré par un prédicat d'admission `P`
    quelconque. Généralise `admissionFoldConj` (qui en est l'instance
    `P := admissibleAll preds`, cf. `admissionFoldConj_eq_admissionFoldP`
    ci-dessous). -/
def admissionFoldP (P : ActivationState V → V × V → Prop)
    [inst : ∀ (cur : ActivationState V) (e : V × V), Decidable (P cur e)]
    (edges : List (V × V)) : ActivationState V :=
  edges.foldl (fun cur e => if P cur e then cur ∪ {e} else cur) ∅

/-- **Loi de classification `P`-abstraite** (A1.3). Sous l'hypothèse de
    symétrie du test joint (`hj_symm`), les deux ordres de soumission de
    `e₁, e₂` produisent le même résultat ssi soit les deux sont rejetées
    seules (`¬h1 ∧ ¬h2`), soit la compatibilité jointe coïncide exactement
    avec l'admission séparée des deux (`hj ↔ (h1 ∧ h2)`). -/
theorem admissionFoldP_classification (P : ActivationState V → V × V → Prop)
    [∀ cur e, Decidable (P cur e)]
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂)
    (hj_symm : P {e₁} e₂ ↔ P {e₂} e₁) :
    admissionFoldP P [e₁, e₂] = admissionFoldP P [e₂, e₁] ↔
    (¬ P ∅ e₁ ∧ ¬ P ∅ e₂) ∨ (P {e₁} e₂ ↔ (P ∅ e₁ ∧ P ∅ e₂)) := by
  by_cases H1 : P ∅ e₁ <;> by_cases H2 : P ∅ e₂ <;> by_cases Hj : P {e₁} e₂
  -- 8 buts (H1,H2,Hj) dans l'ordre : (T,T,T) (T,T,F) (T,F,T) (T,F,F)
  -- (F,T,T) (F,T,F) (F,F,T) (F,F,F) — chacun fermé INDIVIDUELLEMENT (D1.1/D1.2 :
  -- pas de `<;>` générique après ce point).
  · -- (T,T,T)
    have Hj2 : P {e₂} e₁ := hj_symm.mp Hj
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      Finset.singleton_union, if_pos H1, if_pos H2, if_pos Hj, if_pos Hj2]
    constructor
    · intro _; exact Or.inr ⟨fun _ => ⟨H1, H2⟩, fun _ => Hj⟩
    · intro _; exact Finset.pair_comm e₁ e₂
  · -- (T,T,F)
    have Hj2 : ¬ P {e₂} e₁ := fun h => Hj (hj_symm.mpr h)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      if_pos H1, if_pos H2, if_neg Hj, if_neg Hj2]
    constructor
    · intro h; exact absurd (Finset.singleton_inj.mp h) h_ne
    · intro h
      rcases h with ⟨hn1, _⟩ | hiff
      · exact absurd H1 hn1
      · exact absurd (hiff.mpr ⟨H1, H2⟩) Hj
  · -- (T,F,T)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      Finset.singleton_union, if_pos H1, if_neg H2, if_pos Hj]
    constructor
    · intro h
      exfalso
      have he2 : e₂ ∈ (insert e₁ {e₂} : Finset (V × V)) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₂))
      rw [h] at he2
      exact h_ne (Finset.mem_singleton.mp he2).symm
    · intro h
      exfalso
      rcases h with ⟨hn1, _⟩ | hiff
      · exact hn1 H1
      · exact H2 (hiff.mp Hj).2
  · -- (T,F,F)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      if_pos H1, if_neg H2, if_neg Hj]
    constructor
    · intro _; exact Or.inr ⟨fun h => absurd h Hj, fun h => absurd h.2 H2⟩
    · intro _; trivial
  · -- (F,T,T)
    have Hj2 : P {e₂} e₁ := hj_symm.mp Hj
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      Finset.singleton_union, if_neg H1, if_pos H2, if_pos Hj2]
    constructor
    · intro h
      exfalso
      have he1 : e₁ ∈ (insert e₂ {e₁} : Finset (V × V)) :=
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self e₁))
      rw [← h] at he1
      exact h_ne (Finset.mem_singleton.mp he1)
    · intro h
      exfalso
      rcases h with ⟨_, hn2⟩ | hiff
      · exact hn2 H2
      · exact H1 (hiff.mp Hj).1
  · -- (F,T,F)
    have Hj2 : ¬ P {e₂} e₁ := fun h => Hj (hj_symm.mpr h)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      if_neg H1, if_pos H2, if_neg Hj2]
    constructor
    · intro _; exact Or.inr ⟨fun h => absurd h Hj, fun h => absurd h.1 H1⟩
    · intro _; trivial
  · -- (F,F,T)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      if_neg H1, if_neg H2]
    constructor
    · intro _; exact Or.inl ⟨H1, H2⟩
    · intro _; trivial
  · -- (F,F,F)
    simp only [admissionFoldP, List.foldl_cons, List.foldl_nil, Finset.empty_union,
      if_neg H1, if_neg H2]
    constructor
    · intro _; exact Or.inl ⟨H1, H2⟩
    · intro _; trivial

/-! ### 11. Subsomption : les existentiels Fin 3 comme instances

  Les théorèmes §6-§8 sont maintenant dérivables depuis les résultats
  structurels. Cela montre que la caractérisation générale subsume
  les témoins ponctuels. -/

/-- L'existentiel §8 est une instance du théorème structurel. -/
theorem admission_order_dependent_from_structural :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (e₁ e₂ : Fin 3 × Fin 3),
      admissionFold pool demands [e₁, e₂] ≠
      admissionFold pool demands [e₂, e₁] := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    ((0 : Fin 3), (1 : Fin 3)),
    ((0 : Fin 3), (2 : Fin 3)),
    ?_⟩
  exact order_dependence_sufficient _ _ _ _ (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### 12. Défaut monétaire-physique et non-unicité du point fixe

  Le défaut mesure l'excédent de demande par rapport au budget total.
  Au point fixe du clearing, le défaut est ≤ 0 (internalisation) :
  les arêtes survivantes ont une charge totale ≤ budget total.

  Contrairement au clearing Eisenberg-Noe (monotone → Csóka-Herings
  unicité), le coupled_operator est CONTRACTIF et admet PLUSIEURS
  points fixes. L'unicité de Csóka-Herings NE se transfère PAS. -/

def monetary_physical_defect (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) : ℤ :=
  S.sum demands - Finset.univ.sum pool.holdings

lemma vertex_load_le_holdings_at_fixpoint (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V)
    (h_fix : coupled_operator pool demands S = S) (v : V) :
    vertex_load demands S v ≤ pool.holdings v := by
  by_cases hv : ∃ e ∈ S, e.1 = v
  · obtain ⟨e, he, rfl⟩ := hv
    exact fixpoint_satisfies_budget pool demands S h_fix e he
  · push_neg at hv
    show (S.filter (fun e => e.1 = v)).sum demands ≤ pool.holdings v
    have h_empty : S.filter (fun e => e.1 = v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      exact hv e he
    rw [h_empty, Finset.sum_empty]
    exact pool.h_holdings_nonneg v

lemma sum_demands_eq_sum_vertex_load (demands : V × V → ℤ) (S : ActivationState V) :
    S.sum demands = Finset.univ.sum (fun v => vertex_load demands S v) := by
  unfold vertex_load
  exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) demands).symm

theorem defect_nonpos_at_fixpoint (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V)
    (h_fix : coupled_operator pool demands S = S) :
    monetary_physical_defect pool demands S ≤ 0 := by
  unfold monetary_physical_defect
  rw [sum_demands_eq_sum_vertex_load]
  have h_le : Finset.univ.sum (fun v => vertex_load demands S v) ≤
              Finset.univ.sum pool.holdings :=
    Finset.sum_le_sum (fun v _ =>
      vertex_load_le_holdings_at_fixpoint pool demands S h_fix v)
  linarith

/-! Non-unicité : le coupled_operator admet plusieurs points fixes.
  Contre-exemple sur Fin 3 : {e₁}, {e₂}, et ∅ sont tous des points
  fixes (holdings(0)=5, demands(e₁)=3, demands(e₂)=4). -/

theorem multiple_fixpoints_exist :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (S₁ S₂ : ActivationState (Fin 3)),
      S₁ ≠ S₂ ∧
      coupled_operator pool demands S₁ = S₁ ∧
      coupled_operator pool demands S₂ = S₂ := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    {((0 : Fin 3), (1 : Fin 3))},
    {((0 : Fin 3), (2 : Fin 3))},
    ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-! ### 13. Non-monotonie du coupled_operator

  Le coupled_operator est CONTRACTIF (Φ(S) ⊆ S) mais PAS monotone.
  Contre-exemple : S₁ ⊆ S₂ mais Φ(S₁) ⊄ Φ(S₂).
  C'est la distinction architecturale clé avec les opérateurs Tarski
  (Ghrist 2025, Besting-Hoefer-Huth 2026, Csóka-Herings 2024).
  La convergence utilise pigeonhole (descending_chain_stabilizes),
  pas le théorème de Tarski. -/

theorem coupled_operator_not_monotone :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
      (S₁ S₂ : ActivationState (Fin 3)),
      S₁ ⊆ S₂ ∧
      ¬ (coupled_operator pool demands S₁ ⊆ coupled_operator pool demands S₂) := by
  refine ⟨
    ⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 3
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 4
             else 0,
    {((0 : Fin 3), (1 : Fin 3))},
    {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3))},
    ?_, ?_⟩
  · decide
  · decide

/-! ### 14. Éviction all-or-nothing par sommet (n>2)

  Si la charge totale à un sommet dépasse le budget, le
  coupled_operator supprime TOUTES les arêtes à ce sommet en un pas. -/

theorem vertex_eviction_all_or_nothing (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (v : V)
    (h_over : pool.holdings v < vertex_load demands S v) :
    ∀ e ∈ S, e.1 = v → e ∉ coupled_operator pool demands S := by
  intro e he hv
  intro h_mem
  have := (Finset.mem_filter.mp h_mem).2
  rw [hv] at this
  linarith

/-! ### 14bis. Défaut décroissant sous le clearing

  Chaque application de Φ réduit (ou maintient) le défaut monétaire-physique.
  Le clearing INTERNALISE progressivement l'externalité : les arêtes évincées
  réduisent la demande totale, rapprochant le défaut de ≤ 0.

  Ce résultat est un corollaire de la contractivity (Φ(S) ⊆ S) +
  non-négativité de la somme des demandes sur le complément. -/

lemma defect_antimono_of_subset (pool : FuturePool V) (demands : V × V → ℤ)
    (S T : ActivationState V) (h : T ⊆ S) (h_nn : ∀ e, 0 ≤ demands e) :
    monetary_physical_defect pool demands T ≤
    monetary_physical_defect pool demands S := by
  unfold monetary_physical_defect
  have : T.sum demands ≤ S.sum demands :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => h_nn _)
  linarith

theorem defect_decreases_under_clearing (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (h_nn : ∀ e, 0 ≤ demands e) :
    monetary_physical_defect pool demands (coupled_operator pool demands S) ≤
    monetary_physical_defect pool demands S :=
  defect_antimono_of_subset pool demands S _ (coupled_operator_contractive pool demands S) h_nn

theorem defect_along_chain (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) (h_nn : ∀ e, 0 ≤ demands e) (n : ℕ) :
    monetary_physical_defect pool demands (descending_chain pool demands init (n + 1)) ≤
    monetary_physical_defect pool demands (descending_chain pool demands init n) :=
  defect_decreases_under_clearing pool demands _ h_nn

/-! ### 14ter. Borne de convergence sans borne exogène

  La convergence du coupled_operator ne dépend d'AUCUN paramètre exogène
  (pas de max_score, pas de borne spectrale). La seule borne est |S|
  (taille de l'état initial), qui est une propriété INTERNE du système.

  Contraste avec StabilityWFA (convergence par troncature min(·, max)) :
  ici la convergence est endogène (contractivity + finitude). -/

theorem screening_convergence_bound (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    descending_chain pool demands init init.card =
    descending_chain pool demands init (init.card + 1) :=
  (descending_chain_at_card_fixpoint pool demands init).symm

theorem screening_iterations_le_edges (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    ∃ n, n ≤ init.card ∧ ∀ k, n ≤ k →
      descending_chain pool demands init k = descending_chain pool demands init n := by
  obtain ⟨n, hn, h_stab⟩ := descending_chain_stabilizes pool demands init
  exact ⟨n, hn, fun k hk => by
    have := descending_chain_stable_propagates pool demands init n (k - n) h_stab
    rwa [Nat.add_sub_cancel' hk] at this⟩

/-! ### 14quater. Order-dependence n>2 — l'all-or-nothing engendre une cascade

  Pour n≥3 arêtes au même sommet source, l'all-or-nothing crée un effet
  cascade : si la surcharge est assez grande, l'admission d'une arête
  peut bloquer PLUSIEURS autres.

  Théorème structurel (n arêtes, même source) : si chaque arête est
  individuellement admissible mais que la somme totale dépasse le budget,
  alors l'admission séquentielle admet la PREMIÈRE arête et rejette
  TOUTES les suivantes (car le point fixe contextuel depuis
  {e_first} ∪ {e_next} réévince les deux si la somme > budget).

  Le résultat est LIMITÉ au cas "first-takes-all" : l'opérateur ne
  sélectionne PAS un sous-ensemble maximal faisable — il est
  all-or-nothing. C'est une caractérisation honnête de l'opérateur
  RÉEL, pas d'un opérateur hypothétique subset-sum. -/

theorem admissionFold_first_takes_all (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ e₃ : V × V) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃)
    (h_src₁₂ : e₁.1 = e₂.1) (h_src₁₃ : e₁.1 = e₃.1)
    (h_le₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h_over₁₂ : demands e₁ + demands e₂ > pool.holdings e₁.1)
    (h_over₁₃ : demands e₁ + demands e₃ > pool.holdings e₁.1) :
    admissionFold pool demands [e₁, e₂, e₃] = {e₁} := by
  simp only [admissionFold, List.foldl_cons, List.foldl_nil]
  have h_adm₁ : isAdmissible pool demands ∅ e₁ :=
    (isAdmissible_empty_iff pool demands e₁).mpr h_le₁
  have h_rej₂ : ¬ isAdmissible pool demands {e₁} e₂ :=
    not_isAdmissible_pair pool demands e₁ e₂ h₁₂ h_src₁₂ h_over₁₂
  have h_rej₃ : ¬ isAdmissible pool demands {e₁} e₃ :=
    not_isAdmissible_pair pool demands e₁ e₃ h₁₃ h_src₁₃ h_over₁₃
  simp only [h_adm₁, ↓reduceIte, Finset.empty_union, h_rej₂, h_rej₃]

theorem admissionFold_n3_order_dependent (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ e₃ : V × V) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (h_src₁₂ : e₁.1 = e₂.1) (h_src₁₃ : e₁.1 = e₃.1)
    (h_le₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h_le₂ : demands e₂ ≤ pool.holdings e₂.1)
    (h_over₁₂ : demands e₁ + demands e₂ > pool.holdings e₁.1)
    (h_over₁₃ : demands e₁ + demands e₃ > pool.holdings e₁.1)
    (h_over₂₃ : demands e₂ + demands e₃ > pool.holdings e₂.1) :
    admissionFold pool demands [e₁, e₂, e₃] ≠
    admissionFold pool demands [e₂, e₁, e₃] := by
  have h_src₂₃ : e₂.1 = e₃.1 := h_src₁₂.symm.trans h_src₁₃
  have h_lhs := admissionFold_first_takes_all pool demands e₁ e₂ e₃
    h₁₂ h₁₃ h_src₁₂ h_src₁₃ h_le₁ h_over₁₂ h_over₁₃
  have h_rhs := admissionFold_first_takes_all pool demands e₂ e₁ e₃
    h₁₂.symm h₂₃ h_src₁₂.symm h_src₂₃
    (h_src₁₂ ▸ h_le₂)
    (by rw [add_comm]; rw [show pool.holdings e₂.1 = pool.holdings e₁.1
          from congrArg pool.holdings h_src₁₂.symm]; exact h_over₁₂)
    h_over₂₃
  rw [h_lhs, h_rhs]
  intro h_eq
  have : e₁ ∈ ({e₂} : Finset (V × V)) := h_eq ▸ Finset.mem_singleton_self e₁
  exact h₁₂ (Finset.mem_singleton.mp this)

/-! ### 14b. Idempotence de coupled_operator et caractérisation d'admission

  coupled_operator est idempotent : une seule application atteint le point
  fixe. L'admission se réduit à un test de charge au sommet-source, sans W5.
  Les théorèmes W5 (§15) en deviennent des corollaires. -/

/-- Au sommet v dont la charge respecte le budget, coupled_operator ne retire
    aucune arête : les arêtes à v dans Φ(S) sont les mêmes que dans S. -/
lemma vertex_load_preserved_at_surviving_vertex (pool : FuturePool V)
    (demands : V × V → ℤ) (S : ActivationState V) (v : V)
    (h : vertex_load demands S v ≤ pool.holdings v) :
    (coupled_operator pool demands S).filter (fun e => e.1 = v) =
    S.filter (fun e => e.1 = v) := by
  ext e
  constructor
  · intro he
    have ⟨h1, h2⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp h1).1, h2⟩
  · intro he
    have ⟨h1, h2⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨h1, by rw [h2]; exact h⟩, h2⟩

/-- L'opérateur couplé est idempotent : Φ(Φ(S)) = Φ(S).
    La convergence en un pas élimine le besoin de |S| itérations. -/
theorem coupled_operator_idempotent (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) :
    coupled_operator pool demands (coupled_operator pool demands S) =
    coupled_operator pool demands S := by
  apply Finset.Subset.antisymm (coupled_operator_contractive pool demands _)
  intro e he
  have hload := (mem_filter.mp he).2
  have h_filt := vertex_load_preserved_at_surviving_vertex pool demands S e.1 hload
  have h_load_eq : vertex_load demands (coupled_operator pool demands S) e.1 =
      vertex_load demands S e.1 := by
    unfold vertex_load; rw [h_filt]
  exact mem_filter.mpr ⟨he, by rw [h_load_eq]; exact hload⟩

/-- La chaîne descendante atteint le point fixe en un pas : chain(1) = chain(|init|). -/
theorem descending_chain_one_step (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) :
    descending_chain pool demands init 1 =
    descending_chain pool demands init init.card := by
  by_cases h : init.card = 0
  · have h_empty : init = ∅ := Finset.card_eq_zero.mp h
    subst h_empty; simp [descending_chain, coupled_operator]
  · have h_stab : descending_chain pool demands init 1 =
        descending_chain pool demands init (1 + 1) := by
      show coupled_operator pool demands init =
           coupled_operator pool demands (coupled_operator pool demands init)
      exact (coupled_operator_idempotent pool demands init).symm
    have h_prop := descending_chain_stable_propagates pool demands init 1
      (init.card - 1) h_stab
    have : 1 + (init.card - 1) = init.card := by omega
    rw [this] at h_prop
    exact h_prop.symm

/-- L'admission se réduit à un test de charge au sommet source :
    isAdmissible(current, e) ↔ vertex_load(current ∪ {e}, e.src) ≤ holdings(e.src). -/
theorem isAdmissible_iff_load (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V) :
    isAdmissible pool demands current e ↔
    vertex_load demands (current ∪ {e}) e.1 ≤ pool.holdings e.1 := by
  unfold isAdmissible contextual_fixpoint
  rw [← descending_chain_one_step pool demands (current ∪ {e})]
  constructor
  · exact fun he => (mem_filter.mp he).2
  · exact fun hload => mem_filter.mpr
      ⟨mem_union.mpr (Or.inr (mem_singleton.mpr rfl)), hload⟩

/-! ### 14c. Instanciation de la loi `P`-abstraite (§10d) sur `admissibleAll`

  Ce bloc doit venir APRÈS `isAdmissible_iff_load` ci-dessus (voie courte du
  lemme de symétrie) — d'où sa position ici plutôt qu'immédiatement après
  §10d/§10c. -/

/-- `admissionFoldConj` est l'instance `P := admissibleAll preds` d'`admissionFoldP`
    (même fold, même instance `Decidable` via `admissibleAll.decidable`). -/
theorem admissionFoldConj_eq_admissionFoldP
    (preds : List (FuturePool V × (V × V → ℤ))) (edges : List (V × V)) :
    admissionFoldConj preds edges = admissionFoldP (admissibleAll preds) edges := by
  unfold admissionFoldConj admissionFoldP; rfl

/-- Voie courte du lemme de symétrie du test joint, au niveau d'une seule
    contrainte scalaire : passe par `isAdmissible_iff_load` (déjà prouvé),
    pas par un dépliage de `contextual_fixpoint` (le dépliage n'est PAS
    définitionnel — c'est ce théorème qui l'établit). -/
lemma isAdmissible_joint_symm (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_src : e₁.1 = e₂.1) :
    isAdmissible pool demands {e₁} e₂ ↔ isAdmissible pool demands {e₂} e₁ := by
  rw [isAdmissible_iff_load, isAdmissible_iff_load,
    Finset.union_comm ({e₁} : Finset (V × V)) {e₂}, h_src]

/-- Lift vers `admissibleAll` : la symétrie du test joint vaut pour la
    conjonction entière (chaque contrainte de la liste, indépendamment). -/
theorem admissibleAll_joint_symm (preds : List (FuturePool V × (V × V → ℤ)))
    (e₁ e₂ : V × V) (h_src : e₁.1 = e₂.1) :
    admissibleAll preds {e₁} e₂ ↔ admissibleAll preds {e₂} e₁ := by
  unfold admissibleAll
  constructor
  · intro h p hp; exact (isAdmissible_joint_symm p.1 p.2 e₁ e₂ h_src).mp (h p hp)
  · intro h p hp; exact (isAdmissible_joint_symm p.1 p.2 e₁ e₂ h_src).mpr (h p hp)

/-- **Instanciation de la loi `P`-abstraite sur `admissibleAll`** : la
    symétrie requise par `admissionFoldP_classification` est déchargée par
    `admissibleAll_joint_symm` (via `isAdmissible_iff_load` + `h_src`), pas
    postulée. Généralise strictement les 4 théorèmes existants (§9-§10b),
    redérivés comme corollaires ci-dessous. -/
theorem admissionFoldConj_classification (preds : List (FuturePool V × (V × V → ℤ)))
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1) :
    admissionFoldConj preds [e₁, e₂] = admissionFoldConj preds [e₂, e₁] ↔
    (¬ admissibleAll preds ∅ e₁ ∧ ¬ admissibleAll preds ∅ e₂) ∨
    (admissibleAll preds {e₁} e₂ ↔
      admissibleAll preds ∅ e₁ ∧ admissibleAll preds ∅ e₂) := by
  simp only [admissionFoldConj_eq_admissionFoldP]
  exact admissionFoldP_classification (admissibleAll preds) e₁ e₂ h_ne
    (admissibleAll_joint_symm preds e₁ e₂ h_src)

/-! #### Corollaires de non-régression : les 4 théorèmes existants comme cas
    particuliers de `admissionFoldConj_classification`

  Recomposition pure (D1.7) : ne modifie AUCUN théorème existant — ajoute des
  lemmes distincts montrant qu'ils sont dérivables de la loi générale, dans
  l'esprit d'`admissionFoldConj_singleton`. -/

/-- `order_dependence_iff` est la branche `(T,T,·)` de la loi générale,
    spécialisée à `preds = [(pool, demands)]`. -/
theorem order_dependence_iff_of_classification (pool : FuturePool V) (demands : V × V → ℤ)
    (e₁ e₂ : V × V) (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1)
    (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    (admissionFold pool demands [e₁, e₂] ≠
     admissionFold pool demands [e₂, e₁]) ↔
    demands e₁ + demands e₂ > pool.holdings e₁.1 := by
  have hH1 : admissibleAll [(pool, demands)] ∅ e₁ := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp
    exact (isAdmissible_empty_iff pool demands e₁).mpr h₁
  have hH2 : admissibleAll [(pool, demands)] ∅ e₂ := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp
    exact (isAdmissible_empty_iff pool demands e₂).mpr h₂
  have hclass := admissionFoldConj_classification [(pool, demands)] e₁ e₂ h_ne h_src
  rw [admissionFoldConj_singleton, admissionFoldConj_singleton] at hclass
  by_cases h_over : demands e₁ + demands e₂ > pool.holdings e₁.1
  · have hHj : ¬ admissibleAll [(pool, demands)] {e₁} e₂ := fun h =>
      (not_isAdmissible_pair pool demands e₁ e₂ h_ne h_src h_over)
        (h (pool, demands) (List.mem_singleton_self _))
    constructor
    · intro _; exact h_over
    · intro _ h_eq
      rw [hclass] at h_eq
      rcases h_eq with ⟨_, hn2⟩ | hiff
      · exact hn2 hH2
      · exact hHj (hiff.mpr ⟨hH1, hH2⟩)
  · push Not at h_over
    have hHj : admissibleAll [(pool, demands)] {e₁} e₂ := fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp
      refine (isAdmissible_iff_load pool demands {e₁} e₂).mpr ?_
      rw [Finset.singleton_union, ← h_src, vertex_load_pair demands e₁ e₂ h_ne h_src]
      exact h_over
    constructor
    · intro hne
      exfalso
      apply hne
      rw [hclass]
      exact Or.inr ⟨fun _ => ⟨hH1, hH2⟩, fun _ => hHj⟩
    · intro h_gt
      exact absurd h_gt (not_lt.mpr h_over)

/-- `compensation_forces_order_dependence` (donc `compensation_order_dependent`)
    est la branche `(T,F,T)` de la loi générale, spécialisée à `preds =
    [(pool, demands)]` : `h_adm₁`, `h_not_alone`, `h_together` sont
    littéralement `H1`, `¬H2`, `Hj` du squelette. -/
theorem compensation_forces_order_dependence_of_classification
    (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h_adm₁ : isAdmissible pool demands ∅ e₁)
    (h_not_alone : ¬ isAdmissible pool demands ∅ e₂)
    (h_together : isAdmissible pool demands {e₁} e₂) :
    admissionFold pool demands [e₁, e₂] ≠
    admissionFold pool demands [e₂, e₁] := by
  rw [← admissionFoldConj_singleton pool demands [e₁, e₂],
    ← admissionFoldConj_singleton pool demands [e₂, e₁]]
  have hH1 : admissibleAll [(pool, demands)] ∅ e₁ := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact h_adm₁
  have hH2 : ¬ admissibleAll [(pool, demands)] ∅ e₂ := fun h =>
    h_not_alone (h (pool, demands) (List.mem_singleton_self _))
  have hHj : admissibleAll [(pool, demands)] {e₁} e₂ := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact h_together
  intro h_eq
  have := (admissionFoldConj_classification [(pool, demands)] e₁ e₂ h_ne h_src).mp h_eq
  rcases this with ⟨hn1, _⟩ | hiff
  · exact hn1 hH1
  · exact hH2 (hiff.mp hHj).2

/-! ### 15. W5 and context-independence

  Under W5 (out-degree ≤ 1), coupled_operator degenerates to a per-edge
  filter: each edge's admission depends only on its own demand vs vertex
  budget, not on other edges. This is the DUAL of order_dependence_iff:
  W5 prohibits the premise (e₁.1 = e₂.1 with e₁ ≠ e₂). -/

def IsW5 (V : Type*) [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) : Prop :=
  ∀ v : V, (edges.filter (fun e => e.1 = v)).card ≤ 1

lemma IsW5_subset {S T : Finset (V × V)} (h : S ⊆ T)
    (h_w5 : IsW5 V T) : IsW5 V S :=
  fun v => (Finset.card_le_card (Finset.filter_subset_filter _ h)).trans (h_w5 v)

private lemma W5_filter_singleton {S : Finset (V × V)} {e : V × V}
    (h_mem : e ∈ S) (h_w5 : IsW5 V S) :
    S.filter (fun e' => e'.1 = e.1) = {e} := by
  have h_in : e ∈ S.filter (fun e' => e'.1 = e.1) :=
    Finset.mem_filter.mpr ⟨h_mem, rfl⟩
  have h_card : (S.filter (fun e' => e'.1 = e.1)).card = 1 :=
    le_antisymm (h_w5 e.1) (Finset.card_pos.mpr ⟨e, h_in⟩)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card
  rw [ha, Finset.mem_singleton] at h_in; subst h_in; exact ha

lemma W5_vertex_load_eq (demands : V × V → ℤ) (S : ActivationState V)
    (e : V × V) (h_mem : e ∈ S) (h_w5 : IsW5 V S) :
    vertex_load demands S e.1 = demands e := by
  unfold vertex_load
  rw [W5_filter_singleton h_mem h_w5, Finset.sum_singleton]

private lemma W5_coupled_operator_fixpoint (pool : FuturePool V)
    (demands : V × V → ℤ) (S : ActivationState V) (h_w5 : IsW5 V S) :
    coupled_operator pool demands (coupled_operator pool demands S) =
    coupled_operator pool demands S := by
  apply Finset.Subset.antisymm (coupled_operator_contractive pool demands _)
  intro e h_mem
  have h_w5' := IsW5_subset (coupled_operator_contractive pool demands S) h_w5
  apply Finset.mem_filter.mpr
  refine ⟨h_mem, ?_⟩
  rw [W5_vertex_load_eq demands _ e h_mem h_w5']
  have := (Finset.mem_filter.mp h_mem).2
  rwa [W5_vertex_load_eq demands S e
    (coupled_operator_contractive pool demands S h_mem) h_w5] at this

theorem W5_isAdmissible_iff (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V)
    (h_w5 : IsW5 V (current ∪ {e})) :
    isAdmissible pool demands current e ↔ demands e ≤ pool.holdings e.1 := by
  unfold isAdmissible contextual_fixpoint
  set init := current ∪ {e}
  have h_e_mem : e ∈ init := Finset.mem_union_right _ (Finset.mem_singleton_self e)
  have h_card_pos : 0 < init.card := Finset.card_pos.mpr ⟨e, h_e_mem⟩
  have h_stab : descending_chain pool demands init 1 =
                descending_chain pool demands init 2 :=
    (W5_coupled_operator_fixpoint pool demands init h_w5).symm
  have h_prop := descending_chain_stable_propagates pool demands init 1
    (init.card - 1) h_stab
  have : 1 + (init.card - 1) = init.card := by omega
  rw [this] at h_prop
  rw [h_prop]
  show e ∈ coupled_operator pool demands init ↔ _
  rw [coupled_operator, Finset.mem_filter]
  constructor
  · intro ⟨_, h_le⟩
    rwa [W5_vertex_load_eq demands init e h_e_mem h_w5] at h_le
  · intro h_le
    exact ⟨h_e_mem, by rwa [W5_vertex_load_eq demands init e h_e_mem h_w5]⟩

theorem W5_admission_context_independent (pool : FuturePool V)
    (demands : V × V → ℤ) (current₁ current₂ : ActivationState V)
    (e : V × V)
    (h₁ : IsW5 V (current₁ ∪ {e})) (h₂ : IsW5 V (current₂ ∪ {e})) :
    isAdmissible pool demands current₁ e ↔
    isAdmissible pool demands current₂ e := by
  rw [W5_isAdmissible_iff pool demands current₁ e h₁,
      W5_isAdmissible_iff pool demands current₂ e h₂]

/-! ### 15b. Contention depth — max out-degree

  The max out-degree of an edge set measures contention depth: the maximum
  number of edges competing for the same source-vertex budget. This is the
  computable proxy for the Foata height under source-vertex independence
  (indep e₁ e₂ ↔ e₁.1 ≠ e₂.1). Under that independence, a dependency
  chain = edges at the same source, so height = max out-degree
  (by height_eq_max_chain_length, TraceMonoid.lean).

  W5 ↔ max_out_degree ≤ 1 ↔ no coupling possible. -/

def max_out_degree (edges : Finset (V × V)) : ℕ :=
  Finset.univ.sup (fun v => (edges.filter (fun e => e.1 = v)).card)

theorem IsW5_iff_max_out_degree_le_one (edges : Finset (V × V)) :
    IsW5 V edges ↔ max_out_degree edges ≤ 1 := by
  unfold IsW5 max_out_degree
  constructor
  · intro h
    exact Finset.sup_le (fun v _ => h v)
  · intro h v
    exact (Finset.le_sup (f := fun v => (edges.filter (fun e => e.1 = v)).card)
      (Finset.mem_univ v)).trans h

/-! ### 16. Sufficient budget → order-independent admission

  When total demand at each vertex ≤ budget (with non-negative demands),
  ALL edges are admitted regardless of order. Dual of order_dependence_iff
  in the "no contention" regime: budget ample + demands ≥ 0 → no
  order-dependence. Does NOT address the contention regime. -/

omit [Fintype V] in
private lemma vertex_load_mono_subset (demands : V × V → ℤ) (S T : ActivationState V)
    (h_sub : S ⊆ T) (h_nn : ∀ e, 0 ≤ demands e) (v : V) :
    vertex_load demands S v ≤ vertex_load demands T v := by
  unfold vertex_load
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ h_sub) (fun _ _ _ => h_nn _)

private lemma coupled_operator_fixed_of_budget (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V)
    (h_budget : ∀ v, vertex_load demands S v ≤ pool.holdings v) :
    coupled_operator pool demands S = S := by
  unfold coupled_operator
  exact Finset.filter_true_of_mem (fun e _ => h_budget e.1)

private lemma isAdmissible_of_budget (pool : FuturePool V) (demands : V × V → ℤ)
    (all_edges : Finset (V × V))
    (current : ActivationState V) (e : V × V)
    (h_nn : ∀ e, 0 ≤ demands e)
    (h_cur_sub : current ⊆ all_edges)
    (h_e_mem : e ∈ all_edges)
    (h_budget : ∀ v, vertex_load demands all_edges v ≤ pool.holdings v) :
    isAdmissible pool demands current e := by
  have h_sub : current ∪ {e} ⊆ all_edges :=
    Finset.union_subset h_cur_sub (Finset.singleton_subset_iff.mpr h_e_mem)
  have h_budget' : ∀ v, vertex_load demands (current ∪ {e}) v ≤ pool.holdings v :=
    fun v => le_trans (vertex_load_mono_subset demands _ _ h_sub h_nn v) (h_budget v)
  have h_fix := coupled_operator_fixed_of_budget pool demands (current ∪ {e}) h_budget'
  show e ∈ contextual_fixpoint pool demands current e
  simp only [contextual_fixpoint]
  have h_stab : descending_chain pool demands (current ∪ {e}) 0 =
                descending_chain pool demands (current ∪ {e}) 1 := h_fix.symm
  have h_eq : descending_chain pool demands (current ∪ {e}) (current ∪ {e}).card =
              current ∪ {e} := by
    have := descending_chain_stable_propagates pool demands (current ∪ {e}) 0
      (current ∪ {e}).card h_stab
    simpa using this
  rw [h_eq]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self e)

private lemma admissionFold_aux (pool : FuturePool V) (demands : V × V → ℤ)
    (all_edges : Finset (V × V))
    (remaining : List (V × V)) (cur : ActivationState V)
    (h_nn : ∀ e, 0 ≤ demands e)
    (h_cur_sub : cur ⊆ all_edges)
    (h_rem_sub : ∀ e ∈ remaining, e ∈ all_edges)
    (h_budget : ∀ v, vertex_load demands all_edges v ≤ pool.holdings v) :
    remaining.foldl (fun c e =>
      if isAdmissible pool demands c e then c ∪ {e} else c) cur =
    cur ∪ remaining.toFinset := by
  induction remaining generalizing cur with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons, List.toFinset_cons]
    have h_e_mem := h_rem_sub e (List.mem_cons.mpr (Or.inl rfl))
    have h_adm := isAdmissible_of_budget pool demands all_edges cur e h_nn
      h_cur_sub h_e_mem h_budget
    rw [if_pos h_adm]
    have h_cur'_sub : cur ∪ {e} ⊆ all_edges :=
      Finset.union_subset h_cur_sub (Finset.singleton_subset_iff.mpr h_e_mem)
    rw [ih (cur ∪ {e}) h_cur'_sub (fun x hx => h_rem_sub x (List.mem_cons_of_mem e hx))]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem sufficient_budget_order_independent (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V))
    (h_nn : ∀ e, 0 ≤ demands e)
    (h_budget : ∀ v, vertex_load demands edges.toFinset v ≤ pool.holdings v) :
    admissionFold pool demands edges = edges.toFinset := by
  unfold admissionFold
  rw [admissionFold_aux pool demands edges.toFinset edges ∅ h_nn
      (Finset.empty_subset _) (fun e he => List.mem_toFinset.mpr he) h_budget]
  simp

end DualDAG
