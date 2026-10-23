/-
  ThesePlanetaire/DepletionStable.lean
  Phase 6b (2026-10-02) : l'épuisement pur est stablement concurrent (Husson–Morin) ; une seule
  production suffit à casser la stabilité.

  Développé d'abord en `DepletionStable_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 6, 6b) ; analyse :
  `cache/analyse_stabilite_traces_locales_2026-10-02.md` (§3, §4.1, §7).

  Un automate d'ÉPUISEMENT ne fait que consommer : chaque lettre débite des places, aucune n'en
  crédite. En sémantique partielle (`LocalTraceLang`, rejet = lettre non tirable), deux lettres
  se lisent alors dans les deux ordres vers le même résultat, rejet compris : l'automate est
  commutatif, donc stablement concurrent et S2 (critère commutatif de `LocalTraceLang`). Toutes
  les preuves passent par ce critère ; seule la commutativité est à établir, cas par cas, avec
  `LocalTraceLang.isCommutativePA_ofGated` (§7 de `LocalTraceLang`).
  1. épuisement vectoriel `depl c` (état `ι → ℤ`, consommations `c a ≥ 0`) :
     ★ `depl_commutative`, ★ `depl_maxPar_iff` (`a ∥_q b ⟺ a ≠ b ∧ c a + c b ≤ q`, §4.1),
     ★ `depl_stablyConcurrent`, ★ `depl_S2` ; ★ `depl_signed_not_stable` : une consommation
     négative (une PRODUCTION) casse l'axiome du cube ;
  2. screening (`DualDAG.isAdmissible`, lu par `isAdmissible_iff_load`) : ★ `screen_commutative`
     (demandes ≥ 0), ★ `screen_stablyConcurrent`, ★ `screen_S2` ;
     ★ `screen_maxPar_iff_budgetGated` : à l'état vide, la concurrence maximale EST
     `BudgetGatedIndep.budgetGatedCommute`, donc la commutation des `admissionFold` ;
     ★ `screen_signed_not_stable` : une demande négative casse le cube ;
  3. M(1,2) (`RightsCurrencies`) : ★ `rect_stable`, ★ `poly_stable` ;
     ★ `polytope_partial_vs_total` : le polytope, D en sémantique totale (« tester puis
     garder », `polytope_not_diamond`), est commutatif et stable en sémantique partielle
     (`toTotal_ofGated` relie les deux) ;
  4. communs gérés par épuisement : ★ `deplete_stable` (stocks planétaires seuls,
     `PlanetaryLedger`), ★ `burn_stable` (droits non transférables, `TokenizedCommons`). Les
     frontières non gardées sont débitées sans test ; la soustraction commute.

  La circulation monétaire (un paiement crédite son receveur) n'est PAS stable :
  `LedgerNotStable` (Phase 6c, module frère).
-/

import Mathlib.Tactic
import ThesePlanetaire.LocalTraceLang
import ThesePlanetaire.BudgetGatedIndep
import ThesePlanetaire.PlanetaryLedger
import ThesePlanetaire.TokenizedCommons
import ThesePlanetaire.RightsCurrencies

namespace DepletionStable

open LocalTraceLang

/-! ### 1. Épuisement vectoriel -/

section Depletion

variable {ι α : Type*} [Fintype ι]

/-- Automate d'épuisement vectoriel : `a` est tirable ssi l'état couvre sa consommation
    (`c a ≤ q` point par point), et l'état devient `q - c a`. -/
def depl (c : α → ι → ℤ) : PAut (ι → ℤ) α :=
  ofGated (fun q a => ∀ i, c a i ≤ q i) (fun q a => q - c a)

variable {c : α → ι → ℤ}

omit [Fintype ι] in
/-- Sous consommations ≥ 0, « `a` puis `b` » est tirable ssi `c a + c b ≤ q`. -/
lemma depl_pair_iff (hc : ∀ a, 0 ≤ c a) (q : ι → ℤ) (a b : α) :
    ((∀ i, c a i ≤ q i) ∧ ∀ i, c b i ≤ (q - c a) i) ↔ c a + c b ≤ q := by
  simp only [Pi.le_def, Pi.add_apply, Pi.sub_apply]
  constructor
  · rintro ⟨-, hb⟩ i
    linarith [hb i]
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have : 0 ≤ c b i := hc b i
      linarith [h i]
    · linarith [h i]

/-- ★ L'épuisement vectoriel est commutatif (égalité dans `Option`, rejet compris). -/
theorem depl_commutative (hc : ∀ a, 0 ≤ c a) : IsCommutativePA (depl c) :=
  isCommutativePA_ofGated (fun q a b => sub_right_comm q (c a) (c b)) (fun q a b h =>
    (depl_pair_iff hc q b a).mpr (add_comm (c a) (c b) ▸ (depl_pair_iff hc q a b).mp h))

/-- ★ Concurrence maximale de l'épuisement : `a ∥_q b ⟺ a ≠ b ∧ c a + c b ≤ q` (§4.1). -/
theorem depl_maxPar_iff (hc : ∀ a, 0 ≤ c a) (q : ι → ℤ) (a b : α) :
    maxPar (depl c) q a b ↔ a ≠ b ∧ c a + c b ≤ q := by
  rw [maxPar_iff_of_commutative (depl_commutative hc), depl, isSome_run_ofGated_pair,
    depl_pair_iff hc]

/-- ★ L'épuisement vectoriel est stablement concurrent (Déf. 2.4). -/
theorem depl_stablyConcurrent (hc : ∀ a, 0 ≤ c a) : StablyConcurrent (depl c) :=
  stablyConcurrent_of_commutative (depl_commutative hc)

/-- ★ L'épuisement vectoriel vérifie S2 (Déf. 2.1). -/
theorem depl_S2 (hc : ∀ a, 0 ≤ c a) : S2 (depl c) :=
  S2_of_commutative (depl_commutative hc)

end Depletion

/-- Consommations signées sur une place : `0` et `1` consomment une unité, `2` en PRODUIT une. -/
def cSigned : Fin 3 → Fin 1 → ℤ := fun a _ => if a = 2 then -1 else 1

/-- Témoin du cube en `q = 1`, `(a, b, c) = (0, 1, 2)` : membre gauche vrai (`0 ∥ 2`, `1 ∥ 2`,
    et après `2` la place vaut 2, d'où `0 ∥ 1`) ; `0 ∥_q 1` faux (il faudrait `q ≥ 2`). -/
theorem depl_signed_witness :
    (maxPar (depl cSigned) (fun _ => 1) 0 2 ∧ maxPar (depl cSigned) (fun _ => 1) 1 2 ∧
        parAfter (depl cSigned) (fun _ => 1) 2 0 1) ∧
      ¬ maxPar (depl cSigned) (fun _ => 1) 0 1 := by
  decide

/-- ★ Une production casse la stabilité : le membre gauche du cube est vrai, le membre droit
    faux (`depl_signed_witness`). -/
theorem depl_signed_not_stable : ¬ StablyConcurrent (depl cSigned) := fun h =>
  depl_signed_witness.2 ((h _ 0 1 2).mp depl_signed_witness.1).1

/-! ### 2. Screening (DualDAG / BudgetGatedIndep) -/

section Screening

open DualDAG (FuturePool vertex_load vertex_load_singleton vertex_load_pair isAdmissible
  isAdmissible_iff_load admissionFold)
open BudgetGatedIndep (budgetGatedCommute budgetGatedCommute_iff vertex_load_cross)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Screening partiel : l'arête `e` est tirable ssi elle est admissible dans l'ensemble déjà
    activé (`DualDAG.isAdmissible`) ; elle y est alors ajoutée. -/
def screenP (pool : FuturePool V) (demands : V × V → ℤ) : PAut (Finset (V × V)) (V × V) :=
  ofGated (isAdmissible pool demands) (fun S e => S ∪ {e})

/-- Le même automate, gardé par la charge du sommet source. -/
def screenLoadP (pool : FuturePool V) (demands : V × V → ℤ) :
    PAut (Finset (V × V)) (V × V) :=
  ofGated (fun S e => vertex_load demands (S ∪ {e}) e.1 ≤ pool.holdings e.1)
    (fun S e => S ∪ {e})

/-- Le point fixe d'admission se lit sur la charge (`isAdmissible_iff_load`). -/
theorem screenP_eq_load (pool : FuturePool V) (demands : V × V → ℤ) :
    screenP pool demands = screenLoadP pool demands := by
  funext S e
  exact if_congr (isAdmissible_iff_load pool demands S e) rfl rfl

variable {pool : FuturePool V} {demands : V × V → ℤ}

omit [Fintype V] in
/-- Sous demandes ≥ 0, la charge croît avec l'ensemble activé. -/
lemma vertex_load_mono (h_nn : ∀ e, 0 ≤ demands e) {S T : Finset (V × V)} (h : S ⊆ T)
    (v : V) : vertex_load demands S v ≤ vertex_load demands T v :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ h) (fun e _ _ => h_nn e)

omit [Fintype V] in
/-- Une arête d'une autre source ne charge pas `v`. -/
lemma vertex_load_union_other (S : Finset (V × V)) {e : V × V} {v : V} (h : e.1 ≠ v) :
    vertex_load demands (S ∪ {e}) v = vertex_load demands S v := by
  unfold vertex_load
  rw [Finset.filter_union, Finset.filter_singleton, if_neg h, Finset.union_empty]

/-- « `a` puis `b` » passe ssi les charges en `a.1` et en `b.1` de `S ∪ {a} ∪ {b}` tiennent :
    même source, c'est la même charge (croissante, `h_nn`) ; sinon `b` ne charge pas `a.1`. -/
lemma screen_pair_iff (h_nn : ∀ e, 0 ≤ demands e) (S : Finset (V × V)) (a b : V × V) :
    (vertex_load demands (S ∪ {a}) a.1 ≤ pool.holdings a.1 ∧
        vertex_load demands (S ∪ {a} ∪ {b}) b.1 ≤ pool.holdings b.1) ↔
      (vertex_load demands (S ∪ {a} ∪ {b}) a.1 ≤ pool.holdings a.1 ∧
        vertex_load demands (S ∪ {a} ∪ {b}) b.1 ≤ pool.holdings b.1) := by
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, hb⟩
    by_cases hsrc : b.1 = a.1
    · rw [← hsrc]
      exact hb
    · rw [vertex_load_union_other _ hsrc]
      exact ha
  · rintro ⟨ha, hb⟩
    exact ⟨(vertex_load_mono h_nn Finset.subset_union_left a.1).trans ha, hb⟩

/-- ★ Sous demandes ≥ 0, le screening partiel est commutatif. -/
theorem screen_commutative (h_nn : ∀ e, 0 ≤ demands e) :
    IsCommutativePA (screenP pool demands) := by
  rw [screenP_eq_load]
  refine isCommutativePA_ofGated (fun S a b => Finset.union_right_comm S {a} {b})
    (fun S a b h => ?_)
  have h' := (screen_pair_iff h_nn S a b).mp h
  rw [Finset.union_right_comm S {a} {b}] at h'
  exact (screen_pair_iff h_nn S b a).mpr ⟨h'.2, h'.1⟩

/-- ★ Le screening est stablement concurrent (Déf. 2.4). -/
theorem screen_stablyConcurrent (h_nn : ∀ e, 0 ≤ demands e) :
    StablyConcurrent (screenP pool demands) :=
  stablyConcurrent_of_commutative (screen_commutative h_nn)

/-- ★ Le screening vérifie S2 (Déf. 2.1). -/
theorem screen_S2 (h_nn : ∀ e, 0 ≤ demands e) : S2 (screenP pool demands) :=
  S2_of_commutative (screen_commutative h_nn)

/-- ★ Pont avec `budgetGatedCommute` : si chaque arête est seule admissible, la concurrence
    maximale à l'état vide coïncide avec la commutation budget-gated, donc avec la commutation
    des deux `admissionFold` (`budgetGatedCommute_iff`). -/
theorem screen_maxPar_iff_budgetGated (h_nn : ∀ e, 0 ≤ demands e) {a b : V × V} (h_ne : a ≠ b)
    (h₁ : demands a ≤ pool.holdings a.1) (h₂ : demands b ≤ pool.holdings b.1) :
    (maxPar (screenP pool demands) ∅ a b ↔ budgetGatedCommute pool demands a b) ∧
      (maxPar (screenP pool demands) ∅ a b ↔
        admissionFold pool demands [a, b] = admissionFold pool demands [b, a]) := by
  have key : maxPar (screenP pool demands) ∅ a b ↔ budgetGatedCommute pool demands a b := by
    rw [maxPar_iff_of_commutative (screen_commutative h_nn), screenP_eq_load, screenLoadP,
      isSome_run_ofGated_pair, Finset.empty_union, vertex_load_singleton]
    simp only [ne_eq, h_ne, not_false_eq_true, true_and]
    unfold budgetGatedCommute
    by_cases hsrc : a.1 = b.1
    · rw [if_pos hsrc, ← hsrc, ← Finset.insert_eq, vertex_load_pair demands a b h_ne hsrc]
      exact ⟨fun h => h.2, fun h => ⟨h₁, h⟩⟩
    · rw [if_neg hsrc, vertex_load_cross _ _ _ hsrc]
      exact iff_of_true ⟨h₁, h₂⟩ trivial
  exact ⟨key, key.trans (budgetGatedCommute_iff pool demands a b h_ne h₁ h₂)⟩

end Screening

section ScreeningSigned

open DualDAG (FuturePool)

/-- Avoirs du contre-exemple : une unité au sommet `0`, rien ailleurs. -/
def pool₀ : FuturePool (Fin 4) :=
  ⟨fun v => if v = 0 then 1 else 0, fun v => by beta_reduce; split_ifs <;> norm_num⟩

/-- Demandes signées : `(0,1)` et `(0,2)` demandent une unité, `(0,3)` en REND une. -/
def demands₀ : Fin 4 × Fin 4 → ℤ := fun e =>
  if e = (0, 1) ∨ e = (0, 2) then 1 else if e = (0, 3) then -1 else 0

/-- Témoin du cube à l'état vide, `(a, b, c) = ((0,1), (0,2), (0,3))` : membre gauche vrai
    (`a ∥ c`, `b ∥ c`, et après `c` la charge de `a` et `b` vaut 1) ; `a ∥ b` faux (charge
    2 > 1). Calcul sur la charge (`screenP_eq_load`), sans déplier le point fixe. -/
theorem screen_signed_witness :
    (maxPar (screenP pool₀ demands₀) ∅ (0, 1) (0, 3) ∧
        maxPar (screenP pool₀ demands₀) ∅ (0, 2) (0, 3) ∧
        parAfter (screenP pool₀ demands₀) ∅ (0, 3) (0, 1) (0, 2)) ∧
      ¬ maxPar (screenP pool₀ demands₀) ∅ (0, 1) (0, 2) := by
  rw [screenP_eq_load]
  decide

/-- ★ Une demande négative casse la stabilité du screening : le membre gauche du cube est vrai,
    le membre droit faux (`screen_signed_witness`). -/
theorem screen_signed_not_stable : ¬ StablyConcurrent (screenP pool₀ demands₀) := fun h =>
  screen_signed_witness.2 ((h ∅ (0, 1) (0, 2) (0, 3)).mp screen_signed_witness.1).1

end ScreeningSigned

/-! ### 3. M(1,2) : rectangle contre polytope -/

section M12

open RightsCurrencies (Burn Load addLoad rectStep polyStep I_right addLoad_comm sum_addLoad
  polytope_not_diamond)
open GatedStep (Diamond)

/-- Porte rectangle partielle : un burn au-delà du plafond de son droit n'est pas tirable. -/
def rectP (Bcap : Fin 2 → ℕ) : PAut Load Burn :=
  ofGated (fun L a => L a.1 + a.2 ≤ Bcap a.1) addLoad

/-- Porte polytope partielle : un burn au-delà du plafond couplé n'est pas tirable. -/
def polyP (C : ℕ) : PAut Load Burn :=
  ofGated (fun L a => L 0 + L 1 + a.2 ≤ C) addLoad

/-- La porte rectangle partielle est commutative : même droit, « `a` puis `b` » passe ssi la
    somme des deux burns tient sous le plafond ; droits distincts, les tests sont séparés. -/
theorem rect_commutative (Bcap : Fin 2 → ℕ) : IsCommutativePA (rectP Bcap) :=
  isCommutativePA_ofGated addLoad_comm (fun L ⟨i, x⟩ ⟨j, y⟩ h => by
    simp only [addLoad] at h ⊢
    by_cases hij : i = j
    · subst hij
      simp only [if_true] at h ⊢
      omega
    · simp only [hij, Ne.symm hij, if_false] at h ⊢
      exact ⟨h.2, h.1⟩)

/-- La porte polytope partielle est commutative : « `a` puis `b` » passe ssi la charge totale
    plus les deux burns tient sous `C` (`sum_addLoad`). -/
theorem poly_commutative (C : ℕ) : IsCommutativePA (polyP C) :=
  isCommutativePA_ofGated addLoad_comm (fun L a b h => by
    rw [sum_addLoad] at h ⊢
    omega)

/-- ★ Porte rectangle partielle : stablement concurrente et S2. -/
theorem rect_stable (Bcap : Fin 2 → ℕ) : StablyConcurrent (rectP Bcap) ∧ S2 (rectP Bcap) :=
  stable_of_commutative (rect_commutative Bcap)

/-- ★ Porte polytope partielle : stablement concurrente et S2. -/
theorem poly_stable (C : ℕ) : StablyConcurrent (polyP C) ∧ S2 (polyP C) :=
  stable_of_commutative (poly_commutative C)

/-- La sémantique totale de la porte rectangle partielle est `rectStep`. -/
theorem toTotal_rectP (Bcap : Fin 2 → ℕ) : toTotal (rectP Bcap) = rectStep Bcap :=
  toTotal_ofGated _ _

/-- ★ Sémantique partielle contre sémantique totale : la porte polytope est commutative et
    stablement concurrente quand un rejet rend la lettre non tirable ; sa sémantique totale
    (rejet = boucle) est `polyStep`, qui n'a pas de losange pour `I_right` (classe D). -/
theorem polytope_partial_vs_total {C : ℕ} (hC : 1 ≤ C) :
    IsCommutativePA (polyP C) ∧ StablyConcurrent (polyP C) ∧ toTotal (polyP C) = polyStep C ∧
      ¬ Diamond (polyStep C) I_right :=
  ⟨poly_commutative C, stablyConcurrent_of_commutative (poly_commutative C),
    toTotal_ofGated _ _, polytope_not_diamond hC⟩

end M12

/-! ### 4. Communs gérés par épuisement -/

section Commons

open PlanetaryLedger (Footprint deplete gsupp stockAdmissible)
open TokenizedCommons (Attribution holder burn rightsAdmissible burn_comm)

variable {V B : Type*}

/-- Clé scalaire : si deux consommations `x, y ≥ 0` d'une même place `s` passent dans l'ordre
    `x, y`, elles passent dans l'ordre `y, x` (un prélèvement nul n'est pas testé). -/
lemma pair_swap {x y s : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : (x ≠ 0 → x ≤ s) ∧ (y ≠ 0 → y ≤ s - x)) : (y ≠ 0 → y ≤ s) ∧ (x ≠ 0 → x ≤ s - y) := by
  omega

/-- La clé scalaire, place par place sur les frontières gardées. -/
lemma pair_swap_on {G : Finset B} {x y s : B → ℤ} (hx : ∀ c ∈ G, 0 ≤ x c)
    (hy : ∀ c ∈ G, 0 ≤ y c) (ha : ∀ c ∈ G, x c ≠ 0 → x c ≤ s c)
    (hb : ∀ c ∈ G, y c ≠ 0 → y c ≤ s c - x c) :
    (∀ c ∈ G, y c ≠ 0 → y c ≤ s c) ∧ ∀ c ∈ G, x c ≠ 0 → x c ≤ s c - y c :=
  ⟨fun c hc => (pair_swap (hx c hc) (hy c hc) ⟨ha c hc, hb c hc⟩).1,
    fun c hc => (pair_swap (hx c hc) (hy c hc) ⟨ha c hc, hb c hc⟩).2⟩

/-- Stocks planétaires seuls, en sémantique partielle : un paiement est tirable ssi chaque stock
    gardé couvre son émission ; tous les stocks sont alors prélevés. -/
def stockP (fp : Footprint V B) : PAut (B → ℤ) (V × V) :=
  ofGated (fun s e => stockAdmissible fp s e) (fun s e => deplete fp e s)

/-- Sous émissions gardées ≥ 0, les stocks seuls forment un automate commutatif. -/
theorem stock_commutative {fp : Footprint V B} (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    IsCommutativePA (stockP fp) :=
  isCommutativePA_ofGated (fun s a b => funext fun c => sub_right_comm (s c) _ _)
    (fun s a b ⟨ha, hb⟩ => by
      simp only [stockAdmissible, deplete, gsupp, Finset.mem_filter, and_imp] at ha hb ⊢
      exact pair_swap_on (h_emit a) (h_emit b) ha hb)

/-- ★ Les stocks planétaires seuls sont stablement concurrents et vérifient S2. -/
theorem deplete_stable {fp : Footprint V B} (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    StablyConcurrent (stockP fp) ∧ S2 (stockP fp) :=
  stable_of_commutative (stock_commutative h_emit)

variable [DecidableEq V]

/-- Droits non transférables, en sémantique partielle : un paiement est tirable ssi son
    détenteur a les droits gardés ; ses droits sont alors brûlés. -/
def burnP (att : Attribution) (fp : Footprint V B) : PAut (V → B → ℤ) (V × V) :=
  ofGated (rightsAdmissible att fp) (fun r e => burn att fp e r)

/-- Sous émissions gardées ≥ 0, les droits seuls forment un automate commutatif : même
    détenteur, c'est le cas des stocks ; détenteurs distincts, les tests sont indépendants. -/
theorem burn_commutative {att : Attribution} {fp : Footprint V B}
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) : IsCommutativePA (burnP att fp) :=
  isCommutativePA_ofGated (fun r a b => burn_comm att fp b a r) (fun r a b ⟨ha, hb⟩ => by
    simp only [rightsAdmissible, burn, gsupp, Finset.mem_filter, and_imp] at ha hb ⊢
    by_cases hh : holder att a = holder att b
    · simp only [hh, if_true] at ha hb ⊢
      exact pair_swap_on (h_emit a) (h_emit b) ha hb
    · simp only [hh, Ne.symm hh, if_false, sub_zero] at hb ⊢
      exact ⟨hb, ha⟩)

/-- ★ Les droits non transférables sont stablement concurrents et vérifient S2. -/
theorem burn_stable {att : Attribution} {fp : Footprint V B}
    (h_emit : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    StablyConcurrent (burnP att fp) ∧ S2 (burnP att fp) :=
  stable_of_commutative (burn_commutative h_emit)

end Commons

end DepletionStable
