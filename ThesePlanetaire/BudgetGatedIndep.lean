/-
  BudgetGatedIndep.lean — Portage canonique étape 4 (R.C/R.D, G4) :
  budgetGatedCommute — prédicat de commutation budget-gated sur V×V.

  Provenance : scratch budgetGatedIndep_scratch, porté verbatim (3 changements :
  namespace, suppression des #print axioms, résolution des collisions).

  ★ REFRAME de l'étape 4 (finding de dérisque, propagé au portage) :
  le plan disait « Généraliser DynamicIndependence (TraceAdmissibility:63, fixé à
  Letter) à α ». L'exploration canonique révèle que c'est SUR-SCOPÉ ET NON REQUIS :
  (a) DynamicIndependence est une `structure` NON-paramétrée (pas une classe, PAS
      d'`instance : DynamicIndependence` — le rôle « instance Letter » est joué par
      des `def` : cocktail_di, static_cocktail_di, static_r1_di:435).
  (b) Elle est COUPLÉE à Independence (TraceMonoid:169) ET CartierFoata
      (TraceMonoid:233), TOUTES DEUX Letter-hardcodées (champ `.id`, `b.id < a.id`).
  (c) Le type d'état (Finset Letter) et le type d'alphabet (Letter) sont couplés.
  (d) Blast radius = 11 déclarations dans TraceAdmissibility.lean (et généraliser
      vraiment exigerait AUSSI Independence/CartierFoata → TraceMonoid.lean).
  SURTOUT : l'étape 5 (traceQuotient_scratch) a FERMÉ SANS DynamicIndependence
  (setoid toFinset-éq + sufficient_budget_order_independent DualDAG:1556).
  ⟹ Le besoin RÉEL R.C/R.D = un PRÉDICAT de commutation budget-gated sur V×V, FRAIS,
  réutilisant order_dependence_iff (DualDAG:665) + order_independence_sufficient
  (DualDAG:619). NE PAS toucher DynamicIndependence — blast radius sur
  r1_indep/r1_cf/admissible_k2 = ZÉRO.

  Le prédicat :
    budgetGatedCommute pool demands e₁ e₂ :=
      if e₁.1 = e₂.1 then demands e₁ + demands e₂ ≤ pool.holdings e₁.1 else True
  - same-source (e₁.1 = e₂.1) : commute ssi sum ≤ holdings (négation de order_dependence_iff).
  - cross-source (e₁.1 ≠ e₂.1) : commute toujours (les admissions ne disputent pas le
    même holdings — e₁ ne charge pas le sommet e₂.1).

  Gotcha D4 préservé (vertex_load_cross) : garder les `have h1/h2` avec
  `rw [Finset.filter_singleton, if_neg h_src]` explicites — `simp only
  [Finset.filter_singleton]` sur-réduit et laisse `if True then _ else _` que
  `if_neg`/`if_pos` ne matche plus.

  Build : cd lean4 && lake build ThesePlanetaire.BudgetGatedIndep
-/

import Mathlib.Tactic
import ThesePlanetaire.DualDAG
import ThesePlanetaire.GatedStep

namespace BudgetGatedIndep

open DualDAG (FuturePool vertex_load admissionFold isAdmissible isAdmissible_empty_iff
              isAdmissible_iff_load order_dependence_iff order_independence_sufficient)
open GatedStep (union_singleton_comm insertStep_comm foldl_swap_of_step_comm)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Le prédicat budgetGatedCommute (fresh, état-indépendant) -/

/-- Prédicat de commutation budget-gated sur V×V (R.C/R.D, G4).
    Same-source : commute ssi la somme des demandes ≤ budget du sommet source.
    Cross-source : commute toujours (les admissions ne disputent pas le même holdings).
    État-INDÉPENDANT (pas de stateDepIndep — contrairement à DynamicIndependence). -/
def budgetGatedCommute (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V) : Prop :=
  if e₁.1 = e₂.1 then demands e₁ + demands e₂ ≤ pool.holdings e₁.1 else True

/-! ### 2. Cross-source — la charge ignore l'arête hors-sommet -/

/-- La charge en e₂.1 d'un ensemble contenant e₁ (e₁.1 ≠ e₂.1) ignore e₁ :
    `vertex_load ({e₁} ∪ {e₂}) e₂.1 = demands e₂`. Sous-lemme clé du cross-source.
    (Finset.filter_union distribue le filtre ; {e₁}.filter p = ∅ car e₁.1 ≠ e₂.1.) -/
lemma vertex_load_cross (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_src : e₁.1 ≠ e₂.1) :
    vertex_load demands ({e₁} ∪ {e₂} : Finset (V × V)) e₂.1 = demands e₂ := by
  unfold vertex_load
  rw [Finset.filter_union]
  -- {e₁}.filter (x.1 = e₂.1) = ∅ : e₁.1 ≠ e₂.1 (h_src), e₁ filtré du load en e₂.1
  have h1 : (({e₁} : Finset (V × V)).filter fun x => x.1 = e₂.1) = ∅ := by
    rw [Finset.filter_singleton, if_neg h_src]
  -- {e₂}.filter (x.1 = e₂.1) = {e₂} : e₂.1 = e₂.1 par rfl
  have h2 : (({e₂} : Finset (V × V)).filter fun x => x.1 = e₂.1) = {e₂} := by
    rw [Finset.filter_singleton, if_pos rfl]
  rw [h1, h2, Finset.empty_union, Finset.sum_singleton]

/-! ### 3. Cross-source commute toujours (NEW — non couvert par order_independence_sufficient) -/

/-- Cross-source : e₁.1 ≠ e₂.1 (⟹ e₁ ≠ e₂), chaque arête individuellement admissible ⟹
    les deux ordres produisent {e₁, e₂}. Via isAdmissible_iff_load + vertex_load_cross
    (l'arête hors-sommet ne charge pas le holdings disputé). Miroir de
    order_independence_sufficient (DualDAG:615-653) mais SANS h_src. SANS h_nn (signées OK). -/
lemma cross_source_commute (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_src : e₁.1 ≠ e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1) (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    admissionFold pool demands [e₁, e₂] = admissionFold pool demands [e₂, e₁] := by
  have h_adm₁ : isAdmissible pool demands ∅ e₁ := (isAdmissible_empty_iff _ _ _).mpr h₁
  have h_adm₂ : isAdmissible pool demands ∅ e₂ := (isAdmissible_empty_iff _ _ _).mpr h₂
  have h_adm₂₁ : isAdmissible pool demands {e₁} e₂ := by
    rw [isAdmissible_iff_load, vertex_load_cross _ _ _ h_src]
    exact h₂
  have h_adm₁₂ : isAdmissible pool demands {e₂} e₁ := by
    rw [isAdmissible_iff_load, vertex_load_cross _ _ _ h_src.symm]
    exact h₁
  -- dépliage foldl (miroir order_independence_sufficient DualDAG:638-639)
  simp only [admissionFold, List.foldl_cons, List.foldl_nil]
  simp only [h_adm₁, h_adm₂, h_adm₂₁, h_adm₁₂, if_true, Finset.empty_union]
  -- reste {e₁} ∪ {e₂} = {e₂} ∪ {e₁} (union commutative des Finset)
  ac_rfl

/-! ### 4. Same-source — commute ssi sum ≤ holdings (order_dependence_iff DualDAG:665) -/

/-- Same-source : e₁.1 = e₂.1, h₁, h₂ ⟹ (admissionFold [e₁,e₂] = [e₂,e₁]) ↔
    (demands e₁ + demands e₂ ≤ holdings e₁.1).
    ← via order_independence_sufficient (DualDAG:619, sum ≤ budget ⟹ {e₁,e₂} les 2 ordres).
    → via order_dependence_iff (DualDAG:665, contrapositive : sum > budget ⟹ ≠). -/
theorem same_source_commute_iff (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_ne : e₁ ≠ e₂) (h_src : e₁.1 = e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1) (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    (admissionFold pool demands [e₁, e₂] = admissionFold pool demands [e₂, e₁]) ↔
      demands e₁ + demands e₂ ≤ pool.holdings e₁.1 := by
  constructor
  · intro h_eq
    by_contra h_le
    push_neg at h_le
    -- h_le : sum > holdings. order_dependence_iff : admissionFold ≠ ↔ sum > holdings.
    have h_dep := (order_dependence_iff pool demands e₁ e₂ h_ne h_src h₁ h₂).mpr h_le
    exact h_dep h_eq
  · intro h_sum
    have ⟨h_eq₁, h_eq₂⟩ :=
      order_independence_sufficient pool demands e₁ e₂ h_ne h_src h_sum h₁ h₂
    exact h_eq₁.trans h_eq₂.symm

/-! ### 5. La caractérisation unifiée -/

/-- ★ budgetGatedCommute_iff (sous h_ne, h₁, h₂) : le prédicat budget-gated caractérise
    EXACTEMENT la commutation de admissionFold pour une paire. Same-source via (4),
    cross-source via (3). C'est le lemme-clef R.C/R.D : la commutation budget-gated
    descend au quotient toFinset-éq (étape 5). -/
theorem budgetGatedCommute_iff (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_ne : e₁ ≠ e₂)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1) (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    budgetGatedCommute pool demands e₁ e₂ ↔
      admissionFold pool demands [e₁, e₂] = admissionFold pool demands [e₂, e₁] := by
  constructor
  · intro h_comm
    by_cases hsrc : e₁.1 = e₂.1
    · rw [budgetGatedCommute, if_pos hsrc] at h_comm
      exact (same_source_commute_iff _ _ _ _ h_ne hsrc h₁ h₂).mpr h_comm
    · exact cross_source_commute _ _ _ _ hsrc h₁ h₂
  · intro h_eq
    by_cases hsrc : e₁.1 = e₂.1
    · rw [budgetGatedCommute, if_pos hsrc]
      exact (same_source_commute_iff _ _ _ _ h_ne hsrc h₁ h₂).mp h_eq
    · rw [budgetGatedCommute, if_neg hsrc]
      exact trivial

/-! ### 6. Clôture G3a (T5, plan v3.2 §Étape 3) — portée Mazurkiewicz = paires indépendantes

  Décisions A7 ratifiées par l'utilisateur (`cache/verification.md`, round 2 du plan
  d'intégration v3.2 couche dynamique) :
  - sémantique de règlement intra-période de `TimedGame` = **séquentielle**
    (`admissionFold` sur liste, test-and-keep) ;
  - portée du réordonnancement visé par T5 = **(β) I-respectueux seulement** — seuls les
    réordonnancements échangeant des lettres INDÉPENDANTES (relation I fixée) sont requis
    invariants, conformément au sens standard d'une classe de Mazurkiewicz. C'est aussi une
    précondition de cohérence interne pour que B_p/P4/P5 (qui vivent sur le poset des traces,
    pas sur les mots bruts) soient bien posés.

  ★★ CORRECTION (§V135, conseil advisor, vérifiée par calcul — voir `budgetGatedCommute_not_
  context_invariant` plus bas) : la relation I RÉELLEMENT invariante par contexte n'est PAS
  `budgetGatedCommute` dans son ensemble, mais SEULEMENT sa branche cross-source (sources
  distinctes). Sa branche same-source (sum ≤ holdings, paire isolée) satisfait le prédicat
  `budgetGatedCommute` mais NE SURVIT PAS à un préfixe non vide : un témoin à 3 arêtes même
  source (c, a, b, holdings=5, demandes 1/2/3) a `budgetGatedCommute a b` vrai (2+3≤5 depuis
  ∅) mais `admissionFold [c,a,b] = {c,a} ≠ {c,b} = admissionFold [c,b,a]` — la charge
  antérieure de `c` fait basculer le budget contesté. I = **sources distinctes** (pas tout
  `budgetGatedCommute`), et sa branche cross-source (`cross_source_commute`, §3 ci-dessus) est
  l'ingrédient de base de l'énoncé requis : toute paire d'arêtes de sources distinctes commute
  inconditionnellement — DEPUIS ∅. ★ CORRECTION ANTÉRIEURE (§V134, conseil advisor) : ceci
  n'est que le CAS DE BASE. Une classe de Mazurkiewicz exige l'échange dans TOUT contexte, pas
  seulement depuis l'état vide (`admissionFold` étant À ÉTAT, un swap depuis ∅ n'implique pas
  le swap depuis un état quelconque accumulé par un préfixe). Le résultat réellement requis
  pour clore G3a est `cone_commutation_invariant` (§7 ci-dessous), qui généralise à un contexte
  arbitraire — ET restreint I à sources distinctes dès l'hypothèse `h_src`, donc n'hérite PAS
  du problème ci-dessus (il n'a jamais prétendu couvrir la branche same-source). Ce lemme-ci
  (`independent_pairs_commute`) reste vrai et est maintenant un corollaire trivial de §7 (cas
  `u = w = []`), conservé pour sa valeur documentaire (portage direct du nom suggéré par le
  plan avant la correction d'échelle). -/

/-- **Cas de base de la clôture G3a (T5)**, DEPUIS ∅ seulement — voir `cone_commutation_invariant`
    (§7) pour l'énoncé complet dans un contexte arbitraire, qui est ce qui clôt réellement G3a.
    Sous la portée (β) ratifiée (réordonnancements I-respectueux seulement, I = **sources
    distinctes** — PAS tout `budgetGatedCommute`, dont la branche same-source ne survit pas au
    contexte, cf. §V135/`budgetGatedCommute_not_context_invariant`), toute paire d'arêtes
    INDÉPENDANTES (sources distinctes) commute inconditionnellement dans
    `admissionFold [e₁,e₂]` vs `[e₂,e₁]` — exactement `cross_source_commute`, renommé pour
    exposer le résultat au niveau T5/Mazurkiewicz.

    ★ PORTÉE : ce théorème couvre UNIQUEMENT les paires indépendantes (cross-source,
    `h_src : e₁.1 ≠ e₂.1`). Les paires DÉPENDANTES (même source, budget contesté — p. ex.
    e1/e2 de `pool3`, témoin `DualDAG.admission_is_order_dependent`) sont HORS CHAMP par
    construction de l'énoncé — pas un cas non couvert par accident. `admission_is_order_dependent`
    illustre précisément pourquoi cette restriction aux paires indépendantes est nécessaire et
    non cosmétique : sur une paire dépendante, l'ordre d'admission détermine un ensemble
    différent de transactions retenues (aucune invariance ne tient). La question institutionnelle
    de la règle de priorité entre réclamations concurrentes dépendantes reste ouverte et est
    HORS SCOPE de ce théorème et de ce plan — elle n'est pas une faille à fermer ici. -/
theorem independent_pairs_commute (pool : FuturePool V) (demands : V × V → ℤ) (e₁ e₂ : V × V)
    (h_src : e₁.1 ≠ e₂.1)
    (h₁ : demands e₁ ≤ pool.holdings e₁.1) (h₂ : demands e₂ ≤ pool.holdings e₂.1) :
    admissionFold pool demands [e₁, e₂] = admissionFold pool demands [e₂, e₁] :=
  cross_source_commute pool demands e₁ e₂ h_src h₁ h₂

/-! ### 7. Clôture G3a, niveau CLASSE (contexte arbitraire) — correction §V134

  §6 ne compare que `[e₁,e₂]` vs `[e₂,e₁]` DEPUIS ∅. Une classe de Mazurkiewicz exige
  l'échange dans TOUT contexte : `admissionFold (u ++ a :: b :: w) = admissionFold
  (u ++ b :: a :: w)` pour `a.1 ≠ b.1`, quel que soit l'état accumulé par le préfixe `u`
  ET le reste `w`. Cette section généralise `vertex_load_cross`/`cross_source_commute` à un
  état de départ arbitraire `S` (au lieu de ∅), établit la commutation du PAS de fold depuis
  `S`, puis relève le résultat à toute liste via `List.foldl_append`. Remarquablement, AUCUNE
  hypothèse de budget individuel (`h₁`/`h₂` de §3/§6) n'est nécessaire ici : l'admissibilité
  depuis `S` ne dépend que de la charge en `S`, inchangée par l'ajout d'une arête de source
  différente — c'est une propriété purement structurelle (sources disjointes), pas une
  propriété de budget. -/

/-- Généralisation de `vertex_load_cross` à un état `S` quelconque (pas seulement
    `{e₁} ∪ {e₂}`) : insérer `b` (source ≠ `v`) dans `S` ne change pas la charge en `v`. -/
lemma vertex_load_insert_other (demands : V × V → ℤ) (S : Finset (V × V)) (b : V × V) (v : V)
    (h_src : b.1 ≠ v) :
    vertex_load demands (S ∪ {b}) v = vertex_load demands S v := by
  unfold vertex_load
  rw [Finset.filter_union]
  have hb : (({b} : Finset (V × V)).filter fun x => x.1 = v) = ∅ := by
    rw [Finset.filter_singleton, if_neg h_src]
  rw [hb, Finset.union_empty]

/-- L'admissibilité de `a` depuis `S` est inchangée par l'ajout préalable de `b`
    (sources distinctes) : `b` ne charge pas `a.1`, donc ne peut ni faire échouer ni
    faire réussir le test de charge de `a`. Pivot de la commutation de pas (ci-dessous). -/
lemma isAdmissible_insert_other (pool : FuturePool V) (demands : V × V → ℤ)
    (S : Finset (V × V)) (a b : V × V) (h_src : a.1 ≠ b.1) :
    isAdmissible pool demands (S ∪ {b}) a ↔ isAdmissible pool demands S a := by
  rw [isAdmissible_iff_load, isAdmissible_iff_load, union_singleton_comm S b a,
    vertex_load_insert_other demands (S ∪ {a}) b a.1 h_src.symm]

/-- Le pas élémentaire de `admissionFold` (test-and-keep), isolé pour l'induction de
    contexte ci-dessous. Defeq à la lambda interne de `admissionFold` (DualDAG:340). -/
private def admitStep (pool : FuturePool V) (demands : V × V → ℤ) :
    Finset (V × V) → V × V → Finset (V × V) :=
  fun cur e => if isAdmissible pool demands cur e then cur ∪ {e} else cur

/-- `admissionFold` est le foldl de `admitStep` depuis ∅ — pur dépliage (les deux lambdas
    sont syntaxiquement identiques). -/
lemma admissionFold_eq_foldl_admitStep (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) :
    admissionFold pool demands edges = edges.foldl (admitStep pool demands) ∅ := by
  unfold admissionFold admitStep
  rfl

/-- ★ Commutation du PAS de fold depuis un état `S` QUELCONQUE (pas seulement ∅), pour une
    paire de sources distinctes. Généralise `cross_source_commute`. Instance de
    `GatedStep.insertStep_comm` (l'analyse à 4 cas y est faite une fois) :
    `isAdmissible_insert_other` montre que l'admissibilité de l'un depuis `S` est inchangée par
    l'insertion préalable de l'autre (sources distinctes), donc les deux ordres atteignent le
    même état final. -/
lemma admitStep_comm_of_cross_source (pool : FuturePool V) (demands : V × V → ℤ)
    (S : Finset (V × V)) (a b : V × V) (h_src : a.1 ≠ b.1) :
    admitStep pool demands (admitStep pool demands S a) b =
    admitStep pool demands (admitStep pool demands S b) a :=
  insertStep_comm (isAdmissible_insert_other pool demands S a b h_src)
    (isAdmissible_insert_other pool demands S b a h_src.symm)

/-- ★★ **Clôture G3a (T5), énoncé de classe réel** : dans TOUT contexte (préfixe `u`, suffixe
    `w`), échanger une paire d'arêtes INDÉPENDANTES (sources distinctes) laisse `admissionFold`
    invariant. C'est l'énoncé de commutation Mazurkiewicz standard — plus fort que
    `independent_pairs_commute` (qui n'est que le cas `u = w = []`), et c'est CE théorème,
    pas §6, qui clôt réellement G3a sous la portée (β) ratifiée (réordonnancements
    I-respectueux seulement, I = **sources distinctes** — PAS tout `budgetGatedCommute`,
    dont la branche same-source ne passe pas au contexte, cf. §V135 ci-dessous).

    ★ PORTÉE (inchangée par rapport à §6) : ce théorème couvre UNIQUEMENT les paires
    indépendantes (cross-source, `h_src : a.1 ≠ b.1`). Les paires DÉPENDANTES (même source,
    budget contesté — témoin `DualDAG.admission_is_order_dependent`) restent HORS CHAMP par
    construction de l'énoncé : pour elles, aucune invariance de contexte ne tient, et la
    question institutionnelle de la règle de priorité entre réclamations concurrentes
    dépendantes reste ouverte et hors scope de ce plan.

    ★ Remarquablement, AUCUNE hypothèse de budget individuel n'est requise (contrairement à
    §3/§6) : la commutation cross-source est purement structurelle. -/
theorem cone_commutation_invariant (pool : FuturePool V) (demands : V × V → ℤ)
    (u w : List (V × V)) (a b : V × V) (h_src : a.1 ≠ b.1) :
    admissionFold pool demands (u ++ a :: b :: w) =
    admissionFold pool demands (u ++ b :: a :: w) := by
  simp only [admissionFold_eq_foldl_admitStep]
  exact foldl_swap_of_step_comm _ ∅ u w (admitStep_comm_of_cross_source pool demands _ a b h_src)

/-- `independent_pairs_commute` est le cas `u = w = []` de `cone_commutation_invariant` —
    lien explicite entre §6 (porté en premier, depuis ∅ seulement) et §7 (l'énoncé complet). -/
example (pool : FuturePool V) (demands : V × V → ℤ) (a b : V × V) (h_src : a.1 ≠ b.1) :
    admissionFold pool demands [a, b] = admissionFold pool demands [b, a] :=
  cone_commutation_invariant pool demands [] [] a b h_src

/-! ### 8. Témoin — la branche same-source de `budgetGatedCommute` n'est PAS I (§V135)

  Justifie pourquoi §6/§7 restreignent I aux sources distinctes plutôt qu'à tout
  `budgetGatedCommute` : un témoin à 3 arêtes où une paire same-source satisfait le prédicat
  `budgetGatedCommute` (pairwise, depuis ∅) mais où le préfixe non vide `[c]` fait basculer le
  budget contesté et brise l'invariance de contexte. Miroir de
  `DualDAG.admission_is_order_dependent` (même rôle : justifier une restriction, pas un
  accident). -/

/-- **Témoin** : `budgetGatedCommute` (pairwise, depuis ∅) ne garantit PAS l'invariance de
    contexte sur sa branche same-source — contrairement à la branche cross-source
    (`cone_commutation_invariant`). Holdings(0)=5, demandes c↦1, a↦2, b↦3 : `a`,`b` same-source
    satisfont `budgetGatedCommute a b` (2+3≤5 depuis ∅), mais `[c,a,b] → {c,a}` tandis que
    `[c,b,a] → {c,b}` (la charge de `c` fait passer le total à 6>5 selon l'ordre). -/
theorem budgetGatedCommute_not_context_invariant :
    ∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ) (c a b : Fin 3 × Fin 3),
      budgetGatedCommute pool demands a b ∧
      admissionFold pool demands [c, a, b] ≠ admissionFold pool demands [c, b, a] := by
  refine ⟨⟨fun v => if v = (0 : Fin 3) then 5 else 10, by decide⟩,
    fun e => if e = ((0 : Fin 3), (0 : Fin 3)) then 1
             else if e = ((0 : Fin 3), (1 : Fin 3)) then 2
             else if e = ((0 : Fin 3), (2 : Fin 3)) then 3
             else 0,
    ((0 : Fin 3), (0 : Fin 3)), ((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)), ?_, ?_⟩
  · unfold budgetGatedCommute
    decide
  · decide

end BudgetGatedIndep
