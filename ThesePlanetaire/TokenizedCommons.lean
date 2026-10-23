/-
  ThesePlanetaire/TokenizedCommons.lean
  Phase 5a (2026-10-02) : le commun gardé tokenisé — droits individuels brûlés à l'usage
  (L₃ du ch. 10, modèle M(1,2) du corpus CoucheDynamique), T-M12-1, T5 en hiérarchie, bloc
  biens walrasien, Coase.

  Développé d'abord en `TokenizedCommons_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 5, étape 5a, et « Lecture critique du
  plan ») ; analyse : `cache/analyse_marche_communs_2026-10-02.md`.

  La garde FCFS du grand livre planétaire (`PlanetaryLedger`) fait du stock gardé un COMPTE
  COMMUN : deux paiements `I_loc`-indépendants se le disputent et l'ordre attribue le budget
  (`climate_commons`). Tokeniser remplace ce compte par des comptes de droits individuels
  (`RState.rights : V → B → ℤ`), débités à l'usage (burn) chez le détenteur désigné par une
  `Attribution` (payeur par défaut).

  Positionnement dans le marché modulaire (`maj_artefact_modeles_marche_compatibles`) :
  §1-§4 relèvent de la COUCHE D'EXÉCUTION (adjacente : mécanique du règlement, pas un
  théorème de bien-être) ; §5-§6 du BLOC BIENS (compatible strict sous substituts bruts).

  1. [exécution] ★ `tkStep_comm` : losange pour `I_tk att`, relation SANS empreinte (la lecture
     est locale) ; forme fine ★ `tkStep_comm_fine` pour `I_tkfp` = `I_loc` ∧ (détenteurs
     distincts ∨ empreintes gardées disjointes). ★ `I_planet_le_I_tk_consumer` (inclusion
     stricte, témoin : le commun climatique). Attribution producteur :
     `I_planet_not_le_I_tk_producer` — la relation sans empreinte ne contient pas `I_planet`,
     mais la dynamique commute ces paires (`I_planet_le_I_tkfp`) : l'écart est de
     déclaration. ★ `tk_conservation`, ★ `tk_cap` (émissions ≤ Σ dotation = C_plan) ;
  2. [exécution] ★ T-M12-1 `tokenized_gate_iff_budget_gate` (admission intégrale, émissions
     gardées ≥ 0, budget ≥ 0) : règlement intégral sous la porte centrale de budget `S` ⟺
     ∃ dotation ρ ≥ 0 de total `S` sous laquelle il se règle par burn. C'est une IDENTITÉ
     D'AGRÉGATION (Σ_v cum_v = cum, `sum_holderCum`) ; le cas partiel (rejets) n'est pas
     couvert ;
  3. [exécution] commun climatique : ★ `endowment_decides` (la dotation, pas l'ordre, fixe qui
     émet), ★ `tk_same_holder_order` (T résiduel chez un même détenteur), ★
     `producer_attribution_conflict` (au receveur commun, le commun est reconstitué), ★
     `commons_D_rel_Iloc` (file : D relativement à `I_loc`), ★ `tokens_T_rel_Iloc` (jetons
     consommateur : T), `tokens_producer_D_rel_Iloc` (jetons producteur : D) ;
  4. [exécution] T5 en hiérarchie, lettres `Option` (`none` = top) : ★ `fcfs_not_diamond_tick`,
     ★ `tokens_period_commute`, `tokens_not_diamond_tick`, ★ `batch_diamond_tick`,
     ★ `batch_period_perm_invariant`, ★ `t5_hierarchy` (file < jetons < marché d'appel).
     T5 pour le marché d'appel est ARCHITECTURAL : vrai pour toute règle de compensation
     `clear` (`diamond_withTick_iff` : T5 ⟺ règlements commutatifs) ; le contenu économique
     est dans la règle (bloc biens, enchère `RightsAuction`) ;
  5. [biens] équilibre walrasien individuel `WalrasEq` (demande des deux côtés +
     complémentarité). La notion `PriceImplementability.isPriceSupportable` (maximisation du
     surplus parmi les faisables) est une notion de PLANIFICATEUR : à p = 0 elle soutient toute
     allocation efficace, et ne réfute pas Henry. ★ `unit_rights_walras` (empreintes
     unitaires : toute allocation efficace est un équilibre, preuve par échange), ★
     `lumpy_no_walras` (Henry 1970 : tailles 2, 2, 3, valeurs 4, 4, 7, stock 4 — aucun
     équilibre), ★ `lumpy_walras_inefficient_without_clearing` (sans complémentarité, le
     premier théorème du bien-être échoue) ;
  6. [biens] Coase, INFORMATION COMPLÈTE (en valeurs privées, Myerson–Satterthwaite
     l'interdit [MÉM]) : ★ `coase_invariance` (depuis toute dotation de total `C`, échange au
     prix walrasien équilibré et individuellement rationnel), ★
     `coase_use_commutes_rents_dont` (les deux ordres de la file = deux dotations : même usage,
     rentes (3, 0) contre (2, 1)).
-/

import ThesePlanetaire.PlanetaryLedger
import ThesePlanetaire.FeedbackClass

namespace TokenizedCommons

open DualDAG (FuturePool)
open LocalCommutation (I_loc I_loc_symm)
open LedgerCirculation
open GatedStep (gatedStep gatedStep_comm Diamond)
open PlanetaryLedger (Footprint PState gsupp deplete stockAdmissible planetAdmissible planetUpd
  planetStep planetFold planetFoldFrom psettles I_planet I_planet_of_no_gate
  emit_eq_zero_of_not_mem climate_commons)
open FeedbackClass (FClass SemClass)
open CommutativeClassification (IsCommutativeUpdate)

variable {V : Type*} [DecidableEq V] {B : Type*}

/-! ### 1. Droits tokenisés -/

/-- Attribution des émissions d'un paiement : au payeur (consommateur) ou au receveur
    (producteur). -/
inductive Attribution
  | consumer
  | producer
  deriving DecidableEq, Repr

/-- Détenteur dont le compte de droits est débité par `e`. -/
def holder : Attribution → V × V → V
  | .consumer, e => e.1
  | .producer, e => e.2

/-- État du grand livre tokenisé : soldes, droits par détenteur et par frontière, admis. -/
@[ext] structure RState (V B : Type*) where
  bal : V → ℤ
  rights : V → B → ℤ
  adm : Multiset (V × V)

/-- Burn : `e` débite le compte de droits de son détenteur de son émission. -/
def burn (att : Attribution) (fp : Footprint V B) (e : V × V) (r : V → B → ℤ) : V → B → ℤ :=
  fun v c => r v c - if v = holder att e then fp.emit e c else 0

/-- Admission par droits : le compte du détenteur couvre chaque émission gardée de `e`. -/
def rightsAdmissible (att : Attribution) (fp : Footprint V B) (r : V → B → ℤ) (e : V × V) :
    Prop :=
  ∀ c ∈ gsupp fp e, fp.emit e c ≤ r (holder att e) c

instance (att : Attribution) (fp : Footprint V B) (r : V → B → ℤ) (e : V × V) :
    Decidable (rightsAdmissible att fp r e) :=
  Finset.decidableDforallFinset

/-- Un paiement est admis si sa source reste solvable ET si son détenteur a les droits. -/
def tkAdmissible (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B)
    (st : RState V B) (e : V × V) : Prop :=
  ledgerAdmissible demands st.bal e ∧ rightsAdmissible att fp st.rights e

instance (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) (st : RState V B)
    (e : V × V) : Decidable (tkAdmissible att demands fp st e) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Règlement tokenisé : paiement, burn, enregistrement. -/
def tkUpd (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) (st : RState V B)
    (e : V × V) : RState V B :=
  ⟨pay demands e st.bal, burn att fp e st.rights, e ::ₘ st.adm⟩

/-- Pas « tester puis garder » du grand livre tokenisé. -/
def tkStep (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) :
    RState V B → V × V → RState V B :=
  gatedStep (tkAdmissible att demands fp) (tkUpd att demands fp)

def tkFoldFrom (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) (st : RState V B)
    (w : List (V × V)) : RState V B :=
  w.foldl (tkStep att demands fp) st

/-- Indépendance déclarée du grand livre tokenisé, sans référence à l'empreinte : `I_loc`
    (consommateur) ; `I_loc` et receveurs distincts (producteur). -/
def I_tk : Attribution → V × V → V × V → Prop
  | .consumer, a, b => I_loc a b
  | .producer, a, b => I_loc a b ∧ a.2 ≠ b.2

/-- Indépendance fine : `I_loc`, et détenteurs distincts OU empreintes gardées disjointes
    (les comptes de droits sont par détenteur ET par frontière). -/
def I_tkfp (att : Attribution) (fp : Footprint V B) (a b : V × V) : Prop :=
  I_loc a b ∧ (holder att a ≠ holder att b ∨ Disjoint (gsupp fp a) (gsupp fp b))

omit [DecidableEq V] in
theorem I_tk_le_I_tkfp {att : Attribution} (fp : Footprint V B) {a b : V × V}
    (h : I_tk att a b) : I_tkfp att fp a b := by
  cases att
  · exact ⟨h, Or.inl h.1⟩
  · exact ⟨h.1, Or.inl h.2⟩

omit [DecidableEq V] in
theorem I_planet_le_I_tkfp (att : Attribution) {fp : Footprint V B} {a b : V × V}
    (h : I_planet fp a b) : I_tkfp att fp a b :=
  ⟨h.1, Or.inr h.2⟩

lemma burn_comm (att : Attribution) (fp : Footprint V B) (a b : V × V) (r : V → B → ℤ) :
    burn att fp a (burn att fp b r) = burn att fp b (burn att fp a r) := by
  funext v c
  simp only [burn]
  ring

/-- Burner pour `b` ne change pas le test de droits de `a` si leurs détenteurs diffèrent ou
    si leurs empreintes gardées sont disjointes. -/
lemma rightsAdmissible_burn_other (att : Attribution) (fp : Footprint V B) (r : V → B → ℤ)
    (a b : V × V)
    (h : holder att a ≠ holder att b ∨ Disjoint (gsupp fp a) (gsupp fp b)) :
    rightsAdmissible att fp (burn att fp b r) a ↔ rightsAdmissible att fp r a := by
  unfold rightsAdmissible
  refine forall₂_congr fun c hc => ?_
  have hz : (if holder att a = holder att b then fp.emit b c else 0) = 0 := by
    rcases h with h | h
    · exact if_neg h
    · rw [emit_eq_zero_of_not_mem (Finset.mem_filter.mp hc).1
        (Finset.disjoint_left.mp h hc), ite_self]
  rw [burn, hz, sub_zero]

/-- ★ Losange fin du grand livre tokenisé : `I_loc` et (détenteurs distincts ou empreintes
    gardées disjointes). -/
theorem tkStep_comm_fine (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) :
    Diamond (tkStep att demands fp) (I_tkfp att fp) := by
  intro st a b h
  exact gatedStep_comm
    (RState.ext (pay_comm demands b a st.bal) (burn_comm att fp b a st.rights)
      (Multiset.cons_swap b a st.adm))
    (and_congr (ledgerAdmissible_pay_other demands st.bal a b h.1.1.symm h.1.2.2)
      (rightsAdmissible_burn_other att fp st.rights a b h.2))
    (and_congr (ledgerAdmissible_pay_other demands st.bal b a h.1.1 h.1.2.1)
      (rightsAdmissible_burn_other att fp st.rights b a (h.2.imp Ne.symm fun h => h.symm)))

/-- ★ Losange du grand livre tokenisé pour `I_tk att` : la relation ne mentionne pas
    l'empreinte — la lecture est LOCALE (le compte de droits du détenteur). -/
theorem tkStep_comm (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) :
    Diamond (tkStep att demands fp) (I_tk att) :=
  fun st a b h => tkStep_comm_fine att demands fp st a b (I_tk_le_I_tkfp fp h)

omit [DecidableEq V] in
/-- ★ Attribution consommateur : `I_planet ≤ I_tk` (et, sur le commun climatique, l'inclusion
    est stricte : `I_tk` contient la paire du commun, `I_planet` non). -/
theorem I_planet_le_I_tk_consumer :
    (∀ (fp : Footprint V B) (a b : V × V), I_planet fp a b → I_tk .consumer a b) ∧
    ∃ a b : Fin 3 × Fin 3, I_tk .consumer a b ∧ ¬ I_planet PlanetaryLedger.ClimateCommons.fp a b :=
  ⟨fun _ _ _ h => h.1, PlanetaryLedger.ClimateCommons.a, PlanetaryLedger.ClimateCommons.b,
    climate_commons.1, fun h => climate_commons.2.1 h.2⟩

/-- Attribution producteur : la relation sans empreinte `I_tk .producer` ne contient pas
    `I_planet` (deux payeurs, un receveur, aucune frontière gardée) ; le grand livre commute
    pourtant ces paires (`I_planet_le_I_tkfp`) — l'écart est de déclaration, pas de dynamique. -/
theorem I_planet_not_le_I_tk_producer :
    ∃ (fp : Footprint (Fin 3) Unit) (a b : Fin 3 × Fin 3),
      I_planet fp a b ∧ ¬ I_tk .producer a b ∧ I_tkfp .producer fp a b :=
  ⟨⟨fun _ _ => 1, ∅⟩, (0, 2), (1, 2), I_planet_of_no_gate rfl _ _ |>.mpr (by decide),
    fun h => h.2 rfl, I_planet_le_I_tkfp _ (I_planet_of_no_gate rfl _ _ |>.mpr (by decide))⟩

/-! #### Conservation des droits et plafond -/

/-- Émissions de `v` sur `c` enregistrées dans un multi-ensemble de paiements admis. -/
def emittedBy (att : Attribution) (fp : Footprint V B) (m : Multiset (V × V)) (v : V) (c : B) :
    ℤ :=
  (m.map fun e => if v = holder att e then fp.emit e c else 0).sum

/-- ★ Conservation : droits restants + émis = droits initiaux + émis initiaux, pour tout
    détenteur et toute frontière, le long de tout historique. -/
theorem tk_conservation (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B)
    (v : V) (c : B) :
    ∀ (w : List (V × V)) (st : RState V B),
      (tkFoldFrom att demands fp st w).rights v c +
          emittedBy att fp (tkFoldFrom att demands fp st w).adm v c =
        st.rights v c + emittedBy att fp st.adm v c
  | [], _ => rfl
  | e :: w, st => by
    have ih := tk_conservation att demands fp v c w (tkStep att demands fp st e)
    simp only [tkFoldFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    unfold tkStep gatedStep
    split_ifs
    · simp only [tkUpd, burn, emittedBy, Multiset.map_cons, Multiset.sum_cons]
      ring
    · rfl

/-- Les droits gardés restent ≥ 0 (sans hypothèse de signe sur les émissions). -/
lemma tkStep_rights_nonneg {att : Attribution} {demands : V × V → ℤ} {fp : Footprint V B}
    {st : RState V B} (h : ∀ v, ∀ c ∈ fp.gated, 0 ≤ st.rights v c) (e : V × V) :
    ∀ v, ∀ c ∈ fp.gated, 0 ≤ (tkStep att demands fp st e).rights v c := by
  intro v c hc
  unfold tkStep gatedStep
  split_ifs with hadm
  · simp only [tkUpd, burn]
    by_cases hv : v = holder att e
    · subst hv
      rw [if_pos rfl]
      by_cases hs : c ∈ gsupp fp e
      · have := hadm.2 c hs
        omega
      · rw [emit_eq_zero_of_not_mem hc hs]
        simpa using h _ c hc
    · rw [if_neg hv, sub_zero]
      exact h v c hc
  · exact h v c hc

lemma tkFoldFrom_rights_nonneg {att : Attribution} {demands : V × V → ℤ} {fp : Footprint V B} :
    ∀ (w : List (V × V)) {st : RState V B}, (∀ v, ∀ c ∈ fp.gated, 0 ≤ st.rights v c) →
      ∀ v, ∀ c ∈ fp.gated, 0 ≤ (tkFoldFrom att demands fp st w).rights v c
  | [], _, h => h
  | e :: w, _, h => tkFoldFrom_rights_nonneg w (tkStep_rights_nonneg h e)

/-- Agrégation : la somme des émissions par détenteur est l'émission totale. -/
lemma sum_emittedBy [Fintype V] (att : Attribution) (fp : Footprint V B) (m : Multiset (V × V))
    (c : B) : ∑ v, emittedBy att fp m v c = (m.map fun e => fp.emit e c).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [emittedBy]
  | cons e m ih =>
    simp only [emittedBy, Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib] at ih ⊢
    rw [ih, Finset.sum_ite_eq']
    simp

/-- ★ Plafond : depuis une dotation ρ ≥ 0 (sur les frontières gardées) et aucun admis, les
    émissions admises sur chaque frontière gardée sont ≤ Σ_v ρ v c (= C_plan). -/
theorem tk_cap [Fintype V] (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B)
    (bal : V → ℤ) (ρ : V → B → ℤ) (hρ : ∀ v, ∀ c ∈ fp.gated, 0 ≤ ρ v c) (w : List (V × V))
    {c : B} (hc : c ∈ fp.gated) :
    ((tkFoldFrom att demands fp ⟨bal, ρ, 0⟩ w).adm.map fun e => fp.emit e c).sum ≤ ∑ v, ρ v c := by
  rw [← sum_emittedBy att]
  refine Finset.sum_le_sum fun v _ => ?_
  have hcons := tk_conservation att demands fp v c w ⟨bal, ρ, 0⟩
  have hnn := tkFoldFrom_rights_nonneg (att := att) (demands := demands) w
    (st := ⟨bal, ρ, 0⟩) hρ v c hc
  simp only [emittedBy, Multiset.map_zero, Multiset.sum_zero, add_zero] at hcons ⊢
  linarith

/-! ### 2. T-M12-1 : porte tokenisée ⟺ porte de budget -/

/-- Émission cumulée d'un historique sur `c`. -/
def cum (fp : Footprint V B) (w : List (V × V)) (c : B) : ℤ :=
  (w.map fun e => fp.emit e c).sum

/-- Émission cumulée d'un historique attribuée au détenteur `v`. -/
def holderCum (att : Attribution) (fp : Footprint V B) (w : List (V × V)) (v : V) (c : B) : ℤ :=
  (w.map fun e => if v = holder att e then fp.emit e c else 0).sum

/-- Règlement monétaire intégral : chaque paiement est solvable à son tour. -/
def msettles (demands : V × V → ℤ) : (V → ℤ) → List (V × V) → Prop
  | _, [] => True
  | bal, e :: w => ledgerAdmissible demands bal e ∧ msettles demands (pay demands e bal) w

/-- Règlement tokenisé intégral : chaque paiement est admis à son tour. -/
def tksettles (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B) :
    RState V B → List (V × V) → Prop
  | _, [] => True
  | st, e :: w => tkAdmissible att demands fp st e ∧
      tksettles att demands fp (tkUpd att demands fp st e) w

omit [DecidableEq V] in
lemma cum_nonneg {fp : Footprint V B} (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c)
    (w : List (V × V)) {c : B} (hc : c ∈ fp.gated) : 0 ≤ cum fp w c :=
  List.sum_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact h_nn e c hc

lemma holderCum_nonneg {att : Attribution} {fp : Footprint V B}
    (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) (w : List (V × V)) (v : V) {c : B}
    (hc : c ∈ fp.gated) : 0 ≤ holderCum att fp w v c :=
  List.sum_nonneg (by
    simp only [List.mem_map]
    rintro _ ⟨e, _, rfl⟩
    split_ifs
    · exact h_nn e c hc
    · exact le_rfl)

/-- Identité d'agrégation : Σ_v cum_v = cum. -/
lemma sum_holderCum [Fintype V] (att : Attribution) (fp : Footprint V B) (c : B) :
    ∀ w : List (V × V), ∑ v, holderCum att fp w v c = cum fp w c
  | [] => by simp [holderCum, cum]
  | e :: w => by
    have ih := sum_holderCum att fp c w
    simp only [holderCum, cum, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at ih ⊢
    rw [ih, Finset.sum_ite_eq']
    simp

/-- Porte centrale : depuis des stocks gardés ≥ 0, règlement intégral ⟺ règlement monétaire
    et émissions cumulées ≤ stock (émissions gardées ≥ 0). -/
theorem psettles_iff_cum {demands : V × V → ℤ} {fp : Footprint V B}
    (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    ∀ (w : List (V × V)) (st : PState V B), (∀ c ∈ fp.gated, 0 ≤ st.stock c) →
      (psettles demands fp st w ↔
        msettles demands st.bal w ∧ ∀ c ∈ fp.gated, cum fp w c ≤ st.stock c)
  | [], _, hst => by simpa [psettles, msettles, cum] using hst
  | e :: w, st, hst => by
    have hcons : ∀ c, cum fp (e :: w) c = fp.emit e c + cum fp w c := fun c => by
      simp [cum]
    simp only [psettles, msettles, planetAdmissible, hcons]
    by_cases hsa : stockAdmissible fp st.stock e
    · have hst' : ∀ c ∈ fp.gated, 0 ≤ (planetUpd demands fp st e).stock c := by
        intro c hc
        simp only [planetUpd, deplete]
        by_cases hs : c ∈ gsupp fp e
        · linarith [hsa c hs]
        · rw [emit_eq_zero_of_not_mem hc hs]
          simpa using hst c hc
      rw [psettles_iff_cum h_nn w _ hst']
      simp only [planetUpd, deplete]
      constructor
      · rintro ⟨⟨hl, -⟩, hm, hs⟩
        exact ⟨⟨hl, hm⟩, fun c hc => by linarith [hs c hc]⟩
      · rintro ⟨⟨hl, hm⟩, hs⟩
        exact ⟨⟨hl, hsa⟩, hm, fun c hc => by linarith [hs c hc]⟩
    · simp only [hsa, and_false, false_and, false_iff]
      rintro ⟨-, hs⟩
      refine hsa fun c hc => ?_
      have hcg := (Finset.mem_filter.mp hc).1
      linarith [hs c hcg, cum_nonneg h_nn w hcg]

/-- Porte tokenisée : depuis des droits gardés ≥ 0, règlement intégral ⟺ règlement monétaire
    et, pour chaque détenteur, émissions cumulées attribuées ≤ droits (émissions gardées ≥ 0). -/
theorem tksettles_iff_holderCum {att : Attribution} {demands : V × V → ℤ} {fp : Footprint V B}
    (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c) :
    ∀ (w : List (V × V)) (st : RState V B), (∀ v, ∀ c ∈ fp.gated, 0 ≤ st.rights v c) →
      (tksettles att demands fp st w ↔
        msettles demands st.bal w ∧ ∀ v, ∀ c ∈ fp.gated, holderCum att fp w v c ≤ st.rights v c)
  | [], _, hst => by simpa [tksettles, msettles, holderCum] using hst
  | e :: w, st, hst => by
    have hcons : ∀ v c, holderCum att fp (e :: w) v c =
        (if v = holder att e then fp.emit e c else 0) + holderCum att fp w v c := fun v c => by
      simp [holderCum]
    simp only [tksettles, msettles, tkAdmissible, hcons]
    by_cases hra : rightsAdmissible att fp st.rights e
    · have hst' : ∀ v, ∀ c ∈ fp.gated, 0 ≤ (tkUpd att demands fp st e).rights v c := by
        intro v c hc
        simp only [tkUpd, burn]
        by_cases hv : v = holder att e
        · subst hv
          rw [if_pos rfl]
          by_cases hs : c ∈ gsupp fp e
          · linarith [hra c hs]
          · rw [emit_eq_zero_of_not_mem hc hs]
            simpa using hst _ c hc
        · rw [if_neg hv, sub_zero]
          exact hst v c hc
      rw [tksettles_iff_holderCum h_nn w _ hst']
      simp only [tkUpd, burn]
      constructor
      · rintro ⟨⟨hl, -⟩, hm, hs⟩
        exact ⟨⟨hl, hm⟩, fun v c hc => by linarith [hs v c hc]⟩
      · rintro ⟨⟨hl, hm⟩, hs⟩
        exact ⟨⟨hl, hra⟩, hm, fun v c hc => by linarith [hs v c hc]⟩
    · simp only [hra, and_false, false_and, false_iff]
      rintro ⟨-, hs⟩
      refine hra fun c hc => ?_
      have hcg := (Finset.mem_filter.mp hc).1
      have := hs (holder att e) c hcg
      rw [if_pos rfl] at this
      linarith [holderCum_nonneg (att := att) h_nn w (holder att e) hcg]

/-- ★ T-M12-1 (`tokenized_gate_iff_budget_gate`, admission intégrale) : sous émissions
    gardées ≥ 0 et budget gardé ≥ 0, un historique se règle intégralement sous la porte centrale de budget `S`
    ssi il existe une dotation de droits ρ ≥ 0, de total `S c` sur chaque frontière gardée,
    sous laquelle il se règle intégralement par burn. Contenu : l'identité d'agrégation
    Σ_v cum_v = cum (`sum_holderCum`) — la dotation témoin est la consommation de chacun, le
    reliquat allant à un détenteur quelconque. Le cas partiel (rejets) n'est PAS couvert : la
    file admet alors un ensemble qui dépend de l'ordre. -/
theorem tokenized_gate_iff_budget_gate [Fintype V] [Nonempty V] (att : Attribution)
    (demands : V × V → ℤ) (fp : Footprint V B) (h_nn : ∀ e, ∀ c ∈ fp.gated, 0 ≤ fp.emit e c)
    (bal : V → ℤ) (S : B → ℤ) (hS : ∀ c ∈ fp.gated, 0 ≤ S c) (w : List (V × V)) :
    psettles demands fp ⟨bal, S, 0⟩ w ↔
      ∃ ρ : V → B → ℤ, (∀ v, ∀ c ∈ fp.gated, 0 ≤ ρ v c) ∧
        (∀ c ∈ fp.gated, ∑ v, ρ v c = S c) ∧ tksettles att demands fp ⟨bal, ρ, 0⟩ w := by
  rw [psettles_iff_cum h_nn w _ hS]
  constructor
  · rintro ⟨hm, hcum⟩
    obtain ⟨v₀⟩ := ‹Nonempty V›
    refine ⟨fun v c => holderCum att fp w v c + if v = v₀ then S c - cum fp w c else 0,
      fun v c hc => ?_, fun c hc => ?_, ?_⟩
    · have h1 := holderCum_nonneg (att := att) h_nn w v hc
      have h2 := hcum c hc
      dsimp only
      split_ifs <;> linarith
    · rw [Finset.sum_add_distrib, sum_holderCum, Finset.sum_ite_eq']
      simp
    · rw [tksettles_iff_holderCum h_nn w _ fun v c hc => by
        have h1 := holderCum_nonneg (att := att) h_nn w v hc
        have h2 := hcum c hc
        dsimp only
        split_ifs <;> linarith]
      refine ⟨hm, fun v c hc => ?_⟩
      have h2 := hcum c hc
      dsimp only
      split_ifs <;> linarith
  · rintro ⟨ρ, hρ, hsum, htk⟩
    rw [tksettles_iff_holderCum h_nn w _ hρ] at htk
    refine ⟨htk.1, fun c hc => ?_⟩
    show cum fp w c ≤ S c
    rw [← hsum c hc, ← sum_holderCum att]
    exact Finset.sum_le_sum fun v _ => htk.2 v c hc

/-! ### 3. Le commun climatique tokenisé -/

namespace CC

open PlanetaryBoundaries (PlanetaryBoundary)

export PlanetaryLedger.ClimateCommons (pool demands fp S₀ a b)

/-- Toute la dotation (une unité de climat) au détenteur `v₀`. -/
def ρTo (v₀ : Fin 3) : Fin 3 → PlanetaryBoundary → ℤ :=
  fun v c => if v = v₀ ∧ c = .climateChange then 1 else 0

/-- État tokenisé initial : avoirs `(1, 1, 0)`, dotation ρ, aucun admis. -/
def tk0 (ρ : Fin 3 → PlanetaryBoundary → ℤ) : RState (Fin 3) PlanetaryBoundary :=
  ⟨pool.holdings, ρ, 0⟩

/-- Deux paiements du même payeur `0`, qui a de quoi payer les deux. -/
def a₁ : Fin 3 × Fin 3 := (0, 1)
def a₂ : Fin 3 × Fin 3 := (0, 2)

/-- Avoirs `(2, 0, 0)` et l'unité de climat au payeur `0`. -/
def st₂ : RState (Fin 3) PlanetaryBoundary :=
  ⟨fun v => if v = 0 then 2 else 0, ρTo 0, 0⟩

end CC

open CC

/-- ★ La dotation, pas l'ordre, fixe qui émet (attribution consommateur, commun climatique) :
    l'unité de climat au payeur `0` fait admettre `a` dans les deux ordres, au payeur `1`,
    `b` dans les deux ordres. -/
theorem endowment_decides :
    (tkFoldFrom .consumer demands fp (tk0 (ρTo 0)) [a, b]).adm = {a} ∧
    (tkFoldFrom .consumer demands fp (tk0 (ρTo 0)) [b, a]).adm = {a} ∧
    (tkFoldFrom .consumer demands fp (tk0 (ρTo 1)) [a, b]).adm = {b} ∧
    (tkFoldFrom .consumer demands fp (tk0 (ρTo 1)) [b, a]).adm = {b} := by
  decide

/-- ★ T résiduel : au sein d'un même détenteur, l'ordre décide encore. Le payeur `0` peut
    payer les deux paiements (le grand livre monétaire les admet tous deux) mais n'a qu'une
    unité de droit : la première servie l'emporte. -/
theorem tk_same_holder_order :
    holder .consumer a₁ = holder .consumer a₂ ∧
    (ledgerFoldFrom demands ⟨st₂.bal, 0⟩ [a₁, a₂]).adm = {a₁, a₂} ∧
    (tkFoldFrom .consumer demands fp st₂ [a₁, a₂]).adm = {a₁} ∧
    (tkFoldFrom .consumer demands fp st₂ [a₂, a₁]).adm = {a₂} := by
  decide

/-- ★ Attribution producteur : le commun est reconstitué au compte du receveur. Sur le commun
    climatique, la dotation au receveur commun `2` rend l'allocation de nouveau dépendante de
    l'ordre entre deux paiements `I_loc`-indépendants. -/
theorem producer_attribution_conflict :
    I_loc a b ∧
    (tkFoldFrom .producer demands fp (tk0 (ρTo 2)) [a, b]).adm = {a} ∧
    (tkFoldFrom .producer demands fp (tk0 (ρTo 2)) [b, a]).adm = {b} := by
  decide

/-- ★ Le grand livre planétaire du commun climatique est de classe D relativement à
    l'indépendance monétaire `I_loc`. -/
theorem commons_D_rel_Iloc : SemClass (planetStep demands fp) I_loc .D := by
  intro hD
  have h := congrArg PState.adm (hD ⟨pool.holdings, S₀, 0⟩ a b climate_commons.1)
  exact absurd h (by decide)

/-- ★ Le grand livre tokenisé (consommateur) du commun climatique est de classe T
    relativement à `I_loc` : losange (`tkStep_comm`), mais pas commutatif (même détenteur). -/
theorem tokens_T_rel_Iloc : SemClass (tkStep .consumer demands fp) I_loc .T := by
  refine ⟨tkStep_comm .consumer demands fp, fun hc => ?_⟩
  have h := congrArg RState.adm (hc st₂ a₁ a₂)
  exact absurd h (by decide)

/-- ★ Le grand livre tokenisé producteur du commun climatique reste de classe D relativement
    à `I_loc`. -/
theorem tokens_producer_D_rel_Iloc : SemClass (tkStep .producer demands fp) I_loc .D := by
  intro hD
  have h := congrArg RState.adm (hD (tk0 (ρTo 2)) a b climate_commons.1)
  exact absurd h (by decide)

/-! ### 4. T5 en hiérarchie : file < jetons < marché d'appel -/

section Clock

variable {α σ : Type*}

/-- Indépendance d'horloge : deux soumissions (aucune n'est un top) sont déclarées
    indépendantes — c'est la réordonnabilité intra-période de T5. -/
def I_tick (x y : Option α) : Prop := x.isSome ∧ y.isSome

/-- Relèvement d'une indépendance aux lettres horodatées : le top n'est indépendant de rien. -/
def liftOpt (I : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => I a b
  | _, _ => False

/-- Pli horodaté : `some e` règle `e`, `none` est le top de période (`tick`). -/
def withTick (δ : σ → α → σ) (tick : σ → σ) : σ → Option α → σ
  | s, some a => δ s a
  | s, none => tick s

/-- Un losange pour `I` se relève aux lettres horodatées. -/
theorem withTick_diamond {δ : σ → α → σ} {I : α → α → Prop} (hD : Diamond δ I)
    (tick : σ → σ) : Diamond (withTick δ tick) (liftOpt I) := by
  rintro s (_ | a) (_ | b) h <;> simp only [liftOpt] at h
  exact hD s a b h

/-- Un défaut de losange pour `I` se relève aux lettres horodatées. -/
theorem not_diamond_withTick {δ : σ → α → σ} {I : α → α → Prop} (tick : σ → σ)
    (h : ¬ Diamond δ I) : ¬ Diamond (withTick δ tick) (liftOpt I) := by
  intro hD
  exact h fun s a b hab => hD s (some a) (some b) hab

/-- T5 pour un pli horodaté : réordonnabilité intra-période ⟺ les règlements commutent. -/
theorem diamond_withTick_iff (δ : σ → α → σ) (tick : σ → σ) :
    Diamond (withTick δ tick) I_tick ↔ IsCommutativeUpdate δ := by
  constructor
  · intro hD s a b
    exact hD s (some a) (some b) ⟨rfl, rfl⟩
  · rintro hc s (_ | a) (_ | b) ⟨ha, hb⟩
    · exact absurd ha (by simp)
    · exact absurd ha (by simp)
    · exact absurd hb (by simp)
    · exact hc s a b

/-- Marché d'appel : une soumission s'inscrit au carnet (multi-ensemble : deux soumissions
    identiques sont deux paiements). -/
def submit (p : σ × Multiset α) (e : α) : σ × Multiset α := (p.1, e ::ₘ p.2)

/-- Marché d'appel : le top compense le carnet par une règle `clear` ARBITRAIRE, puis le vide. -/
def batchStep (clear : Multiset α → σ → σ) : σ × Multiset α → Option α → σ × Multiset α :=
  withTick submit fun p => (clear p.2 p.1, 0)

theorem submit_commutative : IsCommutativeUpdate (submit (σ := σ) (α := α)) := by
  intro p a b
  simp only [submit, Multiset.cons_swap]

/-- ★ T5 pour le marché d'appel : losange pour `I_tick`, quelle que soit la règle de
    compensation — un énoncé ARCHITECTURAL (la lecture est déplacée au top). -/
theorem batch_diamond_tick (clear : Multiset α → σ → σ) : Diamond (batchStep clear) I_tick :=
  (diamond_withTick_iff _ _).mpr submit_commutative

lemma batch_submit_fold (clear : Multiset α → σ → σ) :
    ∀ (l : List α) (p : σ × Multiset α),
      (l.map some).foldl (batchStep clear) p = (p.1, (l : Multiset α) + p.2)
  | [], p => by simp
  | e :: l, p => by
    rw [List.map_cons, List.foldl_cons]
    rw [show batchStep clear p (some e) = (p.1, e ::ₘ p.2) from rfl, batch_submit_fold clear l]
    simp only [Prod.mk.injEq, true_and]
    rw [Multiset.add_cons, ← Multiset.cons_coe, Multiset.cons_add]

/-- ★ T5, forme permutation : deux périodes dont les soumissions sont permutées l'une de
    l'autre donnent le même état après le top. -/
theorem batch_period_perm_invariant (clear : Multiset α → σ → σ) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (p : σ × Multiset α) :
    (l₁.map some ++ [none]).foldl (batchStep clear) p =
      (l₂.map some ++ [none]).foldl (batchStep clear) p := by
  rw [List.foldl_append, List.foldl_append, batch_submit_fold, batch_submit_fold,
    Multiset.coe_eq_coe.mpr h]

end Clock

/-- ★ La file planétaire réfute T5 : sur le commun climatique, pour toute dynamique du top,
    même les paires `I_loc`-indépendantes ne commutent pas (a fortiori pas `I_tick`). -/
theorem fcfs_not_diamond_tick (tick : PState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary →
      PState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary) :
    ¬ Diamond (withTick (planetStep demands fp) tick) (liftOpt I_loc) ∧
      ¬ Diamond (withTick (planetStep demands fp) tick) I_tick := by
  have h1 := not_diamond_withTick tick commons_D_rel_Iloc
  refine ⟨h1, fun hD => h1 fun s x y hxy => hD s x y ?_⟩
  rcases x with _ | x <;> rcases y with _ | y <;> simp only [liftOpt] at hxy
  exact ⟨rfl, rfl⟩

/-- ★ T5 pour les jetons, entre détenteurs distincts : losange pour `liftOpt (I_tk att)`,
    pour toute dynamique du top. -/
theorem tokens_period_commute (att : Attribution) (demands : V × V → ℤ) (fp : Footprint V B)
    (tick : RState V B → RState V B) :
    Diamond (withTick (tkStep att demands fp) tick) (liftOpt (I_tk att)) :=
  withTick_diamond (tkStep_comm att demands fp) tick

/-- Les jetons ne vérifient pas T5 au sens plein (même détenteur). -/
theorem tokens_not_diamond_tick (tick : RState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary →
      RState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary) :
    ¬ Diamond (withTick (tkStep .consumer demands fp) tick) I_tick := by
  rw [diamond_withTick_iff]
  exact tokens_T_rel_Iloc.2

/-- ★ Hiérarchie T5 sur le commun climatique (toutes dynamiques du top, toute règle de
    compensation) : la file n'a pas de losange pour `I_loc` ; les jetons en ont un pour `I_loc`
    mais pas pour `I_tick` ; le marché d'appel en a un pour `I_tick`. -/
theorem t5_hierarchy {σ : Type*}
    (tick₁ : PState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary →
      PState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary)
    (tick₂ : RState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary →
      RState (Fin 3) PlanetaryBoundaries.PlanetaryBoundary)
    (clear : Multiset (Fin 3 × Fin 3) → σ → σ) :
    ¬ Diamond (withTick (planetStep demands fp) tick₁) (liftOpt I_loc) ∧
    Diamond (withTick (tkStep .consumer demands fp) tick₂) (liftOpt I_loc) ∧
    ¬ Diamond (withTick (tkStep .consumer demands fp) tick₂) I_tick ∧
    Diamond (batchStep clear) I_tick :=
  ⟨(fcfs_not_diamond_tick tick₁).1, tokens_period_commute .consumer demands fp tick₂,
    tokens_not_diamond_tick tick₂, batch_diamond_tick clear⟩

/-! ### 5. Bloc biens : équilibre walrasien des droits -/

section Goods

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Charge d'un ensemble de lots sur le stock. -/
def load (size : ι → ℕ) (S : Finset ι) : ℕ := S.sum size

/-- Allocation efficace : faisable, et de valeur maximale parmi les allocations faisables. -/
def Efficient (C : ℕ) (size : ι → ℕ) (v : ι → ℚ) (S : Finset ι) : Prop :=
  load size S ≤ C ∧ ∀ T : Finset ι, load size T ≤ C → T.sum v ≤ S.sum v

/-- Demande individuelle au prix unitaire `p` : chacun dans `S` veut son lot, chacun hors de
    `S` n'en veut pas ; `S` est faisable. -/
def WalrasDemand (C : ℕ) (size : ι → ℕ) (v : ι → ℚ) (p : ℚ) (S : Finset ι) : Prop :=
  0 ≤ p ∧ load size S ≤ C ∧ (∀ i ∈ S, p * size i ≤ v i) ∧ (∀ i ∉ S, v i ≤ p * size i)

/-- Équilibre walrasien : demande individuelle et complémentarité (un stock non épuisé a un
    prix nul). -/
def WalrasEq (C : ℕ) (size : ι → ℕ) (v : ι → ℚ) (p : ℚ) (S : Finset ι) : Prop :=
  WalrasDemand C size v p S ∧ p * ((C : ℚ) - load size S) = 0

omit [Fintype ι] [DecidableEq ι] in
lemma load_one (S : Finset ι) : load (fun _ => 1) S = S.card := by
  simp [load]

/-- ★ Empreintes unitaires (substituts bruts) : toute allocation efficace est un équilibre
    walrasien, au prix p = la plus forte valeur exclue (0 si aucune). Preuve par échange. -/
theorem unit_rights_walras {C : ℕ} {v : ι → ℚ} (hv : ∀ i, 0 ≤ v i) {S : Finset ι}
    (hS : Efficient C (fun _ => 1) v S) : ∃ p, WalrasEq C (fun _ => 1) v p S := by
  obtain ⟨hfeas, hopt⟩ := hS
  rw [load_one] at hfeas
  by_cases hne : Sᶜ.Nonempty
  · obtain ⟨j, hjc, hjmax⟩ := Finset.exists_mem_eq_sup' hne v
    have hj : j ∉ S := Finset.mem_compl.mp hjc
    refine ⟨v j, ⟨hv j, by rw [load_one]; exact hfeas, fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · -- échange : remplacer `i` par `j`
      have hjT : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
      have hcard : load (fun _ => 1) (insert j (S.erase i)) ≤ C := by
        rw [load_one, Finset.card_insert_of_notMem hjT, Finset.card_erase_of_mem hi]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      have h := hopt _ hcard
      rw [Finset.sum_insert hjT, ← Finset.add_sum_erase S v hi] at h
      simp only [Nat.cast_one, mul_one]
      linarith
    · simp only [Nat.cast_one, mul_one]
      rw [← hjmax]
      exact Finset.le_sup' v (Finset.mem_compl.mpr hi)
    · rcases (hv j).lt_or_eq with hpos | hzero
      · have hcardC : S.card = C := by
          by_contra hlt
          have hcard : load (fun _ => 1) (insert j S) ≤ C := by
            rw [load_one, Finset.card_insert_of_notMem hj]
            omega
          have h := hopt _ hcard
          rw [Finset.sum_insert hj] at h
          linarith
        rw [load_one, hcardC, sub_self, mul_zero]
      · rw [← hzero, zero_mul]
  · have hSu : ∀ i, i ∈ S := fun i => by
      by_contra hi
      exact hne ⟨i, Finset.mem_compl.mpr hi⟩
    refine ⟨0, ⟨le_rfl, by rw [load_one]; exact hfeas, fun i _ => ?_, fun i hi => absurd (hSu i) hi⟩,
      zero_mul _⟩
    simpa using hv i

/-- Les huit parties de `Fin 3`. -/
lemma fin3_finset_cases : ∀ S : Finset (Fin 3),
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨
      S = {0, 1, 2} := by
  decide

/-- Instance de Henry : lots de tailles 2, 2, 3, valeurs 4, 4, 7, stock 4. -/
def sizeL : Fin 3 → ℕ := ![2, 2, 3]
def vL : Fin 3 → ℚ := ![4, 4, 7]

@[simp] lemma sizeL_0 : sizeL 0 = 2 := rfl
@[simp] lemma sizeL_1 : sizeL 1 = 2 := rfl
@[simp] lemma sizeL_2 : sizeL 2 = 3 := rfl
@[simp] lemma vL_0 : vL 0 = 4 := rfl
@[simp] lemma vL_1 : vL 1 = 4 := rfl
@[simp] lemma vL_2 : vL 2 = 7 := rfl

/-- ★ Lots inégaux (Henry 1970) : AUCUN couple (p, S) n'est un équilibre walrasien. -/
theorem lumpy_no_walras : ∀ (p : ℚ) (S : Finset (Fin 3)), ¬ WalrasEq 4 sizeL vL p S := by
  rintro p S ⟨⟨hp, hload, hin, hout⟩, hclear⟩
  rcases fin3_finset_cases S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := hout 0 (by decide)
    rw [show load sizeL ∅ = 0 from rfl] at hclear
    norm_num at h0 hclear
    linarith
  · have h1 := hout 1 (by decide)
    rw [show load sizeL {0} = 2 by decide] at hclear
    norm_num at h1 hclear
    linarith
  · have h0 := hout 0 (by decide)
    rw [show load sizeL {1} = 2 by decide] at hclear
    norm_num at h0 hclear
    linarith
  · have h0 := hout 0 (by decide)
    rw [show load sizeL {2} = 3 by decide] at hclear
    norm_num at h0 hclear
    linarith
  · have h0 := hin 0 (by decide)
    have h2 := hout 2 (by decide)
    norm_num at h0 h2
    linarith
  all_goals exact absurd hload (by decide)

/-- ★ Sans complémentarité, le premier théorème du bien-être échoue : au prix 2, la demande
    individuelle soutient {2} (valeur 7), alors que l'allocation efficace {0, 1} vaut 8. -/
theorem lumpy_walras_inefficient_without_clearing :
    WalrasDemand 4 sizeL vL 2 {2} ∧ Efficient 4 sizeL vL {0, 1} ∧
      ({2} : Finset (Fin 3)).sum vL < ({0, 1} : Finset (Fin 3)).sum vL := by
  refine ⟨⟨by norm_num, by decide, fun i hi => ?_, fun i hi => ?_⟩, ⟨by decide, fun T hT => ?_⟩,
    by norm_num⟩
  · simp only [Finset.mem_singleton] at hi
    subst hi
    norm_num
  · fin_cases i <;> simp_all <;> norm_num
  · rcases fin3_finset_cases T with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hT (by decide)
      | norm_num

end Goods

/-! ### 6. Coase (information complète) -/

section Coase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Usage final : une unité pour chaque membre de `S`. -/
def use (S : Finset ι) (i : ι) : ℚ := if i ∈ S then 1 else 0

/-- Transfert payé par `i` pour passer de sa dotation `ω i` à l'usage `S` au prix `p`. -/
def coaseTransfer (p : ℚ) (S : Finset ι) (ω : ι → ℕ) (i : ι) : ℚ := p * (use S i - ω i)

/-- Utilité après échange. -/
def coaseUtility (v : ι → ℚ) (p : ℚ) (S : Finset ι) (ω : ι → ℕ) (i : ι) : ℚ :=
  v i * use S i - coaseTransfer p S ω i

/-- Utilité de statu quo : chacun use de ses propres droits (demande unitaire). -/
def statusQuo (v : ι → ℚ) (ω : ι → ℕ) (i : ι) : ℚ := if 0 < ω i then v i else 0

/-- ★ Coase (information complète, empreintes unitaires) : depuis TOUTE dotation de total `C`,
    l'échange au prix walrasien atteint l'usage `S` avec des transferts équilibrés et
    individuellement rationnels. -/
theorem coase_invariance {C : ℕ} {v : ι → ℚ} {p : ℚ} {S : Finset ι}
    (hW : WalrasEq C (fun _ => 1) v p S) (ω : ι → ℕ) (hω : ∑ i, ω i = C) :
    (∑ i, coaseTransfer p S ω i = 0) ∧ ∀ i, statusQuo v ω i ≤ coaseUtility v p S ω i := by
  obtain ⟨⟨hp, -, hin, hout⟩, hclear⟩ := hW
  rw [load_one] at hclear
  refine ⟨?_, fun i => ?_⟩
  · have hu : ∑ i, use S i = (S.card : ℚ) := by
      simp [use]
    have hω' : ∑ i, (ω i : ℚ) = C := by exact_mod_cast hω
    simp only [coaseTransfer, ← Finset.mul_sum, Finset.sum_sub_distrib, hu, hω']
    linarith
  · have hin' := hin i
    have hout' := hout i
    simp only [Nat.cast_one, mul_one] at hin' hout'
    simp only [statusQuo, coaseUtility, coaseTransfer, use]
    have hω0 : (0 : ℚ) ≤ ω i := Nat.cast_nonneg _
    by_cases hS : i ∈ S
    · have := hin' hS
      by_cases hpos : 0 < ω i
      · have h1 : (1 : ℚ) ≤ ω i := by exact_mod_cast hpos
        simp only [hS, hpos, if_true]
        nlinarith
      · have h0 : ω i = 0 := by omega
        simp only [hS, h0, if_true]
        simp
        linarith
    · have := hout' hS
      by_cases hpos : 0 < ω i
      · have h1 : (1 : ℚ) ≤ ω i := by exact_mod_cast hpos
        simp only [hS, hpos, if_true, if_false]
        nlinarith
      · have h0 : ω i = 0 := by omega
        simp [hS, h0]

/-- Dotations issues de la file sur le commun climatique : l'ordre `[a, b]` donne le droit au
    payeur `0`, l'ordre `[b, a]` au payeur `1`. -/
def ω₁ : Fin 2 → ℕ := ![1, 0]
def ω₂ : Fin 2 → ℕ := ![0, 1]
def vC : Fin 2 → ℚ := ![3, 1]

/-- ★ L'usage commute, les rentes non : depuis les deux dotations (= les deux ordres de la
    file), l'échange coasien atteint le même usage efficace {0}, mais les utilités finales
    diffèrent — (3, 0) contre (2, 1). -/
theorem coase_use_commutes_rents_dont :
    WalrasEq 1 (fun _ => 1) vC 1 {0} ∧ Efficient 1 (fun _ => 1) vC {0} ∧
    (∑ i, coaseTransfer 1 {0} ω₁ i = 0 ∧ ∀ i, statusQuo vC ω₁ i ≤ coaseUtility vC 1 {0} ω₁ i) ∧
    (∑ i, coaseTransfer 1 {0} ω₂ i = 0 ∧ ∀ i, statusQuo vC ω₂ i ≤ coaseUtility vC 1 {0} ω₂ i) ∧
    (coaseUtility vC 1 {0} ω₁ 0 = 3 ∧ coaseUtility vC 1 {0} ω₁ 1 = 0) ∧
    (coaseUtility vC 1 {0} ω₂ 0 = 2 ∧ coaseUtility vC 1 {0} ω₂ 1 = 1) := by
  have hW : WalrasEq 1 (fun _ => 1) vC 1 {0} := by
    refine ⟨⟨by norm_num, by decide, fun i hi => ?_, fun i hi => ?_⟩, by simp [load]⟩
    · simp only [Finset.mem_singleton] at hi
      subst hi
      simp [vC]
    · fin_cases i
      · simp at hi
      · simp [vC]
  refine ⟨hW, ⟨by decide, fun T hT => ?_⟩, coase_invariance hW ω₁ (by decide),
    coase_invariance hW ω₂ (by decide), ?_, ?_⟩
  · rw [load_one] at hT
    have : T = ∅ ∨ T = {0} ∨ T = {1} := by
      revert T; decide
    rcases this with rfl | rfl | rfl <;> simp [vC]
  · simp [coaseUtility, coaseTransfer, use, ω₁, vC]
  · simp [coaseUtility, coaseTransfer, use, ω₂, vC]
    norm_num

end Coase

end TokenizedCommons
