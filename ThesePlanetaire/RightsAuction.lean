/-
  RightsAuction.lean — Phase 5b' : allocation primaire des droits planétaires par enchère,
  couche STRATÉGIQUE (DSIC).

  Couche nouvelle par rapport au corpus CoucheDynamique, qui n'a aucune composante
  stratégique (`analyse_gouvernance_allocation_preuves_lean4_2026-08-17`). Elle porte sur des
  BIENS PRIVÉS (droits unitaires d'usage du commun), pas sur un bien public : Groves–Ledyard
  et Lindahl ne sont pas visés.

  Cadre : agents `ι` (fini, totalement ordonné pour le départage), valeurs privées
  mono-paramètre (un agent veut un droit unitaire et lui attribue la valeur `v : ℕ`), offres
  `b : ι → ℕ`, utilité quasi-linéaire dans ℤ (valeur − paiement si gagnant, 0 sinon).

  1. Mécanisme à seuil générique : un seuil `τ b i` indépendant de l'offre propre de `i`
     (`OwnBidFree`) ; `i` gagne ⟺ `τ b i ≤ b i`, et paie `τ b i`.
     ★ `threshold_dsic` : dire la vérité est une stratégie dominante (Myerson 1981, forme à
     seuil) ; ★ `threshold_ir` : l'utilité véridique est ≥ 0.
  2. Enchère à k unités (k = droits disponibles) : clé lexicographique (offre, indice),
     `rank` = nombre d'agents de clé strictement supérieure, `i` gagne ⟺ `rank b i < k`.
     ★ `rank_injective`, ★ `winners_card` (= min k |ι|), ★ `kUnit_feasible` (≤ k droits) ;
     ★ `rank_antitone_own_bid` ; seuil `theta` par `Nat.find` (k ≥ 1) ;
     ★ `kUnit_wins_iff_threshold`, ★ `kUnit_dsic`, ★ `kUnit_ir`.
     ★ `kUnit_top_k` : en offres véridiques, tout gagnant a une valeur ≥ celle de tout
     perdant (les k plus hautes valeurs).
  3. ★ `scarcity_price_antitone` : le seuil est antitone en k. C'est un PRIX DE RARETÉ (moins
     de droits ⇒ seuil plus haut), pas la règle de Hotelling : il n'y a ici ni temps ni taux
     d'intérêt (voir `RightsIntertemporal`).
  4. ★ `value_blind_inefficient` : toute règle d'attribution de k droits (0 < k < |ι|) qui
     n'interroge pas les valeurs — file d'arrivée, prorata d'une empreinte MESURÉE,
     grandfathering — manque l'efficacité pour un profil de valeurs. La « DSIC par
     faisabilité » (le 08-08 : les quantités vérifiables ne peuvent être mal déclarées) est
     une véracité VACANTE (rien n'est demandé), payée en efficacité ; les valeurs exigent le
     seuil (items 1-2).

  Portée [ANALYSE] :
  - pas de contrainte budgétaire : l'enchère alloue selon la disposition à payer, qui suppose
    la capacité à payer (Dobzinski–Lavi–Nisan : avec budgets, pas de mécanisme DSIC
    Pareto-efficace en général) ;
  - empreintes unitaires (un droit par agent) ; empreintes inégales : pas de prix uniforme
    (Henry 1970, voir `TokenizedCommons`) ;
  - pas de revente : l'interaction avec la revente (Coase) est hors module.

  Build : cd lean4 && lake build ThesePlanetaire.RightsAuction
-/

import Mathlib.Tactic

namespace RightsAuction

/-! ### 1. Mécanisme à seuil générique -/

section Threshold

variable {ι : Type*} [DecidableEq ι]

/-- Le seuil de `i` ne dépend pas de l'offre propre de `i`. -/
def OwnBidFree (τ : (ι → ℕ) → ι → ℕ) : Prop :=
  ∀ (b : ι → ℕ) (i : ι) (x : ℕ), τ (Function.update b i x) i = τ b i

/-- Utilité quasi-linéaire de `i`, de valeur `v`, au profil d'offres `b` : `i` gagne ⟺
    `τ b i ≤ b i`, et paie alors `τ b i`. -/
def utility (τ : (ι → ℕ) → ι → ℕ) (v : ℕ) (b : ι → ℕ) (i : ι) : ℤ :=
  if τ b i ≤ b i then (v : ℤ) - τ b i else 0

/-- ★ DSIC (forme à seuil, Myerson 1981) : quelles que soient les offres des autres,
    offrir sa valeur `v` rapporte au moins autant que toute autre offre `x`. -/
theorem threshold_dsic {τ : (ι → ℕ) → ι → ℕ} (hτ : OwnBidFree τ) (b : ι → ℕ) (i : ι)
    (v x : ℕ) :
    utility τ v (Function.update b i x) i ≤ utility τ v (Function.update b i v) i := by
  simp only [utility, hτ b i x, hτ b i v, Function.update_self]
  split_ifs <;> omega

/-- DSIC contre le profil courant : dévier de `b i` vers la vérité ne coûte rien. -/
theorem threshold_dsic' {τ : (ι → ℕ) → ι → ℕ} (hτ : OwnBidFree τ) (b : ι → ℕ) (i : ι)
    (v : ℕ) : utility τ v b i ≤ utility τ v (Function.update b i v) i := by
  simpa only [Function.update_eq_self] using threshold_dsic hτ b i v (b i)

/-- ★ Rationalité individuelle : l'utilité véridique est ≥ 0. -/
theorem threshold_ir {τ : (ι → ℕ) → ι → ℕ} (hτ : OwnBidFree τ) (b : ι → ℕ) (i : ι) (v : ℕ) :
    0 ≤ utility τ v (Function.update b i v) i := by
  simp only [utility, hτ b i v, Function.update_self]
  split_ifs <;> omega

end Threshold

/-! ### 2. Enchère à k unités -/

section KUnit

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Clé de classement : l'offre, puis l'indice (départage lexicographique). -/
def key (b : ι → ℕ) (i : ι) : Lex (ℕ × ι) := toLex (b i, i)

omit [Fintype ι] [LinearOrder ι] in
lemma key_injective (b : ι → ℕ) : Function.Injective (key b) := fun i j h => by
  simpa [key] using congrArg (fun z => (ofLex z).2) h

/-- Rang de `i` : nombre d'agents de clé strictement supérieure. -/
def rank (b : ι → ℕ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => key b i < key b j).card

/-- Gagnants de l'enchère à `k` unités : les agents de rang < k. -/
def winners (k : ℕ) (b : ι → ℕ) : Finset ι :=
  Finset.univ.filter fun i => rank b i < k

lemma rank_lt_of_key_lt {b : ι → ℕ} {i j : ι} (h : key b i < key b j) :
    rank b j < rank b i := by
  apply Finset.card_lt_card
  refine ⟨fun l hl => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact h.trans hl
  · have hj : j ∈ Finset.univ.filter fun l => key b j < key b l :=
      hsub (by simp [h])
    simp at hj

/-- ★ Le rang est injectif (clés distinctes, ordre total). -/
theorem rank_injective (b : ι → ℕ) : Function.Injective (rank b) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne ((key_injective b).ne hne) with h | h
  · exact (rank_lt_of_key_lt h).ne' hij
  · exact (rank_lt_of_key_lt h).ne hij

lemma rank_lt_card (b : ι → ℕ) (i : ι) : rank b i < Fintype.card ι := by
  have hsub : (Finset.univ.filter fun j => key b i < key b j) ⊆ Finset.univ.erase i :=
    fun j hj => Finset.mem_erase.mpr
      ⟨fun h => by subst h; simp at hj, Finset.mem_univ _⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  unfold rank
  omega

lemma image_rank (b : ι → ℕ) :
    Finset.univ.image (rank b) = Finset.range (Fintype.card ι) := by
  refine Finset.eq_of_subset_of_card_le
    (fun x hx => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (rank_lt_card b i)
  · rw [Finset.card_range, Finset.card_image_of_injective _ (rank_injective b),
      Finset.card_univ]

/-- ★ Exactement min k |ι| gagnants. -/
theorem winners_card (k : ℕ) (b : ι → ℕ) :
    (winners k b).card = min k (Fintype.card ι) := by
  have h₁ : (winners k b).image (rank b) = (Finset.range (Fintype.card ι)).filter (· < k) := by
    rw [← image_rank, Finset.filter_image]
    rfl
  have h₂ : (Finset.range (Fintype.card ι)).filter (· < k) =
      Finset.range (min k (Fintype.card ι)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_image_of_injective _ (rank_injective b), h₁, h₂, Finset.card_range]

/-- ★ Faisabilité : au plus k droits sont attribués. -/
theorem kUnit_feasible (k : ℕ) (b : ι → ℕ) : (winners k b).card ≤ k := by
  rw [winners_card]
  exact min_le_left _ _

/-- ★ Le rang de `i` décroît (au sens large) quand `i` augmente son offre. -/
theorem rank_antitone_own_bid (b : ι → ℕ) (i : ι) {x y : ℕ} (hxy : x ≤ y) :
    rank (Function.update b i y) i ≤ rank (Function.update b i x) i := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, Function.update_self] at hj ⊢
  by_cases hji : j = i
  · subst hji
    simp at hj
  · rw [Function.update_of_ne hji] at hj ⊢
    rw [Prod.Lex.toLex_lt_toLex] at hj ⊢
    rcases hj with h | ⟨h₁, h₂⟩
    · exact Or.inl (lt_of_le_of_lt hxy h)
    · rcases hxy.lt_or_eq with hlt | heq
      · exact Or.inl (h₁ ▸ hlt)
      · exact Or.inr ⟨heq.trans h₁, h₂⟩

/-- Une offre strictement supérieure à toutes les autres donne le rang 0. -/
lemma exists_win (b : ι → ℕ) (i : ι) {k : ℕ} (hk : 0 < k) :
    ∃ x, rank (Function.update b i x) i < k := by
  refine ⟨Finset.univ.sup b + 1, ?_⟩
  suffices h : rank (Function.update b i (Finset.univ.sup b + 1)) i = 0 by omega
  rw [rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  by_cases hji : j = i
  · subst hji; exact lt_irrefl _
  · simp only [key, Function.update_self, Function.update_of_ne hji, Prod.Lex.toLex_lt_toLex, not_or,
      not_and]
    have := Finset.le_sup (f := b) (Finset.mem_univ j)
    constructor
    · omega
    · intro h; omega

/-- Seuil de `i` dans l'enchère à `k ≥ 1` unités : la plus petite offre gagnante de `i`, les
    autres offres étant fixées. -/
def theta {k : ℕ} (hk : 0 < k) (b : ι → ℕ) (i : ι) : ℕ :=
  Nat.find (exists_win b i hk)

/-- Caractérisation du seuil (monotonie du gain en l'offre propre). -/
lemma theta_le_iff {k : ℕ} (hk : 0 < k) (b : ι → ℕ) (i : ι) (x : ℕ) :
    theta hk b i ≤ x ↔ rank (Function.update b i x) i < k := by
  rw [theta, Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, hwin⟩
    exact lt_of_le_of_lt (rank_antitone_own_bid b i hm) hwin
  · intro h
    exact ⟨x, le_rfl, h⟩

/-- Le seuil ne dépend pas de l'offre propre. -/
theorem theta_ownBidFree {k : ℕ} (hk : 0 < k) : OwnBidFree (theta (ι := ι) hk) := by
  intro b i y
  have key : ∀ x, theta hk (Function.update b i y) i ≤ x ↔ theta hk b i ≤ x := fun x => by
    rw [theta_le_iff, theta_le_iff, Function.update_idem]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

/-- ★ `i` gagne l'enchère à k unités ⟺ son offre atteint son seuil. -/
theorem kUnit_wins_iff_threshold {k : ℕ} (hk : 0 < k) (b : ι → ℕ) (i : ι) :
    i ∈ winners k b ↔ theta hk b i ≤ b i := by
  rw [theta_le_iff, Function.update_eq_self]
  simp [winners]

/-- Utilité de `i` dans l'enchère à k unités : gagnant ⟺ rang < k, paiement = seuil. -/
def kUtility {k : ℕ} (hk : 0 < k) (v : ℕ) (b : ι → ℕ) (i : ι) : ℤ :=
  if i ∈ winners k b then (v : ℤ) - theta hk b i else 0

lemma kUtility_eq {k : ℕ} (hk : 0 < k) (v : ℕ) (b : ι → ℕ) (i : ι) :
    kUtility hk v b i = utility (theta hk) v b i := by
  simp only [kUtility, utility, kUnit_wins_iff_threshold hk b i]

/-- ★ DSIC de l'enchère à k unités au prix-seuil. -/
theorem kUnit_dsic {k : ℕ} (hk : 0 < k) (b : ι → ℕ) (i : ι) (v x : ℕ) :
    kUtility hk v (Function.update b i x) i ≤ kUtility hk v (Function.update b i v) i := by
  rw [kUtility_eq, kUtility_eq]
  exact threshold_dsic (theta_ownBidFree hk) b i v x

/-- ★ Rationalité individuelle de l'enchère à k unités. -/
theorem kUnit_ir {k : ℕ} (hk : 0 < k) (b : ι → ℕ) (i : ι) (v : ℕ) :
    0 ≤ kUtility hk v (Function.update b i v) i := by
  rw [kUtility_eq]
  exact threshold_ir (theta_ownBidFree hk) b i v

/-- ★ Les k plus hautes valeurs : en offres véridiques (`b = v`), tout gagnant a une valeur
    au moins égale à celle de tout perdant. -/
theorem kUnit_top_k (k : ℕ) (v : ι → ℕ) {i j : ι} (hi : i ∈ winners k v)
    (hj : j ∉ winners k v) : v j ≤ v i := by
  simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
  rcases lt_trichotomy (key v i) (key v j) with h | h | h
  · have := rank_lt_of_key_lt h; omega
  · rw [key_injective v h]
  · have h' := Prod.Lex.toLex_lt_toLex.mp h
    rcases h' with h' | ⟨h', -⟩
    · exact h'.le
    · exact h'.le

/-! ### 3. Prix de rareté -/

/-- ★ Prix de rareté : plus il y a de droits (k ≤ k'), plus le seuil est bas. -/
theorem scarcity_price_antitone {k k' : ℕ} (hk : 0 < k) (hkk' : k ≤ k') (b : ι → ℕ) (i : ι) :
    theta (lt_of_lt_of_le hk hkk') b i ≤ theta hk b i :=
  Nat.find_mono fun _ h => lt_of_lt_of_le h hkk'

end KUnit

/-! ### 4. Les règles aveugles aux valeurs manquent l'efficacité -/

/-- ★ Toute règle d'attribution de `k` droits (0 < k < |ι|) qui ne dépend pas des valeurs
    déclarées (`hblind` : même ensemble attribué pour tous les profils — file d'arrivée,
    prorata d'une empreinte mesurée, grandfathering) laisse, pour un profil de valeurs, un
    ensemble faisable de valeur totale strictement supérieure. La véracité « par
    faisabilité » est vacante : rien n'est déclaré, et l'efficacité est perdue. -/
theorem value_blind_inefficient {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hk : 0 < k) (hkn : k < Fintype.card ι) (alloc : (ι → ℕ) → Finset ι)
    (hfeas : ∀ v, (alloc v).card ≤ k) (hblind : ∀ v v', alloc v = alloc v') :
    ∃ v : ι → ℕ, ∃ S : Finset ι, S.card ≤ k ∧ (alloc v).sum v < S.sum v := by
  set W := alloc 0
  have hW : W.card < Fintype.card ι := lt_of_le_of_lt (hfeas 0) hkn
  obtain ⟨j, hj⟩ : ∃ j, j ∉ W := by
    by_contra h
    simp only [not_exists, not_not] at h
    have := Finset.card_le_card (fun x _ => h x : Finset.univ ⊆ W)
    rw [Finset.card_univ] at this
    omega
  refine ⟨fun l => if l = j then 1 else 0, {j}, by simpa using hk, ?_⟩
  rw [hblind _ 0, Finset.sum_singleton, if_pos rfl,
    Finset.sum_eq_zero fun l hl => if_neg (by rintro rfl; exact hj hl)]
  exact Nat.one_pos

end RightsAuction
