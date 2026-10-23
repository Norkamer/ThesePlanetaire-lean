/-
  EchelleCouplages.lean — R1 « L'échelle des couplages : le prix de
  l'intégration organique »

  Origine des actifs cités :
  - Basic.lean:42        abbrev ActivationState V = Finset (V × V)
  - DualDAG.lean:63      vertex_load (charge = arêtes SORTANTES seules)
  - DualDAG.lean:68      coupled_operator (assiette séparable)
  - DualDAG.lean:84      descending_chain
  - DualDAG.lean:173     contextual_fixpoint (init := current ∪ {e} ; chaîne à init.card)
  - DualDAG.lean:180     isAdmissible
  - DualDAG.lean:234     admission_is_order_dependent (barreau 1 : l'ordre casse)
  - DualDAG.lean:1138    coupled_operator_idempotent (barreau 1 : l'idempotence TIENT)
  - DualDAG.lean:1152    descending_chain_one_step (finalité en une ronde)
  - DualDAG.lean:1172    isAdmissible_iff_load (localité du test d'admission)

  Contenu neuf (barreau 2 — couplage par les ENTRÉES = intégration organique
  des externalités) :
  1. `received` : miroir de vertex_load sur la 2e projection ;
  2. `entry_coupled_operator` : la contrainte de v dépend de flux dont v n'est
     pas la source ;
  3. non-idempotence (témoin Fin 3), violation de la ronde unique (Fin 3),
     croissance des rondes (Fin 4 : 3 arêtes → 3 rondes), non-localité (témoin
     Fin 3, en contraste avec le corollaire de localité prouvé ici pour le
     côté séparable), contractivité conservée (mort du rival « contractif ⟹
     un pas ») ;
  4. `echelle_des_couplages` : la synthèse en un théorème ;
  5. A5 — `chain_theta_n` : la loi Θ(n). Sur la chaîne v₀→…→vₙ (n arêtes,
     demandes unitaires, holdings nuls), la solvabilité se propage comme une
     onde — S_k = {e_i : k ≤ i < n} — exactement n rondes : pas de
     stabilisation avant n, stabilisation à n (porté depuis
     J3a_theta_scratch.lean, commit 9c7c936).
  6. J3b — la cellule {P3} de la carte des combinaisons du trilemme :
     `entry_capped_operator` (plafond d'exposition — couplage ANTITONE en r),
     `entry_capped_idempotent` (théorème ∀, idempotence conservée) et
     `entry_capped_admission_not_local` (témoin Fin 3 : localité perdue) —
     la seule combinaison « perdre exactement une propriété » (porté depuis
     J3b_plafond_scratch.lean, commit 9fa6d44 ; carte :
     cache/analyse_j3b_carte_combinaisons).
-/

import ThesePlanetaire.DualDAG

open Finset DualDAG

namespace EchelleCouplages

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. L'opérateur couplé par les entrées -/

/-- Flux reçus par v dans S : miroir exact de `vertex_load` (DualDAG.lean:63)
    sur la seconde projection. -/
def received (demands : V × V → ℤ) (S : ActivationState V) (v : V) : ℤ :=
  (S.filter (fun e => e.2 = v)).sum demands

/-- Opérateur couplé par les ENTRÉES : une arête survit si la charge sortante
    de sa source est couverte par holdings + flux reçus. La contrainte de
    solvabilité de v dépend de flux dont v n'est PAS la source — c'est la
    définition du bilan qui intègre organiquement les externalités. -/
def entry_coupled_operator (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) : ActivationState V :=
  S.filter (fun e =>
    vertex_load demands S e.1 ≤ pool.holdings e.1 + received demands S e.1)

/-- La contractivité est CONSERVÉE au barreau 2 (même argument que
    coupled_operator_contractive, DualDAG.lean:73). -/
lemma entry_coupled_contractive (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) :
    entry_coupled_operator pool demands S ⊆ S :=
  Finset.filter_subset _ _

/-- Chaîne descendante générique : l'itération d'un opérateur — le squelette
    commun des barreaux (les rondes de clearing sont l'itération du couplage ;
    prépare l'itération du chantier rétroaction-regex). -/
def chain_of {α : Type*} (op : α → α) (init : α) : ℕ → α
  | 0 => init
  | n + 1 => op (chain_of op init n)

def entry_chain (pool : FuturePool V) (demands : V × V → ℤ)
    (init : ActivationState V) : ℕ → ActivationState V :=
  chain_of (entry_coupled_operator pool demands) init

/-- Admission couplée par entrées : miroir exact de contextual_fixpoint
    (DualDAG.lean:173) + isAdmissible (:180). -/
def entry_admissible (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V) : Prop :=
  e ∈ entry_chain pool demands (current ∪ {e}) (current ∪ {e}).card

instance (pool : FuturePool V) (demands : V × V → ℤ)
    (current : ActivationState V) (e : V × V) :
    Decidable (entry_admissible pool demands current e) := by
  unfold entry_admissible; infer_instance

/-! ### 2. La localité du côté séparable devient un théorème
    (corollaire direct de isAdmissible_iff_load :1172) -/

/-- Barreaux 0–1 : l'admission séparable est LOCALE — deux états ayant les
    mêmes sorties à la source de e donnent le même verdict. C'est le
    corollaire de :1172 que le barreau 2 va violer. -/
theorem separable_admission_local (pool : FuturePool V) (demands : V × V → ℤ)
    (S₁ S₂ : ActivationState V) (e : V × V)
    (h : S₁.filter (fun f => f.1 = e.1) = S₂.filter (fun f => f.1 = e.1)) :
    isAdmissible pool demands S₁ e ↔ isAdmissible pool demands S₂ e := by
  rw [isAdmissible_iff_load, isAdmissible_iff_load]
  have h_load : vertex_load demands (S₁ ∪ {e}) e.1 =
      vertex_load demands (S₂ ∪ {e}) e.1 := by
    unfold vertex_load
    rw [Finset.filter_union, Finset.filter_union, h]
  rw [h_load]

/-! ### 1. Définitions : la chaîne, ses demandes, le pool nul, la vague -/

/-- L'arête e_i = (i, i+1) pour i < n, vue dans Fin (n+1) × Fin (n+1).
    La preuve `hi : i < n` porte les coercitions ℕ→Fin (la friction de §1.2). -/
def edge {i : ℕ} (hi : i < n) : Fin (n + 1) × Fin (n + 1) :=
  ((⟨i, by omega⟩ : Fin (n + 1)), (⟨i + 1, by omega⟩ : Fin (n + 1)))

/-- Demandes unitaires sur la chaîne : e_i ↦ 1 pour i < n, 0 ailleurs. -/
def chainDemands (n : ℕ) : Fin (n + 1) × Fin (n + 1) → ℤ :=
  fun e => if e.1.val + 1 < n + 1 then 1 else 0

/-- Pool à holdings nuls, générique en n (fix §5.7 : pool0' est Fin 4). -/
def pool0Gen (n : ℕ) : FuturePool (Fin (n + 1)) :=
  ⟨fun _ => 0, by intro v; simp⟩

/-- La vague S_k = {e_i : k ≤ i < n} : le k-ième maillon depuis la racine. -/
def wave (n : ℕ) (k : ℕ) : ActivationState (Fin (n + 1)) :=
  ((Finset.range n).filter (fun i => k ≤ i)).attach.image
    (fun i => edge (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1))

/-- L'état initial : la chaîne complète (S_0). -/
def chainState (n : ℕ) : ActivationState (Fin (n + 1)) :=
  wave n 0

/-- La chaîne descendante de l'opérateur couplé par entrées. -/
def chain (n : ℕ) (k : ℕ) : ActivationState (Fin (n + 1)) :=
  entry_chain (pool0Gen n) (chainDemands n) (chainState n) k

/-! ### 3. Témoins finis du barreau 2 (technologie `decide`,
    la même que DualDAG :208/:234) -/

/-- Chaîne v₀→v₁→v₂ sur Fin 3, demandes unitaires. -/
def demands3 : Fin 3 × Fin 3 → ℤ :=
  fun e => if e = ((0 : Fin 3), (1 : Fin 3)) then 1
           else if e = ((1 : Fin 3), (2 : Fin 3)) then 1 else 0

/-- Budget nul partout : aucune source autonome (instance n=2 du pool générique). -/
def pool0 : FuturePool (Fin 3) := pool0Gen 2

/-- Budget 1 en v₀ seulement : la racine est solvable. -/
def pool1 : FuturePool (Fin 3) := ⟨fun v => if v = 0 then 1 else 0, by decide⟩

/-- Chaîne complète sur Fin 3 (instance n=2 de chainState). -/
def S3 : ActivationState (Fin 3) := chainState 2

/-- T1 — Le couplage par entrées casse l'IDEMPOTENCE : Φ²(S) ≠ Φ(S).
    (Φ(S₃) = {e₁₂} : e₀₁ tombe faute d'entrées en v₀, e₁₂ survit grâce à
    l'entrée e₀₁ ; puis Φ²(S₃) = ∅ : le soutien a disparu.) -/
theorem entry_coupled_not_idempotent :
    entry_coupled_operator pool0 demands3 (entry_coupled_operator pool0 demands3 S3) ≠
    entry_coupled_operator pool0 demands3 S3 := by decide

/-- T2 — Le couplage par entrées casse la FINALITÉ EN UNE RONDE :
    chain(1) ≠ chain(card) — la propriété descending_chain_one_step (:1152)
    du côté séparable est violée au barreau 2. -/
theorem entry_chain_violates_one_step :
    entry_chain pool0 demands3 S3 1 ≠ entry_chain pool0 demands3 S3 S3.card := by
  decide

/-- Chaîne v₀→v₁→v₂→v₃ sur Fin 4 : les rondes CROISSENT avec la profondeur. -/
def demands4 : Fin 4 × Fin 4 → ℤ :=
  fun e => if e = ((0 : Fin 4), (1 : Fin 4)) then 1
           else if e = ((1 : Fin 4), (2 : Fin 4)) then 1
           else if e = ((2 : Fin 4), (3 : Fin 4)) then 1 else 0

def pool0' : FuturePool (Fin 4) := pool0Gen 3

/-- Chaîne complète sur Fin 4 (instance n=3 de chainState). -/
def S4 : ActivationState (Fin 4) := chainState 3

/-- T3 — Le couplage par entrées casse la LOCALITÉ : S₁ = {e₀₁} et S₂ = ∅ ont
    les MÊMES sorties à la source v₁, mais e₁₂ est admissible sous S₁ (l'entrée
    e₀₁ la finance) et pas sous S₂. Contraste formel avec
    separable_admission_local ci-dessus. -/
theorem entry_admission_not_local :
    ((({((0 : Fin 3), (1 : Fin 3))} : ActivationState (Fin 3)).filter
        (fun f => f.1 = (1 : Fin 3))) =
      ((∅ : ActivationState (Fin 3)).filter (fun f => f.1 = (1 : Fin 3)))) ∧
    entry_admissible pool1 demands3 {((0 : Fin 3), (1 : Fin 3))}
      ((1 : Fin 3), (2 : Fin 3)) ∧
    ¬ entry_admissible pool1 demands3 (∅ : ActivationState (Fin 3))
      ((1 : Fin 3), (2 : Fin 3)) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### 4. La synthèse -/

/-- L'ÉCHELLE DES COUPLAGES — le prix de l'intégration organique.
    Barreau 1 (couplage intra-compte, panier-lié) : l'ORDRE casse
    (admission_is_order_dependent :234) mais l'idempotence TIENT
    (coupled_operator_idempotent :1138, inconditionnelle).
    Barreau 2 (couplage par les entrées = externalités intégrées) :
    l'idempotence casse (T1), la finalité en une ronde casse (T2), la
    localité casse (T3 vs separable_admission_local) — et la contractivité
    est conservée : le rival « contractif ⟹ un pas » est mort. -/
theorem echelle_des_couplages :
    -- barreau 1 : l'ordre casse déjà en intra-compte…
    (∃ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
       (e₁ e₂ : Fin 3 × Fin 3),
      isAdmissible pool demands ∅ e₁ ∧ isAdmissible pool demands ∅ e₂ ∧
      ¬ isAdmissible pool demands {e₁} e₂ ∧ ¬ isAdmissible pool demands {e₂} e₁) ∧
    -- …mais l'idempotence intra-compte tient (∀ — théorème de la thèse)
    (∀ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
       (S : ActivationState (Fin 3)),
      coupled_operator pool demands (coupled_operator pool demands S) =
        coupled_operator pool demands S) ∧
    -- barreau 2 : la non-idempotence…
    (entry_coupled_operator pool0 demands3 (entry_coupled_operator pool0 demands3 S3) ≠
      entry_coupled_operator pool0 demands3 S3) ∧
    -- …la perte de la ronde unique…
    (entry_chain pool0 demands3 S3 1 ≠ entry_chain pool0 demands3 S3 S3.card) ∧
    -- …et la contractivité conservée (le rival est mort)
    (∀ (pool : FuturePool (Fin 3)) (demands : Fin 3 × Fin 3 → ℤ)
       (S : ActivationState (Fin 3)),
      entry_coupled_operator pool demands S ⊆ S) :=
  ⟨admission_is_order_dependent,
   fun pool demands S => coupled_operator_idempotent pool demands S,
   entry_coupled_not_idempotent,
   entry_chain_violates_one_step,
   fun pool demands S => entry_coupled_contractive pool demands S⟩


/-! ### 5. A5 — la loi Θ(n) : la solvabilité se propage comme une onde

  Sur la chaîne v₀→v₁→…→vₙ (n arêtes, n+1 sommets, demandes unitaires,
  holdings nuls, couplage par les entrées) : la ronde k valide le
  k-ième maillon depuis la racine — S_k = {e_i : k ≤ i < n}, S_n = ∅,
  exactement n rondes. T1/T2/T2b (témoins Fin 3/4) deviennent la loi
  générale (trilemme 01_definitions.md §4 ; porté depuis
  J3a_theta_scratch.lean, commit 9c7c936). -/

variable {n : ℕ}

/-! ### 2. Lemmas de base : appartenance et demandes -/

/-- Caractérisation de la vague : e ∈ S_k ⟺ ∃ i < n, k ≤ i ∧ e = e_i. -/
lemma wave_mem (k : ℕ) (e : Fin (n + 1) × Fin (n + 1)) :
    e ∈ wave n k ↔ ∃ (i : ℕ), ∃ (hi : i < n), k ≤ i ∧ e = edge hi := by
  unfold wave
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨⟨i, hif⟩, ha, rfl⟩
    refine ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hif).1,
      (Finset.mem_filter.mp hif).2, rfl⟩
  · intro ⟨i, hi, hk, he⟩
    rw [he]
    exact Finset.mem_image.mpr
      ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hk⟩⟩, by simp, rfl⟩

/-- L'arête e_i est dans la chaîne pour i < n. -/
lemma mem_chainState (i : ℕ) (hi : i < n) : edge hi ∈ chainState n := by
  unfold chainState
  exact (wave_mem 0 (edge hi)).mpr ⟨i, hi, by omega, rfl⟩

/-- L'arête e_i a une demande unitaire. -/
lemma chainDemands_of (i : ℕ) (hi : i < n) : chainDemands n (edge hi) = 1 := by
  unfold chainDemands edge
  rw [if_pos (by simp; omega)]

/-- Toute arête de la chaîne a une demande unitaire. -/
lemma chainDemands_mem (e : Fin (n + 1) × Fin (n + 1)) (he : e ∈ chainState n) :
    chainDemands n e = 1 := by
  rcases (wave_mem 0 e).mp he with ⟨i, hi, hk, rfl⟩
  exact chainDemands_of i hi

/-- S_k ⊆ S_0 : la vague ne déborde pas de la chaîne. -/
lemma wave_subset_chain (k : ℕ) : wave n k ⊆ chainState n := by
  intro e he
  rcases (wave_mem k e).mp he with ⟨i, hi, hk, rfl⟩
  exact mem_chainState i hi

/-! ### 3. Unicité des arêtes de la chaîne -/

/-- La SEULE arête de la chaîne partant de ⟨i, _⟩ est e_i. -/
lemma eq_edge_of_src {i : ℕ} (hi : i < n) {e : Fin (n + 1) × Fin (n + 1)}
    (he : e ∈ chainState n) (hsrc : e.1 = (⟨i, by omega⟩ : Fin (n + 1))) :
    e = edge hi := by
  rcases (wave_mem 0 e).mp he with ⟨j, hj, hk, rfl⟩
  have hji : j = i := by
    simpa [edge] using congrArg Fin.val hsrc
  apply Prod.ext
  · simpa [edge] using hsrc
  · ext
    simp [edge, hji]

/-- La SEULE arête de la chaîne arrivant en ⟨i, _⟩ (i ≥ 1) est e_{i-1},
    écrite comme paire brute (la preuve i-1 < n+1 tient de i ≤ n seul). -/
lemma eq_edge_of_tgt {i : ℕ} (hi0 : 0 < i) (hi : i ≤ n)
    {e : Fin (n + 1) × Fin (n + 1)} (he : e ∈ chainState n)
    (htgt : e.2 = (⟨i, by omega⟩ : Fin (n + 1))) :
    e = ((⟨i - 1, by omega⟩ : Fin (n + 1)), (⟨i, by omega⟩ : Fin (n + 1))) := by
  rcases (wave_mem 0 e).mp he with ⟨j, hj, hk, rfl⟩
  have hji : j + 1 = i := by
    simpa [edge] using congrArg Fin.val htgt
  apply Prod.ext
  · simp [edge]
    omega
  · simpa [edge] using htgt

/-- Aucune arête de la chaîne n'arrive en v₀. -/
lemma no_edge_tgt_zero {e : Fin (n + 1) × Fin (n + 1)} (he : e ∈ chainState n) :
    e.2 ≠ (⟨0, by omega⟩ : Fin (n + 1)) := by
  intro htgt
  rcases (wave_mem 0 e).mp he with ⟨j, hj, hk, rfl⟩
  have : j + 1 = 0 := by
    simpa [edge] using congrArg Fin.val htgt
  omega

/-! ### 4. Charges au sommet ⟨i, _⟩ dans un sous-état de la chaîne -/

/-- Charge au sommet ⟨i, _⟩ dans S ⊆ chaîne : 1 ssi e_i ∈ S, sinon 0.
    Corollaire de `filter_src_eq_of_unique_outgoing` (localité de la charge). -/
lemma vertex_load_chain {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ chainState n) {i : ℕ} (hi : i < n) :
    vertex_load (chainDemands n) S (⟨i, by omega⟩ : Fin (n + 1)) =
      if edge hi ∈ S then 1 else 0 := by
  unfold vertex_load
  rw [filter_src_eq_of_unique_outgoing (chainState n) (⟨i, by omega⟩ : Fin (n + 1))
    (⟨i + 1, by omega⟩ : Fin (n + 1))
    (by
      intro e he hev
      have heq := eq_edge_of_src hi he hev
      simpa [edge] using heq) S hS]
  by_cases h : edge hi ∈ S
  · have h' : ((⟨i, by omega⟩ : Fin (n + 1)), (⟨i + 1, by omega⟩ : Fin (n + 1))) ∈ S := by
      simpa [edge] using h
    rw [if_pos h', Finset.sum_singleton]
    have hcd : chainDemands n ((⟨i, by omega⟩ : Fin (n + 1)), (⟨i + 1, by omega⟩ : Fin (n + 1))) = 1 := by
      simpa [edge] using chainDemands_mem (edge hi) (hS h)
    rw [hcd, if_pos h]
  · have h' : ((⟨i, by omega⟩ : Fin (n + 1)), (⟨i + 1, by omega⟩ : Fin (n + 1))) ∉ S := by
      intro hs
      exact h (by simpa [edge] using hs)
    rw [if_neg h', Finset.sum_empty]
    rw [if_neg h]

/-- Flux reçus par ⟨i, _⟩ dans S ⊆ chaîne : 0 en v₀, 1 ssi e_{i-1} ∈ S sinon.
    Corollaire de `filter_tgt_eq_of_unique_incoming` (localité de la charge). -/
lemma received_chain {S : Finset (Fin (n + 1) × Fin (n + 1))}
    (hS : S ⊆ chainState n) {i : ℕ} (hi : i ≤ n) :
    received (chainDemands n) S (⟨i, by omega⟩ : Fin (n + 1)) =
      if i = 0 then 0 else
        if ((⟨i - 1, by omega⟩ : Fin (n + 1)), (⟨i, by omega⟩ : Fin (n + 1))) ∈ S
        then 1 else 0 := by
  unfold received
  rw [filter_tgt_eq_of_unique_incoming (chainState n) (⟨i, by omega⟩ : Fin (n + 1))
    (⟨i - 1, by omega⟩ : Fin (n + 1))
    (by
      intro e he hev
      by_cases h0 : i = 0
      · subst h0
        exact absurd hev (no_edge_tgt_zero he)
      · have hpos : 0 < i := Nat.pos_of_ne_zero h0
        exact eq_edge_of_tgt hpos hi he hev) S hS]
  by_cases h0 : i = 0
  · subst h0
    have hnot : ((⟨0 - 1, by omega⟩ : Fin (n + 1)), (⟨0, by omega⟩ : Fin (n + 1))) ∉ S := by
      intro hs
      exact no_edge_tgt_zero (hS hs) (by simp)
    rw [if_neg hnot, Finset.sum_empty]
    simp
  · have hpos : 0 < i := Nat.pos_of_ne_zero h0
    by_cases hs : ((⟨i - 1, by omega⟩ : Fin (n + 1)), (⟨i, by omega⟩ : Fin (n + 1))) ∈ S
    · rw [if_pos hs, Finset.sum_singleton]
      rw [chainDemands_mem ((⟨i - 1, by omega⟩ : Fin (n + 1)), (⟨i, by omega⟩ : Fin (n + 1))) (hS hs),
        if_neg h0, if_pos hs]
    · rw [if_neg hs, Finset.sum_empty, if_neg h0, if_neg hs]

/-! ### 5. La vague avance : Φ(S_k) = S_{k+1} — l'onde se propage -/

/-- La vague avance d'un cran : l'opérateur couplé par entrées fait passer
    S_k à S_{k+1}. Cœur de la loi Θ(n) : une ronde = un maillon validé. -/
lemma wave_step (k : ℕ) :
    entry_coupled_operator (pool0Gen n) (chainDemands n) (wave n k) = wave n (k + 1) := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    have heS : e ∈ wave n k := (Finset.mem_filter.mp he).1
    rcases (wave_mem k e).mp heS with ⟨j, hj, hkj, rfl⟩
    -- la survie de e_j : charge 1 ≤ 0 + reçus
    have hsurv : vertex_load (chainDemands n) (wave n k) (edge hj).1 ≤
        (pool0Gen n).holdings (edge hj).1 +
          received (chainDemands n) (wave n k) (edge hj).1 := by
      exact (Finset.mem_filter.mp he).2
    have hvload : vertex_load (chainDemands n) (wave n k) (edge hj).1 = 1 := by
      change vertex_load (chainDemands n) (wave n k) ((⟨j, by omega⟩ : Fin (n + 1))) = 1
      rw [vertex_load_chain (wave_subset_chain k) hj, if_pos heS]
    have hhold : (pool0Gen n).holdings (edge hj).1 = 0 := by
      simp [pool0Gen]
    have hrec : received (chainDemands n) (wave n k) (edge hj).1 =
        if j = 0 then 0 else
          if ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1))) ∈ wave n k
          then 1 else 0 := by
      change received (chainDemands n) (wave n k) ((⟨j, by omega⟩ : Fin (n + 1))) =
        if j = 0 then 0 else
          if ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1))) ∈ wave n k
          then 1 else 0
      rw [received_chain (wave_subset_chain k) (by omega : j ≤ n)]
    have hrec1 : received (chainDemands n) (wave n k) (edge hj).1 = 1 := by
      by_cases hj0 : j = 0
      · exfalso
        have : (1 : ℤ) ≤ (0 : ℤ) := by
          rw [hvload, hhold, hrec, if_pos hj0] at hsurv
          omega
        omega
      · by_cases hpred : ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1))) ∈ wave n k
        · simp [hrec, hj0, hpred]
        · exfalso
          have : (1 : ℤ) ≤ (0 : ℤ) := by
            rw [hvload, hhold, hrec, if_neg hj0, if_neg hpred] at hsurv
            omega
          omega
    -- reçus = 1 ⟹ le prédécesseur e_{j-1} est dans S_k
    have hpred : ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1))) ∈ wave n k := by
      by_contra hnp
      have : (1 : ℤ) = (0 : ℤ) := by
        rw [← hrec1, hrec]
        by_cases hj0 : j = 0 <;> simp [hj0, hnp]
      omega
    -- e_{j-1} ∈ S_k ⟹ k ≤ j - 1 ⟹ k + 1 ≤ j
    have hkj' : k + 1 ≤ j := by
      rcases (wave_mem k ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1)))).mp hpred
        with ⟨i, hi', hki, heq⟩
      have hji : j = i + 1 := by
        simpa [edge] using congrArg Fin.val (congrArg Prod.snd heq)
      omega
    exact (wave_mem (k + 1) (edge hj)).mpr ⟨j, hj, hkj', rfl⟩
  · intro he
    rcases (wave_mem (k + 1) e).mp he with ⟨j, hj, hkj', rfl⟩
    have hkj : k ≤ j := by omega
    have heS : edge hj ∈ wave n k := (wave_mem k (edge hj)).mpr ⟨j, hj, hkj, rfl⟩
    have hpos : 0 < j := by omega
    have hpred : ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1))) ∈ wave n k := by
      refine (wave_mem k ((⟨j - 1, by omega⟩ : Fin (n + 1)), (⟨j, by omega⟩ : Fin (n + 1)))).mpr
        ⟨j - 1, by omega, by omega, ?_⟩
      ext <;> simp [edge, Nat.sub_add_cancel hpos]
    have hvload : vertex_load (chainDemands n) (wave n k) (edge hj).1 = 1 := by
      change vertex_load (chainDemands n) (wave n k) ((⟨j, by omega⟩ : Fin (n + 1))) = 1
      rw [vertex_load_chain (wave_subset_chain k) hj, if_pos heS]
    have hhold : (pool0Gen n).holdings (edge hj).1 = 0 := by
      simp [pool0Gen]
    have hrec : received (chainDemands n) (wave n k) (edge hj).1 = 1 := by
      change received (chainDemands n) (wave n k) ((⟨j, by omega⟩ : Fin (n + 1))) = 1
      rw [received_chain (wave_subset_chain k) (by omega : j ≤ n)]
      rw [if_neg (by omega : j ≠ 0), if_pos hpred]
    exact Finset.mem_filter.mpr ⟨heS, by
      rw [hvload, hhold, hrec]
      norm_num⟩

/-! ### 6. La chaîne descendante EST la vague -/

/-- La chaîne descendante de l'opérateur couplé par entrées est exactement
    la vague : chain k = S_k pour tout k ≤ n+1 (induction sur wave_step). -/
lemma chain_eq_wave (k : ℕ) (hk : k ≤ n + 1) : chain n k = wave n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ n := by omega
      calc
        chain n (k + 1) = entry_coupled_operator (pool0Gen n) (chainDemands n) (chain n k) := by
          rfl
        _ = entry_coupled_operator (pool0Gen n) (chainDemands n) (wave n k) := by
          rw [ih (by omega : k ≤ n + 1)]
        _ = wave n (k + 1) := wave_step k

/-! ### 7. Le théorème : loi Θ(n) -/

/-- **A5 — loi Θ(n)** : sur la chaîne v₀→…→vₙ (n arêtes, demandes unitaires,
    holdings nuls, couplage par les entrées), la solvabilité se propage comme
    une onde — exactement n rondes : pas de stabilisation avant n, stabilisation
    à n. -/
theorem chain_theta_n (n : ℕ) (_hn : 1 ≤ n) :
    (∀ k < n, chain n k ≠ chain n (k + 1)) ∧ chain n n = chain n (n + 1) := by
  constructor
  · intro k hk
    -- non-stabilisation : e_k ∈ S_k \ S_{k+1}
    rw [chain_eq_wave k (by omega), chain_eq_wave (k + 1) (by omega)]
    intro h
    have hk_in : edge (by omega : k < n) ∈ wave n k :=
      (wave_mem k (edge (by omega : k < n))).mpr ⟨k, by omega, by omega, rfl⟩
    have hk_out : edge (by omega : k < n) ∉ wave n (k + 1) := by
      intro h'
      rcases (wave_mem (k + 1) (edge (by omega : k < n))).mp h' with ⟨j, hj, hkj, heq⟩
      have hkj_eq : k = j := by
        simpa [edge] using congrArg Fin.val (congrArg Prod.fst heq)
      omega
    exact hk_out (h ▸ hk_in)
  · -- stabilisation : S_n = ∅ = S_{n+1}
    rw [chain_eq_wave n (by omega), chain_eq_wave (n + 1) (by omega)]
    apply Finset.ext
    intro e
    constructor
    · intro he
      rcases (wave_mem n e).mp he with ⟨i, hi, hni, heq⟩
      omega
    · intro he
      rcases (wave_mem (n + 1) e).mp he with ⟨i, hi, hni, heq⟩
      omega

/-! ### 6. J3b — la cellule {P3} de la carte des combinaisons : le plafond
    d'exposition (couplage ANTITONE en r)

  Réf. : cache/analyse_j3b_carte_combinaisons_2026-08-07.md §3-§6. Dans la
  classe C(P) du trilemme (H2 : sensibilité MONOTONE en r — les entrées
  aident), le couplage par les entrées perd les trois propriétés (T1-T3) ;
  la famille ANTITONE en r (plus d'entrées reçues ne peut jamais aider)
  garde l'idempotence et la finalité en une ronde et ne perd que la
  localité — la seule cellule {P3} de la carte. Porté depuis
  J3b_plafond_scratch.lean, commit 9fa6d44. -/

/-- Opérateur plafonné par les entrées : e survit si la charge de sa source
    est couverte ET les flux reçus ne dépassent pas un plafond par sommet.
    ANTITONE en r : plus d'entrées reçues ne peut jamais aider. -/
def entry_capped_operator (pool : FuturePool V) (demands : V × V → ℤ)
    (cap : V → ℤ) (S : ActivationState V) : ActivationState V :=
  S.filter (fun e =>
    vertex_load demands S e.1 ≤ pool.holdings e.1 ∧
    received demands S e.1 ≤ cap e.1)

/-- Contractivité conservée (même argument que entry_coupled_contractive). -/
lemma entry_capped_contractive (pool : FuturePool V) (demands : V × V → ℤ)
    (cap : V → ℤ) (S : ActivationState V) :
    entry_capped_operator pool demands cap S ⊆ S :=
  Finset.filter_subset _ _

/-- Antitonie des sommes filtrées sous inclusion : retirer des arêtes ne
    peut qu'alléger les sommes (demandes ≥ 0). Support de la double
    antitonie du plafond d'exposition (F2). -/
lemma filtered_sum_mono {α : Type*} [DecidableEq α] (f : α → ℤ)
    (h_nn : ∀ e, 0 ≤ f e) {S T : Finset α} (hST : T ⊆ S) (p : α → Prop)
    [DecidablePred p] : (T.filter p).sum f ≤ (S.filter p).sum f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact mem_filter.mpr ⟨hST (mem_filter.mp he).1, (mem_filter.mp he).2⟩
  · intro e _heS _heT
    exact h_nn e

/-- Les flux reçus décroissent : T ⊆ S, demandes ≥ 0 ⟹ received T v ≤ received S v. -/
lemma received_antitone_subset (demands : V × V → ℤ) (h_nn : ∀ e, 0 ≤ demands e)
    {S T : ActivationState V} (hST : T ⊆ S) (v : V) :
    received demands T v ≤ received demands S v := by
  unfold received
  exact filtered_sum_mono demands h_nn hST (fun e => e.2 = v)

/-- La charge décroît : T ⊆ S, demandes ≥ 0 ⟹ vertex_load T v ≤ vertex_load S v. -/
lemma vertex_load_antitone_subset (demands : V × V → ℤ) (h_nn : ∀ e, 0 ≤ demands e)
    {S T : ActivationState V} (hST : T ⊆ S) (v : V) :
    vertex_load demands T v ≤ vertex_load demands S v := by
  unfold vertex_load
  exact filtered_sum_mono demands h_nn hST (fun e => e.1 = v)

/-- **Idempotence du plafond d'exposition** : Φ_cap(Φ_cap(S)) = Φ_cap(S)
    sous demandes ≥ 0. La double antitonie (charge et entrées) rend le test
    plus facile quand l'état décroît — e ∈ Φ(S) ⟹ (ℓ' ≤ ℓ_S ∧ r' ≤ r_S) ⟹
    e repasse. Miroir de coupled_operator_idempotent (DualDAG:1138) ; la
    finalité en une ronde suit par le fait général P1 ⟹ P2 (carte §2.1). -/
theorem entry_capped_idempotent (pool : FuturePool V) (demands : V × V → ℤ)
    (cap : V → ℤ) (h_nn : ∀ e, 0 ≤ demands e) (S : ActivationState V) :
    entry_capped_operator pool demands cap (entry_capped_operator pool demands cap S) =
    entry_capped_operator pool demands cap S := by
  unfold entry_capped_operator
  exact filter_operator_idempotent_of_antitone
    (fun S' e => vertex_load demands S' e.1 ≤ pool.holdings e.1 ∧
      received demands S' e.1 ≤ cap e.1)
    (by
      intro T U e hTU htest
      exact ⟨by
        have h1 := vertex_load_antitone_subset demands h_nn hTU e.1
        omega, by
        have h2 := received_antitone_subset demands h_nn hTU e.1
        omega⟩) S

/-- Chaîne descendante de l'opérateur plafonné (miroir de entry_chain). -/
def entry_capped_chain (pool : FuturePool V) (demands : V × V → ℤ)
    (cap : V → ℤ) (init : ActivationState V) : ℕ → ActivationState V :=
  chain_of (entry_capped_operator pool demands cap) init

/-- Admission plafonnée : miroir de entry_admissible (EchelleCouplages:75). -/
def entry_capped_admissible (pool : FuturePool V) (demands : V × V → ℤ)
    (cap : V → ℤ) (current : ActivationState V) (e : V × V) : Prop :=
  e ∈ entry_capped_chain pool demands cap (current ∪ {e}) (current ∪ {e}).card

instance (pool : FuturePool V) (demands : V × V → ℤ) (cap : V → ℤ)
    (current : ActivationState V) (e : V × V) :
    Decidable (entry_capped_admissible pool demands cap current e) := by
  unfold entry_capped_admissible; infer_instance

/-- Budget 1 en v₁ seulement (la source de e₁₂ est couverte), plafond 0
    partout (aucun flux entrant toléré). -/
def poolCap : FuturePool (Fin 3) := ⟨fun v => if v = (1 : Fin 3) then 1 else 0, by decide⟩

def cap0 : Fin 3 → ℤ := fun _ => 0

/-- **Témoin de non-localité du plafond** : S₁ = {e₀₁} et S₂ = ∅ ont les MÊMES
    sorties à la source v₁, mais e₁₂ est admissible sous S₂ (charge couverte,
    aucun flux entrant) et pas sous S₁ (l'entrée e₀₁ fait dépasser le plafond
    cap ≡ 0). Contraste : le plafond reste IDEMPOTENT (théorème ci-dessus) —
    la cellule {P3} : idempotence et finalité gardées, localité perdue. -/
theorem entry_capped_admission_not_local :
    ((({((0 : Fin 3), (1 : Fin 3))} : ActivationState (Fin 3)).filter
        (fun f => f.1 = (1 : Fin 3))) =
      ((∅ : ActivationState (Fin 3)).filter (fun f => f.1 = (1 : Fin 3)))) ∧
    entry_capped_admissible poolCap demands3 cap0 (∅ : ActivationState (Fin 3))
      ((1 : Fin 3), (2 : Fin 3)) ∧
    ¬ entry_capped_admissible poolCap demands3 cap0
      ({((0 : Fin 3), (1 : Fin 3))} : ActivationState (Fin 3))
      ((1 : Fin 3), (2 : Fin 3)) := by
  refine ⟨by decide, by decide, by decide⟩

end EchelleCouplages
