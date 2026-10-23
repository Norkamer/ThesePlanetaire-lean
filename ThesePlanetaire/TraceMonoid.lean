/-

namespace TraceMonoid
  MonnaiesEndogene/TraceMonoid.lean
  Monoïde de traces sous EXT1 — fondation L4.

  Modèle EXT1 : Trace = Finset Letter (chaque lettre apparaît ≤1 fois).
  L'ordre d'activation n'importe pas ; concat = ∪.

  Extension 2026-05-26 : Independence, CartierFoata, FoataHeight.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace TraceMonoid


/-- L'alphabet des lettres = les 9 frontières planétaires (once-only monoïde M^∞ = (2^A, ∪)).
    Chaque constructeur correspond à une frontière planétaire (Rockström et al. 2009 / Richardson et al. 2023).
    Dans M^∞, chaque lettre apparaît au plus une fois (monoïde once-only). -/
inductive Letter
  | climateChange       -- Changement climatique (CO₂ atmosphérique)
  | biogeochemicalFlows -- Flux biogéochimiques (N, P)
  | freshwaterUse       -- Utilisation de l'eau douce
  | landSystemChange    -- Changement d'usage des terres
  | ozoneDepletion      -- Appauvrissement de l'ozone
  | biosphereIntegrity  -- Intégrité de la biosphère
  | oceanAcidification  -- Acidification des océans
  | novelEntities       -- Entités nouvelles (polluants persistants)
  | atmosphericAerosols -- Aérosols atmosphériques
  deriving DecidableEq, Fintype

/-- Identifiant numérique de la lettre (0 à 8), pour compatibilité avec le code existant utilisant .id -/
def Letter.id (l : Letter) : ℕ :=
  match l with
  | .climateChange => 0
  | .biogeochemicalFlows => 1
  | .freshwaterUse => 2
  | .landSystemChange => 3
  | .ozoneDepletion => 4
  | .biosphereIntegrity => 5
  | .oceanAcidification => 6
  | .novelEntities => 7
  | .atmosphericAerosols => 8

/-- Ordre sur les lettres (ordre des constructeurs, 0 à 8).
    Utilise Letter.id (0 à 8) comme ordre. -/
instance : LinearOrder Letter :=
  LinearOrder.lift' (fun a : Letter => Letter.id a) (fun a b h => by
    have h₁ : Letter.id a = Letter.id b := h
    -- Letter.id is injective on the 9 constructors
    fin_cases a <;> fin_cases b <;> simp [Letter.id] at h₁ ⊢ <;> (try omega) <;> (try aesop)
  )

/-- Trace EXT1 : ensemble de lettres activées. -/
@[ext]
structure Trace where
  letters : Finset Letter
  deriving DecidableEq

namespace Trace

def ofFinset (s : Finset Letter) : Trace := ⟨s⟩

@[simp] theorem letters_ofFinset (s : Finset Letter) :
    (ofFinset s).letters = s := rfl

@[simp] theorem ofFinset_letters (t : Trace) :
    ofFinset t.letters = t := by ext; simp [ofFinset]

def empty : Trace := ⟨∅⟩
def concat (t₁ t₂ : Trace) : Trace := ⟨t₁.letters ∪ t₂.letters⟩

/-- Th.1.1 (Cat A) : Associativité. -/
theorem concat_assoc (a b c : Trace) : concat (concat a b) c = concat a (concat b c) := by
  ext x; simp [concat, Finset.mem_union, or_assoc]

/-- Th.1.1 (Cat A) : Neutre à gauche. -/
theorem empty_concat (t : Trace) : concat empty t = t := by
  ext; dsimp [concat, empty]; simp

/-- Th.1.1 (Cat A) : Neutre à droite. -/
theorem concat_empty (t : Trace) : concat t empty = t := by
  ext; dsimp [concat, empty]; simp

/-- Th.1.1 (Cat A) : Commutativité. -/
theorem concat_comm (t₁ t₂ : Trace) : concat t₁ t₂ = concat t₂ t₁ := by
  ext x; simp [concat, Finset.mem_union, or_comm]

/-- Th.1.1 (Cat A) : Idempotence. -/
theorem concat_idem (t : Trace) : concat t t = t := by
  ext; dsimp [concat]; simp

/-- EXT1-compatibles : disjoints. -/
def ext1_compatible (t₁ t₂ : Trace) : Prop :=
  t₁.letters ∩ t₂.letters = ∅

/-- Th.1.2 (Cat A) : Cancellativité gauche sous disjointness. -/
theorem cancel_left_ext1 {t₁ t₂ t₃ : Trace}
    (h_d₁ : ext1_compatible t₁ t₂) (h_d₂ : ext1_compatible t₁ t₃)
    (h_eq : concat t₁ t₂ = concat t₁ t₃) : t₂ = t₃ := by
  dsimp [ext1_compatible] at h_d₁ h_d₂
  dsimp [concat] at h_eq
  have h_eq_finset : t₁.letters ∪ t₂.letters = t₁.letters ∪ t₃.letters := by
    have := congrArg Trace.letters h_eq
    simpa [concat] using this
  ext x
  constructor
  · intro hx2
    have hx_union : x ∈ t₁.letters ∪ t₂.letters := Finset.mem_union_right _ hx2
    rw [h_eq_finset] at hx_union
    rcases Finset.mem_union.1 hx_union with (hx1 | hx3)
    · exfalso
      have : x ∈ t₁.letters ∩ t₂.letters := Finset.mem_inter.mpr ⟨hx1, hx2⟩
      rw [h_d₁] at this; simp at this
    · exact hx3
  · intro hx3
    have hx_union : x ∈ t₁.letters ∪ t₃.letters := Finset.mem_union_right _ hx3
    rw [← h_eq_finset] at hx_union
    rcases Finset.mem_union.1 hx_union with (hx1 | hx2)
    · exfalso
      have : x ∈ t₁.letters ∩ t₃.letters := Finset.mem_inter.mpr ⟨hx1, hx3⟩
      rw [h_d₂] at this; simp at this
    · exact hx2

/-- Th.1.2 (Cat A) : Cancellativité droite. -/
theorem cancel_right_ext1 {t₁ t₂ t₃ : Trace}
    (h_d₁ : ext1_compatible t₂ t₁) (h_d₂ : ext1_compatible t₃ t₁)
    (h_eq : concat t₂ t₁ = concat t₃ t₁) : t₂ = t₃ :=
  cancel_left_ext1
    (by dsimp [ext1_compatible] at h_d₁ ⊢; rw [Finset.inter_comm]; exact h_d₁)
    (by dsimp [ext1_compatible] at h_d₂ ⊢; rw [Finset.inter_comm]; exact h_d₂)
    (by
      dsimp [concat] at h_eq ⊢
      have h_eq_finset : t₂.letters ∪ t₁.letters = t₃.letters ∪ t₁.letters :=
        congrArg Trace.letters h_eq
      ext x
      simpa [Finset.mem_union, or_comm] using congrArg (λ s : Finset Letter => x ∈ s) h_eq_finset)

def ofList (w : List Letter) : Trace := ⟨w.toFinset⟩

theorem ofList_append (w₁ w₂ : List Letter) :
    ofList (w₁ ++ w₂) = concat (ofList w₁) (ofList w₂) := by
  ext; dsimp [ofList, concat]; simp

noncomputable def length (t : Trace) : ℕ := Finset.card (t.letters)

/-- Additivité de la longueur : |τ₁ ∪ τ₂| = |τ₁| + |τ₂| pour des traces
    disjointes. C'est la loi produit once-only — la cardinalité de l'union
    disjointe qui rend la factorisation B_p(τ₁∪τ₂) = B_p(τ₁)·B_p(τ₂)/B_p(∅)
    vraie (consommé par BoltzmannMeasure, FiniteEXT1Measure, AnchorEventTyped). -/
theorem length_concat (t₁ t₂ : Trace) (h_disjoint : t₁.letters ∩ t₂.letters = ∅) :
    length (concat t₁ t₂) = length t₁ + length t₂ := by
  dsimp [concat, length]
  rw [Finset.card_union_of_disjoint]
  exact (Finset.disjoint_iff_inter_eq_empty).mpr h_disjoint

end Trace

/-! ### Relation d'indépendance

  I(a,b) = True si a et b commutent. La relation est symétrique et irréflexive.
  Sous EXT1, l'indépendance totale correspond au cas où toutes les lettres
  commutent (Trace = Finset). -/

/-- Relation d'indépendance sur l'alphabet : I(a,b) si a et b commutent.
    Symétrique et irréflexive. Utilise `= true` / `= false` pour la décidabilité. -/
structure Independence where
  alphabet : Finset Letter
  indep : Letter → Letter → Bool
  symm : ∀ a b, indep a b = true → indep b a = true
  irrefl : ∀ a, indep a a = false

namespace Independence

/-- Indépendance totale : toutes les paires distinctes commutent. -/
def total (alphabet : Finset Letter) : Independence where
  alphabet := alphabet
  indep a b := a ≠ b
  symm a b h := by
    simp at h ⊢
    exact Ne.symm h
  irrefl a := by simp

/-- Indépendance vide : aucune paire ne commute (ordre total strict). -/
def empty (alphabet : Finset Letter) : Independence where
  alphabet := alphabet
  indep _ _ := false
  symm a b h := by simp at h
  irrefl a := by simp

/-- L'indépendance est symétrique sur les valeurs booléennes. -/
lemma indep_symm_eq (I : Independence) (a b : Letter) : I.indep a b = I.indep b a := by
  by_cases h : I.indep a b = true
  · have h' := I.symm a b h; simp [h, h']
  · by_cases h' : I.indep b a = true
    · have h'' := I.symm b a h'
      exfalso; exact h (h'' ▸ rfl)
    · have h_false_a : I.indep a b = false := by
        have := Bool.eq_false_of_not_eq_true h
        exact this
      have h_false_b : I.indep b a = false := Bool.eq_false_of_not_eq_true h'
      simp [h_false_a, h_false_b]

/-- Restriction d'une relation d'indépendance à un sous-alphabet s ⊆ alphabet.
    H-FIXE : l'activation de s ne modifie pas les dépendances (I_restreint = I|_{s×s}).
    Réf. : Choffrut–Mercaş, DMTCS 12(4), 2010, DOI 10.46298/dmtcs.493. -/
def restrict (I : Independence) (s : Finset Letter) (_hs : s ⊆ I.alphabet) : Independence where
  alphabet := s
  indep := I.indep
  symm := I.symm
  irrefl := I.irrefl

@[simp] lemma restrict_alphabet (I : Independence) (s : Finset Letter) (hs : s ⊆ I.alphabet) :
    (I.restrict s hs).alphabet = s := rfl

@[simp] lemma restrict_indep (I : Independence) (s : Finset Letter) (hs : s ⊆ I.alphabet) :
    (I.restrict s hs).indep = I.indep := rfl

end Independence

/-! ### Décomposition de Cartier-Foata

  La forme normale de Cartier-Foata décompose une trace τ en couches
  F₁·F₂·...·F_k où chaque F_i est une clique du graphe de dépendance.

  Graphe de dépendance : a dépend de b ssi b.id < a.id et ¬ I(a,b).
  La transitivité de > sur ℕ garantit l'absence de cycles. -/

/-- Décomposition de Cartier-Foata. `depend a` = lettres à id plus petit
    qui ne sont pas indépendantes de a. -/
structure CartierFoata where
  indep : Independence
  depend (a : Letter) : Finset Letter
  depend_spec (a b : Letter) : b ∈ depend a ↔ (b ∈ indep.alphabet ∧ b.id < a.id ∧ indep.indep a b = false)

namespace CartierFoata

/-- Construction standard depuis une relation d'indépendance. -/
def ofIndependence (I : Independence) : CartierFoata where
  indep := I
  depend a := I.alphabet.filter (λ b => decide (b.id < a.id ∧ I.indep a b = false))
  depend_spec a b := by
    simp [depend, Finset.mem_filter, decide_eq_true_eq, and_comm, and_assoc, and_left_comm]

/-- Lemme : tout ensemble non vide admet un élément minimal (plus petit id),
    donc sans dépendance non résolue dans l'ensemble. -/
def exists_minimal (cf : CartierFoata) (rem : Finset Letter) (h_ne : rem.Nonempty) :
    { a // a ∈ rem ∧ (cf.depend a) ∩ rem = ∅ } := by
  let a := Finset.min' rem h_ne
  have ha_mem : a ∈ rem := Finset.min'_mem _ h_ne
  have ha_min : (cf.depend a) ∩ rem = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_rem⟩
    rcases (cf.depend_spec a x).mp hx_dep with ⟨_, h_lt, _⟩
    have h_min : a.id ≤ x.id := Finset.min'_le _ _ hx_rem
    linarith
  exact ⟨a, ha_mem, ha_min⟩

/-- Le reste après retrait de la première couche est un sous-ensemble strict :
    cœur du raisonnement greedy de Cartier-Foata — `exists_minimal` garantit
    que la première couche est non vide, donc le reste est strictement plus
    petit, ce qui fonde la strong induction. -/
lemma decomposeAux_layer_ssubset (cf : CartierFoata) (rem : Finset Letter) (hne : rem.Nonempty) :
    rem \ rem.filter (fun a => cf.depend a ∩ rem = ∅) ⊂ rem := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h_eq => ?_⟩
  obtain ⟨m, hm, h_min⟩ := cf.exists_minimal rem hne
  exact (fun hx => (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨hm, h_min⟩)) (h_eq ▸ hm)

/-- Décomposition d'un Finset en couches de Cartier-Foata. -/
noncomputable def decomposeAux (cf : CartierFoata) (rem : Finset Letter) : List (Finset Letter) :=
  Finset.strongInductionOn rem (λ rem ih =>
    if hne : rem.Nonempty then
      let layer := rem.filter (λ a => (cf.depend a ∩ rem) = ∅)
      let h_ss : rem \ layer ⊂ rem := by
        simpa [layer] using decomposeAux_layer_ssubset cf rem hne
      layer :: ih (rem \ layer) h_ss
    else [])

theorem decomposeAux_eq (cf : CartierFoata) (rem : Finset Letter) :
    decomposeAux cf rem =
    if h : rem.Nonempty then
      rem.filter (λ a => (cf.depend a ∩ rem) = ∅) :: decomposeAux cf (rem \ rem.filter (λ a => (cf.depend a ∩ rem) = ∅))
    else [] := by
  conv =>
    lhs
    rw [decomposeAux, Finset.strongInductionOn_eq]
  split <;> dsimp <;> rfl

/-- Cas de base de la hauteur : la décomposition du vide a longueur 0. -/
lemma decomposeAux_empty_length (cf : CartierFoata) :
    (decomposeAux cf (∅ : Finset Letter)).length = 0 := by
  rw [decomposeAux_eq, dif_neg (by simp)]
  rfl

/-- Récurrence de la hauteur : chaque couche non vide ajoute exactement 1
    à la longueur de la décomposition. -/
lemma decomposeAux_length_succ (cf : CartierFoata) (rem : Finset Letter) (hne : rem.Nonempty) :
    (decomposeAux cf rem).length =
      Nat.succ (decomposeAux cf (rem \ rem.filter (fun a => cf.depend a ∩ rem = ∅))).length := by
  rw [decomposeAux_eq, dif_pos hne]
  rfl

/-- Décomposition de Cartier-Foata d'une trace (Th.2.3 Cat A). -/
noncomputable def decompose (cf : CartierFoata) (t : Trace) : List (Finset Letter) :=
  decomposeAux cf t.letters

/-- Hauteur de Foata = nombre de couches. -/
noncomputable def height (cf : CartierFoata) (t : Trace) : ℕ :=
  (decompose cf t).length

/-- Lemme clé : sous h_no_dep, les dépendances d'un élément de s
    sont entièrement contenues dans s (aucune dans t). -/
lemma depend_inter_union_eq_depend_inter_s (cf : CartierFoata) (s t : Finset Letter)
    (h_no_dep : ∀ a ∈ s, ∀ b ∈ t, b ∉ cf.depend a) (a : Letter) (ha : a ∈ s) :
    cf.depend a ∩ (s ∪ t) = cf.depend a ∩ s := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_mem⟩
    rcases Finset.mem_union.mp hx_mem with (hx_s | hx_t)
    · exact Finset.mem_inter.mpr ⟨hx_dep, hx_s⟩
    · exfalso; exact h_no_dep a ha x hx_t hx_dep
  · have h_sub : s ⊆ s ∪ t := by
      intro x hx; exact Finset.mem_union_left t hx
    · intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_s⟩
      have h_sub : s ⊆ s ∪ t := by
        intro y hy; exact Finset.mem_union_left t hy
      exact Finset.mem_inter.mpr ⟨hx_dep, h_sub hx_s⟩

/-- Lemme préparatoire : sous h_consec, les dépendances d'un élément de u
    dans u ∪ v sont exactement ses dépendances dans u. -/
lemma depend_inter_union_eq_depend_inter_u (cf : CartierFoata) (u v : Trace)
    (h_consec : ∀ a ∈ u.letters, ∀ b ∈ v.letters, a.id < b.id) (a : Letter) (ha : a ∈ u.letters) :
    cf.depend a ∩ (u.letters ∪ v.letters) = cf.depend a ∩ u.letters := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_mem⟩
    rcases Finset.mem_union.mp hx_mem with (hx_u | hx_v)
    · exact Finset.mem_inter.mpr ⟨hx_dep, hx_u⟩
    · exfalso
      have h_not_dep : x ∉ cf.depend a := by
        by_contra h
        rcases (cf.depend_spec a x).mp h with ⟨_, hlt, _⟩
        linarith [h_consec a ha x hx_v]
      exact h_not_dep hx_dep
  · have h_sub : u.letters ⊆ u.letters ∪ v.letters := Finset.subset_union_left
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_u⟩
    exact Finset.mem_inter.mpr ⟨hx_dep, h_sub hx_u⟩

/-- Version Finset de `depend_inter_union_eq_depend_inter_u`. -/
lemma depend_inter_union_eq_depend_inter_u_finset (cf : CartierFoata) (u v : Finset Letter)
    (h_consec : ∀ a ∈ u, ∀ b ∈ v, a.id < b.id) (a : Letter) (ha : a ∈ u) :
    cf.depend a ∩ (u ∪ v) = cf.depend a ∩ u := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_mem⟩
    rcases Finset.mem_union.mp hx_mem with (hx_u | hx_v)
    · exact Finset.mem_inter.mpr ⟨hx_dep, hx_u⟩
    · exfalso
      have h_not_dep : x ∉ cf.depend a := by
        by_contra h
        rcases (cf.depend_spec a x).mp h with ⟨_, hlt, _⟩
        linarith [h_consec a ha x hx_v]
      exact h_not_dep hx_dep
  · have h_sub : u ⊆ u ∪ v := Finset.subset_union_left
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_u⟩
    exact Finset.mem_inter.mpr ⟨hx_dep, h_sub hx_u⟩

/-! ### Lemmes pour la fusion de couches sous indépendance totale

    Sous indépendance totale entre deux ensembles s et t (aucune dépendance
    croisée), la décomposition de Cartier-Foata de s ∪ t s'obtient en
    fusionnant les couches de s et t une par une. Cela donne une hauteur
    égale au max des hauteurs individuelles. -/

/-- Sous indépendance totale, aucune dépendance croisée. -/
lemma no_cross_dependency (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true)
    (a : Letter) (ha : a ∈ s) (b : Letter) (hb : b ∈ t) :
    b ∉ cf.depend a := by
  by_contra h_dep
  rcases (cf.depend_spec a b).mp h_dep with ⟨_, _, h_false⟩
  have h_true : cf.indep.indep a b = true := h_indep a ha b hb
  rw [h_true] at h_false
  contradiction

/-- Sous indépendance totale, les dépendances d'un élément de s dans s ∪ t
    sont exactement ses dépendances dans s. -/
lemma depend_inter_union_eq_depend_inter_s_indep (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true)
    (a : Letter) (ha : a ∈ s) :
    cf.depend a ∩ (s ∪ t) = cf.depend a ∩ s := by
  have h_no_dep : ∀ a ∈ s, ∀ b ∈ t, b ∉ cf.depend a :=
    λ a ha b hb => no_cross_dependency cf h_indep a ha b hb
  exact depend_inter_union_eq_depend_inter_s cf s t h_no_dep a ha

/-- Symétrie de `depend_inter_union_eq_depend_inter_s_indep`. -/
lemma depend_inter_union_eq_depend_inter_t_indep (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true)
    (b : Letter) (hb : b ∈ t) :
    cf.depend b ∩ (s ∪ t) = cf.depend b ∩ t := by
  have h_indep' : ∀ b ∈ t, ∀ a ∈ s, cf.indep.indep b a = true := by
    intros b hb a ha
    exact cf.indep.symm a b (h_indep a ha b hb)
  have h_no_dep : ∀ b ∈ t, ∀ a ∈ s, a ∉ cf.depend b :=
    λ b hb a ha => no_cross_dependency cf h_indep' b hb a ha
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_mem⟩
    rcases Finset.mem_union.mp hx_mem with (hx_s | hx_t)
    · exfalso; exact h_no_dep b hb x hx_s hx_dep
    · exact Finset.mem_inter.mpr ⟨hx_dep, hx_t⟩
  · have h_sub : t ⊆ s ∪ t := Finset.subset_union_right
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_dep, hx_t⟩
    exact Finset.mem_inter.mpr ⟨hx_dep, h_sub hx_t⟩

/-- Fusion des premières couches sous indépendance totale.
    Si s et t sont indépendants, la première couche de s ∪ t est
    l'union des premières couches de s et t. -/
lemma first_layer_union_indep (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true) :
    (s ∪ t).filter (λ a => (cf.depend a ∩ (s ∪ t)) = ∅) =
      (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ∪ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
  ext a
  simp
  constructor
  · -- a ∈ première couche de s ∪ t
    intro h
    rcases h with ⟨ha_union, hdep⟩
    rcases ha_union with (ha_s | ha_t)
    · -- a ∈ s
      have hdep_s : cf.depend a ∩ s = ∅ := by
        rw [depend_inter_union_eq_depend_inter_s_indep cf h_indep a ha_s] at hdep
        exact hdep
      exact Or.inl ⟨ha_s, hdep_s⟩
    · -- a ∈ t
      have hdep_t : cf.depend a ∩ t = ∅ := by
        rw [depend_inter_union_eq_depend_inter_t_indep cf h_indep a ha_t] at hdep
        exact hdep
      exact Or.inr ⟨ha_t, hdep_t⟩
  · -- a ∈ (première couche de s) ∪ (première couche de t)
    intro h
    rcases h with (⟨ha_s, hdep_s⟩ | ⟨ha_t, hdep_t⟩)
    · -- a ∈ première couche de s
      have hdep_union : cf.depend a ∩ (s ∪ t) = ∅ := by
        rw [depend_inter_union_eq_depend_inter_s_indep cf h_indep a ha_s]
        exact hdep_s
      exact ⟨Or.inl ha_s, hdep_union⟩
    · -- a ∈ première couche de t
      have hdep_union : cf.depend a ∩ (s ∪ t) = ∅ := by
        rw [depend_inter_union_eq_depend_inter_t_indep cf h_indep a ha_t]
        exact hdep_t
      exact ⟨Or.inr ha_t, hdep_union⟩

/-- Sous indépendance totale, l'intersection s ∩ t est contenue dans la
    première couche de s (et par symétrie, dans la première couche de t).
    C'est la clé qui garantit que les restes après retrait de la première
    couche sont disjoints et fusionnent correctement. -/
lemma intersect_in_layers (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true) :
    s ∩ t ⊆ s.filter (λ a => (cf.depend a ∩ s) = ∅) := by
  intro x hx
  have hx_s : x ∈ s := Finset.mem_of_mem_inter_left hx
  have hx_t : x ∈ t := Finset.mem_of_mem_inter_right hx
  have h_no_dep : ∀ y ∈ s, y ∉ cf.depend x := by
    intros y hy
    by_contra h_dep
    have ⟨_, _, h_indep_false⟩ := (cf.depend_spec x y).mp h_dep
    have h_indep_false' : cf.indep.indep y x = false := by
      rw [cf.indep.indep_symm_eq x y] at h_indep_false
      exact h_indep_false
    have h_indep_true := h_indep y hy x hx_t
    rw [h_indep_false'] at h_indep_true
    contradiction
  simp
  refine ⟨hx_s, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rcases Finset.mem_inter.mp hy with ⟨hy_dep, hy_s⟩
  exact h_no_dep y hy_s hy_dep

/-- Sous indépendance totale, le reste après retrait de la première couche
    de s ∪ t est l'union des restes de s et de t. -/
lemma remainder_union_eq (cf : CartierFoata) {s t : Finset Letter}
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true) :
    (s ∪ t) \ ((s ∪ t).filter (λ a => (cf.depend a ∩ (s ∪ t)) = ∅)) =
      (s \ (s.filter (λ a => (cf.depend a ∩ s) = ∅))) ∪ (t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅))) := by
  have h_layer_union : (s ∪ t).filter (λ a => (cf.depend a ∩ (s ∪ t)) = ∅) =
    (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ∪ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
    exact first_layer_union_indep cf h_indep
  rw [h_layer_union]
  ext x
  constructor
  · -- Forward : x ∈ (s ∪ t) \ layer_union → x ∈ (s \ layer_s) ∪ (t \ layer_t)
    intro h
    have hx_union : x ∈ s ∪ t := (Finset.mem_sdiff.mp h).1
    have hx_not_layer_union : x ∉ (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ∪ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := (Finset.mem_sdiff.mp h).2
    have hx_not_layer_s : x ∉ s.filter (λ a => (cf.depend a ∩ s) = ∅) := by
      intro h'
      exact hx_not_layer_union (Finset.mem_union_left _ h')
    have hx_not_layer_t : x ∉ t.filter (λ a => (cf.depend a ∩ t) = ∅) := by
      intro h'
      exact hx_not_layer_union (Finset.mem_union_right _ h')
    rcases Finset.mem_union.mp hx_union with (hx_s | hx_t)
    · -- x ∈ s
      have hx_in_sdiff : x ∈ s \ (s.filter (λ a => (cf.depend a ∩ s) = ∅)) := by
        apply Finset.mem_sdiff.mpr
        exact ⟨hx_s, hx_not_layer_s⟩
      exact Finset.mem_union_left _ hx_in_sdiff
    · -- x ∈ t
      have hx_in_sdiff : x ∈ t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
        apply Finset.mem_sdiff.mpr
        exact ⟨hx_t, hx_not_layer_t⟩
      exact Finset.mem_union_right _ hx_in_sdiff
  · -- Backward : x ∈ (s \ layer_s) ∪ (t \ layer_t) → x ∈ (s ∪ t) \ layer_union
    intro h
    rcases Finset.mem_union.mp h with (hx_s | hx_t)
    · -- x ∈ s \ layer_s
      have hx_s_mem : x ∈ s := (Finset.mem_sdiff.mp hx_s).1
      have hx_not_layer_s : x ∉ s.filter (λ a => (cf.depend a ∩ s) = ∅) := (Finset.mem_sdiff.mp hx_s).2
      have hx_not_layer_union : x ∉ (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ∪ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
        intro h'
        rcases Finset.mem_union.mp h' with (h_s | h_t)
        · exact hx_not_layer_s h_s
        · -- x ∈ layer_t → x ∈ t → x ∈ s ∩ t → x ∈ layer_s, contradiction
          have hx_t' : x ∈ t := by
            exact (Finset.mem_filter.mp h_t).1
          have h_subset := intersect_in_layers cf h_indep
          have hx_layer_s : x ∈ s.filter (λ a => (cf.depend a ∩ s) = ∅) := by
            apply h_subset
            exact Finset.mem_inter.mpr ⟨hx_s_mem, hx_t'⟩
          exact hx_not_layer_s hx_layer_s
      have hx_union : x ∈ s ∪ t := Finset.mem_union_left _ hx_s_mem
      exact Finset.mem_sdiff.mpr ⟨hx_union, hx_not_layer_union⟩
    · -- x ∈ t \ layer_t
      have hx_t_mem : x ∈ t := (Finset.mem_sdiff.mp hx_t).1
      have hx_not_layer_t : x ∉ t.filter (λ a => (cf.depend a ∩ t) = ∅) := (Finset.mem_sdiff.mp hx_t).2
      have hx_not_layer_union : x ∉ (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ∪ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
        intro h'
        rcases Finset.mem_union.mp h' with (h_s | h_t)
        · -- x ∈ layer_s → x ∈ s → x ∈ s ∩ t → x ∈ layer_t, contradiction
          have hx_s' : x ∈ s := by
            exact (Finset.mem_filter.mp h_s).1
          have h_indep' : ∀ b ∈ t, ∀ a ∈ s, cf.indep.indep b a = true := by
            intros b hb a ha
            exact cf.indep.symm a b (h_indep a ha b hb)
          have h_subset := intersect_in_layers cf h_indep'
          have hx_layer_t : x ∈ t.filter (λ a => (cf.depend a ∩ t) = ∅) := by
            apply h_subset
            exact Finset.mem_inter.mpr ⟨hx_t_mem, hx_s'⟩
          exact hx_not_layer_t hx_layer_t
        · exact hx_not_layer_t h_t
      have hx_union : x ∈ s ∪ t := Finset.mem_union_right _ hx_t_mem
      exact Finset.mem_sdiff.mpr ⟨hx_union, hx_not_layer_union⟩

/-- Égalité des hauteurs sous indépendance totale.
    Si s et t sont indépendants, la hauteur de s ∪ t est le max des hauteurs.
    Preuve par strongInductionOn sur s, en exploitant la fusion des premières
    couches (first_layer_union_indep) et l'égalité des restes
    (remainder_union_eq). -/
lemma decomposeAux_union_indep_eq_max (cf : CartierFoata) (s t : Finset Letter)
    (h_indep : ∀ a ∈ s, ∀ b ∈ t, cf.indep.indep a b = true) :
    (decomposeAux cf (s ∪ t)).length =
      max (decomposeAux cf s).length (decomposeAux cf t).length := by
  revert t
  refine Finset.strongInductionOn s (λ s ih => ?_)
  intro t h_indep
  by_cases hne_s : s.Nonempty
  · -- s non vide
    by_cases hne_t : t.Nonempty
    · -- t non vide : cas inductif principal
      let layer_s := s.filter (λ a => (cf.depend a ∩ s) = ∅)
      let layer_t := t.filter (λ a => (cf.depend a ∩ t) = ∅)
      let layer_union := (s ∪ t).filter (λ a => (cf.depend a ∩ (s ∪ t)) = ∅)
      have h_layer_union : layer_union = layer_s ∪ layer_t := by
        unfold layer_union layer_s layer_t
        exact first_layer_union_indep cf h_indep
      have h_rest : (s ∪ t) \ layer_union = (s \ layer_s) ∪ (t \ layer_t) := by
        unfold layer_union layer_s layer_t
        exact remainder_union_eq cf h_indep
      have h_ss : s \ layer_s ⊂ s := by
        simpa [layer_s] using decomposeAux_layer_ssubset cf s hne_s
      have h_ih := ih (s \ layer_s) h_ss (t \ layer_t) (by
        intro a ha b hb
        simp at ha hb
        exact h_indep a ha.1 b hb.1
      )
      have h_uv_ne : (s ∪ t).Nonempty := by
        rcases hne_s with ⟨a, ha⟩
        use a
        exact Finset.mem_union_left t ha
      have h_lhs : (decomposeAux cf (s ∪ t)).length = Nat.succ (decomposeAux cf ((s ∪ t) \ layer_union)).length :=
        decomposeAux_length_succ cf (s ∪ t) h_uv_ne
      have h_rhs_s : (decomposeAux cf s).length = Nat.succ (decomposeAux cf (s \ layer_s)).length :=
        decomposeAux_length_succ cf s hne_s
      have h_rhs_t : (decomposeAux cf t).length = Nat.succ (decomposeAux cf (t \ layer_t)).length :=
        decomposeAux_length_succ cf t hne_t
      calc
        (decomposeAux cf (s ∪ t)).length
            = Nat.succ (decomposeAux cf ((s ∪ t) \ layer_union)).length := by rw [h_lhs]
        _ = Nat.succ (decomposeAux cf ((s \ layer_s) ∪ (t \ layer_t))).length := by rw [h_rest]
        _ = Nat.succ (max (decomposeAux cf (s \ layer_s)).length (decomposeAux cf (t \ layer_t)).length) := by rw [h_ih]
        _ = max (Nat.succ (decomposeAux cf (s \ layer_s)).length) (Nat.succ (decomposeAux cf (t \ layer_t)).length) := by
            rcases le_total (decomposeAux cf (s \ layer_s)).length (decomposeAux cf (t \ layer_t)).length with h | h
            · have h1 : max (decomposeAux cf (s \ layer_s)).length (decomposeAux cf (t \ layer_t)).length = (decomposeAux cf (t \ layer_t)).length := max_eq_right h
              have h2 : max (Nat.succ (decomposeAux cf (s \ layer_s)).length) (Nat.succ (decomposeAux cf (t \ layer_t)).length) = Nat.succ (decomposeAux cf (t \ layer_t)).length := max_eq_right (Nat.succ_le_succ h)
              rw [h1, h2]
            · have h1 : max (decomposeAux cf (s \ layer_s)).length (decomposeAux cf (t \ layer_t)).length = (decomposeAux cf (s \ layer_s)).length := max_eq_left h
              have h2 : max (Nat.succ (decomposeAux cf (s \ layer_s)).length) (Nat.succ (decomposeAux cf (t \ layer_t)).length) = Nat.succ (decomposeAux cf (s \ layer_s)).length := max_eq_left (Nat.succ_le_succ h)
              rw [h1, h2]
        _ = max (decomposeAux cf s).length (decomposeAux cf t).length := by
            rw [h_rhs_s, h_rhs_t]
    · -- t vide
      have h_t_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne_t
      rw [h_t_empty, Finset.union_empty]
      have h_zero : (decomposeAux cf (∅ : Finset Letter)).length = 0 :=
        decomposeAux_empty_length cf
      rw [h_zero]
      simp
  · -- s vide
    have h_s_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne_s
    rw [h_s_empty, Finset.empty_union]
    have h_zero : (decomposeAux cf (∅ : Finset Letter)).length = 0 :=
      decomposeAux_empty_length cf
    rw [h_zero]
    simp

/-- Monotonie de la hauteur de Foata par inclusion d'ensembles. -/
lemma decomposeAux_subset_length_le (cf : CartierFoata) {s t : Finset Letter}
    (h_sub : s ⊆ t) : (decomposeAux cf s).length ≤ (decomposeAux cf t).length := by
  have H : ∀ (t : Finset Letter), ∀ (s : Finset Letter), s ⊆ t → (decomposeAux cf s).length ≤ (decomposeAux cf t).length := by
    intro t'
    apply @Finset.strongInductionOn _ (λ t => ∀ (s : Finset Letter), s ⊆ t → (decomposeAux cf s).length ≤ (decomposeAux cf t).length) t'
    intro t ih
    intro s h_sub
    by_cases hne : s.Nonempty
    · -- s non vide, donc t aussi
      have htne : t.Nonempty := Finset.Nonempty.mono h_sub hne
      have h_ss : s \ (s.filter (λ a => (cf.depend a ∩ s) = ∅)) ⊆ t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) := by
        intro x hx
        have hx_s : x ∈ s := (Finset.mem_sdiff.mp hx).1
        have hx_not_layer_s : x ∉ s.filter (λ a => (cf.depend a ∩ s) = ∅) := (Finset.mem_sdiff.mp hx).2
        have hx_t : x ∈ t := h_sub hx_s
        have hx_not_layer_t : x ∉ t.filter (λ a => (cf.depend a ∩ t) = ∅) := by
          intro hx_layer_t
          have h_dep : (cf.depend x ∩ t) = ∅ := (Finset.mem_filter.mp hx_layer_t).2
          have h_dep_s : (cf.depend x ∩ s) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro y hy
            have hy_t : y ∈ t := h_sub (Finset.mem_of_mem_inter_right hy)
            have h_contra : y ∈ (cf.depend x ∩ t) := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hy).1, hy_t⟩
            rw [h_dep] at h_contra
            contradiction
          have hx_layer_s : x ∈ s.filter (λ a => (cf.depend a ∩ s) = ∅) := Finset.mem_filter.mpr ⟨hx_s, h_dep_s⟩
          exact hx_not_layer_s hx_layer_s
        exact Finset.mem_sdiff.mpr ⟨hx_t, hx_not_layer_t⟩
      have h_ssubset : t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅)) ⊂ t :=
        decomposeAux_layer_ssubset cf t htne
      have h_ih := ih (t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅))) h_ssubset (s \ (s.filter (λ a => (cf.depend a ∩ s) = ∅))) h_ss
      have h_lhs : (decomposeAux cf s).length = Nat.succ (decomposeAux cf (s \ (s.filter (λ a => (cf.depend a ∩ s) = ∅)))).length :=
        decomposeAux_length_succ cf s hne
      have h_rhs : (decomposeAux cf t).length = Nat.succ (decomposeAux cf (t \ (t.filter (λ a => (cf.depend a ∩ t) = ∅)))).length :=
        decomposeAux_length_succ cf t htne
      rw [h_lhs, h_rhs]
      exact Nat.succ_le_succ h_ih
    · -- s vide
      have h_s_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [h_s_empty]
      have h_zero : (decomposeAux cf (∅ : Finset Letter)).length = 0 :=
        decomposeAux_empty_length cf
      rw [h_zero]
      apply Nat.zero_le
  exact H t s h_sub

/-- Sous-additivité de la longueur de décomposition pour union consécutive. -/
lemma decomposeAux_union_length_le (cf : CartierFoata) (u v : Finset Letter)
    (h_consec : ∀ a ∈ u, ∀ b ∈ v, a.id < b.id) :
    (decomposeAux cf (u ∪ v)).length ≤ (decomposeAux cf u).length + (decomposeAux cf v).length := by
  revert v
  refine Finset.strongInductionOn u (λ u ih => ?_)
  intro v h_consec
  by_cases hne : u.Nonempty
  · -- u est non vide
    have h_uv_ne : (u ∪ v).Nonempty := by
      rcases hne with ⟨a, ha⟩
      use a
      exact Finset.mem_union_left v ha
    have hu_ne : u.Nonempty := hne
    let layer_u := u.filter (λ a => (cf.depend a ∩ u) = ∅)
    let layer_uv := (u ∪ v).filter (λ a => (cf.depend a ∩ (u ∪ v)) = ∅)
    have h_inter : layer_uv ∩ u = layer_u := by
      unfold layer_uv layer_u
      ext a
      simp
      constructor
      · -- a ∈ layer_uv ∩ u → a ∈ layer_u
        intro h
        rcases h with ⟨⟨_, hP⟩, h_u⟩
        refine ⟨h_u, ?_⟩
        rw [depend_inter_union_eq_depend_inter_u_finset cf u v h_consec a h_u] at hP
        exact hP
      · -- a ∈ layer_u → a ∈ layer_uv ∩ u
        intro h
        rcases h with ⟨h_u, hQ⟩
        refine ⟨⟨Or.inl h_u, ?_⟩, h_u⟩
        rw [depend_inter_union_eq_depend_inter_u_finset cf u v h_consec a h_u]
        exact hQ
    have h_u_diff : u \ layer_uv = u \ layer_u := by
      rw [← h_inter]
      simp
    have h_rem : (u ∪ v) \ layer_uv = (u \ layer_u) ∪ (v \ layer_uv) := by
      rw [show u \ layer_u = u \ layer_uv by exact h_u_diff.symm]
      ext x
      simp
      constructor
      · intro h
        rcases h with ⟨hx_uv, hx_not⟩
        rcases hx_uv with (hx_u | hx_v)
        · exact Or.inl ⟨hx_u, hx_not⟩
        · exact Or.inr ⟨hx_v, hx_not⟩
      · intro h
        rcases h with (⟨hx_u, hx_not⟩ | ⟨hx_v, hx_not⟩)
        · exact ⟨Or.inl hx_u, hx_not⟩
        · exact ⟨Or.inr hx_v, hx_not⟩
    have h_v_sub : v \ layer_uv ⊆ v := Finset.sdiff_subset
    have h_u_ss : u \ layer_u ⊂ u := by
      simpa [layer_u] using decomposeAux_layer_ssubset cf u hu_ne
    have h_ih := ih (u \ layer_u) h_u_ss (v \ layer_uv) (by
      intro a ha b hb
      simp at ha hb
      exact h_consec a ha.1 b hb.1
    )
    have h_mono : (decomposeAux cf (v \ layer_uv)).length ≤ (decomposeAux cf v).length := by
      apply decomposeAux_subset_length_le cf h_v_sub
    have h_lhs : (decomposeAux cf (u ∪ v)).length = Nat.succ (decomposeAux cf ((u ∪ v) \ layer_uv)).length :=
      decomposeAux_length_succ cf (u ∪ v) h_uv_ne
    have h_rhs_u : (decomposeAux cf u).length = Nat.succ (decomposeAux cf (u \ layer_u)).length :=
      decomposeAux_length_succ cf u hu_ne
    calc
      (decomposeAux cf (u ∪ v)).length
          = Nat.succ (decomposeAux cf ((u ∪ v) \ layer_uv)).length := by rw [h_lhs]
      _ = Nat.succ (decomposeAux cf ((u \ layer_u) ∪ (v \ layer_uv))).length := by rw [h_rem]
      _ ≤ Nat.succ ((decomposeAux cf (u \ layer_u)).length + (decomposeAux cf (v \ layer_uv)).length) := by
          exact Nat.succ_le_succ h_ih
      _ ≤ Nat.succ ((decomposeAux cf (u \ layer_u)).length + (decomposeAux cf v).length) := by
          exact Nat.succ_le_succ (Nat.add_le_add_left h_mono _)
      _ = Nat.succ (decomposeAux cf (u \ layer_u)).length + (decomposeAux cf v).length := by
          rw [Nat.succ_add]
      _ = (decomposeAux cf u).length + (decomposeAux cf v).length := by
          rw [h_rhs_u]
  · -- u vide
    have h_u_empty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [h_u_empty]
    have h_zero : (decomposeAux cf (∅ : Finset Letter)).length = 0 :=
      decomposeAux_empty_length cf
    rw [h_zero]
    simp

/-- Th.7.1 (Cat A) : Sous-additivité de la hauteur de Foata pour traces consécutives.

    Si toutes les lettres de `u` précèdent strictement celles de `v` dans l'ordre
    d'activation (id), alors h(u·v) ≤ h(u) + h(v). -/
theorem height_subadditive (cf : CartierFoata) (u v : Trace)
    (h_consec : ∀ a ∈ u.letters, ∀ b ∈ v.letters, a.id < b.id) :
    height cf (Trace.concat u v) ≤ height cf u + height cf v := by
  unfold height; simp [decompose, Trace.concat]
  exact decomposeAux_union_length_le cf u.letters v.letters h_consec

lemma decomposeAux_length_le (cf : CartierFoata) (rem : Finset Letter) :
    (decomposeAux cf rem).length ≤ rem.card := by
  refine Finset.strongInductionOn rem ?_
  intro rem ih
  rw [decomposeAux_eq]
  by_cases hne : rem.Nonempty
  · simp [hne]
    have h_ss : rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅)) ⊂ rem :=
      decomposeAux_layer_ssubset cf rem hne
    have h_ih := ih (rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅))) h_ss
    have h_card_lt : (rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅))).card < rem.card :=
      Finset.card_lt_card h_ss
    calc
      Nat.succ ((decomposeAux cf (rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅)))).length)
          ≤ Nat.succ ((rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅))).card) := Nat.succ_le_succ h_ih
      _ ≤ rem.card := Nat.succ_le_of_lt h_card_lt
  · simp [hne]

/-- Th.7.2 (Cat A) : Borne de Moore h(τ) ≤ |Σ|.
    Chaque couche contient ≥ 1 lettre et les couches partitionnent t.letters.
    Hypothèse : toutes les lettres de la trace appartiennent à l'alphabet
    (nécessaire car le type Trace n'impose pas cette restriction). -/
theorem height_bound (cf : CartierFoata) (t : Trace) (h_sub : t.letters ⊆ cf.indep.alphabet) :
    height cf t ≤ cf.indep.alphabet.card := by
  unfold height
  have h := decomposeAux_length_le cf t.letters
  have h_card : t.letters.card ≤ cf.indep.alphabet.card :=
    Finset.card_le_card h_sub
  exact Nat.le_trans h h_card

/-- Énumère toutes les cliques du graphe de concurrence.
    Une clique C est un ensemble non vide de lettres où toute paire
    distincte a,b ∈ C vérifie I(a,b) = true (i.e., elles sont concurrentes).
    Énumération exhaustive des 2^|Σ| sous-ensembles, filtrage par test de clique. -/
noncomputable def cliques (cf : CartierFoata) : List (Finset Letter) :=
  (cf.indep.alphabet.powerset).toList.filter (λ s =>
    s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, a = b ∨ cf.indep.indep a b = true)

/-- Lemme : toutes les couches de `decompose` sont des sous-ensembles de la trace. -/
lemma decompose_layers_subset (cf : CartierFoata) (trace : Trace) :
    ∀ layer ∈ cf.decompose trace, layer ⊆ trace.letters := by
  unfold decompose
  apply @Finset.strongInductionOn _ (λ rem => ∀ layer ∈ decomposeAux cf rem, layer ⊆ rem) trace.letters
  intro rem ih layer hlayer
  rw [decomposeAux_eq] at hlayer
  by_cases hne : rem.Nonempty
  · simp [hne] at hlayer
    rcases hlayer with (rfl | hlayer)
    · intro a ha
      exact (Finset.mem_filter.mp ha).1
    · have h_ih := ih (rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅))) (by
        exact decomposeAux_layer_ssubset cf rem hne
      ) layer hlayer
      intro a ha
      have h_mem : a ∈ rem := by
        have h_a_in_sdiff : a ∈ rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅)) := h_ih ha
        exact (Finset.mem_sdiff.mp h_a_in_sdiff).1
      exact h_mem
  · simp [hne] at hlayer

/-- Lemme : l'union des couches de `decompose` est la trace complète. -/
lemma decompose_union_eq (cf : CartierFoata) (trace : Trace) :
    (cf.decompose trace).foldr (· ∪ ·) ∅ = trace.letters := by
  unfold decompose
  apply @Finset.strongInductionOn _ (λ rem => (decomposeAux cf rem).foldr (· ∪ ·) ∅ = rem) trace.letters
  intro rem ih
  rw [decomposeAux_eq]
  by_cases hne : rem.Nonempty
  · simp [hne]
    have h_ih := ih (rem \ (rem.filter (λ a => (cf.depend a ∩ rem) = ∅))) (by
      exact decomposeAux_layer_ssubset cf rem hne
    )
    rw [h_ih]
    have h_layer_sub : rem.filter (λ a => (cf.depend a ∩ rem) = ∅) ⊆ rem := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    exact Finset.union_sdiff_of_subset h_layer_sub
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-! ### B4 — Chaîne de dépendance ≤ hauteur de Foata -/

/-- Toute chaîne de dépendance a longueur ≤ nombre de couches de Foata.
    Nodup est automatique (depend_spec donne b.id < a.id, les ids décroissent
    strictement), donc non requis en hypothèse. -/
theorem dep_chain_length_le_decomposeAux (cf : CartierFoata) :
    ∀ (rem : Finset Letter) (chain : List Letter),
    (∀ a ∈ chain, a ∈ rem) →
    chain.IsChain (fun a b => b ∈ cf.depend a) →
    chain.length ≤ (decomposeAux cf rem).length := by
  intro rem
  refine Finset.strongInductionOn rem ?_
  intro rem ih chain h_sub h_chain
  rw [decomposeAux_eq]
  by_cases hne : rem.Nonempty
  · rw [dif_pos hne]
    set layer := rem.filter (fun a => cf.depend a ∩ rem = ∅) with layer_def
    set rem' := rem \ layer with rem'_def
    have h_rem'_ss : rem' ⊂ rem := by
      simpa [layer, rem'] using decomposeAux_layer_ssubset cf rem hne
    match chain, h_sub, h_chain with
    | [], _, _ => simp
    | [_], _, _ => simp
    | a :: b :: rest, h_sub', h_chain' =>
      have h_dropLast_sub_rem' : ∀ x ∈ (a :: b :: rest).dropLast, x ∈ rem' := by
        intro x hx
        have hx_rem : x ∈ rem := h_sub' x (List.mem_of_mem_dropLast hx)
        refine Finset.mem_sdiff.mpr ⟨hx_rem, ?_⟩
        intro hx_layer
        have h_dep_empty := (Finset.mem_filter.mp hx_layer).2
        obtain ⟨i, hi, h_eq⟩ := List.mem_iff_getElem.mp hx
        have h_dl_len := @List.length_dropLast _ (a :: b :: rest)
        have hi' : i + 1 < (a :: b :: rest).length := by omega
        have h_get := List.getElem_dropLast (xs := a :: b :: rest) hi
        have h_xi : x = (a :: b :: rest)[i]'(by omega) := h_eq.symm.trans h_get
        have h_rel := h_chain'.getElem i (by omega)
        have h_next_rem := h_sub' _ (List.getElem_mem hi')
        have h_mem : (a :: b :: rest)[i + 1] ∈ cf.depend ((a :: b :: rest)[i]'(by omega)) ∩ rem :=
          Finset.mem_inter.mpr ⟨h_rel, h_next_rem⟩
        rw [← h_xi] at h_mem
        rw [h_dep_empty] at h_mem
        simp at h_mem
      have h_dropLast_chain : (a :: b :: rest).dropLast.IsChain (fun a b => b ∈ cf.depend a) := by
        have h_ne : a :: b :: rest ≠ [] := List.cons_ne_nil _ _
        have h_split : (a :: b :: rest).dropLast ++
            [(a :: b :: rest).getLast h_ne] = a :: b :: rest :=
          List.dropLast_append_getLast h_ne
        exact (h_split ▸ h_chain').left_of_append
      have h_ih := ih rem' h_rem'_ss _ h_dropLast_sub_rem' h_dropLast_chain
      have h_dl_len := @List.length_dropLast _ (a :: b :: rest)
      simp only [List.length_cons] at h_dl_len ⊢
      omega
  · rw [dif_neg hne]
    match chain, h_sub with
    | [], _ => simp
    | c :: _, h_sub' =>
      have := h_sub' c List.mem_cons_self
      rw [Finset.not_nonempty_iff_eq_empty.mp hne] at this
      simp at this

/-- Corollaire : chaîne de dépendance ≤ hauteur de Foata d'une trace. -/
theorem dep_chain_length_le_height (cf : CartierFoata) (t : Trace)
    (chain : List Letter) (h_sub : ∀ a ∈ chain, a ∈ t.letters)
    (h_chain : chain.IsChain (fun a b => b ∈ cf.depend a)) :
    chain.length ≤ height cf t :=
  dep_chain_length_le_decomposeAux cf t.letters chain h_sub h_chain

/-! ### B1 — Maximalité des couches Foata -/

lemma decomposeAux_cons (cf : CartierFoata) (rem : Finset Letter) (hne : rem.Nonempty) :
    decomposeAux cf rem =
    rem.filter (fun a => cf.depend a ∩ rem = ∅) ::
      decomposeAux cf (rem \ rem.filter (fun a => cf.depend a ∩ rem = ∅)) := by
  rw [decomposeAux_eq]; exact dif_pos hne

/-- Maximalité : tout élément de la couche i+1 a une dépendance dans la couche i.
    C'est la propriété « greedy » de Cartier-Foata : chaque couche prend TOUS les
    éléments sans dépendance restante, donc tout élément restant a été filtré. -/
theorem later_layer_has_dep_in_prev (cf : CartierFoata) :
    ∀ (rem : Finset Letter) (i : ℕ) (hi : i + 1 < (decomposeAux cf rem).length)
      (a : Letter) (ha : a ∈ (decomposeAux cf rem)[i + 1]),
    ∃ b, b ∈ cf.depend a ∧ b ∈ (decomposeAux cf rem)[i] := by
  intro rem
  refine Finset.strongInductionOn rem ?_
  intro rem ih i hi a ha
  by_cases hne : rem.Nonempty
  · set layer := rem.filter (fun x => cf.depend x ∩ rem = ∅) with layer_def
    set rem' := rem \ layer with rem'_def
    have h_cons := decomposeAux_cons cf rem hne
    have h_rem'_ss : rem' ⊂ rem := by
      simpa [layer, rem'] using decomposeAux_layer_ssubset cf rem hne
    have h_len : (decomposeAux cf rem').length + 1 = (decomposeAux cf rem).length := by
      simp [h_cons, ← layer_def, ← rem'_def]
    match i with
    | 0 =>
      have h_rest_pos : 0 < (decomposeAux cf rem').length := by omega
      have hne' : rem'.Nonempty := by
        by_contra h_empty
        push_neg at h_empty
        rw [h_empty, decomposeAux_eq, dif_neg Finset.not_nonempty_empty] at h_rest_pos
        simp at h_rest_pos
      have h_eq_succ : (decomposeAux cf rem)[0 + 1] = (decomposeAux cf rem')[0] := by
        simp only [h_cons, List.getElem_cons_succ, ← layer_def, ← rem'_def]
      rw [h_eq_succ] at ha
      have h_head : (decomposeAux cf rem')[0] =
          rem'.filter (fun x => cf.depend x ∩ rem' = ∅) := by
        simp only [decomposeAux_cons cf rem' hne', List.getElem_cons_zero]
      rw [h_head] at ha
      have ha_rem' : a ∈ rem' := (Finset.mem_filter.mp ha).1
      have ha_rem : a ∈ rem := Finset.sdiff_subset ha_rem'
      have ha_not_layer : a ∉ layer := (Finset.mem_sdiff.mp ha_rem').2
      have h_dep_ne : cf.depend a ∩ rem ≠ ∅ := by
        intro h_empty
        exact ha_not_layer (Finset.mem_filter.mpr ⟨ha_rem, h_empty⟩)
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr h_dep_ne
      have hb_dep : b ∈ cf.depend a := (Finset.mem_inter.mp hb).1
      have hb_rem : b ∈ rem := (Finset.mem_inter.mp hb).2
      have ha_dep_rem'_empty : cf.depend a ∩ rem' = ∅ := (Finset.mem_filter.mp ha).2
      have hb_not_rem' : b ∉ rem' := by
        intro hb_rem'
        have : b ∈ cf.depend a ∩ rem' := Finset.mem_inter.mpr ⟨hb_dep, hb_rem'⟩
        rw [ha_dep_rem'_empty] at this; simp at this
      have hb_layer : b ∈ layer := by
        by_contra hb_not
        exact hb_not_rem' (Finset.mem_sdiff.mpr ⟨hb_rem, hb_not⟩)
      refine ⟨b, hb_dep, ?_⟩
      have h_eq_zero : (decomposeAux cf rem)[0] = layer := by
        simp only [h_cons, List.getElem_cons_zero, ← layer_def]
      rw [h_eq_zero]; exact hb_layer
    | j + 1 =>
      have hi' : j + 1 < (decomposeAux cf rem').length := by omega
      have ha' : a ∈ (decomposeAux cf rem')[j + 1] := by
        have h_eq : (decomposeAux cf rem)[j + 1 + 1] = (decomposeAux cf rem')[j + 1] := by
          simp only [h_cons, List.getElem_cons_succ, ← layer_def, ← rem'_def]
        rwa [h_eq] at ha
      obtain ⟨b, hb_dep, hb_mem⟩ := ih rem' h_rem'_ss j hi' a ha'
      refine ⟨b, hb_dep, ?_⟩
      have h_eq : (decomposeAux cf rem)[j + 1] = (decomposeAux cf rem')[j] := by
        simp only [h_cons, List.getElem_cons_succ, ← layer_def, ← rem'_def]
      rw [h_eq]; exact hb_mem
  · rw [decomposeAux_eq, dif_neg hne] at hi; simp at hi

/-! ### Hauteur = plus longue chaîne de dépendance -/

/-- Chaque couche de `decomposeAux` est non vide.
    Conséquence du caractère greedy : `exists_minimal` fournit toujours
    un élément sans dépendance restante. -/
lemma decomposeAux_layer_nonempty (cf : CartierFoata) :
    ∀ (rem : Finset Letter) (i : ℕ) (hi : i < (decomposeAux cf rem).length),
    ((decomposeAux cf rem)[i]).Nonempty := by
  intro rem
  refine Finset.strongInductionOn rem ?_
  intro rem ih i hi
  by_cases hne : rem.Nonempty
  · set layer := rem.filter (fun x => cf.depend x ∩ rem = ∅) with layer_def
    set rem' := rem \ layer with rem'_def
    have h_cons := decomposeAux_cons cf rem hne
    have h_rem'_ss : rem' ⊂ rem := by
      simpa [layer, rem'] using decomposeAux_layer_ssubset cf rem hne
    match i with
    | 0 =>
      have h_eq : (decomposeAux cf rem)[0] = layer := by
        simp only [h_cons, List.getElem_cons_zero, ← layer_def]
      rw [h_eq]
      obtain ⟨m, hm, h_min⟩ := cf.exists_minimal rem hne
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h_min⟩⟩
    | j + 1 =>
      have h_len : (decomposeAux cf rem').length + 1 = (decomposeAux cf rem).length := by
        simp [h_cons, ← layer_def, ← rem'_def]
      have hi' : j < (decomposeAux cf rem').length := by omega
      have h_eq : (decomposeAux cf rem)[j + 1] = (decomposeAux cf rem')[j] := by
        simp only [h_cons, List.getElem_cons_succ, ← layer_def, ← rem'_def]
      rw [h_eq]
      exact ih rem' h_rem'_ss j hi'
  · rw [decomposeAux_eq, dif_neg hne] at hi; simp at hi

/-- Pour tout élément d'une couche j, il existe une chaîne de dépendance
    de longueur j+1 partant de cet élément et descendant jusqu'à la couche 0. -/
private lemma exists_dep_chain_from_element (cf : CartierFoata) (rem : Finset Letter) :
    ∀ (j : ℕ) (hj : j < (decomposeAux cf rem).length)
    (a : Letter) (ha : a ∈ (decomposeAux cf rem)[j]),
    ∃ chain_tail : List Letter,
      (a :: chain_tail).length = j + 1 ∧
      (a :: chain_tail).IsChain (fun x y => y ∈ cf.depend x) ∧
      (∀ x ∈ a :: chain_tail, x ∈ rem) := by
  intro j
  induction j with
  | zero =>
    intro hj a ha
    exact ⟨[], rfl, List.isChain_singleton a, fun x hx => by
      simp at hx; subst hx
      exact decompose_layers_subset cf ⟨rem⟩ _ (List.getElem_mem hj) ha⟩
  | succ j ih =>
    intro hj a ha
    obtain ⟨b, hb_dep, hb_layer⟩ := later_layer_has_dep_in_prev cf rem j (by omega) a ha
    obtain ⟨tail_b, h_len, h_chain, h_mem⟩ := ih (by omega) b hb_layer
    refine ⟨b :: tail_b, ?_, ?_, ?_⟩
    · simp [List.length_cons] at h_len ⊢; omega
    · exact h_chain.cons_of_ne_nil (List.cons_ne_nil _ _) hb_dep
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact decompose_layers_subset cf ⟨rem⟩ _ (List.getElem_mem hj) ha
      · exact h_mem x hx'

/-- Il existe une chaîne de dépendance de longueur exactement égale à la hauteur.
    Combiné avec `dep_chain_length_le_height` (≤), ceci caractérise la hauteur
    comme la longueur de la plus longue chaîne de dépendance. -/
theorem exists_dep_chain_eq_height (cf : CartierFoata) (rem : Finset Letter) :
    ∃ chain : List Letter,
      chain.length = (decomposeAux cf rem).length ∧
      chain.IsChain (fun a b => b ∈ cf.depend a) ∧
      (∀ a ∈ chain, a ∈ rem) := by
  by_cases h_pos : 0 < (decomposeAux cf rem).length
  · set n := (decomposeAux cf rem).length - 1
    have hn : n < (decomposeAux cf rem).length := by omega
    obtain ⟨a, ha⟩ := decomposeAux_layer_nonempty cf rem n hn
    obtain ⟨tail, h_len, h_chain, h_mem⟩ := exists_dep_chain_from_element cf rem n hn a ha
    exact ⟨a :: tail, by omega, h_chain, h_mem⟩
  · have h_len := Nat.not_lt.mp h_pos
    exact ⟨[], by simp at h_len ⊢; omega, .nil, fun _ h => by simp at h⟩

/-! ### Unicité de la première couche (Phase 1)

    Si une partition `layer ∪ rest = rem` sépare les éléments sans dépendance
    dans `rem` (layer) de ceux avec dépendance (rest), alors `layer` est
    exactement le filtre greedy de `decomposeAux`. -/

/-- La première couche d'une décomposition valide est uniquement déterminée.
    C'est le cœur de l'unicité de Cartier-Foata : les conditions
    partition + ordre-consistance + maximalité forcent la première couche. -/
theorem first_layer_eq_filter (cf : CartierFoata) (rem : Finset Letter)
    (layer rest : Finset Letter)
    (h_union : layer ∪ rest = rem)
    (h_layer_ok : ∀ a ∈ layer, cf.depend a ∩ rem = ∅)
    (h_rest_dep : ∀ a ∈ rest, cf.depend a ∩ rem ≠ ∅) :
    layer = rem.filter (fun a => cf.depend a ∩ rem = ∅) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · intro ha
    exact ⟨h_union ▸ Finset.mem_union_left _ ha, h_layer_ok a ha⟩
  · rintro ⟨ha_rem, ha_no_dep⟩
    rw [← h_union] at ha_rem
    rcases Finset.mem_union.mp ha_rem with ha_layer | ha_rest
    · exact ha_layer
    · exact absurd ha_no_dep (h_rest_dep a ha_rest)

/-! ### Phase 2 — Unicité complète de la décomposition de Cartier-Foata

    Prédicat inductif `ValidFoataLayering` caractérisant les décompositions
    valides, puis preuve que `decomposeAux` est l'unique telle décomposition.
    Réf. : Maarand & Uustalu (NFM 2018, Agda). -/

inductive ValidFoataLayering (cf : CartierFoata) :
    Finset Letter → List (Finset Letter) → Prop
  | nil : ValidFoataLayering cf ∅ []
  | cons {rem : Finset Letter} {layer : Finset Letter} {rest : List (Finset Letter)}
    (h_sub : layer ⊆ rem)
    (h_ne : layer.Nonempty)
    (h_no_dep : ∀ a ∈ layer, cf.depend a ∩ rem = ∅)
    (h_max : ∀ a ∈ rem \ layer, cf.depend a ∩ rem ≠ ∅)
    (h_rest : ValidFoataLayering cf (rem \ layer) rest) :
    ValidFoataLayering cf rem (layer :: rest)

/-- **Mort gardé — résultat de thèse** (unicité de Cartier-Foata, groupe
    Mirsky ; vivant uniquement via `foata_decompose_unique`, lui-même mort
    depuis la suppression des corollaires Trace F7). -/
theorem decomposeAux_satisfies_valid (cf : CartierFoata) :
    ∀ (rem : Finset Letter), ValidFoataLayering cf rem (decomposeAux cf rem) := by
  intro rem
  refine Finset.strongInductionOn rem (fun rem ih => ?_)
  by_cases hne : rem.Nonempty
  · obtain ⟨m, hm, h_min⟩ := cf.exists_minimal rem hne
    have hm_layer : m ∈ rem.filter (fun a => cf.depend a ∩ rem = ∅) :=
      Finset.mem_filter.mpr ⟨hm, h_min⟩
    have h_ss : rem \ rem.filter (fun a => cf.depend a ∩ rem = ∅) ⊂ rem :=
      decomposeAux_layer_ssubset cf rem hne
    rw [decomposeAux_cons cf rem hne]
    exact ValidFoataLayering.cons
      (Finset.filter_subset _ rem)
      ⟨m, hm_layer⟩
      (fun a ha => (Finset.mem_filter.mp ha).2)
      (fun a ha h => (Finset.mem_sdiff.mp ha).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, h⟩))
      (ih _ h_ss)
  · have h_empty := Finset.not_nonempty_iff_eq_empty.mp hne
    subst h_empty
    rw [decomposeAux_eq, dif_neg Finset.not_nonempty_empty]
    exact ValidFoataLayering.nil

/-- **Mort gardé — résultat de thèse** (unicité de Cartier-Foata ; vivant
    uniquement via le corollaire Trace supprimé en F7). -/
theorem foata_decompose_unique (cf : CartierFoata) (rem : Finset Letter)
    (layers : List (Finset Letter))
    (h : ValidFoataLayering cf rem layers) :
    layers = decomposeAux cf rem := by
  induction h with
  | nil => rw [decomposeAux_eq, dif_neg Finset.not_nonempty_empty]
  | @cons rem layer rest h_sub h_ne h_no_dep h_max _ ih =>
    have hne_rem : rem.Nonempty := let ⟨x, hx⟩ := h_ne; ⟨x, h_sub hx⟩
    have h_layer_eq := first_layer_eq_filter cf rem layer (rem \ layer)
      (by ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
          exact ⟨fun h => h.elim (fun hx => h_sub hx) fun ⟨hx, _⟩ => hx,
                 fun hx => if hxl : x ∈ layer then .inl hxl else .inr ⟨hx, hxl⟩⟩)
      h_no_dep h_max
    rw [decomposeAux_cons cf rem hne_rem, ← h_layer_eq, ih]

/-! ### Pont Foata ↔ Mirsky (Phase 2, Partie B)

    `height_eq_max_chain_length` + `layer_is_antichain` = construction
    d'une partition en antichaînes (au sens de `depend`, relation directe
    non transitive) de taille = plus longue chaîne de dépendance.
    La lecture en ordre partiel (clôture transitive) suit car des éléments
    comparables tombent dans des couches distinctes, mais n'est pas formalisée.
    C'est la moitié constructive du théorème de Mirsky (1971).
    La minimalité (toute partition en antichaînes a ≥ longest chain couches)
    n'est pas formalisée ici. -/

theorem height_eq_max_chain_length (cf : CartierFoata) (rem : Finset Letter) :
    (∃ chain : List Letter,
      chain.length = (decomposeAux cf rem).length ∧
      chain.IsChain (fun a b => b ∈ cf.depend a) ∧
      (∀ a ∈ chain, a ∈ rem)) ∧
    (∀ chain : List Letter,
      chain.IsChain (fun a b => b ∈ cf.depend a) →
      (∀ a ∈ chain, a ∈ rem) →
      chain.length ≤ (decomposeAux cf rem).length) :=
  ⟨exists_dep_chain_eq_height cf rem,
   fun chain h_chain h_mem => dep_chain_length_le_decomposeAux cf rem chain h_mem h_chain⟩

theorem layer_is_antichain (cf : CartierFoata) :
    ∀ (rem : Finset Letter) (i : ℕ) (hi : i < (decomposeAux cf rem).length)
      (a b : Letter) (ha : a ∈ (decomposeAux cf rem)[i])
      (hb : b ∈ (decomposeAux cf rem)[i]),
    b ∉ cf.depend a := by
  intro rem
  refine Finset.strongInductionOn rem ?_
  intro rem ih i hi a b ha hb
  by_cases hne : rem.Nonempty
  · set layer := rem.filter (fun x => cf.depend x ∩ rem = ∅) with layer_def
    set rem' := rem \ layer with rem'_def
    have h_cons := decomposeAux_cons cf rem hne
    have h_rem'_ss : rem' ⊂ rem := by
      simpa [layer, rem'] using decomposeAux_layer_ssubset cf rem hne
    match i with
    | 0 =>
      simp only [h_cons, List.getElem_cons_zero, ← layer_def] at ha hb
      rw [layer_def] at ha hb
      intro hb_dep
      have := Finset.mem_inter.mpr ⟨hb_dep, (Finset.mem_filter.mp hb).1⟩
      rw [(Finset.mem_filter.mp ha).2] at this
      simp at this
    | j + 1 =>
      have h_len : (decomposeAux cf rem').length + 1 = (decomposeAux cf rem).length := by
        simp [h_cons, ← layer_def, ← rem'_def]
      have hj : j < (decomposeAux cf rem').length := by omega
      simp only [h_cons, List.getElem_cons_succ, ← layer_def, ← rem'_def] at ha hb
      exact ih rem' h_rem'_ss j hj a b ha hb
  · rw [decomposeAux_eq, dif_neg hne] at hi; simp at hi

/-- Restriction d'une décomposition de Cartier-Foata à un sous-alphabet s.
    Construit via ofIndependence : même graphe de dépendance, alphabet réduit à s. -/
def restrict (cf : CartierFoata) (s : Finset Letter) (hs : s ⊆ cf.indep.alphabet) : CartierFoata :=
  ofIndependence (cf.indep.restrict s hs)

@[simp] lemma restrict_indep_alphabet (cf : CartierFoata) (s : Finset Letter)
    (hs : s ⊆ cf.indep.alphabet) :
    (cf.restrict s hs).indep.alphabet = s := rfl

@[simp] lemma restrict_indep_indep (cf : CartierFoata) (s : Finset Letter)
    (hs : s ⊆ cf.indep.alphabet) :
    (cf.restrict s hs).indep.indep = cf.indep.indep := rfl

/-- Membership dans les cliques du système restreint :
    c ∈ cliques(restrict cf s) ↔ c est une I-clique de cf ET c ⊆ s.
    Fondement de la construction du polynôme de Möbius restreint.
    **Mort gardé — fondation Möbius** (consommé par G3Duality gardé via
    `ofCartierFoata_restrict_coeff_one` voisin ; réservé pour la restriction
    dynamique du regex — ancrage chantier rétroaction-regex). -/
lemma mem_cliques_restrict (cf : CartierFoata) (s : Finset Letter) (hs : s ⊆ cf.indep.alphabet)
    (c : Finset Letter) :
    c ∈ cliques (cf.restrict s hs) ↔ c ∈ cliques cf ∧ c ⊆ s := by
  unfold cliques
  simp only [restrict_indep_alphabet, restrict_indep_indep,
             List.mem_filter, Finset.mem_toList, Finset.mem_powerset, decide_eq_true_eq]
  constructor
  · rintro ⟨hcs, hne, hindep⟩
    exact ⟨⟨hcs.trans hs, hne, hindep⟩, hcs⟩
  · rintro ⟨⟨_, hne, hindep⟩, hcs⟩
    exact ⟨hcs, hne, hindep⟩

end CartierFoata

end TraceMonoid

