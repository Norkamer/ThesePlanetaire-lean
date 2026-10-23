/-
  ThesePlanetaire/FeedbackClass.lean
  Phase 4 (2026-10-01) : classes de rétroaction P / T / D, dérivées de la dynamique sur
  l'historique des transactions (et non stipulées frontière par frontière).

  Développé d'abord en `FeedbackClass_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 4, étape 1b) ; analyse :
  `cache/analyse_classes_parikh_2026-10-01.md`.

  L'objet est un pli `δ : σ → α → σ` sur un historique de lettres `α` (les transactions, comme
  dans le WFA : `gatedWFA`, `planetStep`), avec une indépendance statique DÉCLARÉE `I` — en
  général « empreintes lecture ∪ écriture disjointes » (`DisjointFoot`, critère de Bernstein).
  1. `SemClass δ I : FClass → Prop` [LEAN] :
     - P : `δ` commute partout ; toute lecture finale, linéaire ou non, factorise par l'image de
       Parikh (`isCommutativeUpdate_iff_perm`) ;
     - T : losange pour `I` sans commutation totale ; le pli descend sur M(α, I) et pas plus bas
       (`diamond_iff_descends`, `semClass_T_order_sensitive`) ;
     - D : pas de losange pour `I` : deux lettres déclarées indépendantes interagissent ; aucune
       fonction de la trace M(α, I) ne calcule le pli (`semClass_D_no_descent`).
     La classe existe et est unique (`semClass_exists`, `semClass_unique`). [ANALYSE] D est
     relative à l'empreinte déclarée : une empreinte statique sur-approchée rend tout modèle
     T ; D signale que l'indépendance utile est contextuelle (`regime_switch_D`) ;
  2. transfert macro → transactions (`liftDyn`) : si le pli ne lit que l'effet macro `π a`, la
     classe sur l'historique est majorée par la classe macro, égale si `π` est surjective
     (`liftDyn_class_le`, `liftDyn_class_eq`) ;
  3. ★ `decoupled_not_D`, ★ `single_coord_not_D` : sans couplage entre coordonnées (en
     particulier pour un modèle mono-frontière), jamais D ;
  4. modèles canoniques mono-frontière avec horloge (`Option α`, `none` = top de période) :
     mémoire (`Memory`), gouvernance (`Governance`), classe `profileClass` calculée et
     ★ `profileClass_sound` (les 12 combinaisons) ; ★ `noClock_all_P`, ★ `governed_ge_physics` ;
  5. non-additivité ≠ ordre : ★ `nonlinear_readout_P` (seuil, mélanges), ★ `cascade_closure_P`
     (cascade trophique = fermeture, synergique mais commutative), ★ `cocktail_is_T`
     (`CommutativeClassification.cocktail_dynamics` est une garde : T, non D) ;
  6. ★ `regime_switch_D` : un couplage activé au-delà d'un seuil, seul témoin D (deux frontières).

  Mathlib + `GatedStep` seuls : module bas (importable par `PlanetaryBoundaries`).
-/

import Mathlib.Tactic
import ThesePlanetaire.GatedStep

namespace FeedbackClass

open GatedStep (Diamond TraceQ)
open CommutativeClassification (IsCommutativeUpdate commutative_implies_perm_invariant
  noncommutative_implies_order_sensitive)

variable {σ α β ι : Type*}

/-! ### 1. Classes de rétroaction et sémantique -/

/-- Classe de rétroaction : P (écriture seule, Parikh), T (rétroaction à lecture statique,
    traces), D (indépendance dépendant de l'état). -/
inductive FClass
  | P
  | T
  | D
  deriving DecidableEq, Repr, Fintype

/-- Rang numérique (l'ancien `k` de `parikhClass`). -/
def FClass.toNat : FClass → ℕ
  | .P => 0
  | .T => 1
  | .D => 2

theorem FClass.toNat_injective : Function.Injective FClass.toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Ordre P < T < D ; `⊔` est le max. -/
instance : LinearOrder FClass := LinearOrder.lift' FClass.toNat FClass.toNat_injective

/-- Deux lettres commutent depuis l'état `s`. -/
def CommutesAt (δ : σ → α → σ) (s : σ) (a b : α) : Prop := δ (δ s a) b = δ (δ s b) a

instance [DecidableEq σ] (δ : σ → α → σ) (s : σ) (a b : α) : Decidable (CommutesAt δ s a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- Deux lettres commutent depuis tout état. -/
def Commutes (δ : σ → α → σ) (a b : α) : Prop := ∀ s, CommutesAt δ s a b

/-- Indépendance d'empreintes : empreintes déclarées (lecture ∪ écriture) disjointes. -/
def DisjointFoot (supp : α → Finset ι) (a b : α) : Prop := Disjoint (supp a) (supp b)

instance [DecidableEq ι] (supp : α → Finset ι) (a b : α) : Decidable (DisjointFoot supp a b) :=
  inferInstanceAs (Decidable (Disjoint _ _))

/-- Localité d'empreinte : deux lettres d'empreintes disjointes commutent. -/
def FootLocal (δ : σ → α → σ) (supp : α → Finset ι) : Prop := Diamond δ (DisjointFoot supp)

/-- Classe sémantique du pli `δ` relativement à une indépendance statique déclarée `I`. -/
def SemClass (δ : σ → α → σ) (I : α → α → Prop) : FClass → Prop
  | .P => IsCommutativeUpdate δ
  | .T => Diamond δ I ∧ ¬ IsCommutativeUpdate δ
  | .D => ¬ Diamond δ I

theorem diamond_of_commutative {δ : σ → α → σ} (h : IsCommutativeUpdate δ) (I : α → α → Prop) :
    Diamond δ I :=
  fun s a b _ => h s a b

theorem semClass_exists (δ : σ → α → σ) (I : α → α → Prop) : ∃ c, SemClass δ I c := by
  by_cases hP : IsCommutativeUpdate δ
  · exact ⟨.P, hP⟩
  · by_cases hD : Diamond δ I
    · exact ⟨.T, hD, hP⟩
    · exact ⟨.D, hD⟩

theorem semClass_unique {δ : σ → α → σ} {I : α → α → Prop} {c c' : FClass}
    (h : SemClass δ I c) (h' : SemClass δ I c') : c = c' := by
  cases c <;> cases c' <;> simp only [SemClass] at h h' <;>
    first
    | rfl
    | exact absurd h h'.2
    | exact absurd h' h.2
    | exact absurd (diamond_of_commutative h I) h'
    | exact absurd (diamond_of_commutative h' I) h
    | exact absurd h.1 h'
    | exact absurd h'.1 h

/-- Les classes P et T sont exactement celles à losange pour `I`. -/
theorem semClass_le_T_iff {δ : σ → α → σ} {I : α → α → Prop} {c : FClass}
    (h : SemClass δ I c) : c ≤ .T ↔ Diamond δ I := by
  cases c
  · exact ⟨fun _ => diamond_of_commutative h I, fun _ => by decide⟩
  · exact ⟨fun _ => h.1, fun _ => le_refl _⟩
  · exact ⟨fun hc => absurd hc (by decide), fun hD => absurd hD h⟩

/-! ### 2. Factorisations : Parikh, traces, ni l'un ni l'autre -/

/-- P exact : commutation ⟺ le pli ne dépend que de l'image de Parikh de l'historique. -/
theorem isCommutativeUpdate_iff_perm (δ : σ → α → σ) :
    IsCommutativeUpdate δ ↔
      ∀ s (w₁ w₂ : List α), w₁.Perm w₂ → w₁.foldl δ s = w₂.foldl δ s :=
  ⟨fun h s _ _ hp => commutative_implies_perm_invariant h hp s,
    fun h s a b => h s [a, b] [b, a] (List.Perm.swap b a [])⟩

/-- Classe P : toute lecture finale `g`, linéaire ou non, factorise par Parikh. -/
theorem semClass_P_readout {δ : σ → α → σ} {I : α → α → Prop} (h : SemClass δ I .P)
    (g : σ → β) {w₁ w₂ : List α} (hp : w₁.Perm w₂) (s : σ) :
    g (w₁.foldl δ s) = g (w₂.foldl δ s) :=
  congrArg g (commutative_implies_perm_invariant h hp s)

/-- T exact : le losange pour `I` équivaut à la descente du pli sur M(α, I), depuis tout état. -/
theorem diamond_iff_descends (δ : σ → α → σ) (I : α → α → Prop) :
    Diamond δ I ↔
      ∀ s₀, ∃ F : TraceQ I → σ, ∀ w, F (TraceQ.mk I w) = w.foldl δ s₀ := by
  constructor
  · intro hD s₀
    exact ⟨TraceQ.liftFold δ s₀ hD, fun w => rfl⟩
  · intro h s a b hab
    obtain ⟨F, hF⟩ := h s
    have := congrArg F (TraceQ.mk_swap (I := I) [] [] hab)
    rwa [hF, hF] at this

/-- P ou T : le pli descend sur le monoïde de traces M(α, I). -/
theorem semClass_descends {δ : σ → α → σ} {I : α → α → Prop} {c : FClass}
    (h : SemClass δ I c) (hc : c ≤ .T) (s₀ : σ) :
    ∃ F : TraceQ I → σ, ∀ w, F (TraceQ.mk I w) = w.foldl δ s₀ :=
  (diamond_iff_descends δ I).mp ((semClass_le_T_iff h).mp hc) s₀

/-- T : l'ordre compte (pas de factorisation par Parikh). -/
theorem semClass_T_order_sensitive {δ : σ → α → σ} {I : α → α → Prop}
    (h : SemClass δ I .T) :
    ∃ (s : σ) (w₁ w₂ : List α), w₁.Perm w₂ ∧ w₁.foldl δ s ≠ w₂.foldl δ s :=
  noncommutative_implies_order_sensitive h.2

/-- D : une paire déclarée indépendante ne commute pas, et aucune fonction de la trace
    M(α, I) ne calcule le pli. -/
theorem semClass_D_no_descent {δ : σ → α → σ} {I : α → α → Prop} (h : SemClass δ I .D) :
    (∃ s a b, I a b ∧ δ (δ s a) b ≠ δ (δ s b) a) ∧
      ∃ s₀, ¬ ∃ F : TraceQ I → σ, ∀ w, F (TraceQ.mk I w) = w.foldl δ s₀ := by
  have h' : ¬ Diamond δ I := h
  refine ⟨?_, ?_⟩
  · unfold Diamond at h'
    push Not at h'
    exact h'
  · rw [diamond_iff_descends] at h'
    push Not at h'
    obtain ⟨s₀, hs₀⟩ := h'
    exact ⟨s₀, fun ⟨F, hF⟩ => by obtain ⟨w, hw⟩ := hs₀ F; exact hw (hF w)⟩

/-! ### 3. Transfert macro → transactions -/

/-- Pli sur les transactions qui ne lit que l'effet macro `π a` de chaque transaction. -/
def liftDyn (f : σ → β → σ) (π : α → β) : σ → α → σ := fun s a => f s (π a)

/-- Indépendance relevée : deux transactions sont indépendantes si leurs effets macro le sont. -/
def liftRel (J : β → β → Prop) (π : α → β) (a b : α) : Prop := J (π a) (π b)

theorem liftDyn_commutative {f : σ → β → σ} (π : α → β) (h : IsCommutativeUpdate f) :
    IsCommutativeUpdate (liftDyn f π) :=
  fun s a b => h s (π a) (π b)

theorem liftDyn_diamond {f : σ → β → σ} {J : β → β → Prop} (π : α → β) (h : Diamond f J) :
    Diamond (liftDyn f π) (liftRel J π) :=
  fun s a b hab => h s (π a) (π b) hab

theorem liftDyn_commutative_iff {f : σ → β → σ} {π : α → β} (hπ : Function.Surjective π) :
    IsCommutativeUpdate (liftDyn f π) ↔ IsCommutativeUpdate f := by
  refine ⟨fun h s x y => ?_, liftDyn_commutative π⟩
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  exact h s a b

theorem liftDyn_diamond_iff {f : σ → β → σ} {J : β → β → Prop} {π : α → β}
    (hπ : Function.Surjective π) : Diamond (liftDyn f π) (liftRel J π) ↔ Diamond f J := by
  refine ⟨fun h s x y hxy => ?_, liftDyn_diamond π⟩
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  exact h s a b hxy

/-- La classe sur l'historique est majorée par la classe macro. -/
theorem liftDyn_class_le {f : σ → β → σ} {J : β → β → Prop} {π : α → β} {c c' : FClass}
    (hm : SemClass f J c) (ht : SemClass (liftDyn f π) (liftRel J π) c') : c' ≤ c := by
  cases c
  · exact le_of_eq (semClass_unique ht (liftDyn_commutative π hm))
  · exact (semClass_le_T_iff ht).mpr (liftDyn_diamond π hm.1)
  · cases c' <;> decide

/-- Égalité si toute lettre macro est l'effet d'une transaction. -/
theorem liftDyn_class_eq {f : σ → β → σ} {J : β → β → Prop} {π : α → β}
    (hπ : Function.Surjective π) {c c' : FClass} (hm : SemClass f J c)
    (ht : SemClass (liftDyn f π) (liftRel J π) c') : c' = c := by
  refine semClass_unique ht ?_
  cases c
  · exact (liftDyn_commutative_iff hπ).mpr hm
  · exact ⟨(liftDyn_diamond_iff hπ).mpr hm.1, fun h => hm.2 ((liftDyn_commutative_iff hπ).mp h)⟩
  · exact fun h => hm ((liftDyn_diamond_iff hπ).mp h)

/-! ### 4. Sans couplage, jamais D -/

/-- Pli découplé : chaque lettre agit coordonnée par coordonnée sur son empreinte, chaque
    coordonnée n'étant lue que par sa propre mise à jour. -/
def decoupled [DecidableEq ι] {τ : Type*} (supp : α → Finset ι) (f : ι → α → τ → τ) :
    (ι → τ) → α → (ι → τ) :=
  fun s a i => if i ∈ supp a then f i a (s i) else s i

/-- ★ Sans couplage entre coordonnées, deux lettres d'empreintes disjointes commutent. -/
theorem decoupled_not_D [DecidableEq ι] {τ : Type*} (supp : α → Finset ι) (f : ι → α → τ → τ) :
    FootLocal (decoupled supp f) supp ∧ ¬ SemClass (decoupled supp f) (DisjointFoot supp) .D := by
  have hL : FootLocal (decoupled supp f) supp := by
    intro s a b hab
    funext i
    simp only [decoupled]
    by_cases ha : i ∈ supp a
    · have hb : i ∉ supp b := Finset.disjoint_left.mp hab ha
      simp [ha, hb]
    · by_cases hb : i ∈ supp b <;> simp [ha, hb]
  exact ⟨hL, fun h => h hL⟩

/-- ★ Mono-coordonnée : si une lettre d'empreinte vide est l'identité, deux lettres
    d'empreintes disjointes commutent ; un modèle mono-frontière n'est jamais D. -/
theorem single_coord_not_D [Subsingleton ι] {δ : σ → α → σ} {supp : α → Finset ι}
    (hid : ∀ a, supp a = ∅ → ∀ s, δ s a = s) :
    FootLocal δ supp ∧ ¬ SemClass δ (DisjointFoot supp) .D := by
  have hL : FootLocal δ supp := by
    intro s a b hab
    by_cases ha : supp a = ∅
    · rw [hid a ha, hid a ha]
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr ha
      have hb : supp b = ∅ := Finset.eq_empty_of_forall_notMem fun y hy =>
        Finset.disjoint_left.mp hab hx (Subsingleton.elim x y ▸ hy)
      rw [hid b hb, hid b hb]
  exact ⟨hL, fun h => h hL⟩

/-! ### 5. Modèles canoniques mono-frontière : horloge × mémoire × gouvernance -/

/-- Mémoire de la variable de contrôle (calibration, statut B). -/
inductive Memory
  /-- accumulation sans dissipation : le top de période est l'identité -/
  | stock
  /-- dissipation ou régénération plafonnée : le top retire `r` à la charge -/
  | regen
  /-- flux par période : le top remet la charge à zéro -/
  | flow
  deriving DecidableEq, Repr, Fintype

/-- Gouvernance de la frontière. -/
inductive Governance
  /-- aucune garde : l'environnement est en écriture seule -/
  | free
  /-- garde « premier arrivé » : une émission n'est admise que si la charge reste ≤ `cap` -/
  | gated
  deriving DecidableEq, Repr, Fintype

/-- Classe calculée : physique (horloge × mémoire) ⊔ gouvernance. -/
def profileClass (clock : Bool) (mem : Memory) (gov : Governance) : FClass :=
  (if clock ∧ mem ≠ .stock then .T else .P) ⊔ (if gov = .gated then .T else .P)

/-- Effet du top de période sur la charge `L`. -/
def tickOp : Memory → ℕ → ℕ → ℕ
  | .stock, _, L => L
  | .regen, r, L => L - r
  | .flow, _, _ => 0

/-- Effet d'une émission `x` sur la charge `L`. -/
def emitOp : Governance → ℕ → ℕ → ℕ → ℕ
  | .free, _, x, L => L + x
  | .gated, cap, x, L => if L + x ≤ cap then L + x else L

/-- Pas canonique sur l'historique avec horloge : `some a` est la transaction `a` (émission
    `e a`), `none` le top de période, inerte sans horloge. -/
def canonStep (clock : Bool) (mem : Memory) (gov : Governance) (e : α → ℕ) (cap r : ℕ) :
    ℕ → Option α → ℕ
  | L, none => if clock then tickOp mem r L else L
  | L, some a => emitOp gov cap (e a) L

/-- Empreinte mono-coordonnée : toute lettre touche l'unique variable de contrôle. -/
def canonSupp : Option α → Finset Unit := fun _ => Finset.univ

/-- Non-dégénérescence : régénération effective, et deux émissions rivales de tailles
    distinctes, chacune admissible seule mais pas ensemble. -/
def Nondeg (e : α → ℕ) (cap r : ℕ) : Prop :=
  0 < r ∧ ∃ a b, e a ≤ cap ∧ e b ≤ cap ∧ cap < e a + e b ∧ e a ≠ e b

theorem canon_footLocal (clock : Bool) (mem : Memory) (gov : Governance) (e : α → ℕ)
    (cap r : ℕ) : FootLocal (canonStep clock mem gov e cap r) canonSupp :=
  (single_coord_not_D (fun _ h => absurd h Finset.univ_nonempty.ne_empty)).1

/-- Sans horloge, ou avec un stock pur, l'environnement libre est en écriture seule. -/
theorem canon_commutative {clock : Bool} {mem : Memory} (h : clock = false ∨ mem = .stock)
    (e : α → ℕ) (cap r : ℕ) : IsCommutativeUpdate (canonStep clock mem .free e cap r) := by
  intro L x y
  rcases h with rfl | rfl <;> cases x <;> cases y <;>
    simp only [canonStep, tickOp, emitOp, Bool.false_eq_true, if_false, ite_self] <;> omega

/-- La garde rend l'ordre décisif : le premier servi épuise la marge. -/
theorem canon_gated_noncomm {clock : Bool} {mem : Memory} {e : α → ℕ} {cap r : ℕ}
    (h : ∃ a b, e a ≤ cap ∧ e b ≤ cap ∧ cap < e a + e b ∧ e a ≠ e b) :
    ¬ IsCommutativeUpdate (canonStep clock mem .gated e cap r) := by
  obtain ⟨a, b, ha, hb, hab, hne⟩ := h
  intro hc
  have := hc 0 (some a) (some b)
  simp only [canonStep, emitOp] at this
  split_ifs at this <;> omega

/-- Avec horloge, une mémoire non pure (régénération, flux) ne commute pas avec les
    émissions : la classe devient « Parikh par période ». -/
theorem canon_tick_noncomm {mem : Memory} (hm : mem ≠ .stock) {gov : Governance} {e : α → ℕ}
    {cap r : ℕ} (hnd : Nondeg e cap r) :
    ¬ IsCommutativeUpdate (canonStep true mem gov e cap r) := by
  obtain ⟨hr, a, b, ha, hb, hab, -⟩ := hnd
  intro hc
  have := hc 0 none (some a)
  cases mem
  · exact hm rfl
  all_goals
    cases gov <;> simp only [canonStep, tickOp, emitOp, if_true] at this <;>
      (try split_ifs at this) <;> omega

/-- ★ Classe calculée = classe sémantique, pour les 12 combinaisons. -/
theorem profileClass_sound (clock : Bool) (mem : Memory) (gov : Governance) {e : α → ℕ}
    {cap r : ℕ} (hnd : Nondeg e cap r) :
    SemClass (canonStep clock mem gov e cap r) (DisjointFoot canonSupp)
      (profileClass clock mem gov) := by
  have hL := canon_footLocal clock mem gov e cap r
  cases clock <;> cases mem <;> cases gov <;>
    first
    | exact canon_commutative (Or.inl rfl) e cap r
    | exact canon_commutative (Or.inr rfl) e cap r
    | exact ⟨hL, canon_gated_noncomm hnd.2⟩
    | exact ⟨hL, canon_tick_noncomm (by decide) hnd⟩

/-- ★ Sans horloge, toute physique libre est P : seuils, synergies et fermetures restent des
    fonctions du cumul. -/
theorem noClock_all_P (mem : Memory) (e : α → ℕ) (cap r : ℕ) (I : Option α → Option α → Prop) :
    profileClass false mem .free = .P ∧ SemClass (canonStep false mem .free e cap r) I .P :=
  ⟨by cases mem <;> rfl, canon_commutative (Or.inl rfl) e cap r⟩

/-- ★ Garder une frontière n'abaisse jamais sa classe. -/
theorem governed_ge_physics :
    ∀ clock mem, profileClass clock mem .free ≤ profileClass clock mem .gated := by
  decide

/-- Un modèle mono-frontière n'est jamais D. -/
theorem profileClass_le_T : ∀ clock mem gov, profileClass clock mem gov ≤ .T := by
  decide

theorem profileClass_eq_P_iff : ∀ clock mem gov,
    profileClass clock mem gov = .P ↔ (clock = false ∨ mem = .stock) ∧ gov = .free := by
  decide

/-! ### 6. Non-additivité ≠ dépendance à l'ordre -/

/-- Mélange : chaque transaction ajoute un vecteur de charges (écriture seule). -/
def mixStep (em : α → ι → ℕ) (s : ι → ℕ) (a : α) : ι → ℕ := s + em a

/-- Indicatrice de dépassement du seuil `θ`. -/
def threshold (θ L : ℕ) : ℕ := if θ ≤ L then 1 else 0

/-- ★ Une lecture finale non linéaire reste P : seuil sur le cumul, addition des
    concentrations (Loewe) suivie d'une courbe dose-réponse, action indépendante (Bliss) —
    toutes fonctions du vecteur de charges final. Le seuil n'est pas additif, l'historique
    reste sans ordre. -/
theorem nonlinear_readout_P (em : α → ι → ℕ) (I : α → α → Prop) :
    SemClass (mixStep em) I .P ∧
    (∀ (g : (ι → ℕ) → β) (s₀ : ι → ℕ) {w₁ w₂ : List α}, w₁.Perm w₂ →
        g (w₁.foldl (mixStep em) s₀) = g (w₂.foldl (mixStep em) s₀)) ∧
    threshold 2 (1 + 1) ≠ threshold 2 1 + threshold 2 1 := by
  have hP : SemClass (mixStep em) I .P := fun s a b => add_right_comm s (em a) (em b)
  exact ⟨hP, fun g s₀ _ _ hp => semClass_P_readout hP g hp s₀, by decide⟩

/-- Cascade de fermeture : une perte `ins a` déclenche la fermeture `c`. -/
def closureStep [SemilatticeSup β] (c : ClosureOperator β) (ins : α → β) (s : β) (a : α) : β :=
  c (s ⊔ ins a)

/-- Toute cascade de fermeture est commutative (plus petit point fixe, Knaster–Tarski). -/
theorem closureStep_commutative [SemilatticeSup β] (c : ClosureOperator β) (ins : α → β) :
    IsCommutativeUpdate (closureStep c ins) := by
  intro s a b
  simp only [closureStep, ClosureOperator.closure_sup_closure_left, sup_right_comm]

namespace FoodWeb

/-- Proies : 0 et 1 basales, 2 mange 0 et 1, 3 mange 2. -/
def prey (x : Fin 4) : Finset (Fin 4) :=
  if x = 2 then {0, 1} else if x = 3 then {2} else ∅

/-- Un consommateur dont toutes les proies ont disparu disparaît. -/
def starve (s : Finset (Fin 4)) : Finset (Fin 4) :=
  s ∪ Finset.univ.filter (fun x => (prey x).Nonempty ∧ prey x ⊆ s)

/-- Extinctions secondaires (trois tours suffisent pour ce réseau). -/
def cascade (s : Finset (Fin 4)) : Finset (Fin 4) := starve (starve (starve s))

theorem starve_mono : Monotone starve := by
  intro s t h x hx
  simp only [starve, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with hx | ⟨hn, hp⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨hn, hp.trans h⟩

theorem le_starve (s : Finset (Fin 4)) : s ≤ starve s := Finset.subset_union_left

/-- La cascade trophique est un opérateur de fermeture. -/
def cascadeClosure : ClosureOperator (Finset (Fin 4)) where
  toFun := cascade
  monotone' := starve_mono.comp (starve_mono.comp starve_mono)
  le_closure' s := (le_starve s).trans ((le_starve _).trans (le_starve _))
  idempotent' := by decide

end FoodWeb

open FoodWeb in
/-- ★ Cascade trophique topologique : synergique (perdre 0 ou 1 seul ne déclenche rien, les
    deux ensemble éteignent tout le réseau) mais commutative — classe P. -/
theorem cascade_closure_P (I : Fin 4 → Fin 4 → Prop) :
    SemClass (closureStep cascadeClosure (fun a => {a})) I .P ∧
    cascade {0} ∪ cascade {1} = {0, 1} ∧ cascade {0, 1} = Finset.univ :=
  ⟨closureStep_commutative _ _, by decide, by decide⟩

open CommutativeClassification (cocktail_dynamics) in
/-- Empreinte lecture ∪ écriture du cocktail : la substance 1 lit la présence de 0. -/
def cocktailSupp (x : Fin 3) : Finset (Fin 3) := if x = 1 then {0, 1} else {x}

open CommutativeClassification (cocktail_dynamics cocktail_is_noncommutative) in
/-- ★ Le cocktail du corpus est une GARDE (la substance 1 est bloquée si 0 est présente) :
    avec son empreinte lecture ∪ écriture, il est T, non D. Il n'est D que pour l'empreinte
    d'écriture seule, qui ignore la lecture de 0. -/
theorem cocktail_is_T :
    SemClass cocktail_dynamics (DisjointFoot cocktailSupp) .T ∧
    SemClass cocktail_dynamics (DisjointFoot (fun x : Fin 3 => ({x} : Finset (Fin 3)))) .D := by
  refine ⟨⟨?_, cocktail_is_noncommutative⟩, ?_⟩
  · show ∀ s a b, Disjoint (cocktailSupp a) (cocktailSupp b) → _
    decide
  · intro h
    have := h ∅ 0 1 (by decide)
    revert this
    decide

/-! ### 7. Un témoin D : couplage activé au-delà d'un seuil -/

namespace RegimeSwitch

/-- Deux frontières ; la lettre 0 émet 1 sur la frontière 0 ; la lettre 1 émet sur la
    frontière 1 : 1 en régime sûr, 2 au-delà du seuil 2 de la frontière 0. -/
def step (s : ℕ × ℕ) (x : Fin 2) : ℕ × ℕ :=
  if x = 0 then (s.1 + 1, s.2) else (s.1, s.2 + if s.1 < 2 then 1 else 2)

/-- Empreinte d'émission. -/
def emitSupp (x : Fin 2) : Finset (Fin 2) := {x}

/-- Empreinte statique sur-approchée : la lettre 1 lit la frontière 0. -/
def coarseSupp (x : Fin 2) : Finset (Fin 2) := if x = 0 then {0} else {0, 1}

end RegimeSwitch

open RegimeSwitch in
/-- ★ Témoin D : pour l'empreinte d'émission, les deux lettres sont indépendantes en régime
    sûr et dépendantes près du seuil — indépendance contextuelle. L'empreinte statique
    sur-approchée rend le modèle T, au prix de ne jamais les déclarer indépendantes. -/
theorem regime_switch_D :
    SemClass step (DisjointFoot emitSupp) .D ∧
    CommutesAt step (0, 0) 0 1 ∧ ¬ CommutesAt step (1, 0) 0 1 ∧
    SemClass step (DisjointFoot coarseSupp) .T := by
  have h10 : ¬ CommutesAt step (1, 0) 0 1 := by decide
  refine ⟨fun h => h10 (h (1, 0) 0 1 (by decide)), by decide, h10, ?_, fun h => h10 (h _ _ _)⟩
  intro s x y hxy
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd hxy (by decide)
  · exact absurd hxy (by decide)
  · rfl

end FeedbackClass
