/-
  MonnaiesEndogene/Dioid.lean
  Typeclass Dioïde et propriétés (Ch.6)

  Dioïde = semi-anneau idempotent (Gondran & Minoux 2008).
  ⊕ idempotent → ordre partiel canonique: a ≤ b ↔ a ⊕ b = b.
-/

import Mathlib.Algebra.Ring.Defs

/-- Dioïde: semi-anneau idempotent pour l'addition.
    L'idempotence de ⊕ induit l'ordre canonique : a ≤ b ↔ a ⊕ b = b. -/
class Dioid (α : Type*) extends Semiring α where
  add_idem : ∀ a : α, a + a = a

namespace Dioid

variable {α : Type*} [Dioid α]

/-- Ordre canonique du dioïde : a ≤ b ↔ a + b = b.
    Nommé `dle` (dioid-le) pour éviter le conflit avec `LE.le` de Lean. -/
def dle (a b : α) : Prop := a + b = b

/-- Réflexivité de l'ordre canonique (conséquence de l'idempotence). -/
theorem dle_refl (a : α) : dle a a := by
  dsimp [dle]; exact Dioid.add_idem a

/-- Transitivité. -/
theorem dle_trans {a b c : α} (hab : dle a b) (hbc : dle b c) : dle a c := by
  dsimp [dle] at hab hbc ⊢
  calc
    a + c = a + (b + c) := by rw [hbc]
    _ = (a + b) + c := by rw [add_assoc]
    _ = b + c := by rw [hab]
    _ = c := by rw [hbc]

/-- Antisymétrie. -/
theorem dle_antisymm {a b : α} (hab : dle a b) (hba : dle b a) : a = b := by
  dsimp [dle] at hab hba
  calc
    a = b + a := Eq.symm hba
    _ = a + b := add_comm _ _
    _ = b := hab

/-! ### Lemmes de compatibilité pour l'ordre canonique -/

/-- L'addition majore son argument droit : a ≤ a + b. -/
theorem dle_add_right (a b : α) : dle a (a + b) := by
  dsimp [dle]
  calc
    a + (a + b) = (a + a) + b := by rw [add_assoc]
    _ = a + b := by rw [add_idem]

/-- L'addition majore son argument gauche : b ≤ a + b. -/
theorem dle_add_left (a b : α) : dle b (a + b) := by
  dsimp [dle]
  calc
    b + (a + b) = b + (b + a) := by rw [add_comm a b]
    _ = (b + b) + a := by rw [add_assoc]
    _ = b + a := by rw [add_idem]
    _ = a + b := by rw [add_comm b a]

/-- Zéro est l'élément minimal : 0 ≤ a. -/
theorem dle_zero (a : α) : dle (0 : α) a := by
  dsimp [dle]; simp

/-- Dans un dioïde où 1 est l'élément maximal (∀x, x ≤ 1),
    la multiplication à droite réduit : a * b ≤ a. -/
theorem dle_mul_right (a b : α) (h_one_top : ∀ x : α, dle x (1 : α)) : dle (a * b) a := by
  have hb : dle b (1 : α) := h_one_top b
  dsimp [dle] at hb ⊢
  calc
    (a * b) + a = (a * b) + (a * (1 : α)) := by rw [mul_one]
    _ = a * (b + (1 : α)) := by rw [left_distrib]
    _ = a * (1 : α) := by rw [hb]
    _ = a := by rw [mul_one]

/-- Dans un dioïde où 1 est l'élément maximal,
    la multiplication à gauche réduit : a * b ≤ b. -/
theorem dle_mul_left (a b : α) (h_one_top : ∀ x : α, dle x (1 : α)) : dle (a * b) b := by
  have ha : dle a (1 : α) := h_one_top a
  dsimp [dle] at ha ⊢
  calc
    (a * b) + b = (a * b) + ((1 : α) * b) := by rw [one_mul]
    _ = (a + (1 : α)) * b := by rw [right_distrib]
    _ = (1 : α) * b := by rw [ha]
    _ = b := by rw [one_mul]

/-- a ≤ c → b ≤ c → a + b ≤ c (ordre canonique). -/
theorem dle_add_add {a b c : α} (ha : dle a c) (hb : dle b c) : dle (a + b) c := by
  dsimp [dle] at ha hb ⊢
  rw [add_assoc, hb, ha]

/-! ### Monotonie de la multiplication -/

/-- Monotonie à gauche : a ≤ b → c*a ≤ c*b. -/
theorem dle_mul_left_mono {a b c : α} (h : dle a b) : dle (c * a) (c * b) := by
  dsimp [dle] at h ⊢
  rw [← left_distrib, h]

/-- Monotonie à droite : a ≤ b → a*c ≤ b*c. -/
theorem dle_mul_right_mono {a b c : α} (h : dle a b) : dle (a * c) (b * c) := by
  dsimp [dle] at h ⊢
  rw [← right_distrib, h]

end Dioid

/-! ### Kleene Dioid (algèbre de Kleene)

  Algèbre de Kleene = dioïde avec étoile (star) satisfaisant les axiomes
  de point fixe de Kozen (1994). -/

class KleeneDioid (α : Type*) extends Dioid α where
  star : α → α
  star_one_add_self_mul_star : ∀ a, Dioid.dle (1 + a * star a) (star a)
  star_one_add_star_mul_self : ∀ a, Dioid.dle (1 + star a * a) (star a)
  star_induction_right : ∀ a x, Dioid.dle (a * x) x → Dioid.dle (star a * x) x
  star_induction_left  : ∀ a x, Dioid.dle (x * a) x → Dioid.dle (x * star a) x

namespace KleeneDioid

variable {α : Type*} [KleeneDioid α]

/-- 1 ≤ star a. -/
theorem one_le_star (a : α) : Dioid.dle (1 : α) (star a) := by
  have h := star_one_add_self_mul_star a
  -- h: dle (1 + a*star a) (star a)
  have h1 : Dioid.dle (1 : α) (1 + a * star a) := Dioid.dle_add_right _ _
  exact Dioid.dle_trans h1 h

/-- a ≤ star a. -/
theorem a_le_star (a : α) : Dioid.dle a (star a) := by
  have h_one : Dioid.dle (1 : α) (star a) := one_le_star a
  have h_mul : Dioid.dle (a * (star a)) (star a) := by
    have h' := star_one_add_self_mul_star a
    -- h': dle (1 + a*star a) (star a)
    -- So dle (a*star a) (star a)
    have h_add : Dioid.dle (a * star a) (1 + a * star a) := Dioid.dle_add_left _ _
    exact Dioid.dle_trans h_add h'
  have ha : Dioid.dle a (a * star a) := by
    -- a = a*1 ≤ a*star a since 1 ≤ star a
    dsimp [Dioid.dle]
    calc
      a + a * star a = a * 1 + a * star a := by rw [mul_one]
      _ = a * (1 + star a) := by rw [left_distrib]
      _ = a * star a := by
        -- 1 + star a = star a, since 1 ≤ star a
        rw [Dioid.dle] at h_one
        rw [h_one]
  exact Dioid.dle_trans ha h_mul

/-- Lemme combiné : si 1 ≤ x et a*x ≤ x, alors star a ≤ x. -/
theorem dle_induction_right (a x : α) (h_one : Dioid.dle (1 : α) x) (h_mul : Dioid.dle (a * x) x) :
    Dioid.dle (star a) x := by
  have h_star_mul : Dioid.dle (star a * x) x := star_induction_right a x h_mul
  -- star a = star a * 1 ≤ star a * x ≤ x
  have h_star_le_mul : Dioid.dle (star a) (star a * x) := by
    -- star a = star a * 1 ≤ star a * x (since 1 ≤ x)
    have : Dioid.dle (star a * 1) (star a * x) := Dioid.dle_mul_left_mono h_one
    rw [mul_one] at this; exact this
  exact Dioid.dle_trans h_star_le_mul h_star_mul

/-- Lemme combiné dual : si 1 ≤ x et x*a ≤ x, alors star a ≤ x. -/
theorem dle_induction_left (a x : α) (h_one : Dioid.dle (1 : α) x) (h_mul : Dioid.dle (x * a) x) :
    Dioid.dle (star a) x := by
  have h_mul_star : Dioid.dle (x * star a) x := star_induction_left a x h_mul
  -- star a = 1 * star a ≤ x * star a ≤ x
  have h_star_le_mul : Dioid.dle (star a) (x * star a) := by
    have : Dioid.dle (1 * star a) (x * star a) := Dioid.dle_mul_right_mono h_one
    rw [one_mul] at this; exact this
  exact Dioid.dle_trans h_star_le_mul h_mul_star

/-! ### Théorèmes star 0-sorry -/

/-- star a * star a ≤ star a. -/
theorem star_mul_star_le_star (a : α) : Dioid.dle (star a * star a) (star a) := by
  have h_mul : Dioid.dle (a * star a) (star a) := by
    have h_add : Dioid.dle (a * star a) (1 + a * star a) := Dioid.dle_add_left _ _
    have h_ax := star_one_add_self_mul_star a
    exact Dioid.dle_trans h_add h_ax
  exact star_induction_right a (star a) h_mul

/-- star a = 1 + a * star a. -/
theorem star_eq_one_add_self_mul_star (a : α) : star a = 1 + a * star a := by
  apply Dioid.dle_antisymm
  · -- star a ≤ 1 + a * star a
    apply dle_induction_right a (1 + a * star a)
    · -- 1 ≤ 1 + a * star a
      exact Dioid.dle_add_right _ _
    · -- a * (1 + a*star a) ≤ 1 + a*star a
      have haσ_le_σ : Dioid.dle (a * star a) (star a) := by
        have h_aσ_le_1aσ : Dioid.dle (a * star a) (1 + a * star a) := Dioid.dle_add_left _ _
        exact Dioid.dle_trans h_aσ_le_1aσ (star_one_add_self_mul_star a)
      -- a ≤ a * star a (from 1 ≤ star a, multiply by a)
      have ha_le_aσ : Dioid.dle a (a * star a) := by
        have : Dioid.dle (a * (1 : α)) (a * star a) := Dioid.dle_mul_left_mono (one_le_star a)
        rw [mul_one] at this; exact this
      -- a * (a * star a) ≤ a * star a
      have ha_aσ_le_aσ : Dioid.dle (a * (a * star a)) (a * star a) :=
        Dioid.dle_mul_left_mono haσ_le_σ
      -- a + a*(a*star a) ≤ a*star a + a*star a = a*star a ≤ 1 + a*star a
      have hsum_le_aσ : Dioid.dle (a + a * (a * star a)) (a * star a) :=
        Dioid.dle_add_add ha_le_aσ ha_aσ_le_aσ
      have haσ_le_one_aσ : Dioid.dle (a * star a) (1 + a * star a) := Dioid.dle_add_left _ _
      -- Combine: a*(1 + a*star a) = a + a*(a*star a) ≤ a*star a ≤ 1 + a*star a
      have h1 : Dioid.dle (a * (1 + a * star a)) (a + a * (a * star a)) := by
        rw [left_distrib, mul_one]; exact Dioid.dle_refl _
      have h2 : Dioid.dle (a + a * (a * star a)) (a * star a) := hsum_le_aσ
      have h3 : Dioid.dle (a * star a) (1 + a * star a) := haσ_le_one_aσ
      exact Dioid.dle_trans (Dioid.dle_trans h1 h2) h3
  · -- 1 + a*star a ≤ star a : axiom
    exact star_one_add_self_mul_star a

/-- star a = 1 + star a * a. -/
theorem star_eq_one_add_star_mul_self (a : α) : star a = 1 + star a * a := by
  apply Dioid.dle_antisymm
  · -- star a ≤ 1 + star a * a
    apply dle_induction_left a (1 + star a * a)
    · -- 1 ≤ 1 + star a * a
      exact Dioid.dle_add_right _ _
    · -- (1 + star a * a) * a ≤ 1 + star a * a
      have hσa_le_σ : Dioid.dle (star a * a) (star a) := by
        have h_σa_le_1σa : Dioid.dle (star a * a) (1 + star a * a) := Dioid.dle_add_left _ _
        exact Dioid.dle_trans h_σa_le_1σa (star_one_add_star_mul_self a)
      have ha_le_σa : Dioid.dle a (star a * a) := by
        have : Dioid.dle ((1 : α) * a) (star a * a) := Dioid.dle_mul_right_mono (one_le_star a)
        rw [one_mul] at this; exact this
      have hσa_a_le_σa : Dioid.dle ((star a * a) * a) (star a * a) :=
        Dioid.dle_mul_right_mono hσa_le_σ
      have hsum : Dioid.dle (a + (star a * a) * a) (star a * a) :=
        Dioid.dle_add_add ha_le_σa hσa_a_le_σa
      have hσa_le_one_σa : Dioid.dle (star a * a) (1 + star a * a) := Dioid.dle_add_left _ _
      have h1 : Dioid.dle ((1 + star a * a) * a) (a + (star a * a) * a) := by
        rw [right_distrib, one_mul]; exact Dioid.dle_refl _
      have h2 : Dioid.dle (a + (star a * a) * a) (star a * a) := hsum
      exact Dioid.dle_trans (Dioid.dle_trans h1 h2) hσa_le_one_σa
  · -- 1 + star a * a ≤ star a : axiom
    exact star_one_add_star_mul_self a

/-- star est monotone : a ≤ b → star a ≤ star b. -/
theorem star_monotone {a b : α} (h : Dioid.dle a b) : Dioid.dle (star a) (star b) := by
  apply dle_induction_right a (star b)
  · -- 1 ≤ star b
    exact one_le_star b
  · -- a * star b ≤ star b
    have ha_le_b : Dioid.dle (a * star b) (b * star b) := Dioid.dle_mul_right_mono h
    have hb_σ_le_σ : Dioid.dle (b * star b) (star b) := by
      have h_add : Dioid.dle (b * star b) (1 + b * star b) := Dioid.dle_add_left _ _
      exact Dioid.dle_trans h_add (star_one_add_self_mul_star b)
    exact Dioid.dle_trans ha_le_b hb_σ_le_σ

/-- star est idempotent : star (star a) = star a. -/
theorem star_idem (a : α) : star (star a) = star a := by
  apply Dioid.dle_antisymm
  · -- star (star a) ≤ star a
    apply dle_induction_right (star a) (star a)
    · -- 1 ≤ star a
      exact one_le_star a
    · -- star a * star a ≤ star a
      exact star_mul_star_le_star a
  · -- star a ≤ star (star a)
    have h_one : Dioid.dle (1 : α) (star (star a)) := one_le_star (star a)
    -- a * star (star a) ≤ star a * star (star a) ≤ star (star a)
    have ha_le_sa : Dioid.dle a (star a) := a_le_star a
    have h_mul : Dioid.dle (a * star (star a)) (star a * star (star a)) :=
      Dioid.dle_mul_right_mono ha_le_sa
    have h_sa_star : Dioid.dle (star a * star (star a)) (star (star a)) := by
      have h_add : Dioid.dle (star a * star (star a)) (1 + star a * star (star a)) :=
        Dioid.dle_add_left _ _
      exact Dioid.dle_trans h_add (star_one_add_self_mul_star (star a))
    have ha_star : Dioid.dle (a * star (star a)) (star (star a)) :=
      Dioid.dle_trans h_mul h_sa_star
    exact dle_induction_right a (star (star a)) h_one ha_star

/-- Chaque puissance a^n est bornée par star a. -/
theorem pow_le_star (a : α) (n : ℕ) : Dioid.dle (a ^ n) (star a) := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact one_le_star a
  | succ n ih =>
      rw [pow_succ' a n]
      have h_mul : Dioid.dle (a * a ^ n) (a * star a) := Dioid.dle_mul_left_mono ih
      have h_aσ_le_σ : Dioid.dle (a * star a) (star a) := by
        have h_add : Dioid.dle (a * star a) (1 + a * star a) := Dioid.dle_add_left _ _
        exact Dioid.dle_trans h_add (star_one_add_self_mul_star a)
      exact Dioid.dle_trans h_mul h_aσ_le_σ

/-- star 0 = 1. -/
theorem star_zero : star (0 : α) = 1 := by
  have h0 : Dioid.dle (star (0 : α)) (1 : α) := by
    apply dle_induction_right (0 : α) 1
    · exact Dioid.dle_refl (1 : α)
    · rw [zero_mul]; dsimp [Dioid.dle]; exact zero_add 1
  have h1 : Dioid.dle (1 : α) (star (0 : α)) := one_le_star _
  exact Dioid.dle_antisymm h0 h1

/-- star 1 = 1. -/
theorem star_one : star (1 : α) = 1 := by
  have h0 : Dioid.dle (star (1 : α)) (1 : α) := by
    apply dle_induction_right (1 : α) 1
    · exact Dioid.dle_refl (1 : α)
    · rw [one_mul]; exact Dioid.dle_refl (1 : α)
  have h1 : Dioid.dle (1 : α) (star (1 : α)) := one_le_star _
  exact Dioid.dle_antisymm h0 h1

/-- star a = 1 ssi a ≤ 1. -/
theorem star_eq_one_iff (a : α) : star a = 1 ↔ Dioid.dle a 1 := by
  constructor
  · intro h
    have : Dioid.dle a (star a) := a_le_star a
    rw [h] at this; exact this
  · intro h
    have h_le : Dioid.dle (star a) (1 : α) := by
      apply dle_induction_right a 1
      · exact Dioid.dle_refl _
      · refine Dioid.dle_trans (Dioid.dle_mul_right_mono h) ?_
        rw [one_mul]; exact Dioid.dle_refl _
    have h_one : Dioid.dle (1 : α) (star a) := one_le_star a
    exact Dioid.dle_antisymm h_le h_one

/-- star a = a ssi a*a = a et 1 ≤ a. -/
theorem star_eq_self_iff (a : α) : star a = a ↔ a * a = a ∧ Dioid.dle (1 : α) a := by
  constructor
  · intro h_eq
    have h_one : Dioid.dle (1 : α) a := by
      rw [← h_eq]; exact one_le_star a
    have h_aa_le_a : Dioid.dle (a * a) a := by
      simpa [h_eq] using star_mul_star_le_star a
    have h_a_le_aa : Dioid.dle a (a * a) := by
      simpa [mul_one] using Dioid.dle_mul_left_mono h_one
    exact And.intro (Dioid.dle_antisymm h_aa_le_a h_a_le_aa) h_one
  · intro ⟨h_mul, h_one⟩
    apply Dioid.dle_antisymm
    · apply dle_induction_right a a h_one
      rw [h_mul]; exact Dioid.dle_refl a
    · exact a_le_star a

/-- Induction + monotonie combinées : b ≤ c et c*a ≤ c → b*star a ≤ c. -/
theorem mul_star_le (a b c : α) (hb : Dioid.dle b c) (hc : Dioid.dle (c * a) c) :
    Dioid.dle (b * star a) c := by
  have h_mul : Dioid.dle (b * star a) (c * star a) := Dioid.dle_mul_right_mono hb
  have h_cσ_le_c : Dioid.dle (c * star a) c := star_induction_left a c hc
  exact Dioid.dle_trans h_mul h_cσ_le_c

/-- Induction + monotonie combinées dual : b ≤ c et a*c ≤ c → star a*b ≤ c. -/
theorem star_mul_le (a b c : α) (hb : Dioid.dle b c) (hc : Dioid.dle (a * c) c) :
    Dioid.dle (star a * b) c := by
  have h_mul : Dioid.dle (star a * b) (star a * c) := Dioid.dle_mul_left_mono hb
  have h_σc_le_c : Dioid.dle (star a * c) c := star_induction_right a c hc
  exact Dioid.dle_trans h_mul h_σc_le_c

end KleeneDioid

/-! ### Instance dioïde booléen (D4) sur Bool

Addition = or (∨), multiplication = and (∧).
0 = false, 1 = true.
C'est le dioïde booléen minimal, isomorphe à (2^[1], ∪, ∩).

On définit les instances couche par couche pour éviter les problèmes
de synthèse de typeclass (Zero Bool n'existe pas par défaut dans mathlib4). -/

instance : Zero Bool := ⟨false⟩
instance : One Bool  := ⟨true⟩
instance : Add Bool := ⟨(· ∨ ·)⟩
instance : Mul Bool := ⟨(· ∧ ·)⟩

instance : Dioid Bool where
  add := (· ∨ ·)
  add_assoc := by decide
  add_comm := by decide
  zero := false
  zero_add := by decide
  add_zero := by decide
  nsmul := λ n x => if n = 0 then (0 : Bool) else x
  nsmul_zero := by intro x; simp
  nsmul_succ := by
    intro n x
    simp
    by_cases hn : n = 0
    · subst hn; cases x <;> rfl
    · simp [hn]
      cases x <;> rfl
  mul := (· ∧ ·)
  mul_assoc := by decide
  one := true
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  add_idem := by decide
