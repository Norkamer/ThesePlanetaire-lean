/-
  MonnaiesEndogene/Z_max.lean
  Type Z_max = ℤ ∪ {-∞} pour l'arithmétique max-plus (dioïde tropical D1).
  Addition = max, multiplication = addition entière.
  ⊥ = -∞ (zéro du dioïde), ofInt 0 = 1.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.WithBot
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import ThesePlanetaire.Dioid
import Mathlib.Algebra.Tropical.Basic

inductive Z_max : Type where
  | negInf : Z_max
  | ofInt  : ℤ → Z_max
  deriving DecidableEq, Inhabited, Repr

namespace Z_max

protected def add (a b : Z_max) : Z_max :=
  match a, b with
  | negInf, b => b
  | a, negInf => a
  | ofInt a, ofInt b => ofInt (max a b)

protected def mul (a b : Z_max) : Z_max :=
  match a, b with
  | negInf, _ => negInf
  | _, negInf => negInf
  | ofInt a, ofInt b => ofInt (a + b)

instance : Zero Z_max := ⟨negInf⟩
instance : One Z_max := ⟨ofInt 0⟩
instance : Add Z_max := ⟨Z_max.add⟩
instance : Mul Z_max := ⟨Z_max.mul⟩

-- Ponts définitionnels : expose Z_max.add/mul puis le kernel réduit le match
private theorem add_eq (x y : Z_max) : x + y = Z_max.add x y := rfl
private theorem mul_eq (x y : Z_max) : x * y = Z_max.mul x y := rfl

-- 0 = negInf : nécessaire car `simp` ne déplie pas l'instance Zero
@[simp] theorem zero_eq : (0 : Z_max) = negInf := rfl

theorem add_assoc (a b c : Z_max) : (a + b) + c = a + (b + c) := by
  rw [add_eq, add_eq, add_eq, add_eq]
  cases a <;> cases b <;> cases c <;> simp [Z_max.add, max_assoc]

theorem add_comm (a b : Z_max) : a + b = b + a := by
  rw [add_eq, add_eq]
  cases a <;> cases b <;> simp [Z_max.add, max_comm]

theorem zero_add (a : Z_max) : (0 : Z_max) + a = a := by
  rw [add_eq]; cases a <;> simp [Z_max.add]

theorem add_zero (a : Z_max) : a + (0 : Z_max) = a := by
  rw [add_eq]; cases a <;> simp [Z_max.add]

theorem mul_assoc (a b c : Z_max) : (a * b) * c = a * (b * c) := by
  cases a with
  | negInf => simp [mul_eq, Z_max.mul]
  | ofInt a =>
    cases b with
    | negInf => simp [mul_eq, Z_max.mul]
    | ofInt b =>
      cases c with
      | negInf => simp [mul_eq, Z_max.mul]
      | ofInt c =>
        calc
          (ofInt a * ofInt b) * ofInt c = ofInt (a + b) * ofInt c := rfl
          _ = ofInt ((a + b) + c) := rfl
          _ = ofInt (a + (b + c)) := by rw [_root_.add_assoc]
          _ = ofInt a * ofInt (b + c) := rfl
          _ = ofInt a * (ofInt b * ofInt c) := rfl

theorem one_mul (a : Z_max) : (1 : Z_max) * a = a := by
  rw [mul_eq]; cases a <;> simp [Z_max.mul]

theorem mul_one (a : Z_max) : a * (1 : Z_max) = a := by
  rw [mul_eq]; cases a <;> simp [Z_max.mul]

theorem zero_mul (a : Z_max) : (0 : Z_max) * a = (0 : Z_max) := by
  rw [mul_eq]; cases a <;> simp [Z_max.mul]

theorem mul_zero (a : Z_max) : a * (0 : Z_max) = (0 : Z_max) := by
  rw [mul_eq]; cases a <;> simp [Z_max.mul]

theorem left_distrib (a b c : Z_max) : a * (b + c) = (a * b) + (a * c) := by
  rw [mul_eq, add_eq, mul_eq, mul_eq, add_eq]
  cases a <;> cases b <;> cases c <;> simp [Z_max.add, Z_max.mul]

theorem right_distrib (a b c : Z_max) : (a + b) * c = (a * c) + (b * c) := by
  rw [add_eq, mul_eq, mul_eq, mul_eq, add_eq]
  cases c <;> cases a <;> cases b <;> simp [Z_max.add, Z_max.mul]

theorem mul_comm (a b : Z_max) : a * b = b * a := by
  rw [mul_eq, mul_eq]
  cases a <;> cases b <;> simp [Z_max.mul, _root_.add_comm]

theorem add_idem (a : Z_max) : a + a = a := by
  rw [add_eq]
  cases a <;> simp [Z_max.add]

protected def nsmul (n : ℕ) (a : Z_max) : Z_max :=
  if n = 0 then (0 : Z_max) else a

instance : CommSemiring Z_max where
  add := Z_max.add
  add_assoc := add_assoc
  add_comm := add_comm
  zero := negInf
  zero_add := zero_add
  add_zero := add_zero
  nsmul := Z_max.nsmul
  nsmul_zero := by intro a; simp [Z_max.nsmul]
  nsmul_succ := by
    intro n a
    simp [Z_max.nsmul]
    by_cases hn : n = 0
    · subst hn; simp [add_eq, Z_max.add]
    · simp [hn, add_idem a]
  mul := Z_max.mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one := ofInt 0
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib

instance : Dioid Z_max where
  toSemiring := inferInstance
  add_idem := add_idem

/-- SemilatticeSup: sup = max = addition (Z_max.add). Ordre: Dioid.dle. -/
instance : SemilatticeSup Z_max where
  sup a b := a + b
  le := Dioid.dle
  le_refl a := Dioid.dle_refl a
  le_trans a b c := Dioid.dle_trans
  le_antisymm a b := Dioid.dle_antisymm
  le_sup_left a b := by
    unfold Dioid.dle
    calc
      a + (a + b) = (a + a) + b := by rw [add_assoc]
      _ = a + b := by rw [Z_max.add_idem]
  le_sup_right a b := by
    unfold Dioid.dle
    calc
      b + (a + b) = b + (b + a) := by rw [add_comm a b]
      _ = (b + b) + a := by rw [← add_assoc]
      _ = b + a := by rw [Z_max.add_idem]
      _ = a + b := by rw [add_comm b a]
  sup_le a b c hac hbc := by
    unfold Dioid.dle at hac hbc
    unfold Dioid.dle
    calc
      (a + b) + c = a + (b + c) := by rw [add_assoc]
      _ = a + c := by rw [hbc]
      _ = c := by rw [hac]

/-- OrderBot: ⊥ = negInf = 0 est le plus petit élément. -/
instance : OrderBot Z_max where
  bot := 0
  bot_le a := by
    exact Dioid.dle_zero a

/-- Ordre standard ≤ pour Z_max, compatible avec l'ordre dioïde (Dioid.dle). -/
instance : LE Z_max :=
  ⟨fun a b => Dioid.dle a b⟩

/-- Instance DecidableLE pour Z_max (utilise la décidabilité classique). -/
noncomputable instance : DecidableLE Z_max :=
  by
  classical
  exact inferInstance

/-- Preorder pour Z_max basé sur Dioid.dle. -/
instance : Preorder Z_max := by
  classical
  infer_instance

/-- Instance AddLeftMono pour Z_max (nécessaire pour Finset.sum_le_sum_of_subset_of_nonneg). -/
instance : AddLeftMono Z_max := by
  -- Dans Z_max, l'addition est sup (max) et l'ordre est Dioid.dle
  -- L'instance SemilatticeSup fournit la monotonicité de sup (= max = +)
  -- sup_le_sup_left (h : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b
  -- Puisque add = sup dans Z_max, cela donne exactement AddLeftMono
  exact ⟨fun c a b h => sup_le_sup_left h c⟩

/-! ### Distributivité Finset.sup / multiplication

  Dans Z_max, sup = max, * = addition entière.
  L'addition entière distribue sur max : a + max(b,c) = max(a+b, a+c). -/

@[simp]
lemma sup_mul_left {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : Z_max) (f : ι → Z_max) :
    a * Finset.sup s f = Finset.sup s (λ i => a * f i) := by
  refine Finset.induction_on s ?_ ?_
  · simpa using mul_zero a
  · intro i s his ih
    rw [Finset.sup_insert, Finset.sup_insert]
    show a * (f i + Finset.sup s f) = (a * f i) + Finset.sup s (λ i => a * f i)
    rw [left_distrib, ih]

@[simp]
lemma sup_mul_right {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Z_max) (a : Z_max) :
    (Finset.sup s f) * a = Finset.sup s (λ i => f i * a) := by
  refine Finset.induction_on s ?_ ?_
  · simpa using zero_mul a
  · intro i s his ih
    rw [Finset.sup_insert, Finset.sup_insert]
    show (f i + Finset.sup s f) * a = (f i * a) + Finset.sup s (λ i => f i * a)
    rw [right_distrib, ih]

lemma sup_sup_comm {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂] (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (f : ι₁ → ι₂ → Z_max) :
    Finset.sup s₁ (λ i => Finset.sup s₂ (f i)) = Finset.sup s₂ (λ j => Finset.sup s₁ (λ i => f i j)) := by
  apply le_antisymm
  · apply Finset.sup_le; intro i hi
    apply Finset.sup_le; intro j hj
    apply le_trans (Finset.le_sup hi)
    apply Finset.le_sup hj
  · apply Finset.sup_le; intro j hj
    apply Finset.sup_le; intro i hi
    apply le_trans (Finset.le_sup hj)
    apply Finset.le_sup hi

/-- Conversion vers les reels. -/
def toReal (z : Z_max) : ℝ :=
  match z with
  | negInf => 0  -- negInf maps to 0 in ℝ (no negative infinity in ℝ)
  | ofInt n => n

/-- Conversion vers les entiers. -/
def toInt (z : Z_max) : ℤ :=
  match z with
  | negInf => 0  -- negInf maps to 0 (cycle weight should never be negInf for valid cycles)
  | ofInt n => n

/-- Division tropicale : a / b = a - b (dans Z_max, c'est la soustraction dans ℤ) -/
def tdiv (a b : Z_max) : Z_max :=
  match a, b with
  | _, negInf => negInf
  | negInf, _ => negInf
  | ofInt a, ofInt b => ofInt (a - b)

def tdivNat (a : Z_max) (n : ℕ) : Z_max :=
  match a with
  | negInf => negInf
  | ofInt a => ofInt (a - n)  -- tropical division by n is subtraction in ℤ

instance : Div Z_max := ⟨tdiv⟩
instance : HDiv Z_max Z_max Z_max := ⟨fun a b => a / b⟩

/-- Z_max est isomorphe à WithBot ℤ (avec ordre inversé pour que ⊥ = negInf soit le minimum).
    On utilise les instances de treillis complet conditionnel de WithBot ℤ via cet isomorphisme. -/
def Z_max_toWithBot (z : Z_max) : WithBot ℤ :=
  match z with
  | negInf => ⊥
  | ofInt n => ↑n

def WithBot_toZ_max (w : WithBot ℤ) : Z_max :=
  match w with
  | ⊥ => negInf
  | (n : ℤ) => ofInt n

-- Ces fonctions forment un isomorphisme d'ordre PRÉSERVANT l'ordre (et non inversé
-- comme l'indiquait l'ancien commentaire) : dans Z_max, `le = Dioid.dle` (Dioid.lean:22)
-- := « a + b = b » i.e. `a ≤ b` usuel avec `negInf` = plus petit élément (OrderBot, L169),
-- exactement comme `WithBot ℤ` où `⊥ = none` est le plus petit élément.
-- `Z_max_toWithBot` est donc croissante bijective : un `OrderIso`.
-- On transporte la structure `ConditionallyCompleteLattice` de `WithBot ℤ` (qui en a une
-- instance, `WithBot.conditionallyCompleteLattice`) via cet iso.

@[simp] lemma toWithBot_invol (z : Z_max) : WithBot_toZ_max (Z_max_toWithBot z) = z := by
  cases z <;> rfl

@[simp] lemma toZmax_invol (w : WithBot ℤ) : Z_max_toWithBot (WithBot_toZ_max w) = w := by
  cases w <;> rfl

/-- `(a ≤ b : Z_max)` se déplie en `Dioid.dle a b` (= `a + b = b`), car l'instance `LE`
    est `⟨Dioid.dle⟩`. Utile pour le transport d'ordre (les lemmas simp de `LE.le` ne
    déplient pas cette instance). -/
lemma le_def (a b : Z_max) : a ≤ b ↔ Dioid.dle a b := Iff.rfl

/-- L'ordre est préservé par `Z_max_toWithBot` (les 4 cas negInf/ofInt). -/
lemma toWithBot_le_iff (a b : Z_max) :
    Z_max_toWithBot a ≤ Z_max_toWithBot b ↔ a ≤ b := by
  rcases a with rfl | a <;> rcases b with rfl | b
  · -- ⊥ ≤ ⊥ ↔ negInf ≤ negInf
    simp [Z_max_toWithBot, le_def, Dioid.dle, add_eq, Z_max.add, bot_le]
  · -- ⊥ ≤ ↑b ↔ negInf ≤ ofInt b
    simp [Z_max_toWithBot, le_def, Dioid.dle, add_eq, Z_max.add, bot_le]
  · -- ↑a ≤ ⊥ ↔ ofInt a ≤ negInf   (les deux côtés sont faux)
    refine ⟨fun h => absurd h (WithBot.not_coe_le_bot _), fun h => ?_⟩
    simp only [le_def, Dioid.dle, add_eq, Z_max.add] at h
    nomatch h
  · -- ↑a ≤ ↑b ↔ ofInt a ≤ ofInt b
    simp only [Z_max_toWithBot, WithBot.coe_le_coe, le_def, Dioid.dle, add_eq, Z_max.add, ofInt.injEq]
    constructor <;> intro h <;> omega

/-- `Z_max` est isomorphe (en tant qu'ordres) à `WithBot ℤ`. -/
def zmaxOrderIso : Z_max ≃o WithBot ℤ where
  toFun := Z_max_toWithBot
  invFun := WithBot_toZ_max
  left_inv := toWithBot_invol
  right_inv := toZmax_invol
  map_rel_iff' := @toWithBot_le_iff

/-- `SemilatticeInf` par transport : `inf` = min (duale de `sup = max`). Partage le même
    `PartialOrder` que le `SemilatticeSup` existant (pas de redéfinition de `le`, pas de
    diamant). L'ancien `SemilatticeSup` (sup = Z_max.add = max) est inchangé. -/
instance : SemilatticeInf Z_max where
  inf a b := WithBot_toZ_max (Z_max_toWithBot a ⊓ Z_max_toWithBot b)
  inf_le_left a b := by
    rw [← toWithBot_le_iff, toZmax_invol]
    exact inf_le_left
  inf_le_right a b := by
    rw [← toWithBot_le_iff, toZmax_invol]
    exact inf_le_right
  le_inf a b c (hab : a ≤ b) (hac : a ≤ c) := by
    rw [← toWithBot_le_iff, toZmax_invol]
    refine le_inf ?_ ?_
    · exact (toWithBot_le_iff _ _).mpr hab
    · exact (toWithBot_le_iff _ _).mpr hac

/-- `Lattice` = `SemilatticeSup` (existant) + `SemilatticeInf` (ci-dessus), aucun champ
    supplémentaire (`Lattice` n'a pas de champ au-delà des deux parents). -/
instance : Lattice Z_max where

/-- `SupSet` par transport depuis `WithBot ℤ`. -/
noncomputable instance : SupSet Z_max :=
  ⟨fun S => WithBot_toZ_max (sSup (Z_max_toWithBot '' S))⟩

/-- `InfSet` par transport depuis `WithBot ℤ`. -/
noncomputable instance : InfSet Z_max :=
  ⟨fun S => WithBot_toZ_max (sInf (Z_max_toWithBot '' S))⟩

/-- `ConditionallyCompleteLattice` par transport depuis `WithBot ℤ`.
    `sSup`/`sInf` (via `SupSet`/`InfSet`) + `isLUB_csSup`/`isGLB_csInf` délégués à
    `WithBot ℤ` à travers l'`OrderIso` (`isLUB_image'`/`isGLB_image'`). -/
noncomputable instance : ConditionallyCompleteLattice Z_max where
  isLUB_csSup s hne hbd := by
    have key : zmaxOrderIso (sSup s) = sSup (zmaxOrderIso '' s) := by
      show Z_max_toWithBot (WithBot_toZ_max (sSup (Z_max_toWithBot '' s))) = sSup (Z_max_toWithBot '' s)
      rw [toZmax_invol]
    have hbd' : BddAbove (zmaxOrderIso '' s) := by
      obtain ⟨M, hM⟩ := hbd
      refine ⟨zmaxOrderIso M, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact (toWithBot_le_iff _ _).mpr (hM hx)
    exact (OrderIso.isLUB_image' (f := zmaxOrderIso) (x := sSup s)).mp <| by
      rw [key]; exact ConditionallyCompleteLattice.isLUB_csSup _ (hne.image _) hbd'
  isGLB_csInf s hne hbd := by
    have key : zmaxOrderIso (sInf s) = sInf (zmaxOrderIso '' s) := by
      show Z_max_toWithBot (WithBot_toZ_max (sInf (Z_max_toWithBot '' s))) = sInf (Z_max_toWithBot '' s)
      rw [toZmax_invol]
    have hbd' : BddBelow (zmaxOrderIso '' s) := by
      obtain ⟨M, hM⟩ := hbd
      refine ⟨zmaxOrderIso M, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact (toWithBot_le_iff _ _).mpr (hM hx)
    exact (OrderIso.isGLB_image' (f := zmaxOrderIso) (x := sInf s)).mp <| by
      rw [key]; exact ConditionallyCompleteLattice.isGLB_csInf _ (hne.image _) hbd'

end Z_max