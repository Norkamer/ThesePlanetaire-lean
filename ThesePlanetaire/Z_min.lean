/-
  MonnaiesEndogene/Z_min.lean
  Type Z_min = ℤ ∪ {+∞} pour l'arithmétique min-plus (dioïde tropical D2).
  Addition = min, multiplication = addition entière.
  ⊥ = +∞ (zéro du dioïde), ofInt 0 = 1.
  Dual de Z_max via x ↦ -x.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.Linarith
import ThesePlanetaire.Dioid

inductive Z_min : Type where
  | posInf : Z_min
  | ofInt  : ℤ → Z_min
  deriving DecidableEq, Inhabited, Repr

namespace Z_min

protected def add (a b : Z_min) : Z_min :=
  match a, b with
  | posInf, b => b
  | a, posInf => a
  | ofInt a, ofInt b => ofInt (min a b)

protected def mul (a b : Z_min) : Z_min :=
  match a, b with
  | posInf, _ => posInf
  | _, posInf => posInf
  | ofInt a, ofInt b => ofInt (a + b)

instance : Zero Z_min := ⟨posInf⟩
instance : One Z_min := ⟨ofInt 0⟩
instance : Add Z_min := ⟨Z_min.add⟩
instance : Mul Z_min := ⟨Z_min.mul⟩

private theorem add_eq (x y : Z_min) : x + y = Z_min.add x y := rfl
private theorem mul_eq (x y : Z_min) : x * y = Z_min.mul x y := rfl

@[simp] theorem zero_eq : (0 : Z_min) = posInf := rfl

theorem add_assoc (a b c : Z_min) : (a + b) + c = a + (b + c) := by
  rw [add_eq, add_eq, add_eq, add_eq]
  cases a <;> cases b <;> cases c <;> simp [Z_min.add, min_assoc]

theorem add_comm (a b : Z_min) : a + b = b + a := by
  rw [add_eq, add_eq]
  cases a <;> cases b <;> simp [Z_min.add, min_comm]

theorem zero_add (a : Z_min) : (0 : Z_min) + a = a := by
  rw [add_eq]; cases a <;> simp [Z_min.add]

theorem add_zero (a : Z_min) : a + (0 : Z_min) = a := by
  rw [add_eq]; cases a <;> simp [Z_min.add]

theorem mul_assoc (a b c : Z_min) : (a * b) * c = a * (b * c) := by
  cases a with
  | posInf => simp [mul_eq, Z_min.mul]
  | ofInt a =>
    cases b with
    | posInf => simp [mul_eq, Z_min.mul]
    | ofInt b =>
      cases c with
      | posInf => simp [mul_eq, Z_min.mul]
      | ofInt c =>
        calc
          (ofInt a * ofInt b) * ofInt c = ofInt (a + b) * ofInt c := rfl
          _ = ofInt ((a + b) + c) := rfl
          _ = ofInt (a + (b + c)) := by rw [_root_.add_assoc]
          _ = ofInt a * ofInt (b + c) := rfl
          _ = ofInt a * (ofInt b * ofInt c) := rfl

theorem one_mul (a : Z_min) : (1 : Z_min) * a = a := by
  rw [mul_eq]; cases a <;> simp [Z_min.mul]

theorem mul_one (a : Z_min) : a * (1 : Z_min) = a := by
  rw [mul_eq]; cases a <;> simp [Z_min.mul]

theorem zero_mul (a : Z_min) : (0 : Z_min) * a = (0 : Z_min) := by
  rw [mul_eq]; cases a <;> simp [Z_min.mul]

theorem mul_zero (a : Z_min) : a * (0 : Z_min) = (0 : Z_min) := by
  rw [mul_eq]; cases a <;> simp [Z_min.mul]

theorem left_distrib (a b c : Z_min) : a * (b + c) = (a * b) + (a * c) := by
  rw [mul_eq, add_eq, mul_eq, mul_eq, add_eq]
  cases a <;> cases b <;> cases c <;> simp [Z_min.add, Z_min.mul]

theorem right_distrib (a b c : Z_min) : (a + b) * c = (a * c) + (b * c) := by
  rw [add_eq, mul_eq, mul_eq, mul_eq, add_eq]
  cases c <;> cases a <;> cases b <;> simp [Z_min.add, Z_min.mul]

theorem add_idem (a : Z_min) : a + a = a := by
  rw [add_eq]
  cases a <;> simp [Z_min.add]

protected def nsmul (n : ℕ) (a : Z_min) : Z_min :=
  if n = 0 then (0 : Z_min) else a

instance : Semiring Z_min where
  add := Z_min.add
  add_assoc := add_assoc
  add_comm := add_comm
  zero := posInf
  zero_add := zero_add
  add_zero := add_zero
  nsmul := Z_min.nsmul
  nsmul_zero := by intro a; simp [Z_min.nsmul]
  nsmul_succ := by
    intro n a
    simp [Z_min.nsmul]
    by_cases hn : n = 0
    · subst hn; simp [add_eq, Z_min.add]
    · simp [hn, add_idem a]
  mul := Z_min.mul
  mul_assoc := mul_assoc
  one := ofInt 0
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib

instance : Dioid Z_min where
  toSemiring := inferInstance
  add_idem := add_idem

/-- SemilatticeSup: sup = min = addition (Z_min.add). Ordre: Dioid.dle. -/
instance : SemilatticeSup Z_min where
  sup a b := a + b
  le := Dioid.dle
  le_refl a := Dioid.dle_refl a
  le_trans a b c := Dioid.dle_trans
  le_antisymm a b := Dioid.dle_antisymm
  le_sup_left a b := by
    unfold Dioid.dle
    calc
      a + (a + b) = (a + a) + b := by rw [add_assoc]
      _ = a + b := by rw [Z_min.add_idem]
  le_sup_right a b := by
    unfold Dioid.dle
    calc
      b + (a + b) = b + (b + a) := by rw [add_comm a b]
      _ = (b + b) + a := by rw [← add_assoc]
      _ = b + a := by rw [Z_min.add_idem]
      _ = a + b := by rw [add_comm b a]
  sup_le a b c hac hbc := by
    unfold Dioid.dle at hac hbc
    unfold Dioid.dle
    calc
      (a + b) + c = a + (b + c) := by rw [add_assoc]
      _ = a + c := by rw [hbc]
      _ = c := by rw [hac]

/-- OrderBot: ⊥ = posInf = 0 est le plus petit élément. -/
instance : OrderBot Z_min where
  bot := 0
  bot_le a := Dioid.dle_zero a

end Z_min
