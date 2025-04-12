namespace Timelib

private theorem mul_lt_of_lt (a b c : Int) (ha : 0 < a) : b < c →  b * a < c * a := by
  exact fun a_1 => Int.mul_lt_mul_of_pos_right a_1 ha

theorem div_mul_add_eq_of (p : Int) {X r : Int} (_ : r < X) (_ : 1 < X) (_ : 0 <= r) : (p * X + r) / X = p := by
  have h := Int.add_mul_ediv_left (a := r) (b := X) (c := p) (by omega)
  have h' := Int.ediv_eq_zero_of_lt (a := r) (b := X) ‹_› ‹_›
  rw [h', Int.zero_add, Int.mul_comm, Int.add_comm] at h
  assumption

example (a X : Int) (h : 1 < X) (h' : 1 <= a): 1 * X <= a * X :=
  Int.mul_le_mul_of_nonneg_right h' (by omega)

theorem le_mul_left {a X : Int} (h : 1 < X) (h' : 1 <= a): X <= a * X := by
  have eq_mul1 : X = 1 * X := by simp
  conv =>
    lhs; rw [eq_mul1]
  exact Int.mul_le_mul_of_nonneg_right h' (by omega)

example (a X : Int) (h : 1 < X) (h1 : 0 <= a): 0 <= (a * X) := by
  have h0 : 0 <= X := by omega
  have h2 := Int.mul_nonneg h0 h1
  rw [Int.mul_comm] at h2
  omega

theorem conv_helper1(a b c d X : Int)
    (_ : a < b)
    (_ : c <= X+1)
    (lt_X : 1 < X)
    (_ : 1 <= d)
    : a * X + c <= b * X + d := by
  have b_sub_a_ge_1 : b - a ≥ 1 := by omega
  have le_sub : X ≤ (b - a) * X := le_mul_left lt_X b_sub_a_ge_1
  apply Int.le_of_sub_nonpos
  show (a * X + c) - (b * X + d) <= 0
  calc
    ((a * X) + c) - ((b * X) + d) = (a - b) * X + (c - d) := by
      have _ : (a * X) - (b * X) = (a - b) * X := Eq.symm (Int.sub_mul a b X)
      omega
    _ = - ( (b - a) * X - (c - d) ) := by
      rw [Int.neg_sub]
      conv =>
        rhs
        rw [Int.sub_eq_add_neg, Int.add_comm, ← Int.neg_mul, Int.neg_sub]
    _ ≤ 0 := by omega

macro "smesh" : tactic => `(tactic| first | assumption | decide | omega)

def WInfinity.{u} (A : Type u) := Option A

namespace WInfinity

universe u
variable {A : Type u}

instance [Repr A] : Repr (WInfinity A) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

@[coe, match_pattern] def some : A → WInfinity A :=
  Option.some

instance coeTC : CoeTC A (WInfinity A) :=
  ⟨some⟩

instance inhabited [inst : Inhabited A] : Inhabited (WInfinity A) :=
  ⟨inst.default⟩

instance instLT [inst: LT A] : LT (WInfinity A) where
  lt := Option.lt inst.lt

theorem lt_def [inst: LT A] (a b : WInfinity A) : (a < b) = Option.lt inst.lt a b := by
  simp [instLT]

instance [inst : LT A] [DecidableRel inst.lt] : DecidableRel (instLT (inst := inst)).lt := by
  simp only [instLT]; exact inferInstance

end WInfinity
