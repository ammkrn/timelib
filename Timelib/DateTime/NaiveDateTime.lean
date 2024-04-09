
import Timelib.Util
import Timelib.Date.ScalarDate
import Timelib.Date.Convert
import Timelib.Duration.Constants
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Order.WithBot
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
namespace Timelib

/--
If nonnegative, the number of nanoseconds since the epoch (midnight of 0001/Jan/01)
If negative, the number of nanoseconds until the epoch (midnight of 0001/Jan/01)

A `NaiveDateTime pow` represents a date and time in the appropriate SI unit which has no knowledge of
leap seconds or time zones.

`DateTime` elements can only be indexed by SI exponents less than
or equal to zero.
-/
structure NaiveDateTime (p : Int) extends SignedDuration p where
  isLe : p <= 0
deriving DecidableEq, Hashable, Repr

namespace NaiveDateTime
variable {siPow : Int}

/-
Using `Int.fdiv`, because we have a positive denominator (the number of seconds in a day)
and we want to round down if `dt.val` is negative, up if it's nonnegative.

Equivalently, you can round toward zero and only add `1` if the
quotient is greater than of equal to zero.
-/
def toScalarDate (dt : NaiveDateTime siPow) : ScalarDate :=
  let oneDay := SignedDuration.Constants.oneDayDuration dt.isLe
  let zeroBasedDay := dt.val.fdiv oneDay.val
  ⟨zeroBasedDay + 1⟩

--instance instInhabited : Inhabited (NaiveDateTime negSiPow.val) where
--  default := ⟨Inhabited.default, negSiPow.property⟩

instance instInhabited {p : Int} {isLe : p <= 0} : Inhabited (NaiveDateTime p) where
  default := ⟨Inhabited.default, isLe⟩
--def toScalarDate' (dt : NaiveDateTime siPow) : ScalarDate :=
--  let oneDay := SignedDuration.Constants.oneDayDuration siPow
--  if dt.val < 0
--  then
--    let zeroBasedDay := dt.val.div oneDay.val
--    ⟨zeroBasedDay⟩
--  else
--    let zeroBasedDay := dt.val.div oneDay.val
--    ⟨zeroBasedDay + 1⟩

def dayOfWeek (dt : NaiveDateTime siPow) : Int :=
  dt.toScalarDate.dayOfWeek

/-- The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd. We
subtract one to account for the fact that `Date` is one day ahead of the
zero-based `NaiveDateTime`.
-/
def fromYmd
  {siPow : Int}
  {isLe : siPow <= 0}
  (y : Year)
  (m : Month)
  (d : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
: NaiveDateTime siPow :=
  let oneBasedDay := (Ymd.mk y m d hd.left hd.right).toScalarDate.day
  let zeroBasedDay := oneBasedDay - 1
  let oneDay : SignedDuration siPow := SignedDuration.Constants.oneDayDuration isLe
  ⟨oneDay.val * zeroBasedDay, isLe⟩

--instance instHAddSelfSignedDurationSelf' {z : Int} :
--  HAdd (NaiveDateTime siPow) (SignedDuration z) (NaiveDateTime (minLeft siPow z))
--where
--  hAdd da du := ⟨da.val + du.val⟩

@[default_instance]
instance instHAddSelfSignedDurationSelf :
  HAdd (NaiveDateTime siPow) (SignedDuration siPow) (NaiveDateTime siPow)
where
  hAdd da du := ⟨da.toSignedDuration + du, da.isLe⟩

@[default_instance]
instance instHAddSignedDurationSelfSelf :
  HAdd (SignedDuration siPow) (NaiveDateTime siPow) (NaiveDateTime siPow)
where
  hAdd du da := da + du

def toYmd (d : NaiveDateTime siPow) : Ymd := d.toScalarDate.toYmd

def fromYmdsn
  {negSiPow : Int}
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : SignedDuration 0)
  (n : SignedDuration (-9))
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
  (h2 : negSiPow <= -9)
: NaiveDateTime negSiPow :=
  have isLe : negSiPow <= 0 := le_trans h2 (by decide)
  let s' : SignedDuration negSiPow := s.convertLossless isLe
  let n' : SignedDuration negSiPow := n.convertLossless h2
  (fromYmd (isLe := isLe) y m d hd : NaiveDateTime negSiPow) + s' + n'

instance instEquivIntSelf {siPow : Int} {isLe : siPow <= 0} : Equiv Int (NaiveDateTime siPow) where
  toFun := fun z => NaiveDateTime.mk (SignedDuration.mk z) isLe
  invFun := fun d => d.val
  left_inv := by simp only [Function.LeftInverse, forall_const]
  right_inv := by simp only [Function.RightInverse, Function.LeftInverse, implies_true]

instance instEquivSignedDurationSelf {siPow : Int} {isLe : siPow <= 0} : Equiv (SignedDuration siPow) (NaiveDateTime siPow) where
  toFun := fun dur => NaiveDateTime.mk dur.val isLe
  invFun := fun d => d.toSignedDuration
  left_inv _ := rfl
  right_inv _ := rfl

theorem eq_of_val_eq : ∀ {d1 d2 : NaiveDateTime siPow},
  d1.toSignedDuration = d2.toSignedDuration → d1 = d2
| ⟨_, _⟩, _, rfl => rfl

theorem val_eq_of_eq : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 = d2 → d1.toSignedDuration = d2.toSignedDuration
| ⟨_, _⟩, _, rfl => rfl

theorem eq_def : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 = d2 ↔ d1.toSignedDuration = d2.toSignedDuration
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem val_ne_of_ne : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 ≠ d2 → d1.toSignedDuration ≠ d2.toSignedDuration
| ⟨_, _⟩, ⟨_, _⟩, hne, h => hne (congrFun (congrArg mk h) _)

instance instLT : LT (NaiveDateTime siPow) where
  lt := fun a b => a.toSignedDuration < b.toSignedDuration

instance instLE : LE (NaiveDateTime siPow) where
  le := fun a b => a.toSignedDuration <= b.toSignedDuration

@[simp] theorem le_def (d₁ d₂ : NaiveDateTime siPow) :
  (d₁ <= d₂) = (d₁.toSignedDuration <= d₂.toSignedDuration)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : NaiveDateTime siPow) :
  (d₁ < d₂) = (d₁.toSignedDuration < d₂.toSignedDuration)
:= rfl

instance instDecidableLENaiveDateTime (d₁ d₂ : NaiveDateTime siPow) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toSignedDuration <= d₂.toSignedDuration)

instance instDecidableLTNaiveDateTime (d₁ d₂ : NaiveDateTime siPow) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toSignedDuration < d₂.toSignedDuration)

instance instOrd : Ord (NaiveDateTime siPow) where
  --compare l r := compare l.val r.val
  compare l r := compare l.toSignedDuration r.toSignedDuration

theorem compare_def (l r : NaiveDateTime siPow) : compare l r = compare l.toSignedDuration r.toSignedDuration := rfl

instance instLinearOrder : LinearOrder (NaiveDateTime siPow) where
  le_refl (a) := le_refl a.toSignedDuration
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp only [le_def, le_total, implies_true]
  decidableLE := inferInstance
  compare_eq_compareOfLessAndEq := by
    simp only [compare, compareOfLessAndEq, lt_def, eq_def, implies_true]

--instance instToString : ToString (NaiveDateTime siPow) where
--  toString dt :=
--    let ⟨y, m, d, _, _⟩ := dt.toYmd
--    let t : String :=
--      Fin.ofInt'' (dt.nanos % (↑oneDayNanos))
--      |> NaiveClockTime.mk
--      |> ToString.toString
--    s!"{y}/{m.toNat}/{d}; {t}"

@[reducible]
def dateEq : (NaiveDateTime siPow) → (NaiveDateTime siPow) → Prop
| n₁, n₂ => n₁.toScalarDate = n₂.toScalarDate

def dateEq.Equivalence : Equivalence (@dateEq siPow) := {
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instNaiveDateTimeSetoid : Setoid (NaiveDateTime siPow) :=
  ⟨dateEq, dateEq.Equivalence⟩

instance instDecidable_dateEq (d₁ d₂ : NaiveDateTime siPow) :
  Decidable <| d₁.dateEq d₂
:= inferInstance

instance instOfNat {siPow : Int} {isLe : siPow <= 0} {n : Nat} : OfNat (NaiveDateTime siPow) n where
  ofNat := ⟨n, isLe⟩

theorem hAdd_signed_def (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  d + dur = ⟨d.toSignedDuration + dur, d.isLe⟩
:= rfl
theorem hAdd_signed_def_rev (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  dur + d = ⟨d.toSignedDuration + dur, d.isLe⟩
:= rfl

instance instHSubSelfSignedDurationSelf :
  HSub (NaiveDateTime siPow) (SignedDuration siPow) (NaiveDateTime siPow)
where
  hSub t dur := t + -dur

theorem hSub_signed_def (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  d - dur = d + -dur
:= rfl

theorem hAdd_signed_sub_cancel (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t + d - d = t
:= by
  simp only [hAdd_signed_def, hSub_signed_def]
  apply eq_of_val_eq
  exact add_neg_cancel_right t.toSignedDuration d

theorem hAdd_signed_sub_add_cancel (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t - d + d = t
:= by
  simp only [hSub_signed_def, hAdd_signed_def]
  apply eq_of_val_eq
  exact neg_add_cancel_right t.toSignedDuration d

theorem hAdd_signed_comm (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t + d = d + t
:= by simp only [hAdd_signed_def, hAdd_signed_def_rev]

theorem hAdd_signed_assoc (d : NaiveDateTime siPow) (dur₁ dur₂ : (SignedDuration siPow)) : d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp only [hAdd_signed_def, mk.injEq]
  exact add_assoc d.toSignedDuration dur₁ dur₂

def convertLossless
  {fine coarse : Int}
  (d : NaiveDateTime coarse)
  (h : fine <= coarse := by decide) :
  NaiveDateTime fine :=
    ⟨d.toSignedDuration.convertLossless h, le_trans h d.isLe⟩

def le_het {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) : Prop :=
  d1.toSignedDuration.le_het d2.toSignedDuration

theorem le_het_iff {p : Int} (d1 d2 : NaiveDateTime p) : le_het d1 d2 ↔ d1 <= d2 :=
  SignedDuration.le_het_iff d1.toSignedDuration d2.toSignedDuration

def lt_het {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) : Prop :=
  d1.toSignedDuration.lt_het d2.toSignedDuration

theorem lt_het_iff {p : Int} (d1 d2 : NaiveDateTime p) : lt_het d1 d2 ↔ d1 < d2 :=
  SignedDuration.lt_het_iff d1.toSignedDuration d2.toSignedDuration

instance instDecidableLEHet {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) :
  Decidable (le_het d1 d2)
:= inferInstanceAs <| Decidable <| d1.toSignedDuration.le_het d2.toSignedDuration
  --(d1.convertLossless (min_le_left _ _) : NaiveDateTime (min p1 p2)).toSignedDuration
  --<= (d2.convertLossless (min_le_right _ _) : NaiveDateTime (min p1 p2)).toSignedDuration

instance instDecidableLTHet {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) :
  Decidable (lt_het d1 d2)
:= inferInstanceAs <| Decidable <| d1.toSignedDuration.lt_het d2.toSignedDuration
  --(d1.convertLossless (min_le_left _ _) : NaiveDateTime (min p1 p2)).toSignedDuration
  --< (d2.convertLossless (min_le_right _ _) : NaiveDateTime (min p1 p2)).toSignedDuration

theorem le_het_trans
{p1 p2 p3: Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) (d3 : NaiveDateTime p3)
  : le_het d1 d2 → le_het d2 d3 → le_het d1 d3 :=
  SignedDuration.le_het_trans d1.toSignedDuration d2.toSignedDuration d3.toSignedDuration

theorem lt_het_iff_le_het_not_le_het {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2)
  : lt_het d1 d2 ↔ le_het d1 d2 ∧ ¬(le_het d2 d1) :=
  SignedDuration.lt_het_iff_le_het_not_le_het d1.toSignedDuration d2.toSignedDuration
