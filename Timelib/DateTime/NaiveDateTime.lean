
import Timelib.Util
import Timelib.Date.ScalarDate
import Timelib.Date.Convert
import Timelib.Duration.Constants

namespace Timelib

/--
If nonnegative, the number of nanoseconds since the epoch (midnight of 0001/Jan/01)
If negative, the number of nanoseconds until the epoch (midnight of 0001/Jan/01)

A `NaiveDateTime pow` represents a date and time in the appropriate SI unit which has no knowledge of
leap seconds or time zones.

`DateTime` elements can only be indexed by SI exponents less than
or equal to zero.
-/
structure NaiveDateTime (p : NegSiPow) where
  val : Int
deriving DecidableEq, Ord, Hashable, Repr --, Lean.ToJson, Lean.FromJson

namespace NaiveDateTime
variable {siPow : NegSiPow}

instance instInhabited : Inhabited (NaiveDateTime siPow) where
  default := ⟨0⟩

instance instOrd : Ord (NaiveDateTime siPow) where
  compare l r := compare l.val r.val

/-
Using `Int.fdiv`, because we have a positive denominator (the number of seconds in a day)
and we want to round down if `dt.val` is negative, up if it's nonnegative.

Equivalently, you can round toward zero and only add `1` if the
quotient is greater than of equal to zero.
-/
def toScalarDate (dt : NaiveDateTime siPow) : ScalarDate :=
  let oneDay := SignedDuration.Constants.oneDayDuration siPow
  let zeroBasedDay := dt.val.fdiv oneDay.val
  ⟨zeroBasedDay + 1⟩

def toScalarDate2 (dt : NaiveDateTime siPow) : ScalarDate :=
  let oneDay := SignedDuration.Constants.oneDayDuration siPow
  if dt.val < 0
  then
    let zeroBasedDay := dt.val.div oneDay.val
    ⟨zeroBasedDay⟩
  else
    let zeroBasedDay := dt.val.div oneDay.val
    ⟨zeroBasedDay + 1⟩

def dayOfWeek (dt : NaiveDateTime siPow) : Int :=
  dt.toScalarDate.dayOfWeek

/-- The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd. We
subtract one to account for the fact that `Date` is one day ahead of the
zero-based `NaiveDateTime`.
-/
def fromYmd
  (y : Year)
  (m : Month)
  (d : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
: NaiveDateTime siPow :=
  let oneBasedDay := (Ymd.mk y m d hd.left hd.right).toScalarDate.day
  let zeroBasedDay := oneBasedDay - 1
  let oneDay : SignedDuration siPow.val := SignedDuration.Constants.oneDayDuration _
  ⟨oneDay.val * zeroBasedDay⟩
  --⟨oneDay.val * ((Ymd.mk y m d hd.left hd.right).toScalarDate.day - 1)⟩


  --⟨(fromYmd y m d hd).val + (oneSecondval * s) + n⟩

instance instHAddSelfSignedDurationSelf :
  HAdd (NaiveDateTime siPow) (SignedDuration siPow) (NaiveDateTime siPow)
where
  hAdd da du := ⟨da.val + du.val⟩


@[default_instance]
instance instHAddSignedDurationSelfSelf :
  HAdd (SignedDuration siPow) (NaiveDateTime siPow) (NaiveDateTime siPow)
where
  hAdd du da := da + du

def toYmd (d : NaiveDateTime siPow) : Ymd := d.toScalarDate.toYmd

def fromYmdsn
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : SignedDuration 0)
  (n : SignedDuration (-9))
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
  (h2 : siPow.val <= -9)
: NaiveDateTime siPow :=
  let s' : SignedDuration siPow := s.convertLossless siPow.property
  let n' : SignedDuration siPow := n.convertLossless h2
  (fromYmd y m d hd : NaiveDateTime siPow) + s' + n'

instance instEquivIntSelf : Equiv Int (NaiveDateTime siPow) where
  toFun := mk
  invFun := val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.LeftInverse, Function.RightInverse]

theorem eq_of_val_eq : ∀ {d1 d2 : NaiveDateTime siPow},
  d1.val = d2.val → d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem val_eq_of_eq : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 = d2 → d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem eq_def : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 = d2 ↔ d1.val = d2.val
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem val_ne_of_ne : ∀ {d1 d2 : NaiveDateTime siPow},
  d1 ≠ d2 → d1.val ≠ d2.val
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg mk hh

instance instLT : LT (NaiveDateTime siPow) where
  lt := InvImage Int.lt val

instance instLE : LE (NaiveDateTime siPow) where
  le := InvImage Int.le val

@[simp] theorem le_def (d₁ d₂ : NaiveDateTime siPow) :
  (d₁ <= d₂) = (d₁.val <= d₂.val)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : NaiveDateTime siPow) :
  (d₁ < d₂) = (d₁.val < d₂.val)
:= rfl

instance instDecidableLENaiveDateTime (d₁ d₂ : NaiveDateTime siPow) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.val <= d₂.val)

instance instDecidableLTNaiveDateTime (d₁ d₂ : NaiveDateTime siPow) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.val < d₂.val)

instance instLinearOrder : LinearOrder (NaiveDateTime siPow) where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [le_def, le_total]
  decidableLE := inferInstance
  compare_eq_compareOfLessAndEq := by
    simp [compare, compareOfLessAndEq, lt_def, eq_def]

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

instance instOfNat {n : Nat} : OfNat (NaiveDateTime siPow) n where
  ofNat := ⟨n⟩


theorem hAdd_signed_def (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  d + dur = ⟨d.val + dur.val⟩
:= rfl
theorem hAdd_signed_def_rev (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  dur + d = ⟨d.val + dur.val⟩
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
  apply eq_of_val_eq
  simp [hSub_signed_def, hAdd_signed_def]
  apply Int.add_neg_cancel_right

theorem hAdd_signed_sub_add_cancel (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t - d + d = t
:= by
  simp [hSub_signed_def, hAdd_signed_def]
  exact eq_of_val_eq (Int.sub_add_cancel t.val d.val)

theorem hAdd_signed_comm (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t + d = d + t
:= by
  simp [hAdd_signed_def, hAdd_signed_def_rev]

def convertLossless
  {fine coarse : NegSiPow}
  (d : NaiveDateTime coarse)
  (h : fine <= coarse := by decide) :
  NaiveDateTime fine :=
    match coarse.val - fine.val, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val * (10 ^ n)⟩
    | Int.negSucc _, h_zero_le =>
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_of_sign_eq_neg_one rfl))

def convertLossless'
  {p : NegSiPow}
  (d : NaiveDateTime p)
  (tgt: NegSiPow) :
  NaiveDateTime (min p tgt) :=
  if h : p <= tgt
  then (min_eq_left h).symm ▸ d
  else d.convertLossless (min_le_left p tgt)


--instance instHAddSelfUnsignedDurationSelf :
--  HAdd (NaiveDateTime siPow) UnsignedDuration NaiveDateTime
--where
--  hAdd da du := ⟨da.nanos + du.val⟩
--
--instance instHAddUnsignedDurationSelfSelf :
--  HAdd UnsignedDuration NaiveDateTime NaiveDateTime
--where
--  hAdd du da := da + du
--
--theorem hAdd_unsigned_def (d : NaiveDateTime siPow) (dur : UnsignedDuration) :
--  d + dur = ⟨d.val + dur.val⟩
--:= rfl
--
--instance instHSubSelfUnsignedDurationSelf :
--  HSub NaiveDateTime UnsignedDuration NaiveDateTime
--where
--  hSub da du := ⟨da.nanos - du.val⟩
--
--theorem hSub_unsigned_def (d : NaiveDateTime) (dur : UnsignedDuration) :
--  d - dur = ⟨d.nanos - dur.val⟩
--:= rfl
--
--theorem hAdd_unsigned_sub_cancel (t : NaiveDateTime) (d : UnsignedDuration) :
--  t + d - d = t
--:= hAdd_signed_sub_cancel t d
--
--theorem hAdd_unsigned_sub_add_cancel
--  (t : NaiveDateTime) (d : UnsignedDuration)
--: t - d + d = t
--:= hAdd_signed_sub_add_cancel t d
--
--theorem hAdd_unsigned_comm (t : NaiveDateTime) (d : UnsignedDuration) :
--  t + d = d + t
--:= hAdd_signed_comm t d
--
--/--
--Set the clock time of the current day to `tgt`.
---/
--@[reducible]
--def setClockTime (t : NaiveDateTime) (clockTime : NaiveClockTime) :
--  NaiveDateTime
--:=
--  let days := (t.nanos.fdiv oneDayNanos) * oneDayNanos
--  ⟨days + clockTime.nanos.val⟩
