import Timelib.Duration.Constants
import Timelib.Duration.SignedDuration
import Timelib.Date.Scalar
import Timelib.Date.Month
import Timelib.Date.Ymd
import Timelib.Date.Convert

namespace Timelib

/--
A date and time in the proleptic Gregorian calendar. We refer to a type as "Naive"
if it is unaware of time zones, leap seconds, or other offsets/adjustments.

The epoch is midnight on 1 January of the year 0 (0001/01/01 00:00:00)

+ Nonnegative values represent the number of SI time units since the epoch

+ Negative values represent the number of SI time units until the epoch.
-/
@[ext]
structure NaiveDateTime (p : Int) extends SignedDuration p where
  /--
  `p` remains an integer for compatability with the rest of the library,
  but we do not allow `p` to be less than zero. A date time cannot be a lower resolution
  than "seconds", the base SI unit, because that would allow construction of datetimes
  that are ambiguous with respect to date.
  -/
  isLe : p <= 0
deriving DecidableEq, Hashable, Repr


namespace NaiveDateTime

variable {siPow : Int}

def ofSigedDuration
  (duration : SignedDuration siPow)
  (siPowLe : siPow ≤ 0 := by smesh) : NaiveDateTime siPow :=
  ⟨duration, siPowLe⟩

instance : Inhabited (NaiveDateTime 0) where
  default := ⟨0, by decide⟩
/-

Using `Int.fdiv`, because we have a positive denominator (the number of seconds in a day)
and we want to round down if `dt.val` is negative, up if it's nonnegative.

The intuition here is that the number representing where we are relative to the epoch is 0-based
(the number of unit since the epoch), but the Gregorian date itself is 1-based (the first day beginning
with the start of the epoch is day 1).

So:
the date as of 20 seconds since the Gregorian epoch is day 1.
the date as of 20 seconds until the Gregorian epoch is day 0.

Equivalently, we could round toward zero and only add `1` if the
quotient is greater than or equal to zero.
-/
def toScalarDate (dt : NaiveDateTime siPow) : ScalarDate :=
  let zeroBasedDay := dt.val / (SignedDuration.oneDay dt.isLe).val
  ⟨zeroBasedDay + 1⟩

private def toScalarDateEDiv (dt : NaiveDateTime siPow) : ScalarDate :=
  let zeroBasedDay := dt.val.ediv (SignedDuration.oneDay dt.isLe).val
  ⟨zeroBasedDay + 1⟩

private theorem toScalarDate_eq_ediv : @toScalarDate = @toScalarDateEDiv := by
  funext siPow dt;
  simp [toScalarDate, toScalarDateEDiv]
  simp [Int.div_def]

private def toScalarDateFDiv (dt : NaiveDateTime siPow) : ScalarDate :=
  let zeroBasedDay := dt.val.fdiv (SignedDuration.oneDay dt.isLe).val
  ⟨zeroBasedDay + 1⟩

private theorem fdiv_eq_ediv : @toScalarDateFDiv = @toScalarDateEDiv := by
  funext siPow dt;
  simp [toScalarDateFDiv, toScalarDateEDiv]
  have h0 : 0 <= (SignedDuration.oneDay dt.isLe).val := SignedDuration.zero_le_oneDay _
  simp [(Int.fdiv_eq_ediv_of_nonneg dt.val h0), Int.div_def]

def toYmd (dt : NaiveDateTime siPow) : Ymd := dt.toScalarDate.toYmd

def toYmds (dt : NaiveDateTime siPow) : (Ymd × SignedDuration siPow) :=
  let d := dt.toScalarDate
  let t := dt.val % (SignedDuration.oneDay (siPow_le := dt.isLe) : SignedDuration siPow).val
  (d.toYmd, ⟨t⟩)


def toYmdsLeap (dt : NaiveDateTime siPow) (isLeap : Bool) : (Ymd × SignedDuration siPow) :=
  let d := dt.toScalarDate
  if isLeap
  then
    let t := SignedDuration.oneDay dt.isLe
    ((d.subDays 1).toYmd, t)
  else
    let t := dt.val % (SignedDuration.oneDay (siPow_le := dt.isLe) : SignedDuration siPow).val
    (d.toYmd, ⟨t⟩)

instance instInhabited (p : Int) (isLe : p <= 0 := by smesh) : Inhabited (NaiveDateTime p) where
  default := ⟨Inhabited.default, isLe⟩

def dayOfWeek (dt : NaiveDateTime siPow) : Int :=
  dt.toScalarDate.dayOfWeek

/--
The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd. We
subtract one to account for the fact that `Date` is one day ahead of the
zero-based `NaiveDateTime`.
-/
def fromYmd
  {p : Int}
  (y : Year)
  (m : Month)
  (d : Nat)
  (dayGe : d ≥ 1 := by smesh)
  (dayLe : d ≤ m.numDays y := by smesh)
  (isLe : p ≤ 0 := by smesh) : NaiveDateTime p :=
  let oneBasedDay := (Ymd.mk y m d dayGe dayLe).toScalarDate.day
  let zeroBasedDay := oneBasedDay - 1
  let oneDay : SignedDuration p := SignedDuration.oneDay isLe
  ⟨⟨oneDay.val * zeroBasedDay⟩, isLe⟩

--@[default_instance]
instance instHAddSelfSignedDurationSelf :
  HAdd (NaiveDateTime siPow) (SignedDuration siPow) (NaiveDateTime siPow)
where
  hAdd da du := ⟨da.toSignedDuration + du, da.isLe⟩

theorem instHAddSelfSignedDurationSelf_def
  (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
    t + d = ⟨t.toSignedDuration + d, t.isLe⟩ := by simp [instHAddSelfSignedDurationSelf]

--@[default_instance]
instance instHAddSignedDurationSelfSelf :
  HAdd (SignedDuration siPow) (NaiveDateTime siPow) (NaiveDateTime siPow)
where
  hAdd du da := da + du

theorem instHAddSignedDurationSelfSelf_def
  (d : SignedDuration siPow)
    (t : NaiveDateTime siPow) :
    d + t = ⟨t.toSignedDuration + d, t.isLe⟩ := by
    simp [instHAddSignedDurationSelfSelf, instHAddSelfSignedDurationSelf_def]

def fromYmds
  {p : Int} (y : Year) (m : Month) (d : Nat) (s : SignedDuration p)
  (dayGe : d ≥ 1 := by decide)
  (dayLe : d ≤ m.numDays y := by decide)
  (isLe : p ≤ 0 := by decide) : NaiveDateTime p :=
  (fromYmd y m d dayGe dayLe isLe : NaiveDateTime p) + s

def fromYmds?
  {p : Int}
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : SignedDuration p) : Option (NaiveDateTime p) :=
  if h : d ≥ 1 ∧ d ≤ m.numDays y ∧ p ≤ 0
  then
    some (fromYmds y m d s h.left h.right.left h.right.right)
  else
    none

def fromYmdhms?
  {siPow : Int}
  (y : Int)
  (m : Nat)
  (d : Nat)
  (hh : Nat)
  (mm : Nat)
  (ss : Nat) : Option (NaiveDateTime siPow) :=
  if hm : 1 ≤ m ∧ m ≤ 12 ∧ siPow ≤ 0
  then
    let y : Year := ⟨y⟩
    let m : Month := ⟨m, hm.left, hm.right.left⟩
    if h : siPow ≤ 0 ∧ 1 ≤ d ∧ d ≤ m.numDays y ∧ hh < 24
      ∧ mm < 60
      ∧ (0 : SignedDuration 0).convertLossless (fine := siPow) hm.right.right < (⟨61⟩ : SignedDuration siPow)
    then
      let hh : SignedDuration siPow := SignedDuration.oneHour h.left * (Int.ofNat hh)
      let mm : SignedDuration siPow := SignedDuration.oneMinute h.left * (Int.ofNat mm)
      let ss : SignedDuration siPow := ⟨ss⟩
      fromYmds y m d (hh + mm + ss) h.right.left h.right.right.left h.left
    else
      none
  else
    none

def incrementDayBy (date : NaiveDateTime siPow) (numDays : Nat) : NaiveDateTime siPow :=
  date + ((SignedDuration.oneDay date.isLe : SignedDuration siPow) * (Int.ofNat numDays))

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

theorem lt_of_not_ge (d₁ d₂ : NaiveDateTime siPow) :
  ¬d₁ ≤ d₂ → d₂ < d₁ := by
  simp [le_def, lt_def, SignedDuration.le_def, SignedDuration.lt_def]

theorem not_lt_of_le (d₁ d₂ : NaiveDateTime siPow) :
  d₁ ≤ d₂ → ¬(d₂ < d₁) := by
  simp [le_def, lt_def, SignedDuration.le_def, SignedDuration.lt_def]

theorem lt_of_lt_of_le {d₁ d₂ d₃ : NaiveDateTime siPow} :
  d₁ < d₂ → d₂ ≤ d₃ → d₁ < d₃ := by
  simp [le_def, lt_def, SignedDuration.le_def, SignedDuration.lt_def]
  omega

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

instance instMinNaiveDateTime {siPow : Int} : Min (NaiveDateTime siPow) := minOfLe

theorem le_refl (l : NaiveDateTime siPow) : l ≤ l := by simp [SignedDuration.le_def]; done

theorem ne_of_not_le {l r : NaiveDateTime siPow} : ¬(l ≤ r) → l ≠ r := by
  intro hf hff
  exact False.elim ((hff ▸ hf) (le_refl r))

theorem not_le_of_lt {l r : NaiveDateTime siPow} : l < r → ¬(r ≤ l) := by
  simp [NaiveDateTime.le_def, SignedDuration.le_def, NaiveDateTime.lt_def, SignedDuration.lt_def]

theorem min_def {l r : NaiveDateTime siPow} : Min.min l r = (if l ≤ r then l else r) := by
  unfold Min.min
  simp [instMinNaiveDateTime, minOfLe]

theorem min_eq_iff {l r : NaiveDateTime siPow} : (Min.min l r = l) ↔ l ≤ r := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    simp only [min_def]
    by_cases hle : l ≤ r
    case pos => simp [hle]
    case neg =>
      have hf := (ne_of_not_le hle).symm
      simp [hle, hf]
      done
  case mpr =>
    intro hle
    simp [min_def, hle]
    done

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

theorem hAdd_signed_def (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  d + dur = ⟨d.toSignedDuration + dur, d.isLe⟩
:= rfl
theorem hAdd_signed_def_rev (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  dur + d = ⟨d.toSignedDuration + dur, d.isLe⟩ := rfl

instance instHSubSelfSignedDurationSelf :
  HSub (NaiveDateTime siPow) (SignedDuration siPow) (NaiveDateTime siPow)
where
  hSub t dur := t + -dur

theorem hSub_signed_def (d : NaiveDateTime siPow) (dur : SignedDuration siPow) :
  d - dur = d + -dur := rfl

@[simp]
theorem hAdd_signed_sub_cancel (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t + d - d = t := by
  ext
  simp only [hAdd_signed_def, hSub_signed_def]
  exact Int.add_neg_cancel_right t.toSignedDuration.val d.val

@[simp]
theorem hAdd_signed_sub_add_cancel (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t - d + d = t := by
  ext
  simp only [hSub_signed_def, hAdd_signed_def]
  exact Int.neg_add_cancel_right t.toSignedDuration.val d.val

theorem hAdd_signed_comm (t : NaiveDateTime siPow) (d : SignedDuration siPow) :
  t + d = d + t := by simp only [hAdd_signed_def, hAdd_signed_def_rev]

@[simp]
theorem hAdd_zero (d : NaiveDateTime siPow) : d + (0 : SignedDuration siPow) = d := by
  simp [hAdd_signed_def, SignedDuration.add_zero]

@[simp]
theorem zero_hAdd (d : NaiveDateTime siPow) : (0 : SignedDuration siPow) + d = d := by
  simp [← hAdd_signed_comm, hAdd_zero]

theorem hAdd_signed_assoc (d : NaiveDateTime siPow) (dur₁ dur₂ : (SignedDuration siPow)) :
  d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp only [hAdd_signed_def, mk.injEq, SignedDuration.add_def, SignedDuration.mk.injEq]
  exact Int.add_assoc d.toSignedDuration.val dur₁.val dur₂.val

theorem hAdd_lt_hAdd_right (inserted stamp : NaiveDateTime 0) (cumulative : SignedDuration 0) :
  inserted < stamp → inserted + cumulative < stamp + cumulative := by
  simp only [lt_def, SignedDuration.lt_def, hAdd_signed_def, SignedDuration.add_def]
  exact fun a => Int.add_lt_add_right a cumulative.val

theorem hAdd_le_hAdd_right (inserted stamp : NaiveDateTime 0) (cumulative : SignedDuration 0) :
  inserted ≤ stamp → inserted + cumulative ≤ stamp + cumulative := by
  simp only [le_def, SignedDuration.le_def, hAdd_signed_def, SignedDuration.add_def]
  exact fun a => Int.add_le_add_right a cumulative.val

theorem le_hSub_right_of_hAdd_le (a c : NaiveDateTime 0) (b : SignedDuration 0) :
  a + b ≤ c → a ≤ c - b := by
  simp only [hAdd_signed_def, le_def, SignedDuration.le_def, hSub_signed_def]
  exact Int.le_sub_right_of_add_le

instance (siPow : Int) : HSub (NaiveDateTime siPow) (NaiveDateTime siPow) (SignedDuration siPow) where
  hSub a b := a.toSignedDuration - b.toSignedDuration

def convertLossless
  {fine coarse : Int}
  (d : NaiveDateTime coarse)
  (h : fine <= coarse := by smesh) :
  NaiveDateTime fine :=
    ⟨d.toSignedDuration.convertLossless h, Int.le_trans h d.isLe⟩

def eConvertLossy
  {fine coarse : Int}
  (d : NaiveDateTime fine)
  (isLe : coarse ≤ 0 := by smesh)
  (_ : fine <= coarse := by smesh) : NaiveDateTime coarse :=
   ⟨⟨d.val.ediv (10 ^ (coarse - fine).natAbs)⟩, isLe⟩

def le_het {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) : Prop :=
  d1.toSignedDuration.le_het d2.toSignedDuration

def lt_het {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) : Prop :=
  d1.toSignedDuration.lt_het d2.toSignedDuration

instance instDecidableLEHet {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) :
  Decidable (le_het d1 d2) :=
  inferInstanceAs <| Decidable <| d1.toSignedDuration.le_het d2.toSignedDuration

instance instDecidableLTHet {p1 p2 : Int} (d1 : NaiveDateTime p1) (d2 : NaiveDateTime p2) :
  Decidable (lt_het d1 d2) :=
  inferInstanceAs <| Decidable <| d1.toSignedDuration.lt_het d2.toSignedDuration

/--
The NTP epoch: 1 January 1900.
-/
def ntpEpoch {p : Int} (isLe : p ≤ 0 := by smesh) : NaiveDateTime p :=
  NaiveDateTime.fromYmd ⟨1900⟩ 1 1

/--
Unix time:
"It measures time by the number of non-leap seconds that have elapsed
since 00:00:00 UTC on 1 January 1970, the Unix epoch. For example,
at midnight on 1 January 2010, Unix time was 1262304000. "

When descriptions say unix time is "ignoring leap seconds", what they mean is that the
UTC time stamps from during and after a positive leap second:

YYYY-MM-DD   23:59:60
YYYY-MM-DD+1 00:00:00

Are converted to equivalent unix timestamps, because they're calculated by just
multiplying and adding the cumulative durations.

They do NOT mean that leap seconds have no effect on the unix time.
-/
def unixEpoch {siPow : Int} (siPowLe : siPow ≤ 0 := by smesh) : NaiveDateTime siPow :=
  NaiveDateTime.fromYmd ⟨1970⟩ 1 1

/--
The epoch for the proleptic Gregorian calendar: 1 January 1
-/
def prolepticGregorianEpoch {p : Int} (isLe : p ≤ 0 := by smesh) : NaiveDateTime p :=
  NaiveDateTime.fromYmd ⟨1⟩ 1 1

/--
Convert a dateTime defined in terms of the NTP epoch to an equivalent DateTime
expressed in terms of the proleptic Gregorian epoch.
-/
def ntpEpochToProlepticGregorianEpoch {p : Int} (d : NaiveDateTime p) : NaiveDateTime p :=
  d + (ntpEpoch d.isLe).toSignedDuration

def unixEpochToProlepticGregorianEpoch {p : Int} (d : NaiveDateTime p) : NaiveDateTime p :=
  d + (unixEpoch d.isLe).toSignedDuration

def prolepticGregorianEpochToUnixEpoch (d : NaiveDateTime siPow) : Int :=
  d.val - (unixEpoch (siPow := 0)).val

end NaiveDateTime
