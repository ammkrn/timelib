import Timelib.Date.Ymd
import Timelib.Duration.Constants
import Timelib.DateTime.HNaive
import Timelib.DateTime.LeapTable
import Timelib.DateTime.Naive
import Timelib.Duration.SignedDuration
import Timelib.DateTime.TimeZone

namespace Timelib

/-
The two approaches for dealing with the utcToTai conversion w.r.t.
displayed positive leap seconds are:

1.
  + Convert to scalar
  + remove the positive displayed leap seconds from the scalar
  + do the conversion, effectively matching on the "previous" row
  + add the positive displayed leap seconds back to the scalar

2.
  + Convert to scalar
  + When we do match a row, have another check to see if we're inside the leap second
  + If we are, use the `prevCumulative` value.


With the first one, you need to have picked off the number of positive leaps
from the parse phase; it's also harder to check whether the number of displayed
leaps is compliant with the relevant row.
-/

/--
Get the applicable leap second row, if it exists.

The "applicable leap second row" for a given time stamp is the most recently inserted
row which was inserted prior to the `utcStamp`.
-/
def utcToTaiRow?
  {siPow : Int}
  (utcStamp : NaiveDateTime siPow)
  (leapTable : List Row) : Option Row :=
  leapTable.find? <| fun hd =>
    utcStamp ≥ (hd.insertedAtUtc.convertLossless (h := utcStamp.isLe) : NaiveDateTime siPow)

/--
This is the "easier" but somehow weirder version where you account for
the possibility of being "in" a positive leap second by removing any seconds
over 60 before doing the leap table conversion, then re-add them.

It's a little bit weirder because it effectively uses the previous row.
-/
def utcToTaiPrev
  {siPow : Int}
  (utcWLeapSeconds : NaiveDateTime siPow)
  (positiveLeapsDisplayed : SignedDuration siPow)
  (leapTable : List Row) : NaiveDateTime siPow :=
  /- Only sees the timestamp with displayed positive leaps removed from the
  underlying scalar, so if we're "inside" a positive leap second we basically
  use the previous row. -/
  let rec utcToTaiAux
    {siPow : Int}
    (utcStamp : NaiveDateTime siPow)
    (leapTable : List Row) : NaiveDateTime siPow :=
    have _ := utcStamp.isLe
    match leapTable with
    | [] => utcStamp
    | hd :: tl =>
      if utcStamp ≥ (hd.insertedAtUtc.convertLossless : NaiveDateTime siPow)
      then utcStamp + (hd.cumulative.convertLossless : SignedDuration siPow)
      else utcToTaiAux utcStamp tl

  let utcWLeapSeconds := utcWLeapSeconds - positiveLeapsDisplayed
  let out := utcToTaiAux utcWLeapSeconds leapTable
  out + positiveLeapsDisplayed

/--
`utcWLeapSeconds`: The scalar date time represented by the UTC time stamp, INCLUDING
any positive leap seconds

`positiveLeapsDisplayed`: The positive leap seconds *displayed* in the UTC time stamp
(the amount of seconds and fractional seconds ≥ 60). This is needed to ensure that
the time stamp is compatible with the given leap table. Example

hh:mm:61 ~> positiveLeapsDisplayed = 2
hh:mm:59 ~> positiveLeapsdisplayed = 0

A UTC time stamp (the string) may be incompatible with a given leap table:
+ If a leap second is displayed when a corresponding leap second does not exist in the leap table
+ If a leap second is displayed longer than its listed duration in the leap table. For example,
  a leap table with no positive leap seconds greater than 1 second in duration is incompatible
  with a stamp showing `63` in the seconds position.
+ If a time is displayed which should be "skipped" due to a negative leap second; on insertion
  of a negative leap second, the clock face transitions from `58.99` directly to `00` of the
  subsequent minute.

In the unique case of an ongoing positive leap second, we need to do something sort of unintuitive, which
is to apply the PREVIOUS cumulative offset, because the argument `utcWLeapSeconds` will already
include any displayed positive leap seconds.
-/
/-
Even when it's UTC UTC, when you naively convert to a scalar,
23:59:60.1 and 00:00:00.1 corrrespond to the same naive UTC scalar, but the latter
corresponds to a timestamp that is NOT within a leap second, and is actually a second later.

So we add another check to `isInside` which requires the timer to be displaying
positive leap seconds.

This is separate from the other issue, because in this pathology, you end up
not adding ENOUGH of an offset if you just use `prevCumulative`.

This is basically another way of doing the thing where you remove the positive leaps
before doing the rest of the manipulation.

The other one, you remove the visibble leap seconds before, then convert to scalar,
then yyou jsut ddo the utcToTai straight up, and then you re-add the visible leap seconds.
-/
def utcToTai
  {siPow : Int}
  (utcWLeapSeconds : NaiveDateTime siPow)
  (positiveLeapsDisplayed : SignedDuration siPow)
  (leapTable : List Row) : Except String (NaiveDateTime siPow) :=
  have _ := utcWLeapSeconds.isLe
  match utcToTaiRow? utcWLeapSeconds leapTable with
  | none =>
    /-
      If no corresponding leap second is found, ensure that no leap second is reflected in
      the given time stamp
    -/
    if positiveLeapsDisplayed = 0
    then .ok utcWLeapSeconds
    /- Illegal because there's a 6X stamp, while the table has no corresponding leap second. -/
    else .error "Timestamp shows a positive leap second, but no corresponding leap second was found"
  | some row =>
    /-
    Whether we're "inside" a positive OR negative leap second.

    For a negative leap second, this works because it checks that
    (insertedAtUtc := 23:59:59) ≤ utcWLeap ∧ utcWLeaps < 24:00:00

    Which is exactly the error condition.

    For positive leap seconds...

    (insertedAtUtc := **23:59:60.0) ≤ utcWLeap ∧ utcWLeaps < **23:59:61.0
    -/
    let insideLeapSecond := (row.insertedAtUtc.convertLossless) ≤ utcWLeapSeconds
       ∧ utcWLeapSeconds < row.elapsesAt.convertLossless
    if row.duration ≥ 0
    then
      if insideLeapSecond ∧ positiveLeapsDisplayed ≠ 0
      then
        if positiveLeapsDisplayed > (row.duration.convertLossless)
        then .error "Positive leap seconds in time stamp exceed those allowed by leap table row"
        else .ok (utcWLeapSeconds + row.prevCumulative.convertLossless)
      else
        /- if it's not inside, shouldn't be showing 6X -/
        if positiveLeapsDisplayed ≠ 0
        then .error "Timestamp shows an ongoing positive leap second, but no matching leap second was found"
        else .ok (utcWLeapSeconds + row.cumulative.convertLossless)
    else
      if insideLeapSecond
      then .error s!"illegal negative leap second: t := {reprStr utcWLeapSeconds}, row := {reprStr row}"
      else .ok (utcWLeapSeconds + row.cumulative.convertLossless)


/--
Returns the corresponding row (if it exists) for a given TAI time. This ONLY finds
the corresponding row, if it exists; there still needs to be a check to determine
whether the current tai stamp is inside a positive leap second.

Implementation remarks:

1. Uses the sum of the insertion time and the previous cumulative offset to compare
   to a TAI time stamp instead of using an estimation/correction process relying only on the
   TAI insertion time.

2. Works for positive and negative leap seconds;
   @ (+2 -> +3), inserted at 62 tai, (60 + (3 - 1 = 2))
   @ (+5 -> +4), inserted at 65 tai, (59 + (4 - (-1)) = 64)
-/
def taiToUtcFindRow?
  {siPow : Int}
  (taiStamp: NaiveDateTime siPow)
  (leapTable : List Row) : Option Row :=
  have _ := taiStamp.isLe
  leapTable.find? <| fun hd =>
    taiStamp ≥ (hd.insertedAtUtc + (hd.cumulative - hd.duration)).convertLossless (fine := siPow)

/--
Determines whether this tai date time is within a positive leap second application,
and if so, returns the duration of that leap second (for the standard leap table, the duration
will either be 10 (the initial "big" offset), or 1).
-/
def ongoingPositiveLeapSecondDuration? {siPow : Int} (r : Row) (tai : NaiveDateTime siPow) : Option (SignedDuration siPow) :=
  have _ : siPow ≤ 0 := tai.isLe
  let insertedAtUtc := r.insertedAtUtc.convertLossless (fine := siPow)
  let duration := r.duration.convertLossless (fine := siPow)
  let cumulative := r.cumulative.convertLossless (fine := siPow)
  if (0 ≤ r.duration) ∧ (insertedAtUtc + (cumulative - duration) ≤ tai ∧ tai < insertedAtUtc + cumulative)
  then
    some (r.duration.convertLossless (fine := siPow))
  else
    none

/--
Returns a pair `(x, y)` where:

`x` is the utc time WITHOUT any positive ongoing leap seconds,
`y` is the duration of any ongoing positive leap seconds

These need to be returned separately because properly printing a UTC
time with ongoing positive leap seconds requires those to be added to the seconds
position in isolation, allowing it to grow to values ≥ 60 without overflowing into
the minutes position.
-/
def taiToUtc
  {siPow : Int}
  (taiStamp: NaiveDateTime siPow)
  (leapTable : List Row) : (NaiveDateTime siPow × Option (SignedDuration siPow)) :=
  match taiToUtcFindRow? taiStamp leapTable with
  | none => (taiStamp, none)
  | some row =>
    let utcWoOngoingPosLeaps := taiStamp - (row.cumulative.convertLossless (fine := siPow) (siPowLe := taiStamp.isLe))
    (utcWoOngoingPosLeaps, ongoingPositiveLeapSecondDuration? row taiStamp)

def printTaiAsUnix
  {siPow : Int}
  (taiStamp: NaiveDateTime siPow)
  (leapTable : List Row) : String :=
  let (l, r) := taiToUtc taiStamp leapTable
  let z := (l + r.getD 0).prolepticGregorianEpochToUnixEpoch
  s!"{z}"


structure ParseResult where
  isNegative: Bool
  year_ : Nat
  month : Nat
  day : Nat
  hours: Nat
  minutes: Nat
  /--
  The number of "whole" seconds, including any positive leap seconds,
  so this may be ≥ 60
  -/
  rawSeconds: Nat
  fractionalSeconds: Array Nat
  zone: SignedDuration 0
  hZone : zone.abs < ((SignedDuration.oneHour : SignedDuration 0) * (Int.ofNat 24))
deriving Repr

namespace ParseResult

def siPow (p : ParseResult) : Int :=
  Int.negOfNat p.fractionalSeconds.size

theorem siPow_le (p : ParseResult) : p.siPow ≤ 0 := by
  simp only [siPow, Int.negOfNat_eq, Int.ofNat_eq_coe]; omega

def fractionalSecondsDuration (p : ParseResult) : SignedDuration p.siPow :=
  ⟨p.fractionalSeconds.foldl (init := 0) (fun sink next => (sink * 10) + (Int.ofNat next))⟩

def rawSecondsDuration (p : ParseResult) : SignedDuration p.siPow :=
  have _ := p.siPow_le
  (SignedDuration.oneSecond : SignedDuration p.siPow) * (Int.ofNat p.rawSeconds)

/--
Turn e.g. `rawSeconds := 10, fracitonalSeconds := [0, 7, 9]`
into `10079`
-/
def completeSecondsWFractional (p : ParseResult) : Nat := Id.run do
  let mut out := p.rawSeconds
  for digit in p.fractionalSeconds do
    out := (10 * out) + digit
  return out

def secondsWithFractional (p : ParseResult) : (Nat × Nat) := Id.run do
  let mut out := p.rawSeconds
  for digit in p.fractionalSeconds do
    out := (10 * out) + digit
  return (out, (p.rawSeconds - 59) * (10 ^ p.siPow.natAbs))

/--
From a `ParseResul`, yield a `NaiveDateTime` showing the UTC date time, meaning
the time zone offset (if any) is unapplied, but any leap seconds reflected in the
string time stamp are reflected in the `NaiveDateTime`

Returns `none` if any component is invalid, for example if the month is an invalid month
-/
def toUTCDateTime (p : ParseResult) : Option (NaiveDateTime p.siPow) :=
  let local_ := NaiveDateTime.fromYmdhms?
    (if p.isNegative then Int.neg p.year_ else Int.ofNat p.year_)
    p.month
    p.day
    p.hours
    p.minutes
    p.completeSecondsWFractional
    (siPow := p.siPow)
  local_.map (fun x => x - p.zone.convertLossless x.isLe)

/--
Try to convert a parse result to a TAI `NaiveDateTime`.
-/
def toNaiveDateTime? (p : ParseResult) (leapTable : List Row) : Except String (NaiveDateTime p.siPow) :=
/- `positiveLeap` here is just anything 60+ in the time stamp's string -/
 let (secs, positiveLeap) := p.secondsWithFractional
 let naiveUtcWPosLeaps := p.toUTCDateTime
 match  naiveUtcWPosLeaps with
 | none => .error "failed to gget naiveUtcWPosLeaps"
 | some naiveUtcWPosLeaps =>
   (utcToTai naiveUtcWPosLeaps (⟨positiveLeap⟩ : SignedDuration p.siPow) leapTable)

end ParseResult

def tryNeg : Std.Internal.Parsec.String.Parser Bool := do
  if (← Std.Internal.Parsec.peek?) == some '-' then
    Std.Internal.Parsec.String.skipChar '-'
    return true
  else
    return false

def manyNat : Std.Internal.Parsec.String.Parser (Array Nat) := do
  let digits ← Std.Internal.Parsec.many Std.Internal.Parsec.String.digit
  return digits.map (·.toNat - '0'.toNat)

def parseNDigits (n : Nat) : Std.Internal.Parsec.String.Parser Nat := do
  let mut out := 0
  for _ in [0:n] do
    let c := (← Std.Internal.Parsec.satisfy Char.isDigit)
    out := (10 * out) + (c.toNat - '0'.toNat)
  return out

def fractionalTime : Std.Internal.Parsec.String.Parser (Nat × Int) := do
  if (← Std.Internal.Parsec.peek?) == some '.' then
    Std.Internal.Parsec.String.skipChar '.'
    let digits ← Std.Internal.Parsec.many1 (Std.Internal.Parsec.String.digit)
    let siPow := Int.neg digits.size
    let mut seconds := 0
    for elem in digits do
      seconds := (seconds * 10) + elem.toNat - '0'.toNat
    return (seconds, siPow)
  else
    return (0, 0)

def fmtTimeZoneOffset
  (zoneOffset : SignedDuration 0)
  (_ : zoneOffset < (SignedDuration.oneHour : SignedDuration 0) * (Int.ofNat 24)) : String :=
  if zoneOffset = 0
  then "Z"
  else
    let hours := zoneOffset.val / (SignedDuration.oneHour : SignedDuration 0).val.natAbs
    let minutes := (zoneOffset.val % (SignedDuration.oneHour : SignedDuration 0).val) / (SignedDuration.oneMinute : SignedDuration 0).val.natAbs
    let hh := s!"{hours.natAbs}".toList.leftpad 2 '0'
    let mm := s!"{minutes.natAbs}".toList.leftpad 2 '0'
    String.mk <| (if zoneOffset ≥ 0 then '+' else '-') :: (hh ++ mm)

def printTaiAsUtc
  {siPow : Int}
  (t : NaiveDateTime siPow)
  (leapTable : List Row)
  (zoneOffset : SignedDuration 0)
  (_ : zoneOffset < (SignedDuration.oneHour : SignedDuration 0) * (Int.ofNat 24))
  : String :=
  let (utc, ongoingPositiveLeaps) := taiToUtc t leapTable
  let local_ := utc + zoneOffset.convertLossless utc.isLe

  let (ymd, s):= local_.toYmds
  let oneHour := (SignedDuration.oneHour (siPow_le := t.isLe) : SignedDuration siPow).val
  let oneMinute := (SignedDuration.oneMinute (siPow_le := t.isLe) : SignedDuration siPow).val
  let yyyy := String.mk <| s!"{ymd.year}".data.leftpad 4 '0'
  let mm :=   String.mk <| s!"{ymd.month.toNat}".data.leftpad 2 '0'
  let dd :=   String.mk <| s!"{ymd.day}".data.leftpad 2 '0'
  let hh :=   String.mk <| s!"{s.val / oneHour}".data.leftpad 2 '0'
  let mi :=   String.mk <| s!"{((s.val % oneHour)) / oneMinute}".data.leftpad 2 '0'
  let ss := ((s.val % oneMinute))
  let ss := ss + (ongoingPositiveLeaps.getD 0).val
  let fractionalLength := siPow.natAbs
  let ss_str := String.mk <| (s!"{ss}".data.leftpad (2 + fractionalLength) '0').insertIdx 2 '.'
  s!"{yyyy}{mm}{dd}T{hh}{mi}{ss_str}{fmtTimeZoneOffset zoneOffset ‹_›}"

def parseTimeZoneDesignatorZulu : Std.Internal.Parsec.String.Parser (SignedDuration 0) := do
  Std.Internal.Parsec.String.skipChar 'Z'
  return 0

-- `±hh(mm)?`
def parseTimeZoneDesignatorOwise : Std.Internal.Parsec.String.Parser (SignedDuration 0) := do
  let sign ← Std.Internal.Parsec.satisfy (fun c => c == '+' || c == '-')
  let hh ← parseNDigits 2
  --if (← Std.Internal.Parsec.peek?) == some ':' then Std.Internal.Parsec.String.skipChar ':'
  let mm ← (parseNDigits 2) <|> (pure 0)
  let raw : SignedDuration 0 := (SignedDuration.oneHour (siPow := 0) * (Int.ofNat hh)) + (SignedDuration.oneMinute (siPow := 0) * (Int.ofNat mm))
  return (if sign == '-' then -raw else raw)

def parseTimeZoneDesignator : Std.Internal.Parsec.String.Parser (SignedDuration 0) := do
  parseTimeZoneDesignatorZulu <|> parseTimeZoneDesignatorOwise <|> pure 0

/--
Parse an ISO 8601 basic time stamp as a `ParseResult`
-/
def parseIso8601DateTime : Std.Internal.Parsec.String.Parser ParseResult := do
  let fractional : Std.Internal.Parsec.String.Parser (Array Nat) := do
    if (← Std.Internal.Parsec.peek?) == some '.'
    then
      Std.Internal.Parsec.String.skipChar '.'
      manyNat
    else
      return #[]
  let isNegative ← tryNeg
  let year ← parseNDigits 4
  let month ← parseNDigits 2
  let day ← parseNDigits 2
  let _ ← Std.Internal.Parsec.String.skipChar 'T'
  let hours ← parseNDigits 2
  let minutes ← parseNDigits 2
  let rawSeconds ← parseNDigits 2
  let fractionalSeconds ← fractional
  let zone ← parseTimeZoneDesignator --Std.Internal.Parsec.manyChars (Std.Internal.Parsec.String.asciiLetter)
  if hZone : zone.abs < (SignedDuration.oneHour * (Int.ofNat 24))
  then
    return {
      isNegative
      year_ := year
      month
      day
      hours
      minutes
      rawSeconds
      fractionalSeconds
      zone
      hZone
    }
  else
    Std.Internal.Parsec.fail "time zone offsets may not exceed +- 24 hours"

def parseIso8601DateTime'' (table : List Row) (s : String) : Except String (HNaiveDateTime) :=
  match parseIso8601DateTime.run s with
  | .error msg => throw msg
  | .ok x =>
    (x.toNaiveDateTime? table).map HNaiveDateTime.ofNaiveDateTime

def parseUnixAsTai' (unix : Int) (leapTable : List Row) : Except String (NaiveDateTime 0) :=
  let val := unix + (NaiveDateTime.unixEpoch (siPow := 0)).val
  let t : NaiveDateTime 0 := ⟨⟨val⟩, by decide⟩
  utcToTai t 0 leapTable

def parseUnixAsTai (unix : String) (leapTable : List Row) : Except String (NaiveDateTime 0) :=
  let parseUnixAsTaiAux : Std.Internal.Parsec.String.Parser Int := do
    let isNegative ← tryNeg
    let out ← Std.Internal.Parsec.String.digits
    return if isNegative then Int.negOfNat out else Int.ofNat out
  match parseUnixAsTaiAux.run unix with
  | .error msg => throw msg
  | .ok x => parseUnixAsTai' x leapTable
