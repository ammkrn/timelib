import Timelib.Duration.SignedDuration
import Timelib.Duration.Constants
import Timelib.DateTime.Naive
import Timelib.DateTime.LeapTable
import Timelib.DateTime.Parse

open Timelib

def negTable1 : List Row :=
  mkTable [
  ⟨(⟨⟨2272060800 - 10⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-10⟩, by decide⟩,
  ⟨(⟨⟨2287785600 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2303683200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2335219200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2366755200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
 ]

def negTable2 : List Row :=
  mkTable [
  ⟨(⟨⟨2272060800 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2287785600 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2303683200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2335219200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
  ⟨(⟨⟨2366755200 - 1⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨-1⟩, by decide⟩,
 ]

def ckTai (table : List Row) (tai : NaiveDateTime 0) : Bool :=
  let printed := printTaiAsUtc tai table 0 (by decide)
  match parseIso8601DateTime'' table printed with
  | .error _ => false
  | .ok parsed =>
    if h : parsed.siPow = 0
    then
      let parsed := h ▸ parsed.toNaiveDateTime
      let printed' := printTaiAsUtc parsed table 0 (by decide)
      tai == parsed && parsed != ⟨0, by decide⟩
    else
      false

def doTest2 (table : List Row) : Bool := Id.run do
  let mut cks : Array (NaiveDateTime 0 × Bool) := #[]
  for row in table do
    if row.duration < 0
    then
      /-
      For negative leap seconds, we can't convert the initial leap second
      time stamp to UTC since it's not technically valid.
      -/
      let gap := row.duration.abs
      let baseBelow ←
        match (utcToTai (row.insertedAtUtc - gap) 0 table) with
        | .error _ => return false
        | .ok x => x
      let baseAbove ←
        match (utcToTai (row.insertedAtUtc + gap) 0 table) with
        | .error _ => return false
        | .ok x => x

      for i in [0:60] do
        let result := ckTai table (baseAbove + (⟨i⟩ : SignedDuration 0))
        cks := cks.push (row.insertedAtUtc, result)
        let result := ckTai table (baseBelow - (⟨i⟩ : SignedDuration 0))
        cks := cks.push (row.insertedAtUtc, result)
    else
      let base ←
        match (utcToTai row.insertedAtUtc 0 table) with
        | .error _ => return false
        | .ok x => x

      for i in [0:60] do
        let result := ckTai table (base + (⟨i⟩ : SignedDuration 0))
        cks := cks.push (row.insertedAtUtc, result)
        let result := ckTai table (base - (⟨i⟩ : SignedDuration 0))
        cks := cks.push (row.insertedAtUtc, result)
  return cks.size > 0 && (cks.all Prod.snd)

/-- info: true -/
#guard_msgs in
#eval doTest2 LeapTable.baseTable

/-- info: true -/
#guard_msgs in
#eval doTest2 negTable1

/-- info: true -/
#guard_msgs in
#eval doTest2 negTable2

/-- info: true -/
#guard_msgs in
#eval LeapTable.WF negTable1

/-- info: true -/
#guard_msgs in
#eval LeapTable.WF negTable2

/-- info: true -/
#guard_msgs in
#eval LeapTable.WF LeapTable.baseTable
