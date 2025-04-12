import Timelib.Util
import Timelib.DateTime.Naive
import Timelib.Duration.Constants
import Timelib.Duration.SignedDuration
import Std

namespace Timelib

/--
A time zone as an optional (long) name, a short identifier, and some offset
relative to UTC/Zulu.
-/
@[ext]
structure TimeZone where
  longIdent : Option String
  shortIdent : String
  fromZulu : SignedDuration 0
deriving DecidableEq, Hashable

namespace TimeZone

namespace TimeZone
theorem add_sub_cancel {siPow : Int} (z : TimeZone) (zulu : NaiveDateTime siPow) :
  zulu + (z.fromZulu.convertLossless zulu.isLe) - (z.fromZulu.convertLossless zulu.isLe) = zulu := by simp

theorem sub_add_cancel {siPow : Int} (z : TimeZone) (zulu : NaiveDateTime siPow) :
  zulu - (z.fromZulu.convertLossless zulu.isLe) + (z.fromZulu.convertLossless zulu.isLe) = zulu := by simp

@[reducible]
def Zulu : TimeZone := {
  longIdent := some "Zulu"
  shortIdent := "Z"
  fromZulu := 0
}

def Cst : TimeZone := {
  longIdent := some "Central Standard Time"
  shortIdent := "CST"
  fromZulu := -(SignedDuration.oneHour * (6 : Int))
}

def stdTimeZones : List TimeZone := [
  Zulu,
  Cst
]

def stdTimeZonesMap : Std.HashMap String TimeZone :=
  Std.HashMap.ofList <| stdTimeZones.map <| fun x => (x.shortIdent, x)
