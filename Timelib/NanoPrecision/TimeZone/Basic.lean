import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration

structure TimeZone where
  name : String
  abbreviation : String
  offset : SignedDuration

def TimeZone.UTC : TimeZone := {
  name := "Coordinated Universal Time"
  abbreviation := "UTC"
  offset := 0
}

def TimeZone.CST : TimeZone := {
  name := "Central Standard Time"
  abbreviation := "CST"
  offset := SignedDuration.fromHours (-6)
}

