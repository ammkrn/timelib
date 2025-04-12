import Lean
--import Timelib.Duration.SignedDuration

open Lean Elab Term Meta
namespace Timelib

def units: Array (String × String × Int) := #[
  ("quetta", "Q", 30),
  ("ronna", "R",  27),
  ("yotta", "Y",  24),
  ("zetta", "Z",  21),
  ("exa", "E",  18),
  ("peta", "P",  15),
  ("tera", "T",  12),
  ("giga", "G",  9),
  ("mega", "M",  6),
  ("kilo", "k",  3),
  ("hecto", "h",  2),
  ("deca", "da",  1),
  ("", "",  0),
  ("deci", "d", -1),
  ("centi", "c", -2),
  ("milli", "m", -3),
  ("micro", "μ", -6),
  ("nano", "n",   -9),
  ("pico", "p",  -12),
  ("femto", "f",  -15),
  ("atto", "a", -18),
  ("zepto", "z", -21),
  ("yocto", "y", -24),
  ("ronto", "r", -27),
  ("quecto", "q", -30)
]

def timeUnitLookup : Std.HashMap String Int := Id.run do
  let mut out := ∅
  for (long, short, val) in units do
    out := out.insert s!"{long}seconds" val
    out := out.insert s!"{short}s" val
  return out


--def siUnits___: String → Option Int
--  | "quetta" | "Q" => some 30
--  | "ronna" | "R" => some 27
--  | "yotta" | "Y" => some 24
--  | "zetta" | "Z" => some 21
--  | "exa" | "E" => some 18
--  | "peta" | "P" => some 15
--  | "tera" | "T" => some 12
--  | "giga" | "G" => some 9
--  | "mega" | "M" => some 6
--  | "kilo" | "k" => some 3
--  | "hecto" | "h" => some 2
--  | "deca" | "da" => some 1
--  | "" => some 0
--  | "deci" | "d" =>   some <| -1
--  | "centi" | "c" =>  some <| -2
--  | "milli" | "ms" => some <| -3
--  | "micro" | "μs" => some <| -6
--  | "nano" | "n" => some <| -9
--  | "pico" | "p" => some <| -12
--  | "femto" | "f" => some <| -15
--  | "atto" | "a" =>  some <| -18
--  | "zepto" | "z" => some <| -21
--  | "yocto" | "y" => some <| -24
--  | "ronto" | "r" => some <| -27
--  | "quecto" | "q" => some <| -30
--  | _ => none

def intToSiUnit? : (siPow : Int) → Option (String × String)
  | 30 | 29 | 28 => ("quetta", "Q")
  | 27 | 26 | 25 => ("ronna","R")
  | 24 | 23 | 22 => ("yotta","Y")
  | 21 | 20 | 19 => ("zetta","Z")
  | 18 | 17 | 16 => ("exa","E")
  | 15 | 14 | 13 => ("peta","P")
  | 12 | 11 | 10 => ("tera","T")
  | 9 | 8 | 7 =>  ("giga", "G")
  | 6 | 5 | 4 =>  ("mega", "M")
  | 3 =>  ("kilo", "k")
  | 2 =>  ("hecto", "h")
  | 1 =>  ("deca", "da")
  | 0 => ("", "")
  | -1 => ("deci", "d")
  | -2 => ("centi", "c")
  | -3 => ("milli", "m")
  | -6 | -7 | -8 => ("micro", "μ")
  | -9 | -10 | -11 =>  ("nano", "n")
  | -12 | -13 | -14 => ("pico", "p")
  | -15 | -16 | -17 => ("femto", "f")
  | -18 | -19 | -20 => ("atto", "a")
  | -21 | -22 | -23 => ("zepto", "z")
  | -24 | -25 | -26 => ("yocto", "y")
  | -27 | -28 | -29 => ("ronto", "r")
  | -30 => ("quecto", "q")
  | _ => none

--declare_syntax_cat duration_unit
--
--syntax "Qs" : duration_unit
--syntax "μs" : duration_unit
--syntax "microseconds" : duration_unit
--syntax "seconds" : duration_unit
--syntax "s" : duration_unit
--syntax "milliseconds" : duration_unit
--syntax "ms" : duration_unit
--
--def expandSiUnit : TermElab
--  | `(duration_unit| $x), _ => do
--    match x.raw with
--    | Syntax.node _ _ #[Syntax.atom _ val] =>
--      match timeUnitLookup.get? val with
--      | some val => pure <| toExpr val
--      | none => throwError "unsupported time notation: {val}"
--    | _ => throwError "unsupported time notation: {x}"
--
