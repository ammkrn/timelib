namespace Timelib

/-
A two's complement representation of signed integers, implemented as a struct pulling back
on the prelude's signed integer types. For example, the relationship between
unsigned (UInt8) and signed (Int8) is:

unsigned (UInt8) : 0, 1 ............ 127,  128 ............ 254, 255
signed   (Int8)  : 0, 1 ............ 127, -128 ............  -2, -1
-/
structure Int8 where
  val : UInt8
deriving DecidableEq


def Int8.ofNat (n : Nat) : Int8 := ⟨OfNat.ofNat n⟩

instance (n : Nat) : OfNat Int8 n := ⟨Int8.ofNat n⟩

def Int8.neg : Int8 -> Int8
| ⟨⟨a, isLt⟩⟩ => ⟨(UInt8.size - a) % UInt8.size, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) isLt)⟩

instance : Neg Int8 := ⟨Int8.neg⟩

def Int8.max : Int8 := 127
def Int8.min : Int8 := -128

theorem Int8.eq_of_val_eq : ∀ {a b : Int8}, a.val = b.val -> a = b
| ⟨_⟩, _, rfl => rfl

theorem Int8.ne_of_val_ne : ∀ {a b : Int8}, a.val ≠ b.val -> a ≠ b
| _, _, h => fun a_eq_b => Int8.noConfusion a_eq_b h

theorem Int8.val_eq_of_eq : ∀ {a b : Int8}, a = b -> a.val = b.val
| ⟨_⟩, _, rfl => rfl

theorem Int8.val_ne_of_ne : ∀ {a b : Int8}, a ≠ b -> a.val ≠ b.val
| _, _, h => fun h' => absurd (Int8.eq_of_val_eq h') h

def Int8.isPositive (a : Int8) : Bool := a.val.val < (UInt8.size / 2)

def Int8.isNegative (a : Int8) : Bool := ¬a.isPositive

def Int8.toInt (a : Int8) : Int :=
  if a.isPositive
  then Int.ofNat a.val.toNat
  else Int.subNatNat a.val.toNat UInt8.size

def Int8.toString (a : Int8) : String := s!"{a.toInt}"

instance : ToString Int8 := ⟨Int8.toString⟩


def Int8.ofInt : Int -> Int8
| Int.ofNat n => Int8.ofNat n
| Int.negSucc n => -(Int8.ofNat n.succ)

def Int8.modn (a : Int8) (n : Nat) : Int8 := Int8.ofInt <| a.toInt % (Int.ofNat n)

def Int8.shiftLeft (a b : Int8) : Int8 := ⟨a.val.shiftLeft b.val⟩

def Int8.shiftRight (a b : Int8) : Int8 := ⟨a.val.shiftRight b.val⟩

def Int8.land (a b : Int8) : Int8 := ⟨a.val.land b.val⟩

def Int8.lor (a b : Int8) : Int8 := ⟨a.val.lor b.val⟩

def Int8.xor (a b : Int8) : Int8 := ⟨a.val.xor b.val⟩

instance : HMod Int8 Nat Int8 := ⟨Int8.modn⟩
instance : AndOp Int8     := ⟨Int8.land⟩
instance : OrOp Int8      := ⟨Int8.lor⟩
instance : Xor Int8       := ⟨Int8.xor⟩
instance : ShiftLeft Int8  := ⟨Int8.shiftLeft⟩
instance : ShiftRight Int8 := ⟨Int8.shiftRight⟩

def Int8.add : Int8 -> Int8 -> Int8
| ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

instance : Add Int8 := ⟨Int8.add⟩

def Int8.sub (a b : Int8) : Int8 := a + -b

def Int8.mul : Int8 -> Int8 -> Int8
| ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

def Int8.mod (a m : Int8) : Int8 := Int8.ofInt (a.toInt % m.toInt)

def Int8.div (a b : Int8) : Int8 := Int8.ofInt (a.toInt / b.toInt)

instance : Sub Int8 := ⟨Int8.sub⟩

instance : Mul Int8 := ⟨Int8.mul⟩

instance : Mod Int8 := ⟨Int8.mod⟩

instance : Div Int8 := ⟨Int8.div⟩

def Int8.le (a b : Int8) : Prop := a.toInt <= b.toInt
def Int8.lt (a b : Int8) : Prop := a.toInt < b.toInt

instance : LE Int8 := ⟨Int8.le⟩

instance : LT Int8 := ⟨Int8.lt⟩

instance (a b : Int8) : Decidable (a <= b) :=
  dite (a.toInt <= b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

instance (a b : Int8) : Decidable (a < b) :=
  dite (a.toInt < b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

structure Int16 where
  val : UInt16
deriving DecidableEq

def Int16.ofNat (n : Nat) : Int16 := ⟨OfNat.ofNat n⟩

instance (n : Nat) : OfNat Int16 n := ⟨Int16.ofNat n⟩

def Int16.neg : Int16 -> Int16
| ⟨⟨a, isLt⟩⟩ => ⟨(UInt16.size - a) % UInt16.size, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) isLt)⟩

instance : Neg Int16 := ⟨Int16.neg⟩

def Int16.max : Int16 := -32767
def Int16.min : Int16 := -32768

theorem Int16.eq_of_val_eq : ∀ {a b : Int16}, a.val = b.val -> a = b
| ⟨_⟩, _, rfl => rfl

theorem Int16.ne_of_val_ne : ∀ {a b : Int16}, a.val ≠ b.val -> a ≠ b
| _, _, h => fun a_eq_b => Int16.noConfusion a_eq_b h

theorem Int16.val_eq_of_eq : ∀ {a b : Int16}, a = b -> a.val = b.val
| ⟨_⟩, _, rfl => rfl

theorem Int16.val_ne_of_ne : ∀ {a b : Int16}, a ≠ b -> a.val ≠ b.val
| _, _, h => fun h' => absurd (Int16.eq_of_val_eq h') h

def Int16.isPositive (a : Int16) : Bool := a.val.val < (UInt16.size / 2)

def Int16.isNegative (a : Int16) : Bool := ¬a.isPositive

def Int16.toInt (a : Int16) : Int :=
  if a.isPositive
  then Int.ofNat a.val.toNat
  else Int.subNatNat a.val.toNat UInt16.size

def Int16.toString (a : Int16) : String := s!"{a.toInt}"

instance : ToString Int16 := ⟨Int16.toString⟩



def Int16.ofInt : Int -> Int16
| Int.ofNat n => Int16.ofNat n
| Int.negSucc n => -(Int16.ofNat n.succ)

def Int16.modn (a : Int16) (n : Nat) : Int16 := Int16.ofInt <| a.toInt % (Int.ofNat n)

def Int16.shiftLeft (a b : Int16) : Int16 := ⟨a.val.shiftLeft b.val⟩

def Int16.shiftRight (a b : Int16) : Int16 := ⟨a.val.shiftRight b.val⟩

def Int16.land (a b : Int16) : Int16 := ⟨a.val.land b.val⟩

def Int16.lor (a b : Int16) : Int16 := ⟨a.val.lor b.val⟩

def Int16.xor (a b : Int16) : Int16 := ⟨a.val.xor b.val⟩

instance : HMod Int16 Nat Int16 := ⟨Int16.modn⟩
instance : AndOp Int16     := ⟨Int16.land⟩
instance : OrOp Int16      := ⟨Int16.lor⟩
instance : Xor Int16       := ⟨Int16.xor⟩
instance : ShiftLeft Int16  := ⟨Int16.shiftLeft⟩
instance : ShiftRight Int16 := ⟨Int16.shiftRight⟩

def Int16.add : Int16 -> Int16 -> Int16
| ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

instance : Add Int16 := ⟨Int16.add⟩

def Int16.sub (a b : Int16) : Int16 := a + -b

instance : Sub Int16 := ⟨Int16.sub⟩

def Int16.mul : Int16 -> Int16 -> Int16
| ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

def Int16.div (a b : Int16) : Int16 := Int16.ofInt (a.toInt / b.toInt)
def Int16.mod (a m : Int16) : Int16 := Int16.ofInt (a.toInt % m.toInt)

instance : Mul Int16 := ⟨Int16.mul⟩

instance : Mod Int16 := ⟨Int16.mod⟩

instance : Div Int16 := ⟨Int16.div⟩

def Int16.le (a b : Int16) : Prop := a.toInt <= b.toInt
def Int16.lt (a b : Int16) : Prop := a.toInt < b.toInt

instance : LE Int16 := ⟨Int16.le⟩

instance : LT Int16 := ⟨Int16.lt⟩

instance (a b : Int16) : Decidable (a <= b) :=
  dite (a.toInt <= b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

instance (a b : Int16) : Decidable (a < b) :=
  dite (a.toInt < b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

structure Int32 where
  val : UInt32
deriving DecidableEq

def Int32.ofNat (n : Nat) : Int32 := ⟨OfNat.ofNat n⟩

instance (n : Nat) : OfNat Int32 n := ⟨Int32.ofNat n⟩


def Int32.neg : Int32 -> Int32
| ⟨⟨a, isLt⟩⟩ => ⟨(UInt32.size - a) % UInt32.size, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) isLt)⟩

instance : Neg Int32 := ⟨Int32.neg⟩

def Int32.min : Int32 := -2147483648
def Int32.max : Int32 := 2147483647

theorem Int32.eq_of_val_eq : ∀ {a b : Int32}, a.val = b.val -> a = b
| ⟨_⟩, _, rfl => rfl

theorem Int32.ne_of_val_ne : ∀ {a b : Int32}, a.val ≠ b.val -> a ≠ b
| _, _, h => fun a_eq_b => Int32.noConfusion a_eq_b h

theorem Int32.val_eq_of_eq : ∀ {a b : Int32}, a = b -> a.val = b.val
| ⟨_⟩, _, rfl => rfl

theorem Int32.val_ne_of_ne : ∀ {a b : Int32}, a ≠ b -> a.val ≠ b.val
| _, _, h => fun h' => absurd (Int32.eq_of_val_eq h') h

def Int32.isPositive (a : Int32) : Bool := a.val.val < (UInt32.size / 2)

def Int32.isNegative (a : Int32) : Bool := ¬a.isPositive

def Int32.toInt (a : Int32) : Int :=
  if a.isPositive
  then Int.ofNat a.val.toNat
  else Int.subNatNat a.val.toNat UInt32.size

def Int32.toString (a : Int32) : String := s!"{a.toInt}"

instance : ToString Int32 := ⟨Int32.toString⟩


def Int32.ofInt : Int -> Int32
| Int.ofNat n => Int32.ofNat n
| Int.negSucc n => -(Int32.ofNat n.succ)

def Int32.modn (a : Int32) (n : Nat) : Int32 := Int32.ofInt <| a.toInt % (Int.ofNat n)

def Int32.shiftLeft (a b : Int32) : Int32 := ⟨a.val.shiftLeft b.val⟩

def Int32.shiftRight (a b : Int32) : Int32 := ⟨a.val.shiftRight b.val⟩

def Int32.land (a b : Int32) : Int32 := ⟨a.val.land b.val⟩

def Int32.lor (a b : Int32) : Int32 := ⟨a.val.lor b.val⟩

def Int32.xor (a b : Int32) : Int32 := ⟨a.val.xor b.val⟩

instance : HMod Int32 Nat Int32 := ⟨Int32.modn⟩
instance : AndOp Int32     := ⟨Int32.land⟩
instance : OrOp Int32      := ⟨Int32.lor⟩
instance : Xor Int32       := ⟨Int32.xor⟩
instance : ShiftLeft Int32  := ⟨Int32.shiftLeft⟩
instance : ShiftRight Int32 := ⟨Int32.shiftRight⟩

def Int32.add : Int32 -> Int32 -> Int32
| ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

instance : Add Int32 := ⟨Int32.add⟩

def Int32.sub (a b : Int32) : Int32 := a + -b

instance : Sub Int32 := ⟨Int32.sub⟩

def Int32.mul : Int32 -> Int32 -> Int32
| ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

def Int32.div (a b : Int32) : Int32 := Int32.ofInt (a.toInt / b.toInt)
def Int32.mod (a m : Int32) : Int32 := Int32.ofInt (a.toInt % m.toInt)

instance : Mul Int32 := ⟨Int32.mul⟩

instance : Mod Int32 := ⟨Int32.mod⟩

instance : Div Int32 := ⟨Int32.div⟩

def Int32.le (a b : Int32) : Prop := a.toInt <= b.toInt
def Int32.lt (a b : Int32) : Prop := a.toInt < b.toInt

instance : LE Int32 := ⟨Int32.le⟩

instance : LT Int32 := ⟨Int32.lt⟩

instance (a b : Int32) : Decidable (a <= b) :=
  dite (a.toInt <= b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

instance (a b : Int32) : Decidable (a < b) :=
  dite (a.toInt < b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

structure Int64 where
  val : UInt64
deriving DecidableEq

def Int64.ofNat (n : Nat) : Int64 := ⟨OfNat.ofNat n⟩

instance (n : Nat) : OfNat Int64 n := ⟨Int64.ofNat n⟩

theorem Int64.eq_of_val_eq : ∀ {a b : Int64}, a.val = b.val -> a = b
| ⟨_⟩, _, rfl => rfl

theorem Int64.ne_of_val_ne : ∀ {a b : Int64}, a.val ≠ b.val -> a ≠ b
| _, _, h => fun a_eq_b => Int64.noConfusion a_eq_b h

theorem Int64.val_eq_of_eq : ∀ {a b : Int64}, a = b -> a.val = b.val
| ⟨_⟩, _, rfl => rfl

theorem Int64.val_ne_of_ne : ∀ {a b : Int64}, a ≠ b -> a.val ≠ b.val
| _, _, h => fun h' => absurd (Int64.eq_of_val_eq h') h

def Int64.neg : Int64 -> Int64
| ⟨⟨a, isLt⟩⟩ => ⟨(UInt64.size - a) % UInt64.size, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) isLt)⟩

instance : Neg Int64 := ⟨Int64.neg⟩

abbrev Int64.min : Int64 := -9223372036854775808
abbrev Int64.max : Int64 := 9223372036854775807
/-
Fin.val <= 9223372036854775807
-/
/-
Not sure whether it's an issue to cast all the way to `nat` here.
-/
--def Int64.isPositive (a : Int64) : Bool := a.val.val.val < (UInt64.size / 2)
def Int64.isPositive (a : Int64) : Bool := a.val <= (9223372036854775807 : UInt64)

theorem Int64.isPositive_eq_true_iff (a : Int64) : a.isPositive = true ↔ a.val <= (9223372036854775807 : UInt64) := by
  simp [Int64.isPositive]

def Int64.isNegative (a : Int64) : Bool := ¬a.isPositive

/-
There's probably a better way to do this.
-/
def Int64.toInt (a : Int64) : Int :=
  if a.isPositive
  then Int.ofNat a.val.toNat
  else Int.subNatNat a.val.toNat UInt64.size

def Int64.toString (a : Int64) : String := s!"{a.toInt}"

instance : ToString Int64 := ⟨Int64.toString⟩


def Int64.ofInt : Int → Int64
| Int.ofNat n => Int64.ofNat n
| Int.negSucc n => -(Int64.ofNat n.succ)

def Int64.modn (a : Int64) (n : Nat) : Int64 := Int64.ofInt <| a.toInt % (Int.ofNat n)

def Int64.shiftLeft (a b : Int64) : Int64 := ⟨a.val.shiftLeft b.val⟩

def Int64.shiftRight (a b : Int64) : Int64 := ⟨a.val.shiftRight b.val⟩

def Int64.land (a b : Int64) : Int64 := ⟨a.val.land b.val⟩

def Int64.lor (a b : Int64) : Int64 := ⟨a.val.lor b.val⟩

def Int64.xor (a b : Int64) : Int64 := ⟨a.val.xor b.val⟩

instance : HMod Int64 Nat Int64 := ⟨Int64.modn⟩
instance : AndOp Int64     := ⟨Int64.land⟩
instance : OrOp Int64      := ⟨Int64.lor⟩
instance : Xor Int64       := ⟨Int64.xor⟩
instance : ShiftLeft Int64  := ⟨Int64.shiftLeft⟩
instance : ShiftRight Int64 := ⟨Int64.shiftRight⟩

def Int64.add : Int64 -> Int64 -> Int64
| ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

instance : Add Int64 := ⟨Int64.add⟩

def Int64.sub (a b : Int64) : Int64 := a + -b

instance : Sub Int64 := ⟨Int64.sub⟩

def Int64.mul : Int64 -> Int64 -> Int64
| ⟨a⟩, ⟨b⟩ => ⟨a * b⟩


def Int64.div (a b : Int64) : Int64 := Int64.ofInt (a.toInt / b.toInt)
def Int64.mod (a m : Int64) : Int64 := Int64.ofInt (a.toInt % m.toInt)

instance : Mul Int64 := ⟨Int64.mul⟩

instance : Mod Int64 := ⟨Int64.mod⟩

instance : Div Int64 := ⟨Int64.div⟩

def Int64.le (a b : Int64) : Prop := a.toInt <= b.toInt
def Int64.lt (a b : Int64) : Prop := a.toInt < b.toInt

instance : LE Int64 := ⟨Int64.le⟩

instance : LT Int64 := ⟨Int64.lt⟩

instance (a b : Int64) : Decidable (a <= b) :=
  dite (a.toInt <= b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

instance (a b : Int64) : Decidable (a < b) :=
  dite (a.toInt < b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

/-
sameSign a b ∧ differentSign a out
-/
def Int64.wrappingAdd (a b : Int64) : (Bool × Int64) :=
  let sum := a + b
  let oob :=
    if a.isPositive
    then
      if b.isPositive
      then sum.isNegative
      else false
    else
      if b.isNegative
      then sum.isPositive
      else false
  (oob, sum)

def Int64.checkedAdd (a b : Int64) : Option Int64 :=
  match a.wrappingAdd b with
  | (true, _) => none
  | (false, sum) => some sum

structure ISize where
  val : USize
deriving DecidableEq

def ISize.ofNat (n : Nat) : ISize := ⟨OfNat.ofNat n⟩

instance (n : Nat) : OfNat ISize n := ⟨ISize.ofNat n⟩

theorem ISize.eq_of_val_eq : ∀ {a b : ISize}, a.val = b.val -> a = b
| _, _, h => congrArg ISize.mk h

theorem ISize.ne_of_val_ne : ∀ {a b : ISize}, a.val ≠ b.val -> a ≠ b
| _, _, h => fun a_eq_b => ISize.noConfusion a_eq_b h

theorem ISize.val_eq_of_eq : ∀ {a b : ISize}, a = b -> a.val = b.val
| _, _, h => congrArg ISize.val h

theorem ISize.val_ne_of_ne : ∀ {a b : ISize}, a ≠ b -> a.val ≠ b.val
| _, _, h => fun h' => absurd (ISize.eq_of_val_eq h') h

def ISize.isPositive (a : ISize) : Bool := a.val.val < (USize.size / 2)

def ISize.isNegative (a : ISize) : Bool := ¬a.isPositive

def ISize.toInt (a : ISize) : Int :=
  if a.isPositive
  then Int.ofNat a.val.toNat
  else Int.subNatNat a.val.toNat USize.size

def ISize.toString (a : ISize) : String := s!"{a.toInt}"

instance : ToString ISize := ⟨ISize.toString⟩

def ISize.neg : ISize -> ISize
| ⟨⟨a, isLt⟩⟩ => ⟨(USize.size - a) % USize.size, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) isLt)⟩

instance : Neg ISize := ⟨ISize.neg⟩

def ISize.ofInt : Int -> ISize
| Int.ofNat n => ISize.ofNat n
| Int.negSucc n => -(ISize.ofNat n.succ)

def ISize.modn (a : ISize) (n : Nat) : ISize := ISize.ofInt <| a.toInt % (Int.ofNat n)

def ISize.shiftLeft (a b : ISize) : ISize := ⟨a.val.shiftLeft b.val⟩

def ISize.shiftRight (a b : ISize) : ISize := ⟨a.val.shiftRight b.val⟩

def ISize.land (a b : ISize) : ISize := ⟨a.val.land b.val⟩

def ISize.lor (a b : ISize) : ISize := ⟨a.val.lor b.val⟩

def ISize.xor (a b : ISize) : ISize := ⟨a.val.xor b.val⟩

instance : HMod ISize Nat ISize := ⟨ISize.modn⟩
instance : AndOp ISize     := ⟨ISize.land⟩
instance : OrOp ISize      := ⟨ISize.lor⟩
instance : Xor ISize       := ⟨ISize.xor⟩
instance : ShiftLeft ISize  := ⟨ISize.shiftLeft⟩
instance : ShiftRight ISize := ⟨ISize.shiftRight⟩

def ISize.add : ISize -> ISize -> ISize
| ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

instance : Add ISize := ⟨ISize.add⟩

def ISize.sub (a b : ISize) : ISize := a + -b

instance : Sub ISize := ⟨ISize.sub⟩

def ISize.mul : ISize -> ISize -> ISize
| ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

def ISize.div (a b : ISize) : ISize := ISize.ofInt (a.toInt / b.toInt)
def ISize.mod (a m : ISize) : ISize := ISize.ofInt (a.toInt % m.toInt)

instance : Mul ISize := ⟨ISize.mul⟩

instance : Mod ISize := ⟨ISize.mod⟩

instance : Div ISize := ⟨ISize.div⟩

def ISize.le (a b : ISize) : Prop := a.toInt <= b.toInt
def ISize.lt (a b : ISize) : Prop := a.toInt < b.toInt

instance : LE ISize := ⟨ISize.le⟩

instance : LT ISize := ⟨ISize.lt⟩

instance : DecidableEq ISize
| a, b =>
  dite
    (a.val = b.val)
    (fun h => isTrue <| ISize.eq_of_val_eq h)
    (fun h => isFalse <| fun h' => absurd (ISize.val_eq_of_eq h') h)

instance (a b : ISize) : Decidable (a <= b) :=
  dite (a.toInt <= b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)

instance (a b : ISize) : Decidable (a < b) :=
  dite (a.toInt < b.toInt) isTrue (fun h => isFalse <| fun h' => absurd h' h)
