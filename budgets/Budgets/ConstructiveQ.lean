import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic

/-
# ConstructiveQ

Lightweight rational numbers implemented with explicit normalization
so that every value has a unique `(num, den)` representation with
`den > 0`. All computational definitions stay constructive (xBudget = C0),
while proofs can move through the coercion `toRat : ConstructiveQ → ℚ`.
-/

namespace ConstructiveQ

/-- Rational numbers represented by an integer numerator and positive
natural denominator. Values should be introduced via the `normalize`
smart constructor to ensure canonical form. -/
structure Q where
  num : Int
  den : Nat
  den_pos : den > 0
deriving Repr, DecidableEq

attribute [simp] Q.den_pos

/-- Canonical zero. -/
def zero : Q := ⟨0, 1, by decide⟩

/-- Canonical one. -/
def one : Q := ⟨1, 1, by decide⟩

instance : Inhabited Q := ⟨zero⟩

@[simp] theorem zero_den : zero.den = 1 := rfl
@[simp] theorem one_den : one.den = 1 := rfl

/-- Normalize a numerator/denominator pair using GCD reduction.
Ensures canonical representation: gcd(|num|, den) = 1 and den > 0. -/
def normalize (num : Int) (den : Nat) : Q :=
  if _hden : den = 0 then zero
  else
    -- Compute GCD and reduce to canonical form
    let g := Nat.gcd num.natAbs den
    let den' := den / g
    -- Reduce numerator preserving sign (using Nat division on absolute value)
    let num' := if num ≥ 0
                then Int.ofNat (num.natAbs / g)
                else -(Int.ofNat (num.natAbs / g))
    -- Safety check: den' should be positive (g divides den, g > 0)
    if hden' : den' = 0 then zero
    else
      have : den' > 0 := Nat.pos_of_ne_zero hden'
      ⟨num', den', this⟩

/-- Addition using the canonical normalizer. -/
def add (q r : Q) : Q :=
  normalize (q.num * Int.ofNat r.den + r.num * Int.ofNat q.den)
            (q.den * r.den)

/-- Multiplication using the canonical normalizer. -/
def mul (q r : Q) : Q :=
  normalize (q.num * r.num) (q.den * r.den)

/-- Negation using normalization (keeps canonical zero). -/
def neg (q : Q) : Q :=
  normalize (-q.num) q.den

/-- Subtraction via addition + negation. -/
def sub (q r : Q) : Q :=
  add q (neg r)

/-- Absolute value (re-uses normalization for canonical zero). -/
def abs (q : Q) : Q :=
  if q.num ≥ 0 then q else neg q

/-- Reciprocal (returns zero when numerator zero). -/
def inv (q : Q) : Q :=
  if _h : q.num = 0 then zero
  else
    let num' := if q.num > 0 then Int.ofNat q.den else -Int.ofNat q.den
    let den' := q.num.natAbs
    normalize num' den'

/-- Division via multiplication with reciprocal. -/
def div (q r : Q) : Q := mul q (inv r)

/-- Literals embed via normalization. -/
def ofInt (z : Int) : Q := normalize z 1

instance instOfNat {n : Nat} : OfNat Q n := ⟨ofInt n⟩

instance : Zero Q := ⟨zero⟩
instance : One Q := ⟨one⟩
instance : Neg Q := ⟨neg⟩
instance : Add Q := ⟨add⟩
instance : Sub Q := ⟨sub⟩
instance : Mul Q := ⟨mul⟩
instance : Inv Q := ⟨inv⟩
instance : Div Q := ⟨div⟩

instance : ToString Q :=
  ⟨fun q => s!"{q.num}/{q.den}"⟩

end ConstructiveQ

open ConstructiveQ
/-- Order comparison via cross-multiplication (denominators positive). -/
def le (q r : Q) : Prop :=
  q.num * Int.ofNat r.den ≤ r.num * Int.ofNat q.den

/-- Strict order via cross-multiplication. -/
def lt (q r : Q) : Prop :=
  q.num * Int.ofNat r.den < r.num * Int.ofNat q.den

instance : LE Q := ⟨le⟩
instance : LT Q := ⟨lt⟩

instance : DecidableRel (fun q r : Q => q ≤ r) := by
  intro q r
  change Decidable (q.num * Int.ofNat r.den ≤ r.num * Int.ofNat q.den)
  infer_instance

instance : DecidableRel (fun q r : Q => q < r) := by
  intro q r
  change Decidable (q.num * Int.ofNat r.den < r.num * Int.ofNat q.den)
  infer_instance
