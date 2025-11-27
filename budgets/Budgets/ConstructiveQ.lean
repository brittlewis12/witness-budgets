import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Field

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

/-- Integer power using repeated multiplication.
    Enables clean expressions like `R^6` and `C^4` in Lipschitz budget calculations. -/
def pow (q : Q) (n : Nat) : Q :=
  match n with
  | 0 => one
  | k+1 => mul q (pow q k)

instance : Pow Q Nat := ⟨pow⟩

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

/-- Normalization preserves the rational value.

    Mathematical fact: Dividing both numerator and denominator by their GCD
    preserves the rational value: (a/gcd)/(b/gcd) = a/b

    This is a fundamental property of rational number normalization. -/
theorem normalize_preserves_value (num : Int) (den : Nat) (hden : den ≠ 0) :
    let q := normalize num den
    (q.num : ℚ) / (q.den : ℚ) = (num : ℚ) / (den : ℚ) := by
  -- Set up GCD computation
  set g := Nat.gcd num.natAbs den
  set den' := den / g

  -- Prove g > 0 (needed for division)
  have hg_pos : g > 0 := by
    have hden_pos : den > 0 := Nat.pos_of_ne_zero hden
    exact Nat.gcd_pos_of_pos_right _ hden_pos
  have hg_ne_zero : (g : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hg_pos)
  have hg_ne_zero_nat : g ≠ 0 := by exact_mod_cast hg_ne_zero

  -- Get divisibility witnesses
  obtain ⟨numk, hnumk⟩ : g ∣ num.natAbs := Nat.gcd_dvd_left _ _
  obtain ⟨denk, hdenk⟩ : g ∣ den := Nat.gcd_dvd_right _ _

  -- Rewrite divisions using the witnesses
  have hnumk_div :
      num.natAbs / g = numk := by
    have hmul : num.natAbs = numk * g := by
      simpa [Nat.mul_comm] using hnumk
    exact Nat.div_eq_of_eq_mul_left hg_pos hmul
  have hdenk_div_nat :
      den / g = denk := by
    have hmul : den = denk * g := by
      simpa [Nat.mul_comm] using hdenk
    exact Nat.div_eq_of_eq_mul_left hg_pos hmul
  have hden'_eq : den' = denk := by
    simp [den', hdenk_div_nat]

  -- Denominator after normalization is nonzero
  have hdenk_ne_zero : denk ≠ 0 := by
    intro hzero
    have : den = 0 := by simpa [Nat.mul_comm, hzero] using hdenk
    exact hden this
  have hden'_ne_zero : den' ≠ 0 := by
    simpa [hden'_eq] using hdenk_ne_zero

  -- Casted equalities for numerator/denominator
  have hden_cast :
      (den : ℚ) = (g : ℚ) * (denk : ℚ) := by
    have := congrArg (fun t : ℕ => (t : ℚ)) hdenk
    simpa [Nat.cast_mul, mul_comm] using this
  have hdenk_ne_zero_rat : (denk : ℚ) ≠ 0 := by
    exact_mod_cast hdenk_ne_zero
  have hden_ne_zero_rat : (den : ℚ) ≠ 0 := by
    exact_mod_cast hden

  -- Split on numerator sign
  by_cases hnum : num ≥ 0
  · -- Nonnegative numerator.
    have hnum_abs_cast :
        (num : ℚ) = (num.natAbs : ℚ) := by
      have := congrArg (fun t : ℤ => (t : ℚ)) (Int.ofNat_natAbs_of_nonneg hnum)
      simp only [Int.cast_natCast] at this
      exact this.symm
    have hnum_cast :
        (num : ℚ) = (g : ℚ) * (numk : ℚ) := by
      have := congrArg (fun t : ℕ => (t : ℚ)) hnumk
      simp only [Nat.cast_mul] at this
      rw [hnum_abs_cast]
      exact this
    have hq_num :
        (normalize num den).num = Int.ofNat numk := by
      unfold normalize
      simp only [dif_neg hden]
      have : den / Nat.gcd num.natAbs den ≠ 0 := by rw [hdenk_div_nat]; exact hdenk_ne_zero
      rw [dif_neg this]
      simp only [if_pos hnum]
      show Int.ofNat (num.natAbs / Nat.gcd num.natAbs den) = Int.ofNat numk
      rw [hnumk_div]
    have hq_den :
        (normalize num den).den = denk := by
      unfold normalize
      simp only [dif_neg hden]
      have : den / Nat.gcd num.natAbs den ≠ 0 := by rw [hdenk_div_nat]; exact hdenk_ne_zero
      rw [dif_neg this]
      show den / Nat.gcd num.natAbs den = denk
      exact hdenk_div_nat
    have lhs_eq :
        (let q := normalize num den; (q.num : ℚ) / (q.den : ℚ))
          = (numk : ℚ) / (denk : ℚ) := by
      simp [hq_num, hq_den]
    have rhs_eq :
        (numk : ℚ) / (denk : ℚ) = (num : ℚ) / (den : ℚ) := by
      field_simp [hdenk_ne_zero_rat, hden_ne_zero_rat]
      simp [hden_cast, hnum_cast, mul_left_comm, mul_comm]
    exact lhs_eq.trans rhs_eq
  · -- Negative numerator.
    have num_neg : num < 0 := Int.not_le.mp hnum
    have hnum_abs_cast :
        (num : ℚ) = -(num.natAbs : ℚ) := by
      have h :=
        congrArg (fun t : ℤ => (t : ℚ)) (Int.ofNat_natAbs_of_nonpos (le_of_lt num_neg))
      have := congrArg Neg.neg h
      simp only [Int.cast_natCast, Int.cast_neg, neg_neg] at this
      exact this.symm
    have hnum_cast :
        (num : ℚ) = -(g : ℚ) * (numk : ℚ) := by
      have := congrArg (fun t : ℕ => (t : ℚ)) hnumk
      simp only [Nat.cast_mul] at this
      rw [hnum_abs_cast]
      rw [this]
      ring
    have hq_num :
        (normalize num den).num = -Int.ofNat numk := by
      unfold normalize
      simp only [dif_neg hden]
      have : den / Nat.gcd num.natAbs den ≠ 0 := by rw [hdenk_div_nat]; exact hdenk_ne_zero
      rw [dif_neg this]
      simp only [if_neg hnum]
      show -Int.ofNat (num.natAbs / Nat.gcd num.natAbs den) = -Int.ofNat numk
      rw [hnumk_div]
    have hq_den :
        (normalize num den).den = denk := by
      unfold normalize
      simp only [dif_neg hden]
      have : den / Nat.gcd num.natAbs den ≠ 0 := by rw [hdenk_div_nat]; exact hdenk_ne_zero
      rw [dif_neg this]
      show den / Nat.gcd num.natAbs den = denk
      exact hdenk_div_nat
    have lhs_eq :
        (let q := normalize num den; (q.num : ℚ) / (q.den : ℚ))
          = - (numk : ℚ) / (denk : ℚ) := by
      simp [hq_num, hq_den]
    have goal :
        (-(numk : ℚ)) / (denk : ℚ) = (num : ℚ) / (den : ℚ) := by
      field_simp [hdenk_ne_zero_rat, hden_ne_zero_rat]
      simp [hden_cast, hnum_cast, mul_left_comm, mul_comm]
    exact lhs_eq.trans goal

/-- Constructive floor function for ConstructiveQ rationals.
    Returns the greatest integer ≤ q.

    **XBUDGET**: C0 (fully computable)
    - Uses only integer division (ℤ / ℤ)
    - No Classical.choice in computational path
    - Can be evaluated with #eval

    This is the key to avoiding Classical.choice from Int.floor on ℝ
    in the QAL witness construction path. -/
def floor (q : Q) : ℤ :=
  q.num / Int.ofNat q.den

/-- Convert ConstructiveQ to standard ℚ for proof purposes -/
def toRat (q : Q) : ℚ :=
  q.num / q.den

/-- Constructive floor for standard rationals via ConstructiveQ.

    **XBUDGET**: C0 (fully computable)

    Note: While #print axioms may show Classical.choice due to ℚ's internal
    representation in Mathlib, this is only for proof purposes. The function
    is computationally constructive and can be evaluated with #eval. -/
def floorRat (q : ℚ) : ℤ :=
  floor (normalize q.num q.den)

-- =============================================================================
-- Morphism Lemmas: The Bridge from Constructive to Classical
-- =============================================================================
-- These lemmas prove that `toRat : Q → ℚ` preserves the algebraic structure,
-- allowing the simplifier to work automatically when moving between constructive
-- computation and classical proofs.

/-- toRat preserves zero -/
theorem toRat_zero : toRat zero = 0 := by
  unfold toRat zero
  simp

/-- toRat preserves one -/
theorem toRat_one : toRat one = 1 := by
  unfold toRat one
  simp

/-- toRat preserves ofInt -/
theorem toRat_ofInt (z : Int) : toRat (ofInt z) = z := by
  unfold toRat ofInt
  rw [normalize_preserves_value]
  · simp
  · norm_num

/-- Homomorphism: toRat preserves addition -/
theorem toRat_add (a b : Q) : toRat (add a b) = toRat a + toRat b := by
  unfold toRat add
  rw [normalize_preserves_value]
  · simp only [Int.cast_add, Int.cast_mul, Nat.cast_mul]
    have ha : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt a.den_pos)
    have hb : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt b.den_pos)
    rw [div_add_div _ _ ha hb]
    congr 1
    simp only [Int.ofNat_eq_coe, Int.cast_natCast]
    ring
  · apply ne_of_gt
    apply Nat.mul_pos a.den_pos b.den_pos

/-- Homomorphism: toRat preserves multiplication -/
theorem toRat_mul (a b : Q) : toRat (mul a b) = toRat a * toRat b := by
  unfold toRat mul
  rw [normalize_preserves_value]
  · simp only [Int.cast_mul, Nat.cast_mul]
    have ha : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt a.den_pos)
    have hb : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt b.den_pos)
    field_simp [ha, hb]
  · apply ne_of_gt
    apply Nat.mul_pos a.den_pos b.den_pos

/-- Homomorphism: toRat preserves negation -/
theorem toRat_neg (a : Q) : toRat (neg a) = -(toRat a) := by
  unfold toRat neg
  rw [normalize_preserves_value]
  · simp only [Int.cast_neg]
    field_simp
  · apply ne_of_gt
    exact a.den_pos

/-- Homomorphism: toRat preserves subtraction -/
theorem toRat_sub (a b : Q) : toRat (sub a b) = toRat a - toRat b := by
  unfold sub
  rw [toRat_add, toRat_neg]
  ring

/-- toRat preserves power -/
theorem toRat_pow (a : Q) (n : Nat) : toRat (pow a n) = (toRat a) ^ n := by
  induction n with
  | zero => simp [pow, toRat_one]
  | succ k ih =>
    rw [pow]
    rw [toRat_mul, ih]
    ring

-- =============================================================================
-- Order Lemmas: Comparison Bridge
-- =============================================================================
-- These lemmas prove that `toRat` preserves order relations, enabling
-- order-based reasoning to transfer between constructive and classical settings.

/-- Order preservation: toRat preserves ≤ -/
theorem toRat_le (a b : Q) : (a ≤ b) ↔ (toRat a ≤ toRat b) := by
  show le a b ↔ _
  unfold toRat le
  -- Setup positive denominators for division logic
  have ha : (0 : ℚ) < a.den := Nat.cast_pos.mpr a.den_pos
  have hb : (0 : ℚ) < b.den := Nat.cast_pos.mpr b.den_pos
  -- Apply cross-multiplication rule: a/b ≤ c/d ↔ ad ≤ cb
  rw [div_le_div_iff₀ ha hb]
  -- Automatically handle Int -> Rat casting
  norm_cast

/-- Strict order preservation: toRat preserves < -/
theorem toRat_lt (a b : Q) : (a < b) ↔ (toRat a < toRat b) := by
  show lt a b ↔ _
  unfold toRat lt
  -- Setup positive denominators for division logic
  have ha : (0 : ℚ) < a.den := Nat.cast_pos.mpr a.den_pos
  have hb : (0 : ℚ) < b.den := Nat.cast_pos.mpr b.den_pos
  -- Apply cross-multiplication rule: a/b < c/d ↔ ad < cb
  rw [div_lt_div_iff₀ ha hb]
  norm_cast

-- =============================================================================
-- Floor Specification: Correctness of Constructive Floor
-- =============================================================================
-- These theorems prove that the constructive floor function satisfies the
-- standard floor specification: floor(q) ≤ q < floor(q) + 1

/-- Lower bound: floor(q) ≤ q -/
theorem floor_le (q : Q) : (floor q : ℚ) ≤ toRat q := by
  unfold floor toRat
  -- Key insight: Use Euclidean division q.num = q.den * (q.num / q.den) + (q.num % q.den)
  -- with 0 ≤ q.num % q.den
  set f := q.num / Int.ofNat q.den
  have hden_pos : (0 : ℤ) < Int.ofNat q.den := Int.natCast_pos.mpr q.den_pos
  have hden_ne_zero : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt q.den_pos)

  -- Euclidean division property: b * (a / b) + (a % b) = a
  have hdiv : q.num = Int.ofNat q.den * f + q.num % Int.ofNat q.den := by
    exact (Int.mul_ediv_add_emod q.num (Int.ofNat q.den)).symm

  -- The remainder is nonnegative
  have hmod_nonneg : 0 ≤ q.num % Int.ofNat q.den := by
    exact Int.emod_nonneg q.num (ne_of_gt hden_pos)

  -- Convert to rationals and prove the inequality
  have hdiv_rat : (q.num : ℚ) = (q.den : ℚ) * (f : ℚ) + (q.num % Int.ofNat q.den : ℚ) := by
    have := congrArg (fun x : ℤ => (x : ℚ)) hdiv
    push_cast [Int.cast_natCast] at this
    exact this

  -- Prove the inequality using field arithmetic
  have hmod_nonneg_rat : (0 : ℚ) ≤ (q.num % Int.ofNat q.den : ℚ) :=
    Int.cast_nonneg.mpr hmod_nonneg
  have hden_pos_rat : (0 : ℚ) < (q.den : ℚ) := Nat.cast_pos.mpr q.den_pos

  -- The key step: f ≤ q.num / q.den
  suffices (f : ℚ) * (q.den : ℚ) ≤ (q.num : ℚ) by
    exact (le_div_iff₀ hden_pos_rat).mpr this
  calc (f : ℚ) * (q.den : ℚ) = (q.den : ℚ) * (f : ℚ) := by ring
    _ ≤ (q.den : ℚ) * (f : ℚ) + (q.num % Int.ofNat q.den : ℚ) := by
      apply le_add_of_nonneg_right hmod_nonneg_rat
    _ = (q.num : ℚ) := by rw [← hdiv_rat]

/-- Upper bound: q < floor(q) + 1 -/
theorem lt_floor_add_one (q : Q) : toRat q < (floor q : ℚ) + 1 := by
  unfold floor toRat
  set f := q.num / Int.ofNat q.den
  have hden_pos : (0 : ℤ) < Int.ofNat q.den := Int.natCast_pos.mpr q.den_pos
  have hden_ne_zero : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt q.den_pos)

  -- Euclidean division property: b * (a / b) + (a % b) = a
  have hdiv : q.num = Int.ofNat q.den * f + q.num % Int.ofNat q.den := by
    exact (Int.mul_ediv_add_emod q.num (Int.ofNat q.den)).symm

  -- The remainder is strictly less than the divisor
  have hmod_lt : q.num % Int.ofNat q.den < Int.ofNat q.den := by
    exact Int.emod_lt_of_pos q.num hden_pos

  -- Convert to rationals and prove the inequality
  have hdiv_rat : (q.num : ℚ) = (q.den : ℚ) * (f : ℚ) + (q.num % Int.ofNat q.den : ℚ) := by
    have := congrArg (fun x : ℤ => (x : ℚ)) hdiv
    push_cast [Int.cast_natCast] at this
    exact this

  -- The remainder is strictly less than the divisor (as rationals)
  have hmod_lt_rat : (q.num % Int.ofNat q.den : ℚ) < (q.den : ℚ) := by
    calc (q.num % Int.ofNat q.den : ℚ) = (q.num % Int.ofNat q.den : ℤ) := rfl
      _ < (Int.ofNat q.den : ℤ) := Int.cast_lt.mpr hmod_lt
      _ = (q.den : ℕ) := rfl
      _ = (q.den : ℚ) := rfl
  have hden_pos_rat : (0 : ℚ) < (q.den : ℚ) := Nat.cast_pos.mpr q.den_pos

  -- Directly prove q.num / q.den < f + 1
  show (q.num : ℚ) / (q.den : ℚ) < (f : ℚ) + 1
  rw [hdiv_rat]
  calc ((q.den : ℚ) * (f : ℚ) + (q.num % Int.ofNat q.den : ℚ)) / (q.den : ℚ)
      = (q.den : ℚ) * (f : ℚ) / (q.den : ℚ) + (q.num % Int.ofNat q.den : ℚ) / (q.den : ℚ) := by
        rw [add_div]
    _ = (f : ℚ) + (q.num % Int.ofNat q.den : ℚ) / (q.den : ℚ) := by
        rw [mul_div_cancel_left₀ _ hden_ne_zero]
    _ < (f : ℚ) + 1 := by
        apply add_lt_add_left
        rw [div_lt_iff₀ hden_pos_rat]
        calc (q.num % Int.ofNat q.den : ℚ) < (q.den : ℚ) := hmod_lt_rat
          _ = 1 * (q.den : ℚ) := by ring

/-- Complete floor specification: floor(q) ≤ q < floor(q) + 1 -/
theorem floor_spec (q : Q) : (floor q : ℚ) ≤ toRat q ∧ toRat q < (floor q : ℚ) + 1 :=
  ⟨floor_le q, lt_floor_add_one q⟩
