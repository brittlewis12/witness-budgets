import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Cast.Order

/-!
# Canonical Dyadic Rationals

This module implements canonical dyadic rationals (Path A) with efficient normalization.

## Summary

This implementation provides:
1. A canonical dyadic type D with two invariants
2. Conversion to rationals (toRat)
3. Arithmetic operations (add, mul, neg, half, divPow2)
4. Correctness proofs showing operations preserve rational values
5. Ring structure derived from D_ext theorem

Key insights:
- The two invariants ensure unique representation
- D_ext allows lifting rational ring properties to D
- normalize would be marked inline for efficient extraction
- trailingZeros enables efficient normalization (CTZ instruction)

Status:
- File compiles successfully
- Main structure and architecture in place
- ALL proofs complete, NO sorries remaining
- Ready for NumBackend integration

Remaining work:
- Add comparison operations
-/

namespace DyadicCanonical

/-- Canonical dyadic rationals: n/2^k in normal form -/
structure D where
  num : ℤ
  exp : ℕ
  -- Invariant 1: Zero is canonical (0/1, not 0/2^k)
  canonical_zero : num = 0 → exp = 0
  -- Invariant 2: No common power of 2 (numerator is odd OR exp=0)
  normalized : num ≠ 0 → (num % 2 ≠ 0) ∨ exp = 0
  deriving DecidableEq

/-- Conversion to ℚ -/
def toRat (d : D) : ℚ := d.num / (2^d.exp : ℚ)

/-- Count trailing zeros in binary representation of n -/
def trailing_zeros : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then
        1 + trailing_zeros ((n + 1) / 2)
      else
        0
termination_by n => n

/-- trailing_zeros counts factors of 2 -/
lemma trailing_zeros_spec (n : ℕ) (hn : n ≠ 0) :
    let k := trailing_zeros n
    n = (n / 2^k) * 2^k ∧ (n / 2^k) % 2 = 1 := by
  -- Use strong induction on n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp only []
    -- Work directly with the recursive definition
    by_cases h_zero : n = 0
    · contradiction
    ·  -- n ≠ 0, so we can get a representation n = m + 1
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      subst hm
      -- Now work with trailing_zeros (m + 1)
      unfold trailing_zeros
      -- Check if m + 1 is even
      by_cases h_even : (m + 1) % 2 = 0
      · -- Even case: trailing_zeros (m + 1) = 1 + trailing_zeros ((m + 1) / 2)
        simp only [h_even, ite_true]
        -- Apply IH to (m + 1) / 2
        have h_div_ne_zero : (m + 1) / 2 ≠ 0 := by
          intro h
          rw [Nat.div_eq_zero_iff] at h
          omega
        have h_div_lt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (by omega) (by norm_num : 1 < 2)
        have ih_half := ih ((m + 1) / 2) h_div_lt h_div_ne_zero
        simp only at ih_half
        obtain ⟨h_eq, h_odd⟩ := ih_half
        set k' := trailing_zeros ((m + 1) / 2)
        constructor
        · -- Show: m + 1 = ((m + 1) / 2^(1 + k')) * 2^(1 + k')
          -- We know: (m+1)/2 = ((m+1)/2 / 2^k') * 2^k' (from h_eq)
          -- And: m+1 = 2 * ((m+1)/2) (since m+1 is even)
          have h_two_dvd : 2 ∣ m + 1 := Nat.dvd_iff_mod_eq_zero.mpr h_even
          have h_double : m + 1 = 2 * ((m + 1) / 2) := Nat.eq_mul_of_div_eq_right h_two_dvd rfl
          -- Key: (m+1) / 2^(1+k') = ((m+1) / 2) / 2^k'
          have key : (m + 1) / 2^(1 + k') = ((m + 1) / 2) / 2^k' := by
            conv_lhs => rw [show 1 + k' = k' + 1 from add_comm 1 k']
            rw [pow_succ', ← Nat.div_div_eq_div_mul]
          -- Pow relation: 2 * 2^k' = 2^(1+k')
          have pow_rel : (2 : ℕ) ^ (1 + k') = 2 * 2^k' := by
            rw [show 1 + k' = k' + 1 from add_comm 1 k', pow_succ, mul_comm]
          -- Now the proof
          show m + 1 = (m + 1) / 2^(1 + k') * 2^(1 + k')
          rw [key, pow_rel]
          -- Goal: m+1 = ((m+1)/2 / 2^k') * (2 * 2^k')
          -- Transform this to: m+1 = 2 * (((m+1)/2/2^k') * 2^k')
          have step1 : ((m + 1) / 2) / 2^k' * (2 * 2^k') = 2 * (((m + 1) / 2) / 2^k' * 2^k') := by
            have : ((m + 1) / 2) / 2^k' * (2 * 2^k') = ((m + 1) / 2) / 2^k' * 2 * 2^k' := by
              rw [mul_assoc]
            rw [this, mul_comm (((m + 1) / 2) / 2^k') 2, mul_assoc]
          rw [step1, ← h_eq, h_double]
          -- Goal: 2 * ((m + 1) / 2) = 2 * (2 * ((m + 1) / 2) / 2)
          -- Need to show: (m+1)/2 = 2 * ((m+1)/2) / 2
          -- But 2 * ((m+1)/2) = m+1 by h_double, so 2 * ((m+1)/2) / 2 = (m+1) / 2
          have cancel : 2 * ((m + 1) / 2) / 2 = (m + 1) / 2 := by
            simp only [← h_double]
          rw [cancel]
        · -- Show: ((m + 1) / 2^(1 + k')) % 2 = 1
          have key : (m + 1) / 2^(1 + k') = ((m + 1) / 2) / 2^k' := by
            conv_lhs => rw [show 1 + k' = k' + 1 from add_comm 1 k']
            rw [pow_succ', ← Nat.div_div_eq_div_mul]
          rw [key]
          exact h_odd
      · -- Odd case: trailing_zeros (m + 1) = 0
        simp only [h_even, ite_false]
        constructor
        · simp
        · simp
          omega

/-- Normalize dyadic: shift out common powers of 2 -/
def normalize (num : ℤ) (exp : ℕ) : D :=
  if h : num = 0 then
    -- Zero is canonical: ⟨0, 0⟩
    ⟨0, 0, by intro; rfl, by intro h; contradiction⟩
  else
    -- Count trailing zeros in absolute value
    let zeros := trailing_zeros num.natAbs
    -- How many can we actually shift? (can't reduce exp below 0)
    let shift := min zeros exp
    -- Shift numerator right by 'shift' bits
    let shifted_num := num / (2^shift : ℤ)
    -- Reduce exponent by same amount
    let new_exp := exp - shift

    -- Prove invariants:
    ⟨shifted_num, new_exp,
     by -- canonical_zero: if shifted_num = 0, then new_exp = 0
       intro h_zero
       -- h_zero : shifted_num = 0
       -- That is: num / (2^shift : ℤ) = 0
       -- h : num ≠ 0
       -- We'll derive a contradiction, which allows us to prove anything
       exfalso

       -- Step 1: Get the trailing_zeros specification
       have h_nat_ne_zero : num.natAbs ≠ 0 := by
         intro h_abs
         have : num = 0 := Int.natAbs_eq_zero.mp h_abs
         exact absurd this h

       have h_spec := trailing_zeros_spec num.natAbs h_nat_ne_zero
       simp only at h_spec
       obtain ⟨h_eq, h_odd⟩ := h_spec

       -- From h_eq: num.natAbs = (num.natAbs / 2^(trailing_zeros num.natAbs)) * 2^(trailing_zeros num.natAbs)
       -- From h_odd: (num.natAbs / 2^(trailing_zeros num.natAbs)) % 2 = 1

       -- Step 2: Show num.natAbs ≥ 2^(trailing_zeros num.natAbs)
       set m := num.natAbs / 2^(trailing_zeros num.natAbs)
       have h_m_pos : 1 ≤ m := by
         -- m is odd (m % 2 = 1), so m ≠ 0, so m ≥ 1
         by_contra h_not
         push_neg at h_not
         -- h_not : m < 1, so m = 0
         have : m = 0 := Nat.lt_one_iff.mp h_not
         rw [this] at h_odd
         norm_num at h_odd

       have h_lower_bound : 2^(trailing_zeros num.natAbs) ≤ num.natAbs := by
         calc num.natAbs
             = m * 2^(trailing_zeros num.natAbs) := h_eq
           _ ≥ 1 * 2^(trailing_zeros num.natAbs) := by
               apply Nat.mul_le_mul_right
               exact h_m_pos
           _ = 2^(trailing_zeros num.natAbs) := by simp

       -- Step 3: Show shift ≤ trailing_zeros num.natAbs
       have h_shift_le : shift ≤ trailing_zeros num.natAbs := Nat.min_le_left _ _

       -- Step 4: Therefore 2^shift ≤ num.natAbs
       have h_pow_le : 2^shift ≤ num.natAbs := by
         calc 2^shift
             ≤ 2^(trailing_zeros num.natAbs) := by
               apply Nat.pow_le_pow_right
               · norm_num
               · exact h_shift_le
             _ ≤ num.natAbs := h_lower_bound

       -- Step 5: But h_zero says num / 2^shift = 0
       -- For integers: a / b = 0 means |a| < |b|
       -- So: num.natAbs < 2^shift
       have h_div_zero : num.natAbs < 2^shift := by
         -- From h_zero: shifted_num = 0, that is num / (2^shift : ℤ) = 0
         -- Unfold shifted_num in h_zero
         simp only [shifted_num] at h_zero
         -- Now h_zero : num / (2^shift : ℤ) = 0
         -- Prove by contradiction
         by_contra h_not
         push_neg at h_not
         -- If num.natAbs ≥ 2^shift, then |num| ≥ 2^shift
         -- Case split on sign of num
         by_cases h_num_nonneg : 0 ≤ num
         · -- num ≥ 0
           have h_num_eq : num = (num.natAbs : ℤ) := Int.eq_natAbs_of_nonneg h_num_nonneg
           rw [h_num_eq] at h_zero
           -- Then (num.natAbs : ℤ) / (2^shift : ℤ) = 0
           -- But num.natAbs ≥ 2^shift, so num.natAbs / 2^shift ≥ 1
           have h_ge : 2^shift ≤ num.natAbs := h_not
           -- Use Nat.div_pos: if b ≤ a and b > 0, then a / b > 0
           have h_div_pos : 0 < num.natAbs / 2^shift := by
             apply Nat.div_pos h_ge
             exact Nat.pow_pos (by norm_num : 0 < 2)
          -- So (num.natAbs : ℤ) / (2^shift : ℤ) > 0
           -- Since num.natAbs ≥ 2^shift and integer division rounds down
           have : 0 < (num.natAbs : ℤ) / (2^shift : ℤ) := by
             have : (num.natAbs : ℤ) / (2^shift : ℤ) = ↑(num.natAbs / 2^shift) := by
               norm_cast
             rw [this]
             exact Int.natCast_pos.mpr h_div_pos
           omega
         · -- num < 0
           push_neg at h_num_nonneg
           have h_neg : num < 0 := h_num_nonneg
           -- For negative numbers: if |num| ≥ 2^shift, then num / 2^shift ≤ -1
           have h_ge : 2^shift ≤ num.natAbs := h_not
           -- For num < 0 with num.natAbs ≥ 2^shift:
           -- We know num ≤ -num.natAbs ≤ -(2^shift)
           -- So num / 2^shift ≤ -(2^shift) / 2^shift = -1
           -- Which contradicts h_zero : num / 2^shift = 0
           have : num / (2^shift : ℤ) < 0 := by
             -- For num < 0, division by positive gives negative result
             apply Int.ediv_neg_of_neg_of_pos
             · exact h_neg
             · norm_cast
               exact Nat.pow_pos (by norm_num : 0 < 2)
           omega

       -- Step 6: Contradiction!
       omega,
     by -- normalized: shifted_num is odd OR new_exp = 0
       intro h_nonzero
       -- If shift = exp, then new_exp = 0
       by_cases h_shift : shift = exp
       · right
         show exp - shift = 0
         rw [h_shift]
         simp
       · left
         -- If shift < exp, we need to show shifted_num is odd
         -- shift < exp, so shift = min (trailing_zeros num.natAbs) exp = trailing_zeros num.natAbs
         have h_shift_eq : shift = trailing_zeros num.natAbs := by
           simp only [shift]
           have : trailing_zeros num.natAbs ≤ exp := by
             by_contra h_not_le
             have : exp < trailing_zeros num.natAbs := Nat.lt_of_not_le h_not_le
             have : min (trailing_zeros num.natAbs) exp = exp := Nat.min_eq_right (Nat.le_of_lt this)
             -- But this means shift = exp, contradiction
             simp only [shift] at h_shift
             omega
           exact Nat.min_eq_left this
         -- Use trailing_zeros_spec
         have h_spec := trailing_zeros_spec num.natAbs (by
           intro h
           have : num = 0 := Int.natAbs_eq_zero.mp h
           contradiction)
         simp only at h_spec
         have hm_eq := h_spec.1
         have hm_odd := h_spec.2
         -- From hm_odd: (num.natAbs / 2^(trailing_zeros num.natAbs)) % 2 = 1
         let k := trailing_zeros num.natAbs
         let m := num.natAbs / 2^k
         -- We need to show: (num / 2^shift) % 2 ≠ 0
         -- We know: m = num.natAbs / 2^k and m % 2 = 1
         -- Key: num = ± num.natAbs, so num / 2^k = ± m
         -- Therefore (num / 2^k) % 2 = ±1 % 2 ≠ 0
         show shifted_num % 2 ≠ 0
         simp only [shifted_num]
         rw [h_shift_eq]
         intro h_contra
         -- We have: (num / (2^k : ℤ)) % 2 = 0
         -- But from hm_eq and hm_odd, we know num.natAbs / 2^k is odd
         -- From hm_eq: num.natAbs = m * 2^k, so 2^k divides num.natAbs, hence num
         have h_dvd : (2^k : ℕ) ∣ num.natAbs := by
           rw [hm_eq]; exact dvd_mul_left (2^k) m

         -- From hm_eq: num.natAbs = m * 2^k
         -- Since num = ±num.natAbs, we have num = ±(m * 2^k)
         have h_num_cases : num = ((m * 2^k) : ℤ) ∨ num = -((m * 2^k) : ℤ) := by
           have h_abs : num = (num.natAbs : ℤ) ∨ num = -(num.natAbs : ℤ) := Int.natAbs_eq num
           cases h_abs with
           | inl h_pos =>
             left
             have : (num.natAbs : ℤ) = ((m * 2^k) : ℤ) := by
               have : num.natAbs = m * 2^k := hm_eq
               simp only [this]
               norm_cast
             rw [h_pos, this]
           | inr h_neg =>
             right
             have : (num.natAbs : ℤ) = ((m * 2^k) : ℤ) := by
               have : num.natAbs = m * 2^k := hm_eq
               simp only [this]
               norm_cast
             rw [h_neg, this]

         -- In either case, num / 2^k = ±m
         have h_quot_eq : (num / (2^k : ℤ)) = (m : ℤ) ∨ (num / (2^k : ℤ)) = -(m : ℤ) := by
           have h_pow_ne : (2^k : ℤ) ≠ 0 := by
             norm_cast
             exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by norm_num : 0 < 2))
           have h_pow_dvd : (2^k : ℤ) ∣ ((m * 2^k) : ℤ) := by
             norm_cast
             exact dvd_mul_left (2^k) m
           have h_dvd_pow : (2^k : ℤ) ∣ (2^k : ℤ) := by
             norm_cast
           cases h_num_cases with
           | inl h_pos =>
             left
             rw [h_pos]
             -- ((m * 2^k) : ℤ) / (2^k : ℤ) = m
             have h_eq : ((m * 2^k) : ℤ) = (m : ℤ) * (2^k : ℤ) := by norm_cast
             rw [h_eq, Int.mul_ediv_assoc (m : ℤ) h_dvd_pow]
             have h_div : (2^k : ℤ) / (2^k : ℤ) = 1 := Int.ediv_self h_pow_ne
             simp [h_div]
           | inr h_neg =>
             right
             rw [h_neg]
             -- -((m * 2^k) : ℤ) / (2^k : ℤ) = -m
             have h_eq : ((m * 2^k) : ℤ) = (m : ℤ) * (2^k : ℤ) := by norm_cast
             have h_dvd_mk : (2^k : ℤ) ∣ ((m * 2^k) : ℤ) := by norm_cast; exact dvd_mul_left (2^k) m
             rw [h_eq, Int.neg_ediv_of_dvd h_dvd_mk]
             rw [Int.mul_ediv_assoc (m : ℤ) h_dvd_pow]
             have h_div : (2^k : ℤ) / (2^k : ℤ) = 1 := Int.ediv_self h_pow_ne
             simp [h_div]

         -- Now show that ±m % 2 ≠ 0
         cases h_quot_eq with
         | inl h_pos =>
           -- num / 2^k = m, so (num / 2^k) % 2 = m % 2
           rw [h_pos] at h_contra
           norm_cast at h_contra
           rw [hm_odd] at h_contra
           norm_num at h_contra
         | inr h_neg =>
           -- num / 2^k = -m, so (num / 2^k) % 2 = (-m) % 2
           rw [h_neg] at h_contra
           -- For negative of an odd number: (-m) % 2 ≠ 0
           -- Because m is odd: m % 2 = 1, so (-m) % 2 = -1 or 1 (mod 2)
           have h_m_odd_int : (m : ℤ) % 2 = 1 := by
             norm_cast
           have : (-(m : ℤ)) % 2 ≠ 0 := by
             rw [Int.neg_emod_two]
             rw [h_m_odd_int]
             norm_num
           exact this h_contra
    ⟩

/-- Smart constructors -/
def zero : D := ⟨0, 0, by intro; rfl, by intro h; contradiction⟩

def one : D := ⟨1, 0, by intro h; simp at h, by intro _; right; rfl⟩

def two : D := ⟨1, 1, by intro h; simp at h, by intro _; left; simp⟩

def ofInt (n : ℤ) : D := normalize n 0

def ofNat (n : ℕ) : D := normalize (n : ℤ) 0

/-- Arithmetic operations -/
def add (a b : D) : D :=
  if a.exp ≤ b.exp then
    let shift := b.exp - a.exp
    let raw_num := a.num * (2^shift : ℕ) + b.num
    normalize raw_num b.exp
  else
    let shift := a.exp - b.exp
    let raw_num := a.num + b.num * (2^shift : ℕ)
    normalize raw_num a.exp

def mul (a b : D) : D :=
  normalize (a.num * b.num) (a.exp + b.exp)

def neg (a : D) : D :=
  ⟨-a.num, a.exp,
   by intro h; simp at h; exact a.canonical_zero h,
   by
    intro h_nonzero
    have h_orig := a.normalized (by simp at h_nonzero; exact h_nonzero)
    cases h_orig with
    | inl h_odd =>
      left
      -- Need: (-a.num) % 2 ≠ 0
      -- Have: a.num % 2 ≠ 0
      -- Negation preserves oddness modulo 2
      intro h_contra
      -- If (-a.num) % 2 = 0, then a.num % 2 = 0 (by omega)
      have : a.num % 2 = 0 := by omega
      exact h_odd this
    | inr h_exp => right; exact h_exp⟩

def sub (a b : D) : D := add a (neg b)

def half (a : D) : D := normalize a.num (a.exp + 1)

def divPow2 (a : D) (k : ℕ) : D := normalize a.num (a.exp + k)

/-- Key theorem: normalize preserves value -/
theorem normalize_eq (num : ℤ) (exp : ℕ) :
    toRat (normalize num exp) = num / (2^exp : ℚ) := by
  unfold normalize toRat
  split_ifs with h
  · -- num = 0 case
    simp [h]
  · -- num ≠ 0 case
    simp only []
    -- We have: shifted_num / 2^new_exp = num / 2^exp
    -- Where shifted_num = num / 2^shift and new_exp = exp - shift

    let shift := min (trailing_zeros num.natAbs) exp
    let shifted_num := num / (2^shift : ℤ)
    let new_exp := exp - shift

    -- Key insight: (num / 2^shift) / 2^(exp - shift) = num / 2^exp
    have h_shift_le : shift ≤ exp := Nat.min_le_right _ _

    -- Show: shifted_num / 2^new_exp = num / 2^exp
    show (shifted_num : ℚ) / (2^new_exp : ℚ) = (num : ℚ) / (2^exp : ℚ)

    -- Rewrite using division algebra
    have h_sum : shift + new_exp = exp := by
      show shift + (exp - shift) = exp
      omega

    -- Simplify directly: shifted_num = num / 2^shift, new_exp = exp - shift
    show (shifted_num : ℚ) / (2^new_exp : ℚ) = (num : ℚ) / (2^exp : ℚ)

    -- Prove directly in ℚ
    simp only [shifted_num, new_exp]
    -- Goal: ↑(num / 2 ^ shift) / ↑(2 ^ (exp - shift)) = ↑num / ↑(2 ^ exp) (in ℚ)

    -- Use field algebra: rewrite RHS
    have h_exp : exp = shift + (exp - shift) := by omega
    rw [show (2^exp : ℚ) = (2^shift : ℚ) * (2^(exp - shift) : ℚ) by
        norm_cast; rw [← pow_add, ← h_exp]]
    rw [div_mul_eq_div_div]

    -- Now goal: ↑(num / 2^shift) / ↑(2^(exp - shift)) = (↑num / ↑(2^shift)) / ↑(2^(exp - shift))
    -- So we need: ↑(num / 2^shift) = ↑num / ↑(2^shift)
    congr 1

    -- THE KEY STEP: Show ↑(num / 2^shift : ℤ) = (↑num : ℚ) / ↑(2^shift)
    -- This is true when 2^shift ∣ num

    -- Prove divisibility
    have h_divides : (2^shift : ℤ) ∣ num := by
      -- Use trailing_zeros_spec
      have h_nat_ne_zero : num.natAbs ≠ 0 := by
        intro h_abs; have : num = 0 := Int.natAbs_eq_zero.mp h_abs; contradiction
      have h_spec := trailing_zeros_spec num.natAbs h_nat_ne_zero
      simp only at h_spec
      obtain ⟨hm_eq, hm_odd⟩ := h_spec

      -- From hm_eq: num.natAbs = (num.natAbs / 2^(trailing_zeros num.natAbs)) * 2^(trailing_zeros num.natAbs)
      -- So: 2^(trailing_zeros num.natAbs) ∣ num.natAbs
      -- Since shift ≤ trailing_zeros num.natAbs, we have 2^shift ∣ num.natAbs
      -- Therefore 2^shift ∣ num

      have h_shift_le : shift ≤ trailing_zeros num.natAbs := Nat.min_le_left _ _

      -- 2^shift ∣ 2^(trailing_zeros num.natAbs)
      have h_pow_div : (2^shift : ℕ) ∣ 2^(trailing_zeros num.natAbs) := by
        apply Nat.pow_dvd_pow
        exact h_shift_le

      -- And 2^(trailing_zeros num.natAbs) ∣ num.natAbs (from hm_eq)
      set m := num.natAbs / 2^(trailing_zeros num.natAbs)
      have h_trail_div : 2^(trailing_zeros num.natAbs) ∣ num.natAbs := by
        use m
        rw [mul_comm]
        exact hm_eq

      -- By transitivity: 2^shift ∣ num.natAbs
      have h_shift_div_natabs : (2^shift : ℕ) ∣ num.natAbs := Nat.dvd_trans h_pow_div h_trail_div

      -- Convert to ℤ divisibility: (2^shift : ℤ) ∣ num
      -- We have (2^shift : ℕ) ∣ num.natAbs, need to show (2^shift : ℤ) ∣ num
      obtain ⟨k, hk⟩ := h_shift_div_natabs
      -- hk : num.natAbs = 2^shift * k
      -- So num = ±(2^shift * k)
      by_cases h_pos : 0 ≤ num
      · -- num ≥ 0, so num = num.natAbs = 2^shift * k
        use (k : ℤ)
        have : num = (num.natAbs : ℤ) := Int.eq_natAbs_of_nonneg h_pos
        rw [this, hk]
        norm_cast
      · -- num < 0, so num = -num.natAbs = -(2^shift * k)
        use (-(k : ℤ))
        -- For negative numbers, we have num.natAbs = -num (by definition)
        have h_neg : num < 0 := Int.not_le.mp h_pos
        have h_abs_eq : (num.natAbs : ℤ) = -num := Int.natAbs_neg num ▸ Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos (Int.le_of_lt h_neg))
        calc num
            = -(-num) := by simp
          _ = -(num.natAbs : ℤ) := by rw [← h_abs_eq]
          _ = -((2^shift * k : ℕ) : ℤ) := by rw [hk]
          _ = (2^shift : ℤ) * (-(k : ℤ)) := by push_cast; ring

    -- Now use divisibility to relate integer and rational division
    have h_pow_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by
      norm_cast
      exact pow_ne_zero shift (by norm_num : (2 : ℕ) ≠ 0)
    have key := Int.cast_div h_divides h_pow_ne
    -- key : ((num / 2^shift : ℤ) : ℚ) = (num : ℚ) / ((2^shift : ℤ) : ℚ)
    rw [key]
    congr 1
    norm_cast

/-- Helper: Odd integers -/
def Odd (n : ℤ) : Prop := n % 2 ≠ 0

/-- Helper: Even integers -/
def Even (n : ℤ) : Prop := n % 2 = 0

/-- Helper lemma for unique representation -/
lemma pow2_factor_unique {a b : ℤ} {m n : ℕ}
    (ha : Odd a) (hb : Odd b)
    (h : a * (2^m : ℤ) = b * (2^n : ℤ)) :
    a = b ∧ m = n := by
  -- Key insight: if a·2^m = b·2^n with a,b odd, then a=b and m=n
  by_cases hmn : m < n
  · -- If m < n, then a = b·2^(n-m) which is even (contradiction)
    have h_n_decomp : n = m + (n - m) := by omega
    rw [h_n_decomp, pow_add] at h
    have h2m_ne_zero : (2^m : ℤ) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
    have : a = b * (2^(n - m) : ℤ) := by
      -- h says: a * 2^m = b * (2^m * 2^(n - m))
      have h' : a * (2^m : ℤ) = b * (2^m * 2^(n - m) : ℤ) := h
      have : b * (2^m * 2^(n - m) : ℤ) = b * 2^(n - m) * 2^m := by ring
      rw [this] at h'
      exact mul_right_cancel₀ h2m_ne_zero h'
    -- But a is odd and b·2^(n-m) is even
    have h_even : Even (b * (2^(n - m) : ℤ)) := by
      unfold Even
      have : n - m > 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      rw [hk, pow_succ]
      show b * (2^k * 2) % 2 = 0
      have : b * (2^k * 2) = b * 2^k * 2 := by ring
      rw [this]
      simp
    rw [← this] at h_even
    unfold Even at h_even
    unfold Odd at ha
    contradiction
  · by_cases hnm : n < m
    · -- Symmetric case
      have h_m_decomp : m = n + (m - n) := by omega
      rw [h_m_decomp, pow_add] at h
      have h2n_ne_zero : (2^n : ℤ) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
      have : b = a * (2^(m - n) : ℤ) := by
        -- h says: a * (2^n * 2^(m - n)) = b * 2^n
        have h' : a * (2^n * 2^(m - n) : ℤ) = b * (2^n : ℤ) := h
        have : a * (2^n * 2^(m - n) : ℤ) = a * 2^(m - n) * 2^n := by ring
        rw [this] at h'
        exact (mul_right_cancel₀ h2n_ne_zero h').symm
      have h_even : Even (a * (2^(m - n) : ℤ)) := by
        unfold Even
        have : m - n > 0 := by omega
        obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
        rw [hk, pow_succ]
        show a * (2^k * 2) % 2 = 0
        have : a * (2^k * 2) = a * 2^k * 2 := by ring
        rw [this]
        simp
      rw [← this] at h_even
      unfold Even at h_even
      unfold Odd at hb
      contradiction
    · -- m = n
      have hmn_eq : m = n := by omega
      rw [hmn_eq] at h
      have h2n_ne_zero : (2^n : ℤ) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
      have : a = b := by
        have h' : a * (2^n : ℤ) = b * (2^n : ℤ) := h
        exact (mul_right_cancel₀ h2n_ne_zero h')
      exact ⟨this, hmn_eq⟩

/-- The main extensionality theorem:
    Equal as rationals implies structurally equal -/
@[ext]
theorem D_ext {a b : D} (h : toRat a = toRat b) : a = b := by
  -- Key: with both invariants, the representation is unique
  unfold toRat at h
  have h_eq : a.num * (2^b.exp : ℤ) = b.num * (2^a.exp : ℤ) := by
    field_simp at h
    have h' : (a.num : ℚ) * (2^b.exp : ℚ) = (b.num : ℚ) * (2^a.exp : ℚ) := by
      rw [mul_comm (2^a.exp : ℚ) (b.num : ℚ)] at h
      exact h
    have : (↑(a.num * (2^b.exp : ℤ)) : ℚ) = (↑(b.num * (2^a.exp : ℤ)) : ℚ) := by
      push_cast
      exact h'
    exact Int.cast_injective this

  -- Case analysis on whether numerators are zero
  by_cases ha_zero : a.num = 0
  · -- a.num = 0 implies b.num = 0
    have hb_zero : b.num = 0 := by
      rw [ha_zero] at h_eq
      simp only [zero_mul] at h_eq
      have : 0 = b.num * (2^a.exp : ℤ) := h_eq
      have pow_ne : (2^a.exp : ℤ) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
      have : b.num * (2^a.exp : ℤ) = 0 := this.symm
      exact (mul_eq_zero.mp this).resolve_right pow_ne
    -- Both are zero, so by canonical_zero they must be ⟨0, 0⟩
    have ha_exp : a.exp = 0 := a.canonical_zero ha_zero
    have hb_exp : b.exp = 0 := b.canonical_zero hb_zero
    -- Apply extensionality manually
    cases a with | mk num_a exp_a _ _ =>
    cases b with | mk num_b exp_b _ _ =>
    simp only [D.mk.injEq]
    constructor
    · exact ha_zero.trans hb_zero.symm
    · exact ha_exp.trans hb_exp.symm
  · -- a.num ≠ 0, so b.num ≠ 0 too
    have hb_nonzero : b.num ≠ 0 := by
      by_contra hb_zero
      rw [hb_zero] at h_eq
      have : a.num * (2^b.exp : ℤ) = 0 * (2^a.exp : ℤ) := h_eq
      simp only [zero_mul] at this
      have pow_ne : (2^b.exp : ℤ) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
      have : a.num = 0 := (mul_eq_zero.mp this).resolve_right pow_ne
      exact ha_zero this

    -- Use the normalized invariant
    have ha_norm := a.normalized ha_zero
    have hb_norm := b.normalized hb_nonzero

    -- Case analysis on the normalized conditions
    cases ha_norm with
    | inl ha_odd =>
      cases hb_norm with
      | inl hb_odd =>
        -- Both numerators are odd
        have ⟨h_num, h_exp⟩ := pow2_factor_unique ha_odd hb_odd h_eq
        cases a with | mk num_a exp_a _ _ =>
        cases b with | mk num_b exp_b _ _ =>
        simp only [D.mk.injEq]
        constructor
        · simpa using h_num
        · simpa using h_exp.symm
      | inr hb_exp_zero =>
        -- a.num is odd, b.exp = 0
        -- We're given hb_norm says: b.num is odd OR b.exp = 0
        -- We're in the case where hb_norm gave us b.exp = 0 (i.e., hb_exp_zero)
        -- So we can't necessarily conclude b.num is odd
        -- However, from h_eq and oddness of a.num, we can derive a.exp = 0
        rw [hb_exp_zero, pow_zero, mul_one] at h_eq
        have ha_exp_zero : a.exp = 0 := by
          by_contra h_nonzero
          -- If a.exp > 0 and a.num is odd, then a.num * 2^a.exp has exactly a.exp factors of 2
          -- But h_eq says a.num * 2^a.exp = b.num (since hb_exp_zero: b.exp = 0)
          -- So b.num has a.exp > 0 factors of 2
          -- This means b.num is even, so b.num / 2 is an integer
          -- But then b is not normalized (we should have factored out that 2)
          -- Contradiction with the normalized invariant for b
          have : a.exp > 0 := Nat.pos_of_ne_zero h_nonzero
          obtain ⟨k, hk⟩ : ∃ k, a.exp = k + 1 := ⟨a.exp - 1, by omega⟩
          rw [hk, pow_succ] at h_eq
          -- After rw [hk, pow_succ]: h_eq is a.num = b.num * (2^k * 2)
          have h_eq_simplified : a.num = b.num * (2^k * 2) := h_eq
          -- So a.num is even (contradiction with ha_odd)
          have h_a_even : a.num % 2 = 0 := by
            calc a.num % 2
              = (b.num * (2^k * 2)) % 2 := by rw [h_eq_simplified]
              _ = (b.num * 2^k * 2) % 2 := by ring_nf
              _ = 0 := by simp
          -- ha_odd says a.num % 2 ≠ 0, but we just showed a.num % 2 = 0
          have : Odd a.num := ha_odd
          unfold Odd at this
          omega
        rw [ha_exp_zero, pow_zero, mul_one] at h_eq
        cases a with | mk num_a exp_a _ _ =>
        cases b with | mk num_b exp_b _ _ =>
        simp only [D.mk.injEq]
        constructor
        · simpa using h_eq
        · simpa using (ha_exp_zero.trans hb_exp_zero.symm)
    | inr ha_exp_zero =>
      cases hb_norm with
      | inl hb_odd =>
        -- a.exp = 0, b.num is odd
        -- Similar to above case but symmetric
        rw [ha_exp_zero, pow_zero, mul_one] at h_eq
        have hb_exp_zero : b.exp = 0 := by
          by_contra h_nonzero
          -- Symmetric to the above case
          -- h_eq currently: a.num = b.num * 2^b.exp (after simplification)
          -- b.num is odd, b.exp > 0
          have : b.exp > 0 := Nat.pos_of_ne_zero h_nonzero
          obtain ⟨k, hk⟩ : ∃ k, b.exp = k + 1 := ⟨b.exp - 1, by omega⟩
          rw [hk, pow_succ] at h_eq
          -- h_eq: a.num * 2^(k+1) = b.num, so a.num * (2^k * 2) = b.num
          -- Since b.num is odd, a.num * 2^k * 2 must be odd (contradiction)
          exfalso
          -- Original h_eq (before rw): a.num * 2^b.exp = b.num * 2^a.exp
          -- After rw [ha_exp_zero]: a.num * 2^b.exp = b.num * 1
          -- So: a.num * 2^b.exp = b.num
          -- After rw [hk]: a.num * 2^(k+1) = b.num
          -- After rw [pow_succ]: a.num * (2^k * 2) = b.num
          have h_eq_simplified : b.num = a.num * (2^k * 2) := h_eq.symm
          have : Even b.num := by
            unfold Even
            rw [h_eq_simplified]
            ring_nf
            simp
          have : Odd b.num := hb_odd
          unfold Odd Even at *
          omega
        rw [hb_exp_zero, pow_zero, mul_one] at h_eq
        cases a with | mk num_a exp_a _ _ =>
        cases b with | mk num_b exp_b _ _ =>
        simp only [D.mk.injEq]
        constructor
        · simpa using h_eq
        · simpa using (ha_exp_zero.trans hb_exp_zero.symm)
      | inr hb_exp_zero =>
        -- Both exponents are 0
        rw [ha_exp_zero, hb_exp_zero] at h_eq
        simp only [pow_zero, mul_one] at h_eq
        cases a with | mk num_a exp_a _ _ =>
        cases b with | mk num_b exp_b _ _ =>
        simp only [D.mk.injEq]
        constructor
        · simpa using h_eq
        · simpa using (ha_exp_zero.trans hb_exp_zero.symm)

/-- Arithmetic correctness proofs -/
theorem toRat_add (a b : D) : toRat (add a b) = toRat a + toRat b := by
  unfold add
  split_ifs with h
  · rw [normalize_eq]; unfold toRat
    have h_eq : b.exp - a.exp + a.exp = b.exp := by omega
    field_simp
    -- Goal: (a.num * 2^(b.exp - a.exp) + b.num) * 2^a.exp = a.num * 2^b.exp + b.num * 2^a.exp (in ℚ)
    push_cast
    ring_nf
    congr 1
    have : (2 : ℚ)^(b.exp - a.exp) * (2 : ℚ)^a.exp = (2 : ℚ)^b.exp := by
      rw [← pow_add, h_eq]
    calc (a.num : ℚ) * (2 : ℚ)^(b.exp - a.exp) * (2 : ℚ)^a.exp
        = (a.num : ℚ) * ((2 : ℚ)^(b.exp - a.exp) * (2 : ℚ)^a.exp) := by ring
      _ = (a.num : ℚ) * (2 : ℚ)^b.exp := by rw [this]
  · rw [normalize_eq]; unfold toRat
    have h_eq : a.exp - b.exp + b.exp = a.exp := by omega
    field_simp
    -- Goal: (a.num + b.num * 2^(a.exp - b.exp)) * 2^b.exp = a.num * 2^b.exp + b.num * 2^a.exp (in ℚ)
    push_cast
    ring_nf
    congr 1
    have : (2 : ℚ)^(a.exp - b.exp) * (2 : ℚ)^b.exp = (2 : ℚ)^a.exp := by
      rw [← pow_add, h_eq]
    calc (b.num : ℚ) * (2 : ℚ)^(a.exp - b.exp) * (2 : ℚ)^b.exp
        = (b.num : ℚ) * ((2 : ℚ)^(a.exp - b.exp) * (2 : ℚ)^b.exp) := by ring
      _ = (b.num : ℚ) * (2 : ℚ)^a.exp := by rw [this]

/-- Round dyadic to specified precision (bits) -/
def roundToPrecision (d : D) (maxPrecision : ℕ) : D :=
  if d.exp ≤ maxPrecision then
    d  -- Already within precision bound
  else
    -- Need to reduce precision: shift numerator and reduce exponent
    let excessBits := d.exp - maxPrecision
    -- Round to nearest: add 2^(excessBits-1) before division
    let halfRound := if excessBits > 0 then (2^(excessBits - 1) : ℤ) else 0
    let roundedNum := (d.num + halfRound) / (2^excessBits : ℤ)
    normalize roundedNum maxPrecision

/-- Bounded-precision addition (rounds result) -/
def add_bounded (a b : D) (precision : ℕ) : D :=
  roundToPrecision (add a b) precision

/-- Bounded-precision multiplication (rounds result) -/
def mul_bounded (a b : D) (precision : ℕ) : D :=
  roundToPrecision (mul a b) precision

/-- Bounded-precision negation (preserves precision) -/
def neg_bounded (a : D) (maxPrecision : ℕ) : D :=
  roundToPrecision (neg a) maxPrecision

/-- Bounded-precision subtraction (rounds result) -/
def sub_bounded (a b : D) (maxPrecision : ℕ) : D :=
  roundToPrecision (sub a b) maxPrecision

theorem toRat_mul (a b : D) : toRat (mul a b) = toRat a * toRat b := by
  unfold mul
  rw [normalize_eq]; unfold toRat
  field_simp
  push_cast
  rw [pow_add]
  ring

theorem toRat_neg (a : D) : toRat (neg a) = -(toRat a) := by
  unfold neg toRat; simp [neg_div]

theorem toRat_sub (a b : D) : toRat (sub a b) = toRat a - toRat b := by
  unfold sub; rw [toRat_add, toRat_neg]; simp [sub_eq_add_neg]

theorem toRat_half (a : D) : toRat (half a) = toRat a / 2 := by
  unfold half; rw [normalize_eq]; unfold toRat
  rw [div_div]
  norm_cast

theorem toRat_divPow2 (a : D) (k : ℕ) :
    toRat (divPow2 a k) = toRat a / (2^k : ℚ) := by
  unfold divPow2; rw [normalize_eq]; unfold toRat
  rw [div_div]; congr 1; norm_cast; rw [pow_add]

/-- Ring instances -/
instance : Add D := ⟨add⟩
instance : Mul D := ⟨mul⟩
instance : Neg D := ⟨neg⟩
instance : Sub D := ⟨sub⟩
instance : Zero D := ⟨zero⟩
instance : One D := ⟨one⟩

-- Helper lemmas to connect instances with operations
@[simp] lemma add_def (a b : D) : a + b = add a b := rfl
@[simp] lemma mul_def (a b : D) : a * b = mul a b := rfl
@[simp] lemma neg_def (a : D) : -a = neg a := rfl
@[simp] lemma sub_def (a b : D) : a - b = sub a b := rfl
@[simp] lemma zero_def : (0 : D) = zero := rfl
@[simp] lemma one_def : (1 : D) = one := rfl

-- Prove ring axioms using toRat and D_ext
theorem add_comm (a b : D) : a + b = b + a := by
  apply D_ext; simp only [add_def]; rw [toRat_add, toRat_add]; ring

theorem add_assoc (a b c : D) : (a + b) + c = a + (b + c) := by
  apply D_ext; simp only [add_def]; rw [toRat_add, toRat_add, toRat_add, toRat_add]; ring

theorem zero_add (a : D) : 0 + a = a := by
  apply D_ext; simp only [add_def, zero_def]; rw [toRat_add]; unfold zero toRat; simp

theorem add_zero (a : D) : a + 0 = a := by
  apply D_ext; simp only [add_def, zero_def]; rw [toRat_add]; unfold zero toRat; simp

theorem add_left_neg (a : D) : (-a) + a = 0 := by
  apply D_ext; simp only [add_def, neg_def, zero_def]
  rw [toRat_add, toRat_neg]; unfold zero toRat; simp

theorem mul_comm (a b : D) : a * b = b * a := by
  apply D_ext; simp only [mul_def]; rw [toRat_mul, toRat_mul]; ring

theorem mul_assoc (a b c : D) : (a * b) * c = a * (b * c) := by
  apply D_ext; simp only [mul_def]; rw [toRat_mul, toRat_mul, toRat_mul, toRat_mul]; ring

theorem one_mul (a : D) : 1 * a = a := by
  apply D_ext; simp only [mul_def, one_def]; rw [toRat_mul]; unfold one toRat; simp

theorem mul_one (a : D) : a * 1 = a := by
  apply D_ext; simp only [mul_def, one_def]; rw [toRat_mul]; unfold one toRat; simp

theorem left_distrib (a b c : D) : a * (b + c) = a * b + a * c := by
  apply D_ext; simp only [add_def, mul_def]
  rw [toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul]; ring

theorem right_distrib (a b c : D) : (a + b) * c = a * c + b * c := by
  apply D_ext; simp only [add_def, mul_def]
  rw [toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul]; ring

theorem sub_eq_add_neg (a b : D) : a - b = a + (-b) := rfl

/-- Examples showing the type in action -/
example : toRat zero = 0 := by simp [toRat, zero]
example : toRat one = 1 := by simp [toRat, one]
example : toRat two = 1 / 2 := by simp [toRat, two, pow_one]

/-! ## Helper lemmas for IntervalDyadic -/

/-- toRat of zero is zero -/
@[simp]
theorem zero_toRat : toRat zero = 0 := by
  simp [zero, toRat]

/-- toRat of one is one -/
@[simp]
theorem one_toRat : toRat one = 1 := by
  simp [one, toRat]

/-- Negation reverses order -/
theorem neg_le_neg' {a b : D} (h : toRat a ≤ toRat b) :
    toRat (neg b) ≤ toRat (neg a) := by
  simp only [toRat_neg]
  exact neg_le_neg_iff.mpr h

/-- toRat respects order for comparison -/
theorem toRat_le_toRat {a b : D} :
    toRat a ≤ toRat b ↔ a.num * (2^b.exp : ℚ) ≤ b.num * (2^a.exp : ℚ) := by
  unfold toRat
  have ha_pos : (0 : ℚ) < 2^a.exp := by norm_cast; exact Nat.pow_pos (by norm_num)
  have hb_pos : (0 : ℚ) < 2^b.exp := by norm_cast; exact Nat.pow_pos (by norm_num)
  rw [div_le_div_iff₀ ha_pos hb_pos]

/-- Multiplication preserves non-negativity -/
theorem mul_nonneg {a b : D} (ha : 0 ≤ toRat a) (hb : 0 ≤ toRat b) :
    0 ≤ toRat (mul a b) := by
  simp [toRat_mul]
  exact _root_.mul_nonneg ha hb

end DyadicCanonical

-- Export bounded operations for easy use (must be outside namespace)
export DyadicCanonical (roundToPrecision add_bounded mul_bounded neg_bounded sub_bounded zero_toRat)
