import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  {name}`Chapter2.Nat`.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  . exact zero_mul 0
  intro n ih
  rw [succ_mul, add_zero, ih]

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  . repeat rw [zero_mul]
    simp
  intro n ih
  calc
    n++ * m++ = n * m++ + m++ := by rw [succ_mul]
    _ = n * m + n + m++ := by rw [ih]
    _ = n * m + n++ + m := by rw [add_assoc, add_succ, ← succ_add, add_assoc]
  symm
  calc
    n++ * m + n++ = n * m + (m + n++) := by rw [succ_mul, add_assoc]
    _ = n * m + n++ + m := by nth_rw 2 [add_comm]; rw [add_assoc]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert n; apply induction
  . rw [zero_mul, mul_zero]
  intro n ih
  calc
    n++ * m = n * m + m := by rw [succ_mul]
    _ = m * n + m := by rw [ih]
  symm
  calc
    m * n++ = m * n + m := by rw [mul_succ]

/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  apply (uniq_succ_eq n) at h₁
  obtain ⟨b, hb⟩ := h₁
  have hbsucc : b++ = n := hb.left
  by_contra! hc
  rw [isPos_iff] at hc
  simp at hc
  rw [← hbsucc, succ_mul] at hc
  apply add_eq_zero at hc
  tauto

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  . contrapose!
    rw [← isPos_iff]
    rw [← isPos_iff]
    rw [← isPos_iff]
    intro hp
    apply pos_mul_pos hp.left hp.right
  intro hnm
  cases hnm with
  | inl hn =>
    rw [hn, zero_mul]
  | inr hm =>
    rw [hm, mul_zero]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  . rw [mul_zero, mul_zero, mul_zero]
  intro c ih
  calc
    a * b * c++ = (a * b) * c + a * b := by rw [mul_succ]
    _ = a * (b * c) + a * b := by rw [ih]
  symm
  calc
    a * (b * c++) = a * (b * c + b) := by rw [mul_succ]
    _ = a * (b * c) + a * b := by rw [mul_add]

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Not from textbook) {name}`Nat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a _ b c hbc
    obtain ⟨d, hd⟩ := hbc
    use a * d
    rw [hd]
    ring_nf
  mul_le_mul_of_nonneg_right := by
    intro c hc a b hab
    obtain ⟨d, hd⟩ := hab
    use c * d
    rw [hd]
    ring_nf

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  . use 0, 0
    simp
    rw [isPos_iff] at hq
    tauto
  intro n ih
  obtain ⟨m, r, h⟩ := ih
  by_cases hr : (r++) = q
  . use m++, 0
    simp
    rw [isPos_iff] at hq
    have hzlq : 0 < q := by tauto
    have hnsucc : n++ = m++ * q := by
      rw [succ_mul]
      nth_rw 2 [← hr]
      have hnmqr : n = m * q + r := h.right.right
      rw [hnmqr, add_succ]
    exact ⟨hzlq, hnsucc⟩
  use m, (r++)
  have hrq : r++ < q := by
    have hrltq : r < q := h.right.left
    have hrleq : r++ ≤ q := by
      rw [lt_iff_succ_le] at hrltq
      exact hrltq
    tauto
  have hzler: 0 ≤ r++ := zero_le (r++)
  have nmqrsucc : n++ = m * q + r++ := by
    have nmqr : n = m * q + r := h.right.right
    rw [nmqr, add_succ]
  exact ⟨hzler, hrq, nmqrsucc⟩

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4 -/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  calc
    (a + b) ^ (2 : Nat) = (a + b) * (a + b) := by rw [← one_succ, pow_succ, pow_one]
    _ = (a + b) * a + (a + b) * b := by rw [mul_add]
    _ = a * a + b * a + (a * b + b * b) := by rw [add_mul, add_mul]
    _ = a ^ (2 : Nat) + a * b + (a * b + b * b) := by
      nth_rw 1 [← pow_one a]
      rw [← pow_succ, one_succ, mul_comm]
    _ = a ^ (2 : Nat) + a * b + (a * b + b ^ (2 : Nat)) := by
      nth_rw 3 [← pow_one b]
      rw [← pow_succ, one_succ, mul_comm]
    _ = a ^ (2 : Nat) + (a * b + a * b) + b ^ (2 : Nat) := by ring
    _ = a ^ (2 : Nat) + (a * b * 1 + a * b * 1) + b ^ (2 : Nat) := by ring
    _ = a ^ (2 : Nat) + a * b * (1 + 1) + b ^ (2 : Nat) := by ring
    _ = a ^ (2 : Nat) + a * b * 2 + b ^ (2 : Nat) := by rw [← succ_eq_add_one, one_succ]
    _ = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by ring

end Chapter2
