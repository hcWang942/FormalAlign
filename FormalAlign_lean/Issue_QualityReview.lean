import Mathlib

/-
# Quality Review Issues in Lean Formalization

This file contains examples of common issues found in auto-formalization and their corrections.
Each issue type is documented with both incorrect (neg) and correct (pos) examples.
-/

/- ## Issue 1: Range Modification (范围修改)
- Incorrectly modifying the range boundaries of sets or indices.
For example, changing Finset.Icc 1 100 (closed interval [1,100]) to
Finset.range 100 (half-open interval [0,100)).
- 虽然仍然索引了100个数，不影响答案，但是还是和原题有gap。



Original Problem:
Select a subset A from the set {1, 2, ..., 100} such that there are no
two consecutive integers in A. How many ways are there to do this?
Answer: (1/√5) * [((1+√5)/2)^102 - ((1-√5)/2)^102]

从集合 {1, 2, ⋯, 100} 中选取一个子集 A, 使得 A 中不存在连续两个整数. 问有多少种选取方法?
答案是：(1/√5) * [((1+√5)/2)^102 - ((1-√5)/2)^102]
-/

-- Negative example: Using wrong range
theorem neg_range :
  Finset.card (Finset.filter (fun A : Finset ℕ => ∀ i ∈ A, i + 1 ∉ A)
  (Finset.powerset (Finset.range 100))) =
  (1 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ 102 - ((1 - Real.sqrt 5) / 2) ^ 102) := by sorry

-- Positive example: Using correct range that matches the problem
theorem pos_range :
  Finset.card (Finset.filter (fun A : Finset ℕ => ∀ i ∈ A, i + 1 ∉ A)
  (Finset.powerset (Finset.Icc 1 100))) =
  (1 / Real.sqrt 5) * (((1 + Real.sqrt 5) / 2) ^ 102 - ((1 - Real.sqrt 5) / 2) ^ 102) := by sorry

/- ## Issue 2: Index Shift Error (索引偏移错误)
Using incorrect index ranges in arrays, sequences, or summations.
For example, changing Finset.range (n + 1) (from 0 to n) to
Finset.Icc 1 n (from 1 to n), which affects the answer.

Binomial theorem: (a + b)^n = Σ_{k=0}^n C(n,k) * a^(n-k) * b^k
-/

-- Negative example: Wrong index range
theorem neg_index :
  ∀ (n : ℕ) (a b : ℝ), (a + b) ^ n =
  ∑ k ∈ Finset.Icc 1 n, (Nat.choose n k : ℝ) * a ^ (n - k) * b ^ k := by sorry

-- Positive example: Correct index range matching mathematical definition
theorem pos_index :
  ∀ (n : ℕ) (a b : ℝ), (a + b) ^ n =
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * a ^ (n - k) * b ^ k := by sorry

/- ## Issue 3: Constraint Missing (约束缺失)
Missing key constraint conditions, especially when problems require
positive integers, non-zero values, etc.

Common confusion between:
- Natural number (ℕ): includes 0
- Positive Natural number (ℕ+): excludes 0
- Or use constraints like (n : ℕ) (hn: n > 0)
-/

/- ### Example 3.1
Original Problem:
Prove that any positive integer can be expressed as the difference of
two positive integers a and b, and the number of distinct prime factors
of a and b is the same.

证明：任意一个正整数都可以表示为某两个正整数 a, b 的差，
并且 a, b 的不同素因子的个数相同.
-/

-- Negative example: Missing positivity constraints
theorem neg_constraint_1 (n : ℕ) :
  ∃ (a b : ℕ), a > b ∧
  a - b = n ∧
  Finset.card (Finset.filter Nat.Prime (Nat.divisors a)) =
  Finset.card (Finset.filter Nat.Prime (Nat.divisors b)) := by sorry

-- Positive example: Using ℕ+ or explicit constraints
theorem pos_constraint_1a (n : ℕ) (h_n : n > 0):
  ∃ (a b : ℕ+), a > b ∧
  a - b = n ∧
  Finset.card (Finset.filter Nat.Prime (Nat.divisors a)) =
  Finset.card (Finset.filter Nat.Prime (Nat.divisors b)) := by sorry

-- Alternative positive example: Using explicit constraints
theorem pos_constraint_1b (n : ℕ) (h_n : n > 0):
  ∃ (a b : ℕ),
  a > b ∧
  b ≥ 1 ∧
  a - b = n ∧
  Finset.card (Finset.filter Nat.Prime (Nat.divisors a)) =
  Finset.card (Finset.filter Nat.Prime (Nat.divisors b)) := by sorry

/- ### Example 3.2
Original Problem:
Given that {aₙ} is a sequence of positive numbers satisfying a₁=1,
and (n²+1)aₙ₋₁² = (n-1)²aₙ² for n ≥ 2, prove that
1/a₁ + 1/(2a₂) + ⋯ + 1/(naₙ) ≤ 1 + √(1 - n²/aₙ²)

已知 {aₙ} 为正数数列, 满足 a₁=1, (n²+1)aₙ₋₁²=(n-1)²aₙ²(n ≥ 2),
证明 1/a₁ + 1/(2a₂) + ⋯ + 1/(naₙ) ≤ 1 + √(1 - n²/aₙ²).
-/

-- Negative example: Missing positivity constraint for sequence
theorem neg_constraint_2 (a : ℕ → ℝ):
  (a 1 = 1) ∧
  (∀ n : ℕ, n ≥ 2 → (n^2 + 1) * (a (n - 1))^2 = (n - 1)^2 * (a n)^2) →
  ∀ n : ℕ, n ≥ 1 →
  Finset.sum (Finset.Icc 1 n) (fun i => 1 / (i * a i)) ≤ 1 + Real.sqrt (1 - (n^2) / (a n)^2) := by sorry

-- Positive example: Including positivity constraint
theorem pos_constraint_2 (a : ℕ → ℝ):
  (∀ n : ℕ, n ≥ 1 → a n > 0) ∧
  (a 1 = 1) ∧
  (∀ n : ℕ, n ≥ 2 → (n^2 + 1) * (a (n - 1))^2 = (n - 1)^2 * (a n)^2) →
  ∀ n : ℕ, n ≥ 1 →
  Finset.sum (Finset.Icc 1 n) (fun i => 1 / (i * a i)) ≤ 1 + Real.sqrt (1 - (n^2) / (a n)^2) := by sorry

/- ### Example 3.3
Original Problem:
If p and q are distinct natural numbers, and in an arithmetic sequence,
Sₚ = Sq. Prove that Sₚ₊q = 0.

如果 p, q 是互不相等的自然数, 且在一个等差数列中, Sₚ=Sq.
证明: Sₚ₊q=0.
-/

-- Negative example: Domain constraints incomplete (allows p=0 or q=0)
theorem neg_constraint_3
  (a : ℕ → ℝ)
  (S : ℕ → ℝ)
  (p q : ℕ)
  (d : ℝ)
  (h_pq : p ≠ q)
  (h_arith : ∀ n : ℕ, a (n + 1) - a n = d)
  (h_sum : ∀ n : ℕ, 1 ≤ n → S n = ∑ i ∈ Finset.Icc 1 n, a i)
  (h_Speq : S p = S q) :
  S (p + q) = 0 := by sorry

-- Positive example: Adding proper constraints
theorem pos_constraint_3
  (a : ℕ → ℝ)
  (S : ℕ → ℝ)
  (p q : ℕ) (h_p : 1 ≤ p) (h_q : 1 ≤ q)
  (d : ℝ)
  (h_pq : p ≠ q)
  (h_arith : ∀ n : ℕ, a (n + 1) - a n = d)
  (h_sum : ∀ n : ℕ, 1 ≤ n → S n = ∑ i ∈ Finset.Icc 1 n, a i)
  (h_Speq : S p = S q) :
  S (p + q) = 0 := by sorry

/- ## Issue 4: Operator Precedence Error (运算符优先级错误)
Missing parentheses leading to incorrect operator precedence.
For example, writing (a + b) * c as a + b * c.

Original Problem:
Given the sequence {aₙ} satisfying a₁=2t-3 (t ∈ ℝ, t ≠ ±1),
aₙ₊₁ = [(2t^(n+1)-3)aₙ + 2(t-1)t^n - 1] / [aₙ + 2t^n - 1] (n ∈ ℕ⁺)
For t>0, compare the magnitudes of aₙ₊₁ and aₙ.
Answer: aₙ₊₁ > aₙ, n ∈ ℕ⁺.

设已知数列 {aₙ} 满足 a₁=2t-3 (t ∈ ℝ, t ≠ ±1),
aₙ₊₁=[(2t^(n+1)-3)aₙ+2(t-1)t^n-1]/[aₙ+2t^n-1] (n ∈ ℕ⁺),
求 t>0, 试比较 aₙ₊₁ 与 aₙ的大小.
答案是 aₙ₊₁>aₙ, (n ∈ ℕ⁺).
-/

-- Negative example: Missing parentheses causing precedence error
theorem neg_precedence (a : ℕ → ℝ) (t : ℝ) :
  t > 0 ∧ t ≠ 1 ∧ t ≠ -1 ∧ a 1 = 2 * t - 3 ∧
  (∀ n : ℕ, n ≥ 1 → a (n + 1) = (2 * t^(n + 1) - 3) * a n + 2 * (t - 1) * t^n - 1 / (a n + 2 * t^n - 1)) →
  ∀ n : ℕ, n ≥ 1 → a (n + 1) > a n := by sorry

-- Positive example: Correct parentheses for proper precedence
theorem pos_precedence (a : ℕ → ℝ) (t : ℝ) :
  t > 0 ∧ t ≠ 1 ∧ t ≠ -1 ∧ a 1 = 2 * t - 3 ∧
  (∀ n : ℕ, n ≥ 1 → a (n + 1) = ((2 * t^(n + 1) - 3) * a n + 2 * (t - 1) * t^n - 1) / (a n + 2 * t^n - 1)) →
  ∀ n : ℕ, n ≥ 1 → a (n + 1) > a n := by sorry

/- ## Issue 5: Better Formalization Practices (更符合形式化习惯的例子)
Using more idiomatic Lean constructions instead of verbose alternatives.

Original Problem:
Consider strings of length 99 composed of the letters x, y, and z,
where each letter appears an odd number of times. Find the number of such strings.
Answer: (1/4)(3^99 - 3).

考虑用字母 x, y, z 构成的长度为 99 的字符串, 其中每个字母均出现奇数次.
求这样的字符串的个数。答案是 (1/4)(3^99 - 3).
-/

-- Negative example: Using verbose if-then-else instead of filter
theorem neg_style :
    Finset.card ((Finset.pi (Finset.univ : Finset (Fin 99))
    (fun _ => (Finset.univ : Finset (Fin 3)))).filter (fun s => ∀ c ∈ (Finset.univ : Finset (Fin 3)),
    ((∑ i ∈ (Finset.univ : Finset (Fin 99)), if s i (Finset.mem_univ i) = c then 1 else 0) % 2) = 1 ) ) = (3 ^ 99 - 3) / 4 := by
    sorry
-- Positive example: Using idiomatic Finset.filter for counting
theorem pos_style :
  (Fintype.card {f : Fin 99 → Fin 3 // ∀ c : Fin 3,
    (Finset.filter (fun i => f i = c) (Finset.univ : Finset (Fin 99))).card % 2 = 1})
  = (3^99 - 3) / 4 := by sorry

-- Note: '% 2 = 1' also can be used to express "odd number" in Lean
