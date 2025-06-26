import Mathlib

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = 26 := by sorry

theorem amc12a_2015_p10_1 (x y : ℤ) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = 26 := by sorry

theorem amc12a_2015_p10_2 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x ≥ 26 := by sorry

theorem amc12a_2015_p10_3 (x y : ℕ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = 26 := by sorry

theorem amc12a_2015_p10_4 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x > 20 := by sorry

theorem amc12a_2015_p10_5 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : ∃ x : ℤ, x = 26 := by sorry

theorem amc12a_2009_p9 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∃ x, f (x + 3) = 3 * x ^ 2 + 7 * x + 4)
  (h₁ : ∀ x, f x = a * x ^ 2 + b * x + c) : a + b + c = 2 := by sorry
