import Mathlib

namespace Wrong
def property (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬(7 ∣ x + y)

theorem theorem_proving_zh_blue_41 :
  IsGreatest {n | ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 50 ∧ property s ∧ n = s.card} 16 := by sorry
end Wrong

namespace Right

def propertyRational (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬(∃ k : ℤ, (x + y : ℚ) = k * 7)

theorem theorem_proving_zh_blue_41 :
  IsGreatest {n | ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 50 ∧ propertyRational s ∧ n = s.card} 16 := by
  sorry

end Right

theorem cmos_2010_combination_12205
  (l : (y r g b : ℕ) → List ℕ)
  (l_def : ∀ y r g b, l y r g b = List.replicate y 0 ++ List.replicate r 1 ++ List.replicate g 2 ++ List.replicate b 3)
  (ys : List (Fin 20))
  (ys_def : ∀ y, y ∈ ys ↔ ∃ (r g b : Fin 20), y + r + g + b = 20 ∧ (l y r g b).permutations.dedup.length = 1140)
  : ys.maximum = some 17 := by sorry


theorem cmos_2010_combination_122051 :
  ∃ (y r g b : ℕ), y + r + g + b = 20 ∧
  Nat.factorial 20 / (Nat.factorial y * Nat.factorial r * Nat.factorial g * Nat.factorial b) = 1140 ∧
  (∀ (y' r' g' b' : ℕ), y' + r' + g' + b' = 20 →
  Nat.factorial 20 / (Nat.factorial y' * Nat.factorial r' * Nat.factorial g' * Nat.factorial b') = 1140 →
  y' ≤ 17) ∧
  y = 17 := by sorry

theorem cmos_2010_combination_1220511{yellow red green blue : ℕ }
  -- 假设：总共有20个球
  (h_total : yellow + red + green + blue = 20)
  -- 假设：有1140种不同排列方式
  (h_arrangements : Nat.factorial 20 / (Nat.factorial yellow * Nat.factorial red *
                                        Nat.factorial green * Nat.factorial blue) = 1140) :
  -- 结论：黄球数量为17，且这是满足条件的最大可能值
  yellow = 17 ∧
  (∀ (y r g b : ℕ),
    y + r + g + b = 20 →
    Nat.factorial 20 / (Nat.factorial y * Nat.factorial r *
                        Nat.factorial g * Nat.factorial b) = 1140 →
    y ≤ 17) :=
by sorry


theorem imo_2024_number_theory_12807
  (p : ℕ)
  (hp : Nat.Prime p) :
  ¬ ∃ (l n m : ℕ), l ≥ 1 ∧
  (n * (n + 1)) / 2 / ((m * (m + 1)) / 2) = p^(2 * l) := by
  push_neg
  intro l n m hl
  by_contra h1


  sorry
theorem imo_2024_number_theory_12807_fixed
  (p : ℕ)
  (hp : Nat.Prime p) :
  ¬ ∃ (l n m : ℕ), l ≥ 1 ∧ n > 0 ∧ m > 0 ∧ n ≠ m ∧
  (m * (m + 1)) / 2 ∣ (n * (n + 1)) / 2 ∧
  (n * (n + 1)) / 2 = p^(2 * l) * ((m * (m + 1)) / 2) := by
  push_neg
  intro l n m hl hn hm ho h2
  by_contra h1

  sorry

theorem lecture08_2008_combinatorics_606_2_fixed
  (S : Finset ℕ)
  (h_S : S = {0, 1, 3, 5, 7}) :
  (Finset.filter (fun (abc : ℕ × ℕ × ℕ) =>
    abc.1 ∈ S ∧ abc.2.1 ∈ S ∧ abc.2.2 ∈ S ∧
    abc.1 ≠ 0 ∧
    abc.1 ≠ abc.2.1 ∧ abc.2.1 ≠ abc.2.2 ∧ abc.1 ≠ abc.2.2 ∧
    ((abc.2.1 : ℤ) * (abc.2.1 : ℤ) - 4 * (abc.1 : ℤ) * (abc.2.2 : ℤ)) ≥ 0
  ) (S.product (S.product S))).card = 18 := by
  sorry



theorem entd1_2024_number_theory_127941
  (n : ℕ)
  (h_n_pos : 0 < n)
  (h_prime : Nat.Prime (2 * n - 1))
  (a : ℕ → ℕ)
  (a_unique : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ≠ j ∧ a i ≠ a j) :
  ∃ i ∈ Finset.Icc 1 n, ∃ j ∈ Finset.Icc 1 n, i ≠ j ∧ (a i + a j) / Nat.gcd (a i) (a j) ≥ 2 * n - 1 := by
  sorry

theorem entd1_2024_number_theory_12794
  (n : ℕ)
  (h_n_pos : 0 < n)
  (h_prime : Nat.Prime (2 * n - 1))
  (a : ℕ → ℕ)
  (a_pos : ∀ i ∈ Finset.Icc 1 n, 0 < a i) --add
  (a_distinct : ∀ i j : Finset.Icc 1 n, i ≠ j → a i ≠ a j) :
  ∃ i j : Finset.Icc 1 n, i ≠ j ∧ (a i + a j) / Nat.gcd (a i) (a j) ≥ 2 * n - 1 := by sorry
