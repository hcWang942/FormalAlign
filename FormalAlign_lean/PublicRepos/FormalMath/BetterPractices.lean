import Mathlib

/-"Given 20 balls in various colors including yellow, blue, green, and red (it is allowed
  for some colors to have no balls). Assuming that balls of the same color are indistinguishable.
  It is known that arranging all the balls in a line yields 1,140 distinct permutations.
  The question is: What is the maximum possible number of yellow balls?
  Show that it is 17."
 "有 $20$ 个小球, 颜色分别是黄色、蓝色、绿色、红色(允许某种颜色的球一个也没有). 假定同色球是无区别的. 已知
  将所有小球排成一列, 共有 $1140$ 种不同排列方法. 问至多可能有多少个黄色球.
  答案是 $17$."		-/

theorem q1
  (l : (y r g b : ℕ) → List ℕ)
  (l_def : ∀ y r g b, l y r g b = List.replicate y 0 ++ List.replicate r 1 ++ List.replicate g 2 ++ List.replicate b 3)
  (ys : List (Fin 20))
  (ys_def : ∀ y, y ∈ ys ↔ ∃ (r g b : Fin 20), y + r + g + b = 20 ∧ (l y r g b).permutations.dedup.length = 1140)
  : ys.maximum = some 17 := by sorry
-- theorem q1':
--   ∃ (y r g b : ℕ), y + r + g + b = 20 ∧
--   Nat.factorial 20 / (Nat.factorial y * Nat.factorial r * Nat.factorial g * Nat.factorial b) = 1140 ∧
--   (∀ (y' r' g' b' : ℕ), y' + r' + g' + b' = 20 →
--   Nat.factorial 20 / (Nat.factorial y' * Nat.factorial r' * Nat.factorial g' * Nat.factorial b') = 1140 →
--   y' ≤ 17) ∧
--   y = 17 := by sorry

theorem q1' {y r g b: ℕ }
  (h_total : y + r + g + b = 20)  -- 假设：总共有20个球
  (h_arrangements : Nat.factorial 20 / (Nat.factorial y * Nat.factorial r *  -- 假设：有1140种不同排列方式
                                        Nat.factorial g * Nat.factorial b) = 1140) :
  y ≤ 17 :=  sorry

-- theorem g1'':
--   max {y : ℕ | ∃ (r g b : ℕ), y + r + g + b = 20 ∧
--                 Nat.factorial 20 / (Nat.factorial y * Nat.factorial r *
--                                    Nat.factorial g * Nat.factorial b) = 1140} = 17 :=sorry
-- theorem yellow_max_17 :
--   let valid_yellows := Finset.filter
--     (λ y, ∃ (r g b : ℕ), y + r + g + b = 20 ∧
--           Nat.factorial 20 / (Nat.factorial y * Nat.factorial r *
--                              Nat.factorial g * Nat.factorial b) = 1140)
--     (Finset.range 21)

--   -- 证明集合非空（因为我们要使用max）
--   have h_nonempty : valid_yellows.Nonempty := by sorry--事实上是不可得证的 题目中说(允许某种颜色的球一个也没有)，所以这种方式只能作罢

--   -- 使用Finset.max函数
--   Finset.max valid_yellows = some 17 :=
-- by
--   -- 证明思路:
--   -- 1. 证明17在valid_yellows中 (即存在r,g,b使得条件满足)
--   -- 2. 证明没有大于17的元素在valid_yellows中
--   sorry


theorem cmos_2010_combination_12206 :
  Fintype.card {f : Fin 7 → Fin 7 | ∀ (x : Fin 7), f (f x) = 0} = 1057 :=
by sorry




theorem cmos_2010_combination_12212 :
  Finset.card
  ((Finset.pi (Finset.univ : Finset (Fin 7)) (fun _ => Finset.Icc 1 270)).filter
  (fun f =>
  (∑ i : Fin 7, f i (Finset.mem_univ i)) = 270 ∧
  (∀ (i : Fin 7) (h : i ∈ Finset.univ), i.val < 4 → 7 ∣ f i h) ∧
  (∀ (i : Fin 7) (h : i ∈ Finset.univ), 4 ≤ i.val ∧ i.val < 7 → 13 ∣ f i h)))
  = 42244 := by sorry

theorem cmos_2010_combination_12214
 (n k : ℕ)
 (h_nk : n ≥ k)
 (h_kpos : 1 ≤ k) :
 ((Finset.pi Finset.univ (fun _ : Fin k => Finset.Icc 1 n)).filter
  (fun seq =>
  (∀ i : Fin k, (seq i (Finset.mem_univ i)) % 2 = ((i.val + 1) % 2))
  ∧ (∀ i j : Fin k, i ≤ j → seq i (Finset.mem_univ i) ≤ seq j (Finset.mem_univ j)))).card
 = Nat.choose ((n + k) / 2) k := by sorry


theorem entd1_2024_number_theory127830
  (n : ℕ)
  (h_n : 6 ≤ n)
  (S : Finset ℕ)
  (h_S_def : S = {k | 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k}) :
  ∃ (perm : List ℕ),
  (List.length perm = Finset.card S) ∧
  (List.toFinset perm = S) ∧
  (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)
  := by sorry
--set 和finset的gap，不知道该怎么考虑，需要改吗
/-从题目的可解性和严谨性角度考虑，我认为这个 `Set` 和 `Finset` 的差异确实需要修正。以下是我的分析：

### 为什么需要修改

1. **类型不一致**：在第一个版本中，`h_S_def : S = {k | 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k}` 存在类型不匹配的问题。左侧 `S` 是 `Finset ℕ`，而右侧 `{k | ...}` 是 `Set ℕ`。在 Lean 中，这两种类型是不同的：
   - `Set ℕ` 是任意自然数集合，可以是无限的
   - `Finset ℕ` 专门用于有限集合

2. **编译问题**：即使在这个特定情况下集合是有限的（因为上限是 n），Lean 的类型系统仍然会将 `{k | ...}` 识别为 `Set`。没有自动的从 `Set` 到 `Finset` 的转换，这会导致编译错误。

3. **证明难度**：使用不正确的类型会使证明变得不必要地复杂，甚至可能无法完成。

### 第二个版本的优势

第二个版本 `S = Finset.filter (fun k => 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k) (Finset.range (n+1))` 明确使用了 `Finset` 的构造方法：

1. **类型一致性**：确保了 `S` 的定义与其类型声明一致
2. **明确的范围**：`Finset.range (n+1)` 明确了我们只考虑 0 到 n 的自然数
3. **函数式风格**：使用 `Finset.filter` 是 Lean 中处理有限集合的惯用方法

### 另一种可能的修正

如果想保持集合构造语法的简洁性，可以使用 `{k ∈ Finset.range (n+1) | ...}` 的形式：

```lean
theorem entd1_2024_number_theory12783''
  (n : ℕ)
  (h_n : 6 ≤ n)
  (S : Finset ℕ)
  (h_S_def : S = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k}) :
  ∃ (perm : List ℕ),
  (List.length perm = Finset.card S) ∧
  (List.toFinset perm = S) ∧
  (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)
  := by sorry
```

这种写法在语义上等同于 `Finset.filter`，但视觉上更接近原始的集合构造语法。

### 结论

从可解性角度来看，**修改是必要的**。第二个版本（使用 `Finset.filter`）或我提供的第三个版本（使用 `{k ∈ ... | ...}`）都是正确的。选择哪一个主要取决于个人偏好和可读性考虑。对于初学者，第三个版本可能更容易理解，

以下可以用于选择“更符合习惯”
您提供的两种修正方案都是很好的选择，让我比较一下这些方案与现有版本的优劣：

### 比较三个版本

1. **现有版本**:
```lean
(S : Finset ℕ)
(h_S_def : S = Finset.filter (fun k => 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k) (Finset.range (n+1))) :
```

2. **修正方案1**:
```lean
(S : Finset ℕ)
(h_S_def : S = (Finset.range (n+1)).filter (fun k => 2 ≤ k ∧ ¬ Nat.Prime k)) :
```

3. **修正方案2**:
```lean
(S : Finset ℕ)
(h_S_def : S = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k}) :
```

### 分析

1. **语法风格**:
   - 修正方案1使用了点表示法（method chaining），这是函数式编程中常见的风格
   - 修正方案2使用了集合构建器语法，更接近数学表示法
   - 现有版本使用了函数应用风格

2. **简洁性**:
   - 修正方案1和2都移除了`k ≤ n`条件，这实际上是多余的，因为`k ∈ Finset.range (n+1)`已经保证了`k ≤ n`
   - 修正方案1和2在这方面更简洁

3. **可读性**:
   - 修正方案2最接近数学中的集合表示法，对数学背景的读者最直观
   - 修正方案1对熟悉函数式编程的人来说很自然
   - 现有版本略显冗长

4. **语义明确性**:
   - 所有三个版本在语义上都是正确的
   - 修正方案1和2通过去除冗余条件，更加清晰地表达了意图

### 推荐

在这三个版本中，我认为**修正方案2**是最佳选择，理由如下：

1. 它使用了`{k ∈ ... | ...}`的集合构建器语法，这与数学中表示集合的方式最接近，提高了可读性
2. 它移除了冗余的`k ≤ n`条件，使定义更加简洁
3. 对于可能不熟悉函数式编程的数学家或学生来说，这种语法更容易理解
4. 在Lean中，这种集合构建器语法会被自动转换为等价的`Finset.filter`表达式，因此在性能或功能上没有损失

因此，我建议采用修正方案2：
```lean
(S : Finset ℕ)
(h_S_def : S = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k}) :
```

这种表示法既数学上直观，又技术上正确，同时避免了类型不匹配的问题。-/
theorem entd1_2024_number_theory12783
  (n : ℕ)
  (h_n : 6 ≤ n)
  (S : Finset ℕ)
  (h_S_def : S = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k})
  (h_S_def' : S = {k | 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k}):
  ∃ (perm : List ℕ),
    (List.length perm = Finset.card S) ∧
    (List.toFinset perm = S) ∧
    (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)--用zip和tail是很好的想法！
  := by sorry

theorem entd1_2024_number_theory12783'
  (n : ℕ)
  (h_n : 6 ≤ n)
  (S : Finset ℕ)
  (h_S_def : S = Finset.filter (fun k => 2 ≤ k ∧ k ≤ n ∧ ¬ Nat.Prime k) (Finset.range (n+1))) :
  ∃ (perm : List ℕ),
    (List.length perm = Finset.card S) ∧
    (List.toFinset perm = S) ∧
    (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)
  := by sorry

theorem entd1_2024_number_theory12783_optimal
  (n : ℕ)
  (h_n : 6 ≤ n) :
  ∃ (perm : List ℕ),
    (perm.toFinset = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k}) ∧
    (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)
  := by sorry
theorem entd1_2024_number_theory12783_hyp1
  (n : ℕ)
  (h_n : 6 ≤ n)
  (S : Finset ℕ)
  (h_S : S = {k ∈ Finset.range (n+1) | 2 ≤ k ∧ ¬ Nat.Prime k}) :
  ∃ (perm : List ℕ),
    (perm.toFinset = S) ∧
    (∀ (x y : ℕ), (x, y) ∈ List.zip perm (List.tail perm) → Nat.gcd x y > 1)
  := by sorry

 theorem imo_2024_number_theory_12807
  (p : ℕ)
  (hp : Nat.Prime p) :
  ¬ ∃ (l n m : ℕ), l ≥ 1 ∧ n > 0 ∧ m > 0 ∧
  (m * (m + 1)) / 2 ∣ (n * (n + 1)) / 2 ∧
  (n * (n + 1)) / 2 = p^(2 * l) * ((m * (m + 1)) / 2):=sorry


theorem lecture08_2008_combinatorics_606_2
  (S : Finset ℕ)
  (h_S : S = {0, 1, 3, 5, 7}) :
  (Finset.filter (λ (abc : ℕ × ℕ × ℕ) =>
    abc.1 ∈ S ∧ abc.2.1 ∈ S ∧ abc.2.2 ∈ S ∧       -- 系数从S中选取
    abc.1 ≠ 0 ∧                                   -- a ≠ 0 (确保是二次方程)
    abc.1 ≠ abc.2.1 ∧ abc.2.1 ≠ abc.2.2 ∧ abc.1 ≠ abc.2.2 ∧  -- 三个系数互不相同
    ((abc.2.1 : ℤ) * (abc.2.1 : ℤ) - 4 * (abc.1 : ℤ) * (abc.2.2 : ℤ)) ≥ 0  -- 判别式非负，有实根
  ) (S.product (S.product S))).card = 18 := by sorry


theorem cmos_2010_combination_12223 (α : Type*) [DecidableEq α] (n : ℕ) :
  ∀ (S : Finset α), Finset.card S = n →
  Finset.sum S.powerset (fun A =>
    Finset.sum S.powerset (fun B =>
      Finset.card (A ∩ B)))
  = n * 4^(n - 1) := by sorry

theorem cmos_2010_number_theory_12191 :
  let S := { m : ℕ | ∀ k : ℕ, (1 < k ∧ k < m) → Nat.gcd k m = 1 → ∃ (p e : ℕ), Nat.Prime p ∧ 1 ≤ e ∧ k = p ^ e };
  IsGreatest S 60 :=by sorry

theorem cmos_2010_number_theory_12191'
  (S : Set ℕ)
  (h_S : S = { m : ℕ | ∀ k : ℕ, (1 < k ∧ k < m) → Nat.gcd k m = 1 → ∃ (p e : ℕ), Nat.Prime p ∧ 1 ≤ e ∧ k = p ^ e })
  (h_mem : 60 ∈ S)
  (h_upper : ∀ m : ℕ, m ∈ S → m ≤ 60) :
  IsGreatest S 60 :=by sorry

 theorem entd1_2024_number_theory_12794
  (n : ℕ)
  (h_n_pos : 0 < n)
  (h_prime : Nat.Prime (2 * n - 1))
  (a : ℕ → ℕ)
  (h_a_pos : ∀ i ∈ Finset.Icc 1 n, 0 < a i)
  (a_unique : ∀ i j, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → i ≠ j → a i ≠ a j) :
  ∃ i ∈ Finset.Icc 1 n, ∃ j ∈ Finset.Icc 1 n, i ≠ j ∧ (a i + a j) / Nat.gcd (a i) (a j) ≥ 2 * n - 1 := by sorry

 theorem lecture02_2008_algbra_12
  (f : ℝ → ℝ)
  (h_f_pos : ∀ x > 0, f x > 0) -- 确保正实数映射
  (h_f_scaling : ∀ x > 0, f (3 * x) = 3 * f x)
  (h_f_piecewise : ∀ x ∈ Set.Ico 1 3, f x = 1 - |x - 2|)
  : (426 : ℝ) > 0 ∧
  f 426 = f 2004 ∧
  (∀ y : ℝ, y > 0 ∧ y < 426 → f y ≠ f 2004) := by sorry

 theorem nesbitt_inequality
  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by sorry

 theorem lecture02_2008_algbra_14
  (a b : ℝ)
  (f : ℝ → ℝ)
  (n : ℕ)
  (x : ℝ)
  (h_f : ∀ x, f x = a * x + b)
  (h_a_ne : a ≠ 1)
  (h_n_pos : n > 0)
  :
  f^[n] x = a^n * (x + b / (a - 1)) - b / (a - 1) := by sorry

theorem lecture02_2010_algebra_23 :
  { (x0, x1, x2, x3, x4) : ℝ × ℝ × ℝ × ℝ × ℝ |
    x0 ∈ Set.Icc 0 1 ∧ x1 ∈ Set.Icc 0 1 ∧ x2 ∈ Set.Icc 0 1 ∧
    x3 ∈ Set.Icc 0 1 ∧ x4 ∈ Set.Icc 0 1 ∧
    x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x0 ≠ x4 ∧
    x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
    (∀ (f : ℝ → ℝ),
      (∀ x : ℝ, 0 ≤ x ∧ x < 1 / 3 → f x = 2 * x + 1 / 3) ∧
      (∀ x : ℝ, 1 / 3 ≤ x ∧ x ≤ 1 → f x = 3 * (1 - x) / 2) →
      f x0 = x1 ∧ f x1 = x2 ∧ f x2 = x3 ∧ f x3 = x4 ∧ f x4 = x0) } =
  { ((6 : ℝ)/ 73, (109: ℝ) / 219, (3 : ℝ) * (1 - 109 / 219) / 2, (3 : ℝ) * (1 - (3 * (1 - 109 / 219) / 2)) / 2, (3 : ℝ) * (1 - (3 * (1 - (3 * (1 - 109 / 219) / 2)) / 2)) / 2) }:=sorry

theorem lecture02_2010_algebra_231 :
  let f : ℝ → ℝ := fun x => if x < 1/3 ∧ x ≥ 0 then 2*x + 1/3 else if x ≥ 1/3 ∧ x ≤ 1 then 3*(1-x)/2 else 0;
  { (x0, x1, x2, x3, x4) : ℝ × ℝ × ℝ × ℝ × ℝ |
    x0 ∈ Set.Icc 0 1 ∧ x1 ∈ Set.Icc 0 1 ∧ x2 ∈ Set.Icc 0 1 ∧
    x3 ∈ Set.Icc 0 1 ∧ x4 ∈ Set.Icc 0 1 ∧
    x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x0 ≠ x4 ∧
    x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
    f x0 = x1 ∧ f x1 = x2 ∧ f x2 = x3 ∧ f x3 = x4 ∧ f x4 = x0 } =
  { ((6 : ℝ)/ 73, (109: ℝ) / 219, (3 : ℝ) * (1 - 109 / 219) / 2, (3 : ℝ) * (1 - (3 * (1 - 109 / 219) / 2)) / 2, (3 : ℝ) * (1 - (3 * (1 - (3 * (1 - 109 / 219) / 2)) / 2)) / 2) }:= by sorry

 theorem lecture02_2010_algebra_24 (a : ℝ) (hn : a > 2) (n : ℕ) (a_seq : ℕ → ℝ)
  (a_def_base : a_seq 0 = 1)
  (a_def_init : a_seq 1 = a)
  (a_def_step : ∀ k ≥ 1, a_seq (k + 1) = (a_seq k ^ 2 / a_seq (k - 1) ^ 2 - 2) * a_seq k) :
  ∑ i ∈ Finset.Icc 1 n, 1 / a_seq i < 1 / 2 * (a - Real.sqrt (a ^ 2 - 4)) := by sorry

theorem lecture02_2010_algebra_32
  (alpha : ℝ)
  (h_alpha : alpha = (Real.sqrt 5 + 1) / 2)
  (f : ℕ → ℕ)
  (h_f_domain : ∀ n : ℕ, n ≥ 1 → f n ≥ 1)
  (h_f_condition : ∀ n : ℕ, n ≥ 1 → f (f n) + f (n + 1) = n + 2):
  ∀ n : ℕ, n ≥ 1 → f n = (Int.floor (n * alpha) - (n : Int) + 1).toNat :=
 by sorry

 theorem imo16_2024_combinatorics_12285 :
  (Finset.filter (fun (x, y, z) => x + y + z = 2010 ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≤ y ∧ y ≤ z)
  (Finset.range 2009 ×ˢ Finset.range 2009 ×ˢ Finset.range 2009)).card = 336675 :=
 by sorry

 theorem hscmc_2010_combinatorics_12494 :
  ∀ (a b n : ℕ),
  a > 0 →
  b > 0 →
  a * b > a + b → -- 添加此约束
  Nat.gcd a b = 1 →
  (n > a * b - a - b → ∃ x y : ℕ, a * x + b * y = n) ∧
  (n = a * b - a - b → ¬∃ x y : ℕ, a * x + b * y = n):= by sorry


theorem hscmc_2010_combinatorics_12466
  (p : ℕ)
  (f : ℕ → ℕ)
  (f_def : ∀ x, f x = x^2 + x + p)
  (h_primes : ∀ x : ℕ, x ≤ Int.floor (Real.sqrt ((p : ℝ) / 3)) → Nat.Prime (f x)) :
  ∀ x : ℕ, x ≤ p - 2 → Nat.Prime (f x) := by sorry

theorem lecture02_2010_algebra_11:
  ∀ n : ℕ, n ≥ 1 →
  (∃ k : ℕ, k ≥ 1 ∧
    (∑ i ∈ Finset.range (k + 1), i) / ((k + 32 : ℝ) * (∑ i ∈ Finset.range (k + 2), i)) = 1/50) ∧
  (∑ i ∈ Finset.range (n + 1), i) / ((n + 32 : ℝ) * (∑ i ∈ Finset.range (n + 2), i)) ≤ 1/50 := by sorry


theorem lecture05_2009_number_theory_581 (a : ℕ+ → ℤ) (h_pos_inf : { n : ℕ+ | a n > 0 }.Infinite)
  (h_neg_inf : { n : ℕ+ | a n < 0 }.Infinite)
  (h_distinct_mod : ∀ n : ℕ+, Function.Injective (fun k => (a k) % n)) :
  ∀ z : ℤ, ∃! n : ℕ+, a n = z := by sorry

theorem lecture05_2009_number_theory_581' (a : ℕ+ → ℤ)
  (h_pos_inf : { n : ℕ+ | a n > 0 }.Infinite)
  (h_neg_inf : { n : ℕ+ | a n < 0 }.Infinite)
  (h_distinct_mod : ∀ n : ℕ+, ∀ i j : ℕ+, i ≤ n → j ≤ n → i ≠ j → (a i) % n ≠ (a j) % n) :
  ∀ z : ℤ, ∃! n : ℕ+, a n = z := by sorry
