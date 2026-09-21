import Mathlib.Tactic











namespace GD.N0232.N0720.N1246

open scoped BigOperators

variable {ι : Type*} [Fintype ι]



noncomputable def d002162
    (value : ι → ℝ) (basis : ι → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, value i * basis i x



theorem d002163
    (trueValue center radius : ι → ℝ)
    (basis : ι → ℝ → ℝ)
    (hball : ∀ i, |trueValue i - center i| ≤ radius i)
    (x : ℝ) :
    |_root_.GD.N0232.N0720.N1246.d002162 trueValue basis x -
        _root_.GD.N0232.N0720.N1246.d002162 center basis x| ≤
      ∑ i, radius i * |basis i x| := by
  calc
    |_root_.GD.N0232.N0720.N1246.d002162 trueValue basis x -
        _root_.GD.N0232.N0720.N1246.d002162 center basis x| =
        |∑ i, (trueValue i - center i) * basis i x| := by
          simp only [_root_.GD.N0232.N0720.N1246.d002162]
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ ∑ i, |(trueValue i - center i) * basis i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |trueValue i - center i| * |basis i x| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, radius i * |basis i x| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hball i) (abs_nonneg _)



theorem d002164 :
    22 * (7 * ((1 : ℝ) / 14) / 2) ^ (13 + 1) <
      82 / 1000000000 := by
  norm_num [div_pow]



theorem d002165
    (f p : ℝ → ℝ) (domain : Set ℝ) (error : ℝ)
    (herror : ∀ x ∈ domain, |f x - p x| ≤ error)
    (hmargin : ∀ x ∈ domain, error < p x) :
    ∀ x ∈ domain, 0 < f x := by
  intro x hx
  have hlower : -error ≤ f x - p x := (abs_le.mp (herror x hx)).1
  linarith [hmargin x hx]




theorem d002166
    (f : ℝ → ℝ) (domain : Set ℝ)
    (trueValue center radius : ι → ℝ)
    (basis : ι → ℝ → ℝ)
    (analyticError pointError : ℝ)
    (hball : ∀ i, |trueValue i - center i| ≤ radius i)
    (hanalytic : ∀ x ∈ domain,
      |f x - _root_.GD.N0232.N0720.N1246.d002162 trueValue basis x| ≤ analyticError)
    (hbasis : ∀ x ∈ domain,
      ∑ i, radius i * |basis i x| ≤ pointError)
    (hmargin : ∀ x ∈ domain,
      analyticError + pointError < _root_.GD.N0232.N0720.N1246.d002162 center basis x) :
    ∀ x ∈ domain, 0 < f x := by
  apply _root_.GD.N0232.N0720.N1246.d002165 f
    (_root_.GD.N0232.N0720.N1246.d002162 center basis) domain (analyticError + pointError)
  · intro x hx
    exact (abs_sub_le (f x) (_root_.GD.N0232.N0720.N1246.d002162 trueValue basis x)
      (_root_.GD.N0232.N0720.N1246.d002162 center basis x)).trans <|
        add_le_add (hanalytic x hx)
          ((_root_.GD.N0232.N0720.N1246.d002163 trueValue center radius basis
            hball x).trans (hbasis x hx))
  · exact hmargin




theorem d002167
    {β : Type*}
    (f : ℝ → ℝ) (target : Set ℝ) (domain : β → Set ℝ)
    (trueValue center radius : β → ι → ℝ)
    (basis : β → ι → ℝ → ℝ)
    (analyticError pointError : β → ℝ)
    (hcover : ∀ x ∈ target, ∃ b, x ∈ domain b)
    (hball : ∀ b i,
      |trueValue b i - center b i| ≤ radius b i)
    (hanalytic : ∀ b x, x ∈ domain b →
      |f x - _root_.GD.N0232.N0720.N1246.d002162 (trueValue b) (basis b) x| ≤ analyticError b)
    (hbasis : ∀ b x, x ∈ domain b →
      ∑ i, radius b i * |basis b i x| ≤ pointError b)
    (hmargin : ∀ b x, x ∈ domain b →
      analyticError b + pointError b <
        _root_.GD.N0232.N0720.N1246.d002162 (center b) (basis b) x) :
    ∀ x ∈ target, 0 < f x := by
  intro x hx
  obtain ⟨b, hxb⟩ := hcover x hx
  exact _root_.GD.N0232.N0720.N1246.d002166 f (domain b)
    (trueValue b) (center b) (radius b) (basis b)
    (analyticError b) (pointError b) (hball b)
    (hanalytic b) (hbasis b) (hmargin b) x hxb


theorem d002168
    (f p : ℝ → ℝ) (domain : Set ℝ)
    (herror : ∀ x ∈ domain,
      |f x - p x| ≤ 22 * (7 * ((1 : ℝ) / 14) / 2) ^ (13 + 1))
    (hmargin : ∀ x ∈ domain, (82 : ℝ) / 1000000000 ≤ p x) :
    ∀ x ∈ domain, 0 < f x := by
  apply _root_.GD.N0232.N0720.N1246.d002165 f p domain
    (22 * (7 * ((1 : ℝ) / 14) / 2) ^ (13 + 1)) herror
  intro x hx
  exact lt_of_lt_of_le _root_.GD.N0232.N0720.N1246.d002164 (hmargin x hx)

end GD.N0232.N0720.N1246
