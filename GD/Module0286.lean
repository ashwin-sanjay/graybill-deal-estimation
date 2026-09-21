import GD.Module0274















namespace GD
namespace N0235

open MeasureTheory ProbabilityTheory





def d004247 (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![p.1, (1 - p.1) * p.2, (1 - p.1) * (1 - p.2)]

@[fun_prop]
theorem d004248 : Measurable _root_.GD.N0235.d004247 := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [_root_.GD.N0235.d004247] <;> fun_prop



theorem d004249 (p : ℝ × ℝ) :
    ∑ i : Fin 3, _root_.GD.N0235.d004247 p i = 1 := by
  simp [_root_.GD.N0235.d004247, Fin.sum_univ_succ]
  ring








noncomputable def d004250 (α₀ α₁ α₂ : ℝ) :
    Measure (Fin 3 → ℝ) :=
  Measure.map _root_.GD.N0235.d004247
    ((betaMeasure α₀ (α₁ + α₂)).prod (betaMeasure α₁ α₂))



theorem d004251
    {α₀ α₁ α₂ : ℝ} (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    IsProbabilityMeasure (_root_.GD.N0235.d004250 α₀ α₁ α₂) := by
  letI : IsProbabilityMeasure (betaMeasure α₀ (α₁ + α₂)) :=
    isProbabilityMeasureBeta hα₀ (add_pos hα₁ hα₂)
  letI : IsProbabilityMeasure (betaMeasure α₁ α₂) :=
    isProbabilityMeasureBeta hα₁ hα₂
  simpa [_root_.GD.N0235.d004250] using
    (Measure.isProbabilityMeasure_map
      (μ := (betaMeasure α₀ (α₁ + α₂)).prod (betaMeasure α₁ α₂))
      _root_.GD.N0235.d004248.aemeasurable)






theorem d004252
    (α₀ α₁ α₂ : ℝ) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (i j k : ℕ) :
    (∫ x : Fin 3 → ℝ,
        (x 0) ^ i * (x 1) ^ j * (x 2) ^ k
      ∂_root_.GD.N0235.d004250 α₀ α₁ α₂) =
      (∫ u : ℝ,
          u ^ i * (1 - u) ^ (j + k)
        ∂betaMeasure α₀ (α₁ + α₂)) *
      (∫ v : ℝ,
          v ^ j * (1 - v) ^ k
        ∂betaMeasure α₁ α₂) := by
  letI : IsProbabilityMeasure (betaMeasure α₀ (α₁ + α₂)) :=
    isProbabilityMeasureBeta hα₀ (add_pos hα₁ hα₂)
  letI : IsProbabilityMeasure (betaMeasure α₁ α₂) :=
    isProbabilityMeasureBeta hα₁ hα₂
  rw [_root_.GD.N0235.d004250,
    integral_map_of_stronglyMeasurable _root_.GD.N0235.d004248 (by fun_prop),
    ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp [_root_.GD.N0235.d004247]
  rw [mul_pow, mul_pow, pow_add]
  ring



theorem d004253
    (α₀ α₁ α₂ : ℝ) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (i j k : ℕ) :
    (∫ x : Fin 3 → ℝ,
        (x 0) ^ i * (x 1) ^ j * (x 2) ^ k
      ∂_root_.GD.N0235.d004250 α₀ α₁ α₂) =
      (beta (α₀ + i) (α₁ + α₂ + (j + k)) /
        beta α₀ (α₁ + α₂)) *
      (beta (α₁ + j) (α₂ + k) / beta α₁ α₂) := by
  rw [_root_.GD.N0235.d004252 α₀ α₁ α₂ hα₀ hα₁ hα₂ i j k,
    _root_.GD.N0235.d004044 hα₀ (add_pos hα₁ hα₂) i (j + k),
    _root_.GD.N0235.d004044 hα₁ hα₂ j k]
  norm_num [Nat.cast_add]


theorem d004254
    (α₀ α₁ α₂ : ℝ) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    (∫ x : Fin 3 → ℝ, x 1 * x 2
      ∂_root_.GD.N0235.d004250 α₀ α₁ α₂) =
      (∫ u : ℝ, (1 - u) ^ 2
        ∂betaMeasure α₀ (α₁ + α₂)) *
      (∫ v : ℝ, v * (1 - v)
        ∂betaMeasure α₁ α₂) := by
  simpa using _root_.GD.N0235.d004252
    α₀ α₁ α₂ hα₀ hα₁ hα₂ 0 1 1


theorem d004255
    (α₀ α₁ α₂ : ℝ) (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    (∫ x : Fin 3 → ℝ, (x 2) ^ 3
      ∂_root_.GD.N0235.d004250 α₀ α₁ α₂) =
      (∫ u : ℝ, (1 - u) ^ 3
        ∂betaMeasure α₀ (α₁ + α₂)) *
      (∫ v : ℝ, (1 - v) ^ 3
        ∂betaMeasure α₁ α₂) := by
  simpa using _root_.GD.N0235.d004252
    α₀ α₁ α₂ hα₀ hα₁ hα₂ 0 0 3

end N0235
end GD
