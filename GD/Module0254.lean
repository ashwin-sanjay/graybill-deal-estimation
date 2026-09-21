import GD.Module0253















namespace GD.N0232.N0719.N0883

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open _root_.GD.N0232.N0719.N0886


theorem d003665
    (p₁ p₂ p₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0) :
    Integrable
      (fun z : ℝ × (ℝ × ℝ) ↦ (_root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z) ^ 2)
      (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  let e₁₁ : ℕ × ℕ × ℕ := (2, 0, 0)
  let e₂₂ : ℕ × ℕ × ℕ := (0, 2, 0)
  let e₃₃ : ℕ × ℕ × ℕ := (0, 0, 2)
  let e₁₂ : ℕ × ℕ × ℕ := (1, 1, 0)
  let e₁₃ : ℕ × ℕ × ℕ := (1, 0, 1)
  let e₂₃ : ℕ × ℕ × ℕ := (0, 1, 1)
  have hpoint :
      (fun z : ℝ × (ℝ × ℝ) ↦ (_root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z) ^ 2) =
      (fun z ↦
        p₁ ^ 2 * _root_.GD.N0232.N0719.N0886.d003655 e₁₁ z +
        p₂ ^ 2 * _root_.GD.N0232.N0719.N0886.d003655 e₂₂ z +
        p₃ ^ 2 * _root_.GD.N0232.N0719.N0886.d003655 e₃₃ z +
        (2 * p₁ * p₂) * _root_.GD.N0232.N0719.N0886.d003655 e₁₂ z +
        (2 * p₁ * p₃) * _root_.GD.N0232.N0719.N0886.d003655 e₁₃ z +
        (2 * p₂ * p₃) * _root_.GD.N0232.N0719.N0886.d003655 e₂₃ z) := by
    funext z
    rcases z with ⟨z₁, z₂, z₃⟩
    dsimp [_root_.GD.N0232.N0719.N0886.d003653, _root_.GD.N0232.N0719.N0886.d003650,
      _root_.GD.N0232.N0719.N0886.d003651, _root_.GD.N0232.N0719.N0886.d003652,
      _root_.GD.N0232.N0719.N0886.d003655, e₁₁, e₂₂, e₃₃, e₁₂, e₁₃, e₂₃]
    ring
  rw [hpoint]
  have h₁₁ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₁).const_mul (p₁ ^ 2)
  have h₂₂ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₂₂).const_mul (p₂ ^ 2)
  have h₃₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₃₃).const_mul (p₃ ^ 2)
  have h₁₂ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₂).const_mul (2 * p₁ * p₂)
  have h₁₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₃).const_mul (2 * p₁ * p₃)
  have h₂₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₂₃).const_mul (2 * p₂ * p₃)
  exact ((((h₁₁.add h₂₂).add h₃₃).add h₁₂).add h₁₃).add h₂₃


theorem d003666
    (p₁ p₂ p₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0) :
    (∫ z : ℝ × (ℝ × ℝ),
        (_root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z) ^ 2
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
      p₁ ^ 2 * (v₁ : ℝ) +
        p₂ ^ 2 * (v₂ : ℝ) +
        p₃ ^ 2 * (v₃ : ℝ) := by
  let e₁₁ : ℕ × ℕ × ℕ := (2, 0, 0)
  let e₂₂ : ℕ × ℕ × ℕ := (0, 2, 0)
  let e₃₃ : ℕ × ℕ × ℕ := (0, 0, 2)
  let e₁₂ : ℕ × ℕ × ℕ := (1, 1, 0)
  let e₁₃ : ℕ × ℕ × ℕ := (1, 0, 1)
  let e₂₃ : ℕ × ℕ × ℕ := (0, 1, 1)
  let c₁₁ := p₁ ^ 2
  let c₂₂ := p₂ ^ 2
  let c₃₃ := p₃ ^ 2
  let c₁₂ := 2 * p₁ * p₂
  let c₁₃ := 2 * p₁ * p₃
  let c₂₃ := 2 * p₂ * p₃
  have hpoint :
      (fun z : ℝ × (ℝ × ℝ) ↦ (_root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z) ^ 2) =
      (fun z ↦
        c₁₁ * _root_.GD.N0232.N0719.N0886.d003655 e₁₁ z +
        c₂₂ * _root_.GD.N0232.N0719.N0886.d003655 e₂₂ z +
        c₃₃ * _root_.GD.N0232.N0719.N0886.d003655 e₃₃ z +
        c₁₂ * _root_.GD.N0232.N0719.N0886.d003655 e₁₂ z +
        c₁₃ * _root_.GD.N0232.N0719.N0886.d003655 e₁₃ z +
        c₂₃ * _root_.GD.N0232.N0719.N0886.d003655 e₂₃ z) := by
    funext z
    rcases z with ⟨z₁, z₂, z₃⟩
    dsimp [_root_.GD.N0232.N0719.N0886.d003653, _root_.GD.N0232.N0719.N0886.d003650,
      _root_.GD.N0232.N0719.N0886.d003651, _root_.GD.N0232.N0719.N0886.d003652,
      _root_.GD.N0232.N0719.N0886.d003655, e₁₁, e₂₂, e₃₃, e₁₂, e₁₃, e₂₃,
      c₁₁, c₂₂, c₃₃, c₁₂, c₁₃, c₂₃]
    ring
  have h₁₁ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₁).const_mul c₁₁
  have h₂₂ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₂₂).const_mul c₂₂
  have h₃₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₃₃).const_mul c₃₃
  have h₁₂ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₂).const_mul c₁₂
  have h₁₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₁₃).const_mul c₁₃
  have h₂₃ := (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ e₂₃).const_mul c₂₃
  have hm₁₁ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₁₁ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = (v₁ : ℝ) := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₁₁, measureReal_def]
  have hm₂₂ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₂₂ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = (v₂ : ℝ) := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₂₂, measureReal_def]
  have hm₃₃ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₃₃ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = (v₃ : ℝ) := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₃₃, measureReal_def]
  have hm₁₂ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₁₂ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = 0 := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₁₂, measureReal_def]
  have hm₁₃ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₁₃ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = 0 := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₁₃, measureReal_def]
  have hm₂₃ :
      (∫ z, _root_.GD.N0232.N0719.N0886.d003655 e₂₃ z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = 0 := by
    rw [_root_.GD.N0232.N0719.N0886.d003657]
    simp [e₂₃, measureReal_def]
  rw [hpoint]
  change
    (∫ z,
      ((((((fun z ↦ c₁₁ * _root_.GD.N0232.N0719.N0886.d003655 e₁₁ z) +
              (fun z ↦ c₂₂ * _root_.GD.N0232.N0719.N0886.d003655 e₂₂ z)) +
            (fun z ↦ c₃₃ * _root_.GD.N0232.N0719.N0886.d003655 e₃₃ z)) +
          (fun z ↦ c₁₂ * _root_.GD.N0232.N0719.N0886.d003655 e₁₂ z)) +
        (fun z ↦ c₁₃ * _root_.GD.N0232.N0719.N0886.d003655 e₁₃ z)) +
      (fun z ↦ c₂₃ * _root_.GD.N0232.N0719.N0886.d003655 e₂₃ z)) z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = _
  rw [integral_add' ((((h₁₁.add h₂₂).add h₃₃).add h₁₂).add h₁₃) h₂₃,
    integral_add' (((h₁₁.add h₂₂).add h₃₃).add h₁₂) h₁₃,
    integral_add' ((h₁₁.add h₂₂).add h₃₃) h₁₂,
    integral_add' (h₁₁.add h₂₂) h₃₃,
    integral_add' h₁₁ h₂₂]
  simp_rw [integral_const_mul]
  rw [hm₁₁, hm₂₂, hm₃₃, hm₁₂, hm₁₃, hm₂₃]
  dsimp [c₁₁, c₂₂, c₃₃, c₁₂, c₁₃, c₂₃]
  ring

end

end GD.N0232.N0719.N0883

#print axioms _root_.GD.N0232.N0719.N0883.d003665
#print axioms _root_.GD.N0232.N0719.N0883.d003666
