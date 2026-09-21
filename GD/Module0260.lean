import GD.Module0249
import GD.Module0259










namespace GD.N0232.N0719.N0894

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open _root_.GD.N0232.N0719.N0887
open _root_.GD.N0232.N0719.N0886
open _root_.GD.N0232.N0719.N0879


def d003737 (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-a * x ^ 2 + b * x))

@[fun_prop]
theorem d003738 (a b : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0894.d003737 a b) := by
  unfold _root_.GD.N0232.N0719.N0894.d003737
  fun_prop

theorem d003739 (a b x : ℝ) :
    _root_.GD.N0232.N0719.N0894.d003737 a b x ≠ ∞ := by
  simp [_root_.GD.N0232.N0719.N0894.d003737]




theorem d003740
    {v : ℝ≥0} {a b : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    (gaussianReal 0 v).withDensity (_root_.GD.N0232.N0719.N0894.d003737 a b) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0887.d003558 v a b) •
        gaussianReal (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    gaussianReal_of_var_ne_zero
      (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003562 hv hh)]
  rw [← withDensity_mul volume
      (measurable_gaussianPDF 0 v)
      (_root_.GD.N0232.N0719.N0894.d003738 a b),
    ← withDensity_smul
      (μ := volume)
      (ENNReal.ofReal (_root_.GD.N0232.N0719.N0887.d003558 v a b))
      (measurable_gaussianPDF
        (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a))]
  congr 1
  funext x
  unfold _root_.GD.N0232.N0719.N0894.d003737 gaussianPDF
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x),
    ← ENNReal.ofReal_mul (_root_.GD.N0232.N0719.N0887.d003569 hh).le]
  apply
    (ENNReal.ofReal_eq_ofReal_iff
      (mul_nonneg (gaussianPDFReal_nonneg 0 v x)
        (Real.exp_nonneg _))
      (mul_nonneg (_root_.GD.N0232.N0719.N0887.d003569 hh).le
        (gaussianPDFReal_nonneg
          (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x))).2
  rw [mul_comm (gaussianPDFReal 0 v x)
      (Real.exp (-a * x ^ 2 + b * x)),
    _root_.GD.N0232.N0719.N0887.d003566
    (v := v) (a := a) (b := b) (x := x) hv hh]


def d003741
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ)
    (z : ℝ × (ℝ × ℝ)) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0894.d003737 a₁ b₁ z.1 *
    (_root_.GD.N0232.N0719.N0894.d003737 a₂ b₂ z.2.1 *
      _root_.GD.N0232.N0719.N0894.d003737 a₃ b₃ z.2.2)

@[fun_prop]
theorem d003742
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0894.d003741 a₁ b₁ a₂ b₂ a₃ b₃) := by
  unfold _root_.GD.N0232.N0719.N0894.d003741
  fun_prop

theorem d003743
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ)
    (z : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0232.N0719.N0894.d003741 a₁ b₁ a₂ b₂ a₃ b₃ z ≠ ∞ := by
  unfold _root_.GD.N0232.N0719.N0894.d003741
  exact ENNReal.mul_ne_top
    (_root_.GD.N0232.N0719.N0894.d003739 a₁ b₁ z.1)
    (ENNReal.mul_ne_top
      (_root_.GD.N0232.N0719.N0894.d003739 a₂ b₂ z.2.1)
      (_root_.GD.N0232.N0719.N0894.d003739 a₃ b₃ z.2.2))





theorem d003744
    {v₁ v₂ v₃ : ℝ≥0}
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hh₁ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₁ a₁)
    (hh₂ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₂ a₂)
    (hh₃ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₃ a₃) :
    (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃).withDensity
        (_root_.GD.N0232.N0719.N0894.d003741 a₁ b₁ a₂ b₂ a₃ b₃) =
      ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0887.d003558 v₁ a₁ b₁ *
            _root_.GD.N0232.N0719.N0887.d003558 v₂ a₂ b₂ *
            _root_.GD.N0232.N0719.N0887.d003558 v₃ a₃ b₃) •
        _root_.GD.N0232.N0719.N0879.d003730
          (_root_.GD.N0232.N0719.N0887.d003557 v₁ a₁ b₁)
          (_root_.GD.N0232.N0719.N0887.d003557 v₂ a₂ b₂)
          (_root_.GD.N0232.N0719.N0887.d003557 v₃ a₃ b₃)
          (_root_.GD.N0232.N0719.N0887.d003556 v₁ a₁)
          (_root_.GD.N0232.N0719.N0887.d003556 v₂ a₂)
          (_root_.GD.N0232.N0719.N0887.d003556 v₃ a₃) := by
  have h₁ :=
    _root_.GD.N0232.N0719.N0894.d003740
      (v := v₁) (a := a₁) (b := b₁) hv₁ hh₁
  have h₂ :=
    _root_.GD.N0232.N0719.N0894.d003740
      (v := v₂) (a := a₂) (b := b₂) hv₂ hh₂
  have h₃ :=
    _root_.GD.N0232.N0719.N0894.d003740
      (v := v₃) (a := a₃) (b := b₃) hv₃ hh₃
  have hg₂₃ :
      Measurable (fun z : ℝ × ℝ ↦
        _root_.GD.N0232.N0719.N0894.d003737 a₂ b₂ z.1 *
          _root_.GD.N0232.N0719.N0894.d003737 a₃ b₃ z.2) :=
    ((_root_.GD.N0232.N0719.N0894.d003738 a₂ b₂).comp measurable_fst).mul
      ((_root_.GD.N0232.N0719.N0894.d003738 a₃ b₃).comp measurable_snd)
  have hprod :
      (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃).withDensity
          (_root_.GD.N0232.N0719.N0894.d003741 a₁ b₁ a₂ b₂ a₃ b₃) =
        ((gaussianReal 0 v₁).withDensity
            (_root_.GD.N0232.N0719.N0894.d003737 a₁ b₁)).prod
          (((gaussianReal 0 v₂).withDensity
              (_root_.GD.N0232.N0719.N0894.d003737 a₂ b₂)).prod
            ((gaussianReal 0 v₃).withDensity
              (_root_.GD.N0232.N0719.N0894.d003737 a₃ b₃))) := by
    unfold _root_.GD.N0232.N0719.N0886.d003649 _root_.GD.N0232.N0719.N0894.d003741
    calc
      _ =
          ((gaussianReal 0 v₁).withDensity
              (_root_.GD.N0232.N0719.N0894.d003737 a₁ b₁)).prod
            (((gaussianReal 0 v₂).prod
                (gaussianReal 0 v₃)).withDensity
              (fun z : ℝ × ℝ ↦
                _root_.GD.N0232.N0719.N0894.d003737 a₂ b₂ z.1 *
                  _root_.GD.N0232.N0719.N0894.d003737 a₃ b₃ z.2)) :=
        (prod_withDensity
          (_root_.GD.N0232.N0719.N0894.d003738 a₁ b₁) hg₂₃).symm
      _ = _ := by
        rw [← prod_withDensity
          (_root_.GD.N0232.N0719.N0894.d003738 a₂ b₂)
          (_root_.GD.N0232.N0719.N0894.d003738 a₃ b₃)]
  rw [hprod, h₁, h₂, h₃]
  unfold _root_.GD.N0232.N0719.N0879.d003730
  rw [
    Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_right]
  simp only [smul_smul]
  rw [ENNReal.ofReal_mul
      (mul_nonneg (_root_.GD.N0232.N0719.N0887.d003569 hh₁).le
        (_root_.GD.N0232.N0719.N0887.d003569 hh₂).le),
    ENNReal.ofReal_mul (_root_.GD.N0232.N0719.N0887.d003569 hh₁).le]
  rw [mul_assoc]





theorem d003745
    {v₁ v₂ v₃ : ℝ≥0}
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (f : ℝ × (ℝ × ℝ) → ℝ)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hh₁ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₁ a₁)
    (hh₂ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₂ a₂)
    (hh₃ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₃ a₃) :
    ∫ z,
        (Real.exp (-a₁ * z.1 ^ 2 + b₁ * z.1) *
          (Real.exp (-a₂ * z.2.1 ^ 2 + b₂ * z.2.1) *
            Real.exp (-a₃ * z.2.2 ^ 2 + b₃ * z.2.2))) *
          f z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ =
      (_root_.GD.N0232.N0719.N0887.d003558 v₁ a₁ b₁ *
        _root_.GD.N0232.N0719.N0887.d003558 v₂ a₂ b₂ *
        _root_.GD.N0232.N0719.N0887.d003558 v₃ a₃ b₃) *
        ∫ z, f z
          ∂_root_.GD.N0232.N0719.N0879.d003730
            (_root_.GD.N0232.N0719.N0887.d003557 v₁ a₁ b₁)
            (_root_.GD.N0232.N0719.N0887.d003557 v₂ a₂ b₂)
            (_root_.GD.N0232.N0719.N0887.d003557 v₃ a₃ b₃)
            (_root_.GD.N0232.N0719.N0887.d003556 v₁ a₁)
            (_root_.GD.N0232.N0719.N0887.d003556 v₂ a₂)
            (_root_.GD.N0232.N0719.N0887.d003556 v₃ a₃) := by
  let N :=
    _root_.GD.N0232.N0719.N0887.d003558 v₁ a₁ b₁ *
      _root_.GD.N0232.N0719.N0887.d003558 v₂ a₂ b₂ *
      _root_.GD.N0232.N0719.N0887.d003558 v₃ a₃ b₃
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg
      (mul_nonneg (_root_.GD.N0232.N0719.N0887.d003569 hh₁).le
        (_root_.GD.N0232.N0719.N0887.d003569 hh₂).le)
      (_root_.GD.N0232.N0719.N0887.d003569 hh₃).le
  calc
    (∫ z,
        (Real.exp (-a₁ * z.1 ^ 2 + b₁ * z.1) *
          (Real.exp (-a₂ * z.2.1 ^ 2 + b₂ * z.2.1) *
            Real.exp (-a₃ * z.2.2 ^ 2 + b₃ * z.2.2))) *
          f z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
        ∫ z, f z
          ∂(_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃).withDensity
            (_root_.GD.N0232.N0719.N0894.d003741 a₁ b₁ a₂ b₂ a₃ b₃) := by
      rw [integral_withDensity_eq_integral_toReal_smul
        (_root_.GD.N0232.N0719.N0894.d003742 a₁ b₁ a₂ b₂ a₃ b₃)
        (ae_of_all _
          (fun z ↦ lt_top_iff_ne_top.mpr
            (_root_.GD.N0232.N0719.N0894.d003743 a₁ b₁ a₂ b₂ a₃ b₃ z))) f]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [_root_.GD.N0232.N0719.N0894.d003741, _root_.GD.N0232.N0719.N0894.d003737,
        ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    _ =
        ∫ z, f z
          ∂ENNReal.ofReal N •
            _root_.GD.N0232.N0719.N0879.d003730
              (_root_.GD.N0232.N0719.N0887.d003557 v₁ a₁ b₁)
              (_root_.GD.N0232.N0719.N0887.d003557 v₂ a₂ b₂)
              (_root_.GD.N0232.N0719.N0887.d003557 v₃ a₃ b₃)
              (_root_.GD.N0232.N0719.N0887.d003556 v₁ a₁)
              (_root_.GD.N0232.N0719.N0887.d003556 v₂ a₂)
              (_root_.GD.N0232.N0719.N0887.d003556 v₃ a₃) := by
      rw [_root_.GD.N0232.N0719.N0894.d003744
        hv₁ hv₂ hv₃ hh₁ hh₂ hh₃]
    _ = N *
        ∫ z, f z
          ∂_root_.GD.N0232.N0719.N0879.d003730
            (_root_.GD.N0232.N0719.N0887.d003557 v₁ a₁ b₁)
            (_root_.GD.N0232.N0719.N0887.d003557 v₂ a₂ b₂)
            (_root_.GD.N0232.N0719.N0887.d003557 v₃ a₃ b₃)
            (_root_.GD.N0232.N0719.N0887.d003556 v₁ a₁)
            (_root_.GD.N0232.N0719.N0887.d003556 v₂ a₂)
            (_root_.GD.N0232.N0719.N0887.d003556 v₃ a₃) := by
      rw [integral_smul_measure]
      simp [ENNReal.toReal_ofReal hN]
    _ = _ := rfl

end

end GD.N0232.N0719.N0894
