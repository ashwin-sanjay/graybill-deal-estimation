import GD.Module0250
import GD.Module0256














namespace GD.N0232.N0719.N0895

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open _root_.GD.N0232.N0719.N0887
open _root_.GD.N0232.N0719.N0888
open _root_.GD.N0232.N0719.N0892

def d003746 (p : ℝ) (v : ℝ≥0) : ℝ :=
  p * (v : ℝ)

def d003747
    (p : ℝ) (v : ℝ≥0) (t u : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0887.d003558 v (t * p) (Real.sqrt (2 * t) * u * p)

def d003748
    (p₁ p₂ p₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0) (t : ℝ) : ℝ :=
  (Real.sqrt
      (1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁))⁻¹ *
    (Real.sqrt
      (1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂))⁻¹ *
    (Real.sqrt
      (1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃))⁻¹

theorem d003749
    (p : ℝ) (v : ℝ≥0) (t : ℝ) :
    _root_.GD.N0232.N0719.N0887.d003554 v (t * p) =
      1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p v := by
  unfold _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0719.N0895.d003746
  ring

theorem d003750
    {p t u : ℝ} {v : ℝ≥0} (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0895.d003747 p v t u =
      (Real.sqrt
          (1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p v))⁻¹ *
        Real.exp
          (t * u ^ 2 * p *
            _root_.GD.N0232.N0719.N0888.d003689 (_root_.GD.N0232.N0719.N0895.d003746 p v) t) := by
  have hsqrt : Real.sqrt (2 * t) ^ 2 = 2 * t := by
    rw [Real.sq_sqrt]
    positivity
  unfold _root_.GD.N0232.N0719.N0895.d003747 _root_.GD.N0232.N0719.N0887.d003558
  rw [_root_.GD.N0232.N0719.N0895.d003749]
  congr 1
  unfold _root_.GD.N0232.N0719.N0888.d003689 _root_.GD.N0232.N0719.N0895.d003746
  have hsquare :
      (Real.sqrt (2 * t) * u * p) ^ 2 =
        (2 * t) * u ^ 2 * p ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt]
  rw [hsquare]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem d003751
    {p₁ p₂ p₃ t u : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0895.d003747 p₁ v₁ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₂ v₂ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₃ v₃ t u =
      _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
        Real.exp
          (t * u ^ 2 *
            _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃
              (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
              (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
              (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t) := by
  rw [_root_.GD.N0232.N0719.N0895.d003750 ht,
    _root_.GD.N0232.N0719.N0895.d003750 ht,
    _root_.GD.N0232.N0719.N0895.d003750 ht]
  unfold _root_.GD.N0232.N0719.N0895.d003748 _root_.GD.N0232.N0719.N0888.d003690
  have hexp :
      Real.exp
            (t * u ^ 2 * p₁ *
              _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁) t) *
          Real.exp
            (t * u ^ 2 * p₂ *
              _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂) t) *
          Real.exp
            (t * u ^ 2 * p₃ *
              _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t) =
        Real.exp
          (t * u ^ 2 *
            (p₁ * _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁) t +
              p₂ * _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂) t +
              p₃ * _root_.GD.N0232.N0719.N0888.d003689
                (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

theorem d003752
    {p t : ℝ} {v : ℝ≥0} (hp : 0 ≤ p) (ht : 0 ≤ t) :
    0 < 1 + 2 * t * _root_.GD.N0232.N0719.N0895.d003746 p v := by
  unfold _root_.GD.N0232.N0719.N0895.d003746
  positivity






theorem d003753
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    0 <
      _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
        (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
        (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t := by
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  have hd₁ : 0 ≤ d₁ := by
    dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₂ : 0 ≤ d₂ := by
    dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₃ : 0 ≤ d₃ := by
    dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have h₁ : 0 < 1 + 2 * t * d₁ := by positivity
  have h₂ : 0 < 1 + 2 * t * d₂ := by positivity
  have h₃ : 0 < 1 + 2 * t * d₃ := by positivity
  have hdet :
      0 < _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t :=
    _root_.GD.N0232.N0719.N0892.d003681 hp₁ hp₂ hp₃ hsum
      hd₁ hd₂ hd₃ ht
  have hfactor :=
    _root_.GD.N0232.N0719.N0888.d003693
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) (t := t)
      hsum h₁.ne' h₂.ne' h₃.ne'
  have hprod :
      0 <
        (1 + 2 * t * d₁) *
          (1 + 2 * t * d₂) *
          (1 + 2 * t * d₃) := by positivity
  dsimp [d₁, d₂, d₃] at hfactor ⊢
  nlinarith





theorem d003754
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    ∫ u : ℝ,
      (_root_.GD.N0232.N0719.N0895.d003747 p₁ v₁ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₂ v₂ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₃ v₃ t u)
      ∂gaussianReal 0 1 =
      _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
        (Real.sqrt
          (_root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ := by
  let m :=
    _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃
      (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
      (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
      (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t
  have hrank :
      0 <
        _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t :=
    _root_.GD.N0232.N0719.N0895.d003753 hp₁ hp₂ hp₃ hsum ht
  have hprecision :
      _root_.GD.N0232.N0719.N0887.d003554 (1 : ℝ≥0) (-t * m) =
        _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t := by
    unfold _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0719.N0888.d003691
    simp only [NNReal.coe_one, m]
    ring
  have hmass :=
    _root_.GD.N0232.N0719.N0887.d003568
      (v := (1 : ℝ≥0)) (a := -t * m) (b := 0)
      one_ne_zero (by
        rw [hprecision]
        exact hrank)
  calc
    (∫ u : ℝ,
        (_root_.GD.N0232.N0719.N0895.d003747 p₁ v₁ t u *
          _root_.GD.N0232.N0719.N0895.d003747 p₂ v₂ t u *
          _root_.GD.N0232.N0719.N0895.d003747 p₃ v₃ t u)
        ∂gaussianReal 0 1) =
        ∫ u : ℝ,
          _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
            Real.exp (t * u ^ 2 * m)
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with u
      simpa only [m] using
        (_root_.GD.N0232.N0719.N0895.d003751
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
          (t := t) (u := u) ht)
    _ =
        _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
          ∫ u : ℝ, Real.exp (t * u ^ 2 * m)
            ∂gaussianReal 0 1 := by
      rw [integral_const_mul]
    _ =
        _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
          (Real.sqrt
            (_root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
              (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
              (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
              (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ := by
      congr 1
      calc
        ∫ u : ℝ, Real.exp (t * u ^ 2 * m) ∂gaussianReal 0 1 =
            ∫ u : ℝ, Real.exp (-(-t * m) * u ^ 2 + 0 * u)
              ∂gaussianReal 0 1 := by
                apply integral_congr_ae
                filter_upwards [] with u
                congr 1
                ring
        _ = _root_.GD.N0232.N0719.N0887.d003558 (1 : ℝ≥0) (-t * m) 0 := hmass
        _ = (Real.sqrt
              (_root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
                (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
                (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
                (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ := by
              unfold _root_.GD.N0232.N0719.N0887.d003558
              rw [hprecision]
              simp



theorem d003755
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
        (Real.sqrt
          (_root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ =
      (Real.sqrt
        (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ := by
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  let r := _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t
  let h₁ := 1 + 2 * t * d₁
  let h₂ := 1 + 2 * t * d₂
  let h₃ := 1 + 2 * t * d₃
  have hd₁ : 0 ≤ d₁ := by
    dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₂ : 0 ≤ d₂ := by
    dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₃ : 0 ≤ d₃ := by
    dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hr : 0 < r := by
    dsimp [r, d₁, d₂, d₃]
    exact _root_.GD.N0232.N0719.N0895.d003753 hp₁ hp₂ hp₃ hsum ht
  have hh₁ : 0 < h₁ := by dsimp [h₁]; positivity
  have hh₂ : 0 < h₂ := by dsimp [h₂]; positivity
  have hh₃ : 0 < h₃ := by dsimp [h₃]; positivity
  have hfactor :
      r * (h₁ * h₂ * h₃) =
        _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t := by
    dsimp [r, h₁, h₂, h₃]
    exact _root_.GD.N0232.N0719.N0888.d003693
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) (t := t)
      hsum (by positivity) (by positivity) (by positivity)
  have hsqrt :
      Real.sqrt r * Real.sqrt h₁ * Real.sqrt h₂ * Real.sqrt h₃ =
        Real.sqrt
          (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t) := by
    calc
      Real.sqrt r * Real.sqrt h₁ * Real.sqrt h₂ * Real.sqrt h₃ =
          Real.sqrt (r * h₁) * Real.sqrt h₂ * Real.sqrt h₃ := by
            rw [Real.sqrt_mul hr.le]
      _ = Real.sqrt ((r * h₁) * h₂) * Real.sqrt h₃ := by
            rw [Real.sqrt_mul (mul_nonneg hr.le hh₁.le)]
      _ = Real.sqrt (((r * h₁) * h₂) * h₃) := by
            rw [Real.sqrt_mul
              (mul_nonneg (mul_nonneg hr.le hh₁.le) hh₂.le)]
      _ = Real.sqrt
          (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t) := by
            congr 1
            rw [← hfactor]
            ring
  dsimp [_root_.GD.N0232.N0719.N0895.d003748, d₁, d₂, d₃, r, h₁, h₂, h₃] at *
  rw [← hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hr,
    Real.sqrt_ne_zero'.mpr hh₁,
    Real.sqrt_ne_zero'.mpr hh₂,
    Real.sqrt_ne_zero'.mpr hh₃]


theorem d003756
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    ∫ u : ℝ,
      (_root_.GD.N0232.N0719.N0895.d003747 p₁ v₁ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₂ v₂ t u *
        _root_.GD.N0232.N0719.N0895.d003747 p₃ v₃ t u)
      ∂gaussianReal 0 1 =
      (Real.sqrt
        (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t))⁻¹ := by
  rw [_root_.GD.N0232.N0719.N0895.d003754
    hp₁ hp₂ hp₃ hsum ht]
  exact _root_.GD.N0232.N0719.N0895.d003755
    hp₁ hp₂ hp₃ hsum ht

end

end GD.N0232.N0719.N0895
