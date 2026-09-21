import GD.Module0232

















namespace GD.N0232.N0719.N0887

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal


def d003554 (v : ℝ≥0) (a : ℝ) : ℝ :=
  1 + 2 * a * (v : ℝ)


def d003555 (v : ℝ≥0) (a : ℝ) : ℝ :=
  (v : ℝ) / _root_.GD.N0232.N0719.N0887.d003554 v a


def d003556 (v : ℝ≥0) (a : ℝ) : ℝ≥0 :=
  (_root_.GD.N0232.N0719.N0887.d003555 v a).toNNReal


def d003557 (v : ℝ≥0) (a b : ℝ) : ℝ :=
  b * (v : ℝ) / _root_.GD.N0232.N0719.N0887.d003554 v a


def d003558 (v : ℝ≥0) (a b : ℝ) : ℝ :=
  (Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a))⁻¹ *
    Real.exp (b ^ 2 * (v : ℝ) / (2 * _root_.GD.N0232.N0719.N0887.d003554 v a))

theorem d003559
    {v : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) :
    0 < _root_.GD.N0232.N0719.N0887.d003554 v a := by
  unfold _root_.GD.N0232.N0719.N0887.d003554
  positivity

theorem d003560
    {v : ℝ≥0} {a : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    0 < _root_.GD.N0232.N0719.N0887.d003555 v a := by
  unfold _root_.GD.N0232.N0719.N0887.d003555
  exact div_pos
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)) hh

@[simp]
theorem d003561
    {v : ℝ≥0} {a : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ) = _root_.GD.N0232.N0719.N0887.d003555 v a := by
  rw [_root_.GD.N0232.N0719.N0887.d003556,
    Real.coe_toNNReal _ (_root_.GD.N0232.N0719.N0887.d003560 hv hh).le]

theorem d003562
    {v : ℝ≥0} {a : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    _root_.GD.N0232.N0719.N0887.d003556 v a ≠ 0 := by
  apply NNReal.coe_ne_zero.mp
  rw [_root_.GD.N0232.N0719.N0887.d003561 hv hh]
  exact (_root_.GD.N0232.N0719.N0887.d003560 hv hh).ne'


theorem d003563
    {v : ℝ≥0} {a b x : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    -a * x ^ 2 + b * x - x ^ 2 / (2 * (v : ℝ)) =
      b ^ 2 * (v : ℝ) / (2 * _root_.GD.N0232.N0719.N0887.d003554 v a) -
        (x - _root_.GD.N0232.N0719.N0887.d003557 v a b) ^ 2 /
          (2 * _root_.GD.N0232.N0719.N0887.d003555 v a) := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hdiv :
      ∀ y : ℝ,
        y / (2 * ((v : ℝ) / _root_.GD.N0232.N0719.N0887.d003554 v a)) =
          y * _root_.GD.N0232.N0719.N0887.d003554 v a / (2 * (v : ℝ)) := by
    intro y
    field_simp [hvR, hh.ne']
  have hden :
      1 + a * (v : ℝ) * 2 ≠ 0 := by
    simpa only [_root_.GD.N0232.N0719.N0887.d003554, mul_assoc, mul_left_comm, mul_comm]
      using hh.ne'
  have hden2 :
      2 + a * (v : ℝ) * 4 ≠ 0 := by
    have : 0 < 2 + a * (v : ℝ) * 4 := by
      unfold _root_.GD.N0232.N0719.N0887.d003554 at hh
      nlinarith
    exact this.ne'
  unfold _root_.GD.N0232.N0719.N0887.d003557 _root_.GD.N0232.N0719.N0887.d003555
  rw [hdiv]
  unfold _root_.GD.N0232.N0719.N0887.d003554
  ring_nf
  field_simp [hvR, hden, hden2] <;> ring


theorem d003564
    {v : ℝ≥0} {a b x : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    Real.exp (-a * x ^ 2 + b * x) *
        Real.exp (-x ^ 2 / (2 * (v : ℝ))) =
      Real.exp
          (b ^ 2 * (v : ℝ) /
            (2 * _root_.GD.N0232.N0719.N0887.d003554 v a)) *
        Real.exp
          (-(x - _root_.GD.N0232.N0719.N0887.d003557 v a b) ^ 2 /
            (2 * _root_.GD.N0232.N0719.N0887.d003555 v a)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  convert
    _root_.GD.N0232.N0719.N0887.d003563
      (v := v) (a := a) (b := b) (x := x) hv hh using 1 <;> ring


theorem d003565
    {v : ℝ≥0} {a : ℝ} (hv : v ≠ 0)
    (hhpos : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ =
      (Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a))⁻¹ *
        (Real.sqrt (2 * Real.pi * (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ)))⁻¹ := by
  have hspos : 0 < _root_.GD.N0232.N0719.N0887.d003555 v a :=
    _root_.GD.N0232.N0719.N0887.d003560 hv hhpos
  have hprod :
      _root_.GD.N0232.N0719.N0887.d003554 v a * (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ) = (v : ℝ) := by
    rw [_root_.GD.N0232.N0719.N0887.d003561 hv hhpos]
    unfold _root_.GD.N0232.N0719.N0887.d003555
    field_simp [hhpos.ne']
  have hsqrt :
      Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a) *
          Real.sqrt (2 * Real.pi * (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ)) =
        Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [← Real.sqrt_mul (le_of_lt hhpos)]
    congr 1
    calc
      _root_.GD.N0232.N0719.N0887.d003554 v a *
            (2 * Real.pi * (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ)) =
          2 * Real.pi *
            (_root_.GD.N0232.N0719.N0887.d003554 v a * (_root_.GD.N0232.N0719.N0887.d003556 v a : ℝ)) := by ring
      _ = 2 * Real.pi * (v : ℝ) := by rw [hprod]
  rw [← hsqrt, mul_inv_rev]
  ring


theorem d003566
    {v : ℝ≥0} {a b x : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    Real.exp (-a * x ^ 2 + b * x) * gaussianPDFReal 0 v x =
      _root_.GD.N0232.N0719.N0887.d003558 v a b *
        gaussianPDFReal (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x := by
  have hexp :=
    _root_.GD.N0232.N0719.N0887.d003564
      (v := v) (a := a) (b := b) (x := x) hv hh
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [sub_zero]
  rw [_root_.GD.N0232.N0719.N0887.d003565 hv hh, _root_.GD.N0232.N0719.N0887.d003561 hv hh]
  calc
    Real.exp (-a * x ^ 2 + b * x) *
          ((Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a))⁻¹ *
              (Real.sqrt (2 * Real.pi * _root_.GD.N0232.N0719.N0887.d003555 v a))⁻¹ *
            Real.exp (-x ^ 2 / (2 * (v : ℝ)))) =
        (Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a))⁻¹ *
          (Real.sqrt (2 * Real.pi * _root_.GD.N0232.N0719.N0887.d003555 v a))⁻¹ *
          (Real.exp (-a * x ^ 2 + b * x) *
            Real.exp (-x ^ 2 / (2 * (v : ℝ)))) := by ring
    _ = (Real.sqrt (_root_.GD.N0232.N0719.N0887.d003554 v a))⁻¹ *
          (Real.sqrt (2 * Real.pi * _root_.GD.N0232.N0719.N0887.d003555 v a))⁻¹ *
          (Real.exp
              (b ^ 2 * (v : ℝ) /
                (2 * _root_.GD.N0232.N0719.N0887.d003554 v a)) *
            Real.exp
              (-(x - _root_.GD.N0232.N0719.N0887.d003557 v a b) ^ 2 /
                (2 * _root_.GD.N0232.N0719.N0887.d003555 v a))) := by rw [hexp]
    _ = _root_.GD.N0232.N0719.N0887.d003558 v a b *
          ((Real.sqrt (2 * Real.pi * _root_.GD.N0232.N0719.N0887.d003555 v a))⁻¹ *
            Real.exp
              (-(x - _root_.GD.N0232.N0719.N0887.d003557 v a b) ^ 2 /
                (2 * _root_.GD.N0232.N0719.N0887.d003555 v a))) := by
          unfold _root_.GD.N0232.N0719.N0887.d003558
          ring









theorem d003567
    {v : ℝ≥0} {a b : ℝ} (f : ℝ → ℝ)
    (hv : v ≠ 0) (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    ∫ x, Real.exp (-a * x ^ 2 + b * x) * f x ∂gaussianReal 0 v =
      _root_.GD.N0232.N0719.N0887.d003558 v a b *
        ∫ x, f x ∂gaussianReal
          (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    ∫ x, gaussianPDFReal 0 v x *
          (Real.exp (-a * x ^ 2 + b * x) * f x) =
        ∫ x, _root_.GD.N0232.N0719.N0887.d003558 v a b *
          (gaussianPDFReal (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x *
            f x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              have hpdf :=
                _root_.GD.N0232.N0719.N0887.d003566
                  (v := v) (a := a) (b := b) (x := x) hv hh
              calc
                gaussianPDFReal 0 v x *
                      (Real.exp (-a * x ^ 2 + b * x) * f x) =
                    (Real.exp (-a * x ^ 2 + b * x) *
                      gaussianPDFReal 0 v x) * f x := by ring
                _ = (_root_.GD.N0232.N0719.N0887.d003558 v a b *
                      gaussianPDFReal
                        (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x) *
                      f x := by rw [hpdf]
                _ = _root_.GD.N0232.N0719.N0887.d003558 v a b *
                      (gaussianPDFReal
                        (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x *
                        f x) := by ring
    _ = _root_.GD.N0232.N0719.N0887.d003558 v a b *
          ∫ x, gaussianPDFReal (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) x *
            f x := by rw [integral_const_mul]
    _ = _root_.GD.N0232.N0719.N0887.d003558 v a b *
          ∫ x, f x ∂gaussianReal
            (_root_.GD.N0232.N0719.N0887.d003557 v a b) (_root_.GD.N0232.N0719.N0887.d003556 v a) := by
              congr 1
              rw [integral_gaussianReal_eq_integral_smul
                (_root_.GD.N0232.N0719.N0887.d003562 hv hh)]
              simp only [smul_eq_mul]


theorem d003568
    {v : ℝ≥0} {a b : ℝ} (hv : v ≠ 0)
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    ∫ x, Real.exp (-a * x ^ 2 + b * x) ∂gaussianReal 0 v =
      _root_.GD.N0232.N0719.N0887.d003558 v a b := by
  simpa using
    _root_.GD.N0232.N0719.N0887.d003567
      (v := v) (a := a) (b := b) (fun _ ↦ (1 : ℝ)) hv hh

theorem d003569
    {v : ℝ≥0} {a b : ℝ}
    (hh : 0 < _root_.GD.N0232.N0719.N0887.d003554 v a) :
    0 < _root_.GD.N0232.N0719.N0887.d003558 v a b := by
  unfold _root_.GD.N0232.N0719.N0887.d003558
  exact mul_pos
    (inv_pos.mpr (Real.sqrt_pos.2 hh))
    (Real.exp_pos _)

end

end GD.N0232.N0719.N0887
