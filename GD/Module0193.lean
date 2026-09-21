import Mathlib










open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real

namespace GD.N0232.N0720.N1277

noncomputable section



def d002621 (v x : ℝ) : ℝ :=
  gaussianPDFReal 0 v.toNNReal x



def d002622 (v : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹

theorem d002623
    {v x : ℝ} (hv : 0 < v) :
    _root_.GD.N0232.N0720.N1277.d002621 v x = _root_.GD.N0232.N0720.N1277.d002622 v *
      Real.exp (-(x ^ 2) / (2 * v)) := by
  simp [_root_.GD.N0232.N0720.N1277.d002621, _root_.GD.N0232.N0720.N1277.d002622, gaussianPDFReal,
    Real.coe_toNNReal v hv.le]

theorem d002624 {v x : ℝ} (hv : 0 < v) :
    0 < _root_.GD.N0232.N0720.N1277.d002621 v x := by
  exact gaussianPDFReal_pos 0 v.toNNReal x
    (ne_of_gt (Real.toNNReal_pos.mpr hv))

theorem d002625 (v : ℝ) :
    Integrable (_root_.GD.N0232.N0720.N1277.d002621 v) := by
  exact integrable_gaussianPDFReal 0 v.toNNReal

theorem d002626 {v : ℝ} (hv : 0 < v) :
    ∫ x : ℝ, _root_.GD.N0232.N0720.N1277.d002621 v x = 1 := by
  exact integral_gaussianPDFReal_eq_one 0
    (ne_of_gt (Real.toNNReal_pos.mpr hv))

theorem d002627 {v : ℝ} (hv : 0 < v) :
    ∫ x : ℝ, x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 v x = v := by
  let vn : ℝ≥0 := v.toNNReal
  have hvn : vn ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hv)
  have hvarN :
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 vn) = (vn : ℝ) := by
    have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := vn)
    rw [variance_eq_integral measurable_id'.aemeasurable] at h
    simp only [integral_id_gaussianReal, sub_zero] at h
    exact h
  rw [integral_gaussianReal_eq_integral_smul (E := ℝ) hvn] at hvarN
  simpa [_root_.GD.N0232.N0720.N1277.d002621, vn, Real.coe_toNNReal v hv.le, mul_comm] using hvarN




def d002628 (a b : ℝ) : ℝ :=
  a * b / (a + b)


def d002629 (a b x : ℝ) : ℝ :=
  a / (a + b) * x

theorem d002630 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < _root_.GD.N0232.N0720.N1277.d002628 a b := by
  unfold _root_.GD.N0232.N0720.N1277.d002628
  positivity

theorem d002631 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a + b) * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002628 a b) =
      Real.sqrt a * Real.sqrt b := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ a + b),
    ← Real.sqrt_mul ha.le]
  congr 1
  unfold _root_.GD.N0232.N0720.N1277.d002628
  field_simp

theorem d002632
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0232.N0720.N1277.d002622 a * _root_.GD.N0232.N0720.N1277.d002622 b =
      _root_.GD.N0232.N0720.N1277.d002622 (a + b) *
        _root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002628 a b) := by
  have hab : 0 < a + b := add_pos ha hb
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  have hfactor (v : ℝ) (hv : 0 ≤ v) :
      Real.sqrt (2 * Real.pi * v) =
        Real.sqrt (2 * Real.pi) * Real.sqrt v := by
    rw [show 2 * Real.pi * v = (2 * Real.pi) * v by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  unfold _root_.GD.N0232.N0720.N1277.d002622
  rw [hfactor a ha.le, hfactor b hb.le, hfactor (a + b) hab.le,
    hfactor (_root_.GD.N0232.N0720.N1277.d002628 a b) ht.le]
  have hS : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have hsab : Real.sqrt (a + b) ≠ 0 := (Real.sqrt_pos.2 hab).ne'
  have hst : Real.sqrt (_root_.GD.N0232.N0720.N1277.d002628 a b) ≠ 0 :=
    (Real.sqrt_pos.2 ht).ne'
  field_simp
  nlinarith [_root_.GD.N0232.N0720.N1277.d002631 ha hb]

theorem d002633
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -(y ^ 2) / (2 * a) + (-(x - y) ^ 2) / (2 * b) =
      -(x ^ 2) / (2 * (a + b)) +
        (-(y - _root_.GD.N0232.N0720.N1277.d002629 a b x) ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002628 a b) := by
  unfold _root_.GD.N0232.N0720.N1277.d002629 _root_.GD.N0232.N0720.N1277.d002628
  field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
  ring



theorem d002634
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y) =
      _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b) (y - _root_.GD.N0232.N0720.N1277.d002629 a b x) := by
  have hab : 0 < a + b := add_pos ha hb
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  have hexp := _root_.GD.N0232.N0720.N1277.d002633 (x := x) (y := y) ha hb
  simp only [_root_.GD.N0232.N0720.N1277.d002621, gaussianPDFReal]
  simp only [Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hb.le,
    Real.coe_toNNReal _ hab.le, Real.coe_toNNReal _ ht.le, sub_zero]
  change _root_.GD.N0232.N0720.N1277.d002622 a * Real.exp (-(y ^ 2) / (2 * a)) *
      (_root_.GD.N0232.N0720.N1277.d002622 b * Real.exp (-((x - y) ^ 2) / (2 * b))) =
    _root_.GD.N0232.N0720.N1277.d002622 (a + b) * Real.exp (-(x ^ 2) / (2 * (a + b))) *
      (_root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002628 a b) *
        Real.exp (-((y - _root_.GD.N0232.N0720.N1277.d002629 a b x) ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002628 a b)))
  calc
    _ = (_root_.GD.N0232.N0720.N1277.d002622 a * _root_.GD.N0232.N0720.N1277.d002622 b) *
        Real.exp (-(y ^ 2) / (2 * a) + (-(x - y) ^ 2) / (2 * b)) := by
          rw [Real.exp_add]
          ring
    _ = (_root_.GD.N0232.N0720.N1277.d002622 a * _root_.GD.N0232.N0720.N1277.d002622 b) *
        Real.exp (-(x ^ 2) / (2 * (a + b)) +
          (-(y - _root_.GD.N0232.N0720.N1277.d002629 a b x) ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002628 a b)) := by
          rw [hexp]
    _ = (_root_.GD.N0232.N0720.N1277.d002622 (a + b) *
          _root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002628 a b)) *
        Real.exp (-(x ^ 2) / (2 * (a + b)) +
          (-(y - _root_.GD.N0232.N0720.N1277.d002629 a b x) ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002628 a b)) := by
          rw [_root_.GD.N0232.N0720.N1277.d002632 ha hb]
    _ = _ := by
      rw [Real.exp_add]
      ring



theorem d002635 (t m : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, _root_.GD.N0232.N0720.N1277.d002621 t (y - m) = 1 := by
  rw [integral_sub_right_eq_self (μ := volume) (_root_.GD.N0232.N0720.N1277.d002621 t) m]
  exact _root_.GD.N0232.N0720.N1277.d002626 ht

theorem d002636 (t m : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, y * _root_.GD.N0232.N0720.N1277.d002621 t (y - m) = m := by
  let tn : ℝ≥0 := t.toNNReal
  have htn : tn ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr ht)
  have hmean := integral_id_gaussianReal (μ := m) (v := tn)
  rw [integral_gaussianReal_eq_integral_smul (E := ℝ) htn] at hmean
  have hshift (y : ℝ) :
      _root_.GD.N0232.N0720.N1277.d002621 t (y - m) = gaussianPDFReal m tn y := by
    change gaussianPDFReal 0 tn (y - m) = gaussianPDFReal m tn y
    simpa using gaussianPDFReal_sub (μ := (0 : ℝ)) (v := tn) y m
  simpa only [hshift, smul_eq_mul, mul_comm] using hmean


theorem d002637
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y : ℝ, _root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y) =
      _root_.GD.N0232.N0720.N1277.d002621 (a + b) x := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  calc
    _ = ∫ y : ℝ, _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b) (y - _root_.GD.N0232.N0720.N1277.d002629 a b x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦
          _root_.GD.N0232.N0720.N1277.d002634 ha hb
    _ = _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
          (∫ y : ℝ, _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b)
            (y - _root_.GD.N0232.N0720.N1277.d002629 a b x)) := by
        rw [integral_const_mul]
    _ = _root_.GD.N0232.N0720.N1277.d002621 (a + b) x := by
        rw [_root_.GD.N0232.N0720.N1277.d002635 _ _ ht, mul_one]


theorem d002638
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y : ℝ, y *
        (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y)) =
      _root_.GD.N0232.N0720.N1277.d002629 a b x * _root_.GD.N0232.N0720.N1277.d002621 (a + b) x := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  calc
    _ = ∫ y : ℝ, y *
          (_root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b) (y - _root_.GD.N0232.N0720.N1277.d002629 a b x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          change y * (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y)) =
            y * (_root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
              _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b) (y - _root_.GD.N0232.N0720.N1277.d002629 a b x))
          rw [_root_.GD.N0232.N0720.N1277.d002634 ha hb]
    _ = _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
          (∫ y : ℝ, y * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b)
            (y - _root_.GD.N0232.N0720.N1277.d002629 a b x)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by ring
    _ = _root_.GD.N0232.N0720.N1277.d002629 a b x * _root_.GD.N0232.N0720.N1277.d002621 (a + b) x := by
        rw [_root_.GD.N0232.N0720.N1277.d002636 _ _ ht]
        ring

theorem d002639
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ ↦
      _root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y)) := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  have hs := (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1277.d002628 a b)).comp_sub_right
    (_root_.GD.N0232.N0720.N1277.d002629 a b x)
  have hscaled := hs.const_mul (_root_.GD.N0232.N0720.N1277.d002621 (a + b) x)
  refine hscaled.congr ?_
  exact Filter.Eventually.of_forall fun y ↦
    (_root_.GD.N0232.N0720.N1277.d002634 ha hb).symm

theorem d002640 (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ x * _root_.GD.N0232.N0720.N1277.d002621 t x) := by
  have hb : 0 < (2 * t)⁻¹ := by positivity
  have hbase := (integrable_mul_exp_neg_mul_sq hb).const_mul
    (_root_.GD.N0232.N0720.N1277.d002622 t)
  refine hbase.congr ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    change _root_.GD.N0232.N0720.N1277.d002622 t *
        (x * Real.exp (-(2 * t)⁻¹ * x ^ 2)) =
      x * _root_.GD.N0232.N0720.N1277.d002621 t x
    rw [_root_.GD.N0232.N0720.N1277.d002623 ht]
    have he : -(2 * t)⁻¹ * x ^ 2 = -(x ^ 2) / (2 * t) := by
      field_simp
    rw [he]
    ring

theorem d002641 (t m : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ ↦ y * _root_.GD.N0232.N0720.N1277.d002621 t (y - m)) := by
  have hcenter := (_root_.GD.N0232.N0720.N1277.d002640 t ht).comp_sub_right m
  have hmass := ((_root_.GD.N0232.N0720.N1277.d002625 t).comp_sub_right m).const_mul m
  refine (hcenter.add hmass).congr ?_
  exact Filter.Eventually.of_forall fun y ↦ by
    change (y - m) * _root_.GD.N0232.N0720.N1277.d002621 t (y - m) +
        m * _root_.GD.N0232.N0720.N1277.d002621 t (y - m) =
      y * _root_.GD.N0232.N0720.N1277.d002621 t (y - m)
    ring

theorem d002642
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ ↦ y *
      (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y))) := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  have hs := _root_.GD.N0232.N0720.N1277.d002641
    (_root_.GD.N0232.N0720.N1277.d002628 a b) (_root_.GD.N0232.N0720.N1277.d002629 a b x) ht
  have hscaled := hs.const_mul (_root_.GD.N0232.N0720.N1277.d002621 (a + b) x)
  refine hscaled.congr ?_
  exact Filter.Eventually.of_forall fun y ↦ by
    change _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
        (y * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b) (y - _root_.GD.N0232.N0720.N1277.d002629 a b x)) =
      y * (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y))
    rw [_root_.GD.N0232.N0720.N1277.d002634 ha hb]
    ring




theorem d002643
    {U w v V v₀ c d x : ℝ}
    (hU : 0 < U) (hw : 0 < w) (hv : 0 < v)
    (hUV : U + v = V) (hwv : w + v = v₀) :
    ∫ y : ℝ, (c * _root_.GD.N0232.N0720.N1277.d002621 U y - d * _root_.GD.N0232.N0720.N1277.d002621 w y) *
        _root_.GD.N0232.N0720.N1277.d002621 v (x - y) =
      c * _root_.GD.N0232.N0720.N1277.d002621 V x - d * _root_.GD.N0232.N0720.N1277.d002621 v₀ x := by
  have hiU := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) hU hv
  have hiw := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) hw hv
  rw [show (fun y : ℝ ↦
      (c * _root_.GD.N0232.N0720.N1277.d002621 U y - d * _root_.GD.N0232.N0720.N1277.d002621 w y) *
        _root_.GD.N0232.N0720.N1277.d002621 v (x - y)) =
      (fun y : ℝ ↦ c *
        (_root_.GD.N0232.N0720.N1277.d002621 U y * _root_.GD.N0232.N0720.N1277.d002621 v (x - y)) -
          d * (_root_.GD.N0232.N0720.N1277.d002621 w y * _root_.GD.N0232.N0720.N1277.d002621 v (x - y))) by
    funext y; ring]
  rw [integral_sub (hiU.const_mul c) (hiw.const_mul d),
    integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002637 hU hv,
    _root_.GD.N0232.N0720.N1277.d002637 hw hv,
    hUV, hwv]




theorem d002644
    {U w v V v₀ c d x : ℝ}
    (hU : 0 < U) (hw : 0 < w) (hv : 0 < v)
    (hUV : U + v = V) (hwv : w + v = v₀) :
    ∫ y : ℝ, y *
        ((c * _root_.GD.N0232.N0720.N1277.d002621 U y - d * _root_.GD.N0232.N0720.N1277.d002621 w y) *
          _root_.GD.N0232.N0720.N1277.d002621 v (x - y)) =
      c * (U / V * x) * _root_.GD.N0232.N0720.N1277.d002621 V x -
        d * (w / v₀ * x) * _root_.GD.N0232.N0720.N1277.d002621 v₀ x := by
  have hiU := _root_.GD.N0232.N0720.N1277.d002642
    (x := x) hU hv
  have hiw := _root_.GD.N0232.N0720.N1277.d002642
    (x := x) hw hv
  rw [show (fun y : ℝ ↦ y *
      ((c * _root_.GD.N0232.N0720.N1277.d002621 U y - d * _root_.GD.N0232.N0720.N1277.d002621 w y) *
        _root_.GD.N0232.N0720.N1277.d002621 v (x - y))) =
      (fun y : ℝ ↦ c *
        (y * (_root_.GD.N0232.N0720.N1277.d002621 U y * _root_.GD.N0232.N0720.N1277.d002621 v (x - y))) -
          d * (y * (_root_.GD.N0232.N0720.N1277.d002621 w y * _root_.GD.N0232.N0720.N1277.d002621 v (x - y)))) by
    funext y; ring]
  rw [integral_sub (hiU.const_mul c) (hiw.const_mul d),
    integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002638 hU hv,
    _root_.GD.N0232.N0720.N1277.d002638 hw hv,
    hUV, hwv]
  unfold _root_.GD.N0232.N0720.N1277.d002629
  rw [hUV, hwv]
  ring




def d002645 (v₀ V : ℝ) : ℝ :=
  2 * V - v₀


def d002646 (v₀ V : ℝ) : ℝ :=
  v₀ * V / _root_.GD.N0232.N0720.N1277.d002645 v₀ V


def d002647 (v₀ V : ℝ) : ℝ :=
  V / (Real.sqrt v₀ * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V))

theorem d002648 {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    0 < _root_.GD.N0232.N0720.N1277.d002645 v₀ V := by
  unfold _root_.GD.N0232.N0720.N1277.d002645
  linarith

theorem d002649 {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    0 < _root_.GD.N0232.N0720.N1277.d002646 v₀ V := by
  unfold _root_.GD.N0232.N0720.N1277.d002646
  exact div_pos (mul_pos hv₀ (lt_trans hv₀ hV))
    (_root_.GD.N0232.N0720.N1277.d002648 hv₀ hV)

theorem d002650
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    Real.sqrt (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) *
        Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) =
      Real.sqrt v₀ * Real.sqrt V := by
  have hD : 0 < _root_.GD.N0232.N0720.N1277.d002645 v₀ V := _root_.GD.N0232.N0720.N1277.d002648 hv₀ hV
  rw [← Real.sqrt_mul (_root_.GD.N0232.N0720.N1277.d002649 hv₀ hV).le,
    ← Real.sqrt_mul hv₀.le]
  congr 1
  unfold _root_.GD.N0232.N0720.N1277.d002646
  field_simp

theorem d002651
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    _root_.GD.N0232.N0720.N1277.d002622 v₀ ^ 2 =
      _root_.GD.N0232.N0720.N1277.d002647 v₀ V * _root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) *
        _root_.GD.N0232.N0720.N1277.d002622 V := by
  have hV0 : 0 < V := lt_trans hv₀ hV
  have hD : 0 < _root_.GD.N0232.N0720.N1277.d002645 v₀ V := _root_.GD.N0232.N0720.N1277.d002648 hv₀ hV
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002646 v₀ V := _root_.GD.N0232.N0720.N1277.d002649 hv₀ hV
  have hfactor (v : ℝ) (hv : 0 ≤ v) :
      Real.sqrt (2 * Real.pi * v) =
        Real.sqrt (2 * Real.pi) * Real.sqrt v := by
    rw [show 2 * Real.pi * v = (2 * Real.pi) * v by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  unfold _root_.GD.N0232.N0720.N1277.d002622 _root_.GD.N0232.N0720.N1277.d002647
  rw [hfactor v₀ hv₀.le, hfactor (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) ht.le,
    hfactor V hV0.le]
  have hS : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hs0 : Real.sqrt v₀ ≠ 0 := (Real.sqrt_pos.2 hv₀).ne'
  have hsV : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV0).ne'
  have hsD : Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) ≠ 0 :=
    (Real.sqrt_pos.2 hD).ne'
  have hst : Real.sqrt (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) ≠ 0 :=
    (Real.sqrt_pos.2 ht).ne'
  field_simp
  have hs0sq := Real.sq_sqrt hv₀.le
  have hsVsq := Real.sq_sqrt hV0.le
  calc
    Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) *
          Real.sqrt (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) * Real.sqrt V =
        (Real.sqrt (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) *
          Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V)) * Real.sqrt V := by ring
    _ = (Real.sqrt v₀ * Real.sqrt V) * Real.sqrt V := by
      rw [_root_.GD.N0232.N0720.N1277.d002650 hv₀ hV]
    _ = Real.sqrt v₀ * (Real.sqrt V ^ 2) := by ring
    _ = Real.sqrt v₀ * V := by rw [hsVsq]

theorem d002652
    {v₀ V x : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    -(x ^ 2) / (2 * v₀) + -(x ^ 2) / (2 * v₀) =
      -(x ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002646 v₀ V) + -(x ^ 2) / (2 * V) := by
  unfold _root_.GD.N0232.N0720.N1277.d002646 _root_.GD.N0232.N0720.N1277.d002645
  field_simp [hv₀.ne', (lt_trans hv₀ hV).ne', (by linarith : (2 * V - v₀) ≠ 0)]
  ring


theorem d002653
    {v₀ V x : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    _root_.GD.N0232.N0720.N1277.d002621 v₀ x ^ 2 / _root_.GD.N0232.N0720.N1277.d002621 V x =
      _root_.GD.N0232.N0720.N1277.d002647 v₀ V * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) x := by
  have hV0 : 0 < V := lt_trans hv₀ hV
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002646 v₀ V := _root_.GD.N0232.N0720.N1277.d002649 hv₀ hV
  rw [div_eq_iff (_root_.GD.N0232.N0720.N1277.d002624 hV0).ne']
  rw [_root_.GD.N0232.N0720.N1277.d002623 hv₀,
    _root_.GD.N0232.N0720.N1277.d002623 hV0,
    _root_.GD.N0232.N0720.N1277.d002623 ht]
  calc
    (_root_.GD.N0232.N0720.N1277.d002622 v₀ * Real.exp (-(x ^ 2) / (2 * v₀))) ^ 2 =
        _root_.GD.N0232.N0720.N1277.d002622 v₀ ^ 2 *
          Real.exp (-(x ^ 2) / (2 * v₀) + -(x ^ 2) / (2 * v₀)) := by
      rw [Real.exp_add]
      ring
    _ = (_root_.GD.N0232.N0720.N1277.d002647 v₀ V * _root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) *
          _root_.GD.N0232.N0720.N1277.d002622 V) *
        Real.exp (-(x ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002646 v₀ V) + -(x ^ 2) / (2 * V)) := by
      rw [_root_.GD.N0232.N0720.N1277.d002651 hv₀ hV,
        _root_.GD.N0232.N0720.N1277.d002652 hv₀ hV]
    _ = (_root_.GD.N0232.N0720.N1277.d002647 v₀ V *
          (_root_.GD.N0232.N0720.N1277.d002622 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) *
            Real.exp (-(x ^ 2) / (2 * _root_.GD.N0232.N0720.N1277.d002646 v₀ V)))) *
        (_root_.GD.N0232.N0720.N1277.d002622 V * Real.exp (-(x ^ 2) / (2 * V))) := by
      rw [Real.exp_add]
      ring


theorem d002654
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    _root_.GD.N0232.N0720.N1277.d002647 v₀ V * _root_.GD.N0232.N0720.N1277.d002646 v₀ V =
      Real.sqrt v₀ * V ^ 2 /
        (_root_.GD.N0232.N0720.N1277.d002645 v₀ V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V)) := by
  have hD : 0 < _root_.GD.N0232.N0720.N1277.d002645 v₀ V := _root_.GD.N0232.N0720.N1277.d002648 hv₀ hV
  have hs0 : Real.sqrt v₀ ≠ 0 := (Real.sqrt_pos.2 hv₀).ne'
  have hsD : Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) ≠ 0 :=
    (Real.sqrt_pos.2 hD).ne'
  have hs0sq := Real.sq_sqrt hv₀.le
  unfold _root_.GD.N0232.N0720.N1277.d002647 _root_.GD.N0232.N0720.N1277.d002646
  field_simp
  nlinarith







theorem d002655
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    ∫ x : ℝ, x ^ 2 *
        (_root_.GD.N0232.N0720.N1277.d002621 v₀ x ^ 2 / _root_.GD.N0232.N0720.N1277.d002621 V x) =
      Real.sqrt v₀ * V ^ 2 /
        (_root_.GD.N0232.N0720.N1277.d002645 v₀ V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V)) := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002646 v₀ V := _root_.GD.N0232.N0720.N1277.d002649 hv₀ hV
  calc
    _ = ∫ x : ℝ, _root_.GD.N0232.N0720.N1277.d002647 v₀ V *
          (x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change x ^ 2 * (_root_.GD.N0232.N0720.N1277.d002621 v₀ x ^ 2 /
            _root_.GD.N0232.N0720.N1277.d002621 V x) =
          _root_.GD.N0232.N0720.N1277.d002647 v₀ V *
            (x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) x)
        rw [_root_.GD.N0232.N0720.N1277.d002653 hv₀ hV]
        ring
    _ = _root_.GD.N0232.N0720.N1277.d002647 v₀ V *
          (∫ x : ℝ, x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002646 v₀ V) x) := by
      rw [integral_const_mul]
    _ = _root_.GD.N0232.N0720.N1277.d002647 v₀ V * _root_.GD.N0232.N0720.N1277.d002646 v₀ V := by
      rw [_root_.GD.N0232.N0720.N1277.d002627 ht]
    _ = _ := _root_.GD.N0232.N0720.N1277.d002654 hv₀ hV

theorem d002656
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    Real.sqrt v₀ * V ^ 2 /
        (_root_.GD.N0232.N0720.N1277.d002645 v₀ V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V)) ≤
      Real.sqrt (v₀ * V) := by
  have hV0 : 0 < V := lt_trans hv₀ hV
  have hD : 0 < _root_.GD.N0232.N0720.N1277.d002645 v₀ V := _root_.GD.N0232.N0720.N1277.d002648 hv₀ hV
  have hVD : V ≤ _root_.GD.N0232.N0720.N1277.d002645 v₀ V := by
    unfold _root_.GD.N0232.N0720.N1277.d002645
    linarith
  have hsVD : Real.sqrt V ≤ Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) :=
    Real.sqrt_le_sqrt hVD
  have hsVsq := Real.sq_sqrt hV0.le
  have hprod : V ≤ Real.sqrt V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) := by
    calc
      V = Real.sqrt V * Real.sqrt V := by nlinarith
      _ ≤ Real.sqrt V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V) :=
        mul_le_mul_of_nonneg_left hsVD (Real.sqrt_nonneg V)
  have hmain : V ^ 2 ≤ Real.sqrt V *
      (_root_.GD.N0232.N0720.N1277.d002645 v₀ V * Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645 v₀ V)) := by
    have hm := mul_le_mul hVD hprod hV0.le hD.le
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg v₀)
  have hsprod : Real.sqrt (v₀ * V) = Real.sqrt v₀ * Real.sqrt V := by
    rw [Real.sqrt_mul hv₀.le]
  rw [hsprod, div_le_iff₀ (mul_pos hD (Real.sqrt_pos.2 hD))]
  nlinarith

theorem d002657
    {v₀ V : ℝ} (hv₀ : 0 < v₀) (hV : v₀ < V) :
    (∫ x : ℝ, x ^ 2 *
        (_root_.GD.N0232.N0720.N1277.d002621 v₀ x ^ 2 / _root_.GD.N0232.N0720.N1277.d002621 V x)) ≤
      Real.sqrt (v₀ * V) := by
  rw [_root_.GD.N0232.N0720.N1277.d002655 hv₀ hV]
  exact _root_.GD.N0232.N0720.N1277.d002656 hv₀ hV



theorem d002658
    {w U c d : ℝ} (hw : 0 < w) (hWU : w ≤ U)
    (hpeak : d * Real.sqrt U ≤ c * Real.sqrt w) :
    d * _root_.GD.N0232.N0720.N1277.d002622 w ≤
      c * _root_.GD.N0232.N0720.N1277.d002622 U := by
  have hU : 0 < U := lt_of_lt_of_le hw hWU
  have hfactor (v : ℝ) (hv : 0 ≤ v) :
      Real.sqrt (2 * Real.pi * v) =
        Real.sqrt (2 * Real.pi) * Real.sqrt v := by
    rw [show 2 * Real.pi * v = (2 * Real.pi) * v by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  unfold _root_.GD.N0232.N0720.N1277.d002622
  rw [hfactor w hw.le, hfactor U hU.le]
  have hS : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.2 hU
  change d / (Real.sqrt (2 * Real.pi) * Real.sqrt w) ≤
    c / (Real.sqrt (2 * Real.pi) * Real.sqrt U)
  rw [div_le_div_iff₀ (mul_pos hS hsw) (mul_pos hS hsU)]
  nlinarith

theorem d002659
    {w U x : ℝ} (hw : 0 < w) (hWU : w ≤ U) :
    -(x ^ 2) / (2 * w) ≤ -(x ^ 2) / (2 * U) := by
  have hU : 0 < U := lt_of_lt_of_le hw hWU
  have hi : 1 / U ≤ 1 / w := one_div_le_one_div_of_le hw hWU
  have hx : 0 ≤ x ^ 2 / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hi hx
  have hw0 : w ≠ 0 := hw.ne'
  have hU0 : U ≠ 0 := hU.ne'
  have hfrac : x ^ 2 / (2 * U) ≤ x ^ 2 / (2 * w) := by
    calc
      x ^ 2 / (2 * U) = (x ^ 2 / 2) * (1 / U) := by
        field_simp
      _ ≤ (x ^ 2 / 2) * (1 / w) := hm
      _ = x ^ 2 / (2 * w) := by
        field_simp
  calc
    -(x ^ 2) / (2 * w) = -(x ^ 2 / (2 * w)) := by ring
    _ ≤ -(x ^ 2 / (2 * U)) := neg_le_neg hfrac
    _ = -(x ^ 2) / (2 * U) := by ring




theorem d002660
    {w U c d x : ℝ} (hw : 0 < w) (hWU : w ≤ U)
    (hc : 0 ≤ c)
    (hpeak : d * Real.sqrt U ≤ c * Real.sqrt w) :
    d * _root_.GD.N0232.N0720.N1277.d002621 w x ≤ c * _root_.GD.N0232.N0720.N1277.d002621 U x := by
  have hU : 0 < U := lt_of_lt_of_le hw hWU
  rw [_root_.GD.N0232.N0720.N1277.d002623 hw,
    _root_.GD.N0232.N0720.N1277.d002623 hU]
  have hn := _root_.GD.N0232.N0720.N1277.d002658 hw hWU hpeak
  have he : Real.exp (-(x ^ 2) / (2 * w)) ≤
      Real.exp (-(x ^ 2) / (2 * U)) :=
    Real.exp_le_exp.mpr (_root_.GD.N0232.N0720.N1277.d002659 (x := x) hw hWU)
  calc
    d * (_root_.GD.N0232.N0720.N1277.d002622 w * Real.exp (-(x ^ 2) / (2 * w))) =
        (d * _root_.GD.N0232.N0720.N1277.d002622 w) * Real.exp (-(x ^ 2) / (2 * w)) := by ring
    _ ≤ (c * _root_.GD.N0232.N0720.N1277.d002622 U) * Real.exp (-(x ^ 2) / (2 * U)) := by
      exact mul_le_mul hn he (Real.exp_pos _).le
        (mul_nonneg hc (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    _ = c * (_root_.GD.N0232.N0720.N1277.d002622 U * Real.exp (-(x ^ 2) / (2 * U))) := by ring

theorem d002661
    {w U c d x : ℝ} (hw : 0 < w) (hWU : w ≤ U)
    (hc : 0 ≤ c)
    (hpeak : d * Real.sqrt U ≤ c * Real.sqrt w) :
    0 ≤ c * _root_.GD.N0232.N0720.N1277.d002621 U x - d * _root_.GD.N0232.N0720.N1277.d002621 w x := by
  exact sub_nonneg.mpr
    (_root_.GD.N0232.N0720.N1277.d002660 (x := x) hw hWU hc hpeak)

#print axioms _root_.GD.N0232.N0720.N1277.d002637
#print axioms _root_.GD.N0232.N0720.N1277.d002638
#print axioms _root_.GD.N0232.N0720.N1277.d002655
#print axioms _root_.GD.N0232.N0720.N1277.d002660

end

end GD.N0232.N0720.N1277
