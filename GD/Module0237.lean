import GD.Module0232



















namespace GD
namespace N0228
namespace N0546

noncomputable section


def d003454 (τ u : ℝ) : ℝ :=
  1 + (τ - 1) * u


def d003455 (τ u : ℝ) : ℝ :=
  τ * u / _root_.GD.N0228.N0546.d003454 τ u


def d003456 (τ v : ℝ) : ℝ :=
  τ + (1 - τ) * v


def d003457 (τ v : ℝ) : ℝ :=
  v / _root_.GD.N0228.N0546.d003456 τ v



theorem d003458
    {τ v : ℝ} (hH : _root_.GD.N0228.N0546.d003456 τ v ≠ 0) :
    _root_.GD.N0228.N0546.d003454 τ (_root_.GD.N0228.N0546.d003457 τ v) =
      τ / _root_.GD.N0228.N0546.d003456 τ v := by
  rw [eq_div_iff hH]
  simp only [_root_.GD.N0228.N0546.d003454, _root_.GD.N0228.N0546.d003457]
  rw [add_mul, mul_assoc, div_mul_cancel₀ v hH]
  simp only [_root_.GD.N0228.N0546.d003456]
  ring



theorem d003459
    {τ v : ℝ} (hH : _root_.GD.N0228.N0546.d003456 τ v ≠ 0) :
    1 - _root_.GD.N0228.N0546.d003457 τ v =
      τ * (1 - v) / _root_.GD.N0228.N0546.d003456 τ v := by
  rw [eq_div_iff hH]
  simp only [_root_.GD.N0228.N0546.d003457]
  rw [sub_mul, one_mul, div_mul_cancel₀ v hH]
  simp only [_root_.GD.N0228.N0546.d003456]
  ring


theorem d003460
    {τ v : ℝ} (hτ : τ ≠ 0) (hH : _root_.GD.N0228.N0546.d003456 τ v ≠ 0) :
    _root_.GD.N0228.N0546.d003455 τ (_root_.GD.N0228.N0546.d003457 τ v) = v := by
  rw [_root_.GD.N0228.N0546.d003455, _root_.GD.N0228.N0546.d003458 hH]
  simp only [_root_.GD.N0228.N0546.d003457]
  field_simp [hτ, hH]



theorem d003461
    {τ u : ℝ} (hD : _root_.GD.N0228.N0546.d003454 τ u ≠ 0) :
    _root_.GD.N0228.N0546.d003456 τ (_root_.GD.N0228.N0546.d003455 τ u) =
      τ / _root_.GD.N0228.N0546.d003454 τ u := by
  rw [eq_div_iff hD]
  simp only [_root_.GD.N0228.N0546.d003456, _root_.GD.N0228.N0546.d003455]
  rw [add_mul, mul_assoc, div_mul_cancel₀ (τ * u) hD]
  simp only [_root_.GD.N0228.N0546.d003454]
  ring


theorem d003462
    {τ u : ℝ} (hτ : τ ≠ 0) (hD : _root_.GD.N0228.N0546.d003454 τ u ≠ 0) :
    _root_.GD.N0228.N0546.d003457 τ (_root_.GD.N0228.N0546.d003455 τ u) = u := by
  rw [_root_.GD.N0228.N0546.d003457, _root_.GD.N0228.N0546.d003461 hD]
  simp only [_root_.GD.N0228.N0546.d003455]
  field_simp [hτ, hD]


theorem d003463
    {τ u : ℝ} (hτ : 0 < τ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < _root_.GD.N0228.N0546.d003454 τ u := by
  by_cases hτ1 : 1 ≤ τ
  · have hcoef : 0 ≤ τ - 1 := sub_nonneg.mpr hτ1
    simp only [_root_.GD.N0228.N0546.d003454]
    nlinarith [mul_nonneg hcoef hu0]
  · have hτle : τ < 1 := lt_of_not_ge hτ1
    have hcoef : τ - 1 < 0 := sub_neg.mpr hτle
    have hmul : (τ - 1) * u ≥ (τ - 1) * 1 :=
      mul_le_mul_of_nonpos_left hu1 hcoef.le
    simp only [_root_.GD.N0228.N0546.d003454]
    nlinarith


theorem d003464
    {τ v : ℝ} (hτ : 0 < τ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < _root_.GD.N0228.N0546.d003456 τ v := by
  by_cases hτ1 : τ ≤ 1
  · have hcoef : 0 ≤ 1 - τ := sub_nonneg.mpr hτ1
    simp only [_root_.GD.N0228.N0546.d003456]
    nlinarith [mul_nonneg hcoef hv0]
  · have honeτ : 1 - τ < 0 := sub_neg.mpr (lt_of_not_ge hτ1)
    have hmul : (1 - τ) * v ≥ (1 - τ) * 1 :=
      mul_le_mul_of_nonpos_left hv1 honeτ.le
    simp only [_root_.GD.N0228.N0546.d003456]
    nlinarith


theorem d003465
    {τ u : ℝ} (hτ : 0 < τ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ _root_.GD.N0228.N0546.d003455 τ u := by
  exact div_nonneg (mul_nonneg hτ.le hu0)
    (_root_.GD.N0228.N0546.d003463 hτ hu0 hu1).le


theorem d003466
    {τ u : ℝ} (hτ : 0 < τ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    _root_.GD.N0228.N0546.d003455 τ u ≤ 1 := by
  have hD := _root_.GD.N0228.N0546.d003463 hτ hu0 hu1
  rw [_root_.GD.N0228.N0546.d003455, div_le_one hD]
  simp only [_root_.GD.N0228.N0546.d003454]
  nlinarith


theorem d003467
    {τ u : ℝ} (hτ : 0 < τ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0228.N0546.d003455 τ u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨_root_.GD.N0228.N0546.d003465 hτ hu.1 hu.2,
    _root_.GD.N0228.N0546.d003466 hτ hu.1 hu.2⟩


theorem d003468
    {τ v : ℝ} (hH : _root_.GD.N0228.N0546.d003456 τ v ≠ 0) :
    HasDerivAt (_root_.GD.N0228.N0546.d003457 τ)
      (τ / _root_.GD.N0228.N0546.d003456 τ v ^ 2) v := by
  have hden :
      HasDerivAt (_root_.GD.N0228.N0546.d003456 τ) (1 - τ) v := by
    have hbase :
        HasDerivAt (fun x : ℝ => τ + (1 - τ) * x) (1 - τ) v := by
      simpa only [mul_one] using
        (((hasDerivAt_id' v).const_mul (1 - τ)).const_add τ)
    have hev :
        _root_.GD.N0228.N0546.d003456 τ =ᶠ[nhds v]
          (fun x : ℝ => τ + (1 - τ) * x) := by
      filter_upwards with x
      rfl
    exact hbase.congr_of_eventuallyEq hev
  have hquot := (hasDerivAt_id' v).div hden hH
  have hscalar :
      (1 * _root_.GD.N0228.N0546.d003456 τ v - v * (1 - τ)) /
          _root_.GD.N0228.N0546.d003456 τ v ^ 2 =
        τ / _root_.GD.N0228.N0546.d003456 τ v ^ 2 := by
    congr 1
    simp only [_root_.GD.N0228.N0546.d003456]
    ring
  rw [hscalar] at hquot
  have hev :
      _root_.GD.N0228.N0546.d003457 τ =ᶠ[nhds v]
        (fun x : ℝ => x / _root_.GD.N0228.N0546.d003456 τ x) := by
    filter_upwards with x
    rfl
  exact hquot.congr_of_eventuallyEq hev



theorem d003469
    {τ : ℝ} (hτ : 0 < τ) :
    StrictMonoOn (_root_.GD.N0228.N0546.d003457 τ) (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
  · intro v hv
    exact (_root_.GD.N0228.N0546.d003468
      (ne_of_gt (_root_.GD.N0228.N0546.d003464 hτ hv.1 hv.2))).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : v ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hv
    rw [(_root_.GD.N0228.N0546.d003468
      (ne_of_gt (_root_.GD.N0228.N0546.d003464 hτ hv'.1.le hv'.2.le))).deriv]
    exact div_pos hτ (sq_pos_of_pos
      (_root_.GD.N0228.N0546.d003464 hτ hv'.1.le hv'.2.le))

end
end N0546
end N0228
end GD
