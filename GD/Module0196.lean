import Mathlib.Tactic


















namespace GD
namespace N0232
namespace N0720
namespace N1285

noncomputable section

def d002679 (N : ℝ) : ℝ := 1 / N ^ 2
def d002680 (N : ℝ) : ℝ := N ^ 11
def d002681 (N : ℝ) : ℝ := 1 - _root_.GD.N0232.N0720.N1285.d002679 N
def d002682 (N : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1285.d002680 N + _root_.GD.N0232.N0720.N1285.d002681 N) / _root_.GD.N0232.N0720.N1285.d002681 N
def d002683 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002681 N +
    _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N / 4
def d002684 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002682 N - 2 * Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N)



def d002685 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002683 N ^ 2 /
    (4 * (Real.sqrt (2 * _root_.GD.N0232.N0720.N1285.d002683 N - 1)) ^ 3)

theorem d002686 {N : ℝ} (hN : 0 < N) :
    0 < _root_.GD.N0232.N0720.N1285.d002679 N := by
  unfold _root_.GD.N0232.N0720.N1285.d002679
  positivity

theorem d002687 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002679 N ≤ 1 / 9 := by
  have hN0 : 0 < N := by linarith
  unfold _root_.GD.N0232.N0720.N1285.d002679
  apply (div_le_div_iff₀ (pow_pos hN0 2) (by norm_num : (0 : ℝ) < 9)).2
  nlinarith [sq_nonneg (N - 3)]

theorem d002688 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1285.d002681 N := by
  have he := _root_.GD.N0232.N0720.N1285.d002687 hN
  unfold _root_.GD.N0232.N0720.N1285.d002681
  linarith

theorem d002689 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002681 N ≤ 1 := by
  unfold _root_.GD.N0232.N0720.N1285.d002681
  exact sub_le_self _ (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le

theorem d002690 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1285.d002680 N := by
  unfold _root_.GD.N0232.N0720.N1285.d002680
  positivity



theorem d002691
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002680 N ≤ _root_.GD.N0232.N0720.N1285.d002682 N := by
  have hs : 0 < _root_.GD.N0232.N0720.N1285.d002681 N := _root_.GD.N0232.N0720.N1285.d002688 hN
  have hs1 : _root_.GD.N0232.N0720.N1285.d002681 N ≤ 1 := _root_.GD.N0232.N0720.N1285.d002689 hN
  have hM : 0 < _root_.GD.N0232.N0720.N1285.d002680 N := _root_.GD.N0232.N0720.N1285.d002690 hN
  unfold _root_.GD.N0232.N0720.N1285.d002682
  apply (le_div_iff₀ hs).2
  nlinarith [mul_le_mul_of_nonneg_left hs1 hM.le]

theorem d002692
    {N : ℝ} (hN : 3 ≤ N) :
    4 ≤ _root_.GD.N0232.N0720.N1285.d002682 N := by
  have hcM := _root_.GD.N0232.N0720.N1285.d002691 hN
  have hpow : (3 : ℝ) ^ 11 ≤ N ^ 11 :=
    pow_le_pow_left₀ (by norm_num) hN 11
  unfold _root_.GD.N0232.N0720.N1285.d002680 at hcM
  norm_num at hpow
  linarith



theorem d002693
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002683 N ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / 9 := by
  have hs1 : _root_.GD.N0232.N0720.N1285.d002681 N ≤ 1 := _root_.GD.N0232.N0720.N1285.d002689 hN
  have he9 : _root_.GD.N0232.N0720.N1285.d002679 N ≤ 1 / 9 := _root_.GD.N0232.N0720.N1285.d002687 hN
  have hc4 : 4 ≤ _root_.GD.N0232.N0720.N1285.d002682 N :=
    _root_.GD.N0232.N0720.N1285.d002692 hN
  have hc0 : 0 ≤ _root_.GD.N0232.N0720.N1285.d002682 N := by linarith
  have hcSq : 12 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 := by
    nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1285.d002682 N - 4)]
  unfold _root_.GD.N0232.N0720.N1285.d002683
  have hterm :
      _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N / 4 ≤
        _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / 36 := by
    nlinarith [mul_le_mul_of_nonneg_left he9 (sq_nonneg
      (_root_.GD.N0232.N0720.N1285.d002682 N))]
  nlinarith


theorem d002694
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002682 N / 3 ≤ _root_.GD.N0232.N0720.N1285.d002684 N := by
  have hB := _root_.GD.N0232.N0720.N1285.d002693 hN
  have hB0 : 0 ≤ _root_.GD.N0232.N0720.N1285.d002683 N := by
    unfold _root_.GD.N0232.N0720.N1285.d002683
    exact add_nonneg (_root_.GD.N0232.N0720.N1285.d002688 hN).le
      (div_nonneg
        (mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le)
        (by norm_num))
  have hc0 : 0 ≤ _root_.GD.N0232.N0720.N1285.d002682 N / 3 := by
    have := _root_.GD.N0232.N0720.N1285.d002692 hN
    positivity
  have hsquare :
      (Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N)) ^ 2 ≤
        (_root_.GD.N0232.N0720.N1285.d002682 N / 3) ^ 2 := by
    rw [Real.sq_sqrt hB0]
    nlinarith
  have hsqrt :
      Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N) ≤
        _root_.GD.N0232.N0720.N1285.d002682 N / 3 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hc0).mp hsquare
  unfold _root_.GD.N0232.N0720.N1285.d002684
  linarith



theorem d002695
    {N : ℝ} (hN : 3 ≤ N) :
    1 ≤ _root_.GD.N0232.N0720.N1285.d002683 N := by
  have hs : 0 < _root_.GD.N0232.N0720.N1285.d002681 N := _root_.GD.N0232.N0720.N1285.d002688 hN
  have hcM := _root_.GD.N0232.N0720.N1285.d002691 hN
  have hM : 0 < _root_.GD.N0232.N0720.N1285.d002680 N := _root_.GD.N0232.N0720.N1285.d002690 hN
  have he : 0 < _root_.GD.N0232.N0720.N1285.d002679 N := _root_.GD.N0232.N0720.N1285.d002686 (by linarith)
  have hMeq : _root_.GD.N0232.N0720.N1285.d002680 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N = N ^ 20 := by
    unfold _root_.GD.N0232.N0720.N1285.d002680 _root_.GD.N0232.N0720.N1285.d002679
    have hN0 : N ≠ 0 := (by linarith : 0 < N).ne'
    field_simp [hN0]
  have hNpow : 9 ≤ N ^ 20 := by
    have hN2 : (3 : ℝ) ^ 2 ≤ N ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hN 2
    have hgrow : N ^ 2 ≤ N ^ 20 :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) (by norm_num)
    norm_num at hN2
    linarith
  have hce : 9 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N := by
    have hcSq : _root_.GD.N0232.N0720.N1285.d002680 N ^ 2 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 :=
      pow_le_pow_left₀ hM.le hcM 2
    have hmul := mul_le_mul_of_nonneg_right hcSq he.le
    rw [hMeq] at hmul
    linarith
  unfold _root_.GD.N0232.N0720.N1285.d002683
  nlinarith


theorem d002696
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002683 N ≤
      _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / N ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hs1 : _root_.GD.N0232.N0720.N1285.d002681 N ≤ 1 := _root_.GD.N0232.N0720.N1285.d002689 hN
  have hM : 0 < _root_.GD.N0232.N0720.N1285.d002680 N := _root_.GD.N0232.N0720.N1285.d002690 hN
  have hcM := _root_.GD.N0232.N0720.N1285.d002691 hN
  have he : _root_.GD.N0232.N0720.N1285.d002679 N = 1 / N ^ 2 := rfl
  have hMeq : _root_.GD.N0232.N0720.N1285.d002680 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N = N ^ 20 := by
    unfold _root_.GD.N0232.N0720.N1285.d002680 _root_.GD.N0232.N0720.N1285.d002679
    field_simp [hN0.ne']
  have hNpow : 2 ≤ N ^ 20 := by
    have hgrow : N ^ 2 ≤ N ^ 20 :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) (by norm_num)
    nlinarith [sq_nonneg (N - 3)]
  have hce : 2 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N := by
    have hcSq : _root_.GD.N0232.N0720.N1285.d002680 N ^ 2 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 :=
      pow_le_pow_left₀ hM.le hcM 2
    have hmul := mul_le_mul_of_nonneg_right hcSq
      (_root_.GD.N0232.N0720.N1285.d002686 hN0).le
    rw [hMeq] at hmul
    linarith
  unfold _root_.GD.N0232.N0720.N1285.d002683
  rw [he]
  have htarget :
      _root_.GD.N0232.N0720.N1285.d002681 N ≤
        3 * (_root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / N ^ 2) / 4 := by
    have : 2 ≤ _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / N ^ 2 := by
      simpa [_root_.GD.N0232.N0720.N1285.d002679, div_eq_mul_inv] using hce
    nlinarith
  have hreorder :
      _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * (1 / N ^ 2) =
        _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / N ^ 2 := by ring
  rw [hreorder]
  linarith



theorem d002697
    {B : ℝ} (hB : 1 ≤ B) :
    B ^ 2 / (4 * (Real.sqrt (2 * B - 1)) ^ 3) ≤ Real.sqrt B / 4 := by
  have hB0 : 0 ≤ B := by linarith
  have htwo : 0 < 2 * B - 1 := by linarith
  have hsqrtB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hsqrtBig : 0 < Real.sqrt (2 * B - 1) := Real.sqrt_pos.2 htwo
  have hroot : Real.sqrt B ≤ Real.sqrt (2 * B - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcubes : (Real.sqrt B) ^ 3 ≤
      (Real.sqrt (2 * B - 1)) ^ 3 :=
    pow_le_pow_left₀ hsqrtB hroot 3
  have hBsq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
  have hnum : B ^ 2 ≤
      Real.sqrt B * (Real.sqrt (2 * B - 1)) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hcubes hsqrtB
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 4 *
    (Real.sqrt (2 * B - 1)) ^ 3)).2
  nlinarith


theorem d002698
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002685 N ≤
      _root_.GD.N0232.N0720.N1285.d002682 N / (4 * N) := by
  have hN0 : 0 < N := by linarith
  have hB1 : 1 ≤ _root_.GD.N0232.N0720.N1285.d002683 N := _root_.GD.N0232.N0720.N1285.d002695 hN
  have hmoment := _root_.GD.N0232.N0720.N1285.d002697 hB1
  have hBscale := _root_.GD.N0232.N0720.N1285.d002696 hN
  have hc : 0 ≤ _root_.GD.N0232.N0720.N1285.d002682 N / N := by
    positivity [_root_.GD.N0232.N0720.N1285.d002692 hN]
  have hsquare :
      (Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N)) ^ 2 ≤
        (_root_.GD.N0232.N0720.N1285.d002682 N / N) ^ 2 := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ _root_.GD.N0232.N0720.N1285.d002683 N)]
    simpa [div_pow] using hBscale
  have hsqrt : Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N) ≤
      _root_.GD.N0232.N0720.N1285.d002682 N / N :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hc).mp hsquare
  unfold _root_.GD.N0232.N0720.N1285.d002685
  calc
    _root_.GD.N0232.N0720.N1285.d002683 N ^ 2 /
        (4 * Real.sqrt (2 * _root_.GD.N0232.N0720.N1285.d002683 N - 1) ^ 3) ≤
      Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N) / 4 := hmoment
    _ ≤ (_root_.GD.N0232.N0720.N1285.d002682 N / N) / 4 := by linarith
    _ = _root_.GD.N0232.N0720.N1285.d002682 N / (4 * N) := by ring



theorem d002699
    {N : ℝ} (hN : 3 ≤ N) :
    1 / (4 * _root_.GD.N0232.N0720.N1285.d002683 N) ≤
      1 / (_root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N) := by
  have hB : 0 < _root_.GD.N0232.N0720.N1285.d002683 N :=
    lt_of_lt_of_le zero_lt_one (_root_.GD.N0232.N0720.N1285.d002695 hN)
  have hc : 0 < _root_.GD.N0232.N0720.N1285.d002682 N := by
    linarith [_root_.GD.N0232.N0720.N1285.d002692 hN]
  have he : 0 < _root_.GD.N0232.N0720.N1285.d002679 N := _root_.GD.N0232.N0720.N1285.d002686 (by linarith)
  have hlower : _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N ≤
      4 * _root_.GD.N0232.N0720.N1285.d002683 N := by
    unfold _root_.GD.N0232.N0720.N1285.d002683
    nlinarith [_root_.GD.N0232.N0720.N1285.d002688 hN]
  exact one_div_le_one_div_of_le (by positivity) hlower


theorem d002700
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1285.d002680 N ≤ _root_.GD.N0232.N0720.N1285.d002682 N ∧
    _root_.GD.N0232.N0720.N1285.d002682 N / 3 ≤ _root_.GD.N0232.N0720.N1285.d002684 N ∧
    _root_.GD.N0232.N0720.N1285.d002685 N ≤
      _root_.GD.N0232.N0720.N1285.d002682 N / (4 * N) ∧
    1 / (4 * _root_.GD.N0232.N0720.N1285.d002683 N) ≤
      1 / (_root_.GD.N0232.N0720.N1285.d002682 N ^ 2 * _root_.GD.N0232.N0720.N1285.d002679 N) := by
  exact ⟨_root_.GD.N0232.N0720.N1285.d002691 hN,
    _root_.GD.N0232.N0720.N1285.d002694 hN,
    _root_.GD.N0232.N0720.N1285.d002698 hN,
    _root_.GD.N0232.N0720.N1285.d002699 hN⟩

end

end N1285
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1285.d002700
