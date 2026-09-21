import GD.Module0269












open MeasureTheory

namespace GD.N0232.N0720.N1279

noncomputable section

open _root_.GD.N0232.N0720.N1277
open _root_.GD.N0232.N0720.N1280
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1284
open _root_.GD.N0232.N0720.N1285

def d003958 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002681 N * _root_.GD.N0232.N0720.N1280.d003878

def d003959 (N : ℝ) : ℝ :=
  (1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N) * _root_.GD.N0232.N0720.N1280.d003878

def d003960 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002679 N * _root_.GD.N0232.N0720.N1280.d003878

def d003961 (N : ℝ) : ℝ :=
  2 * _root_.GD.N0232.N0720.N1285.d002679 N * _root_.GD.N0232.N0720.N1280.d003878

def d003962 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003879 N - _root_.GD.N0232.N0720.N1279.d003958 N

def d003963 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003879 N - _root_.GD.N0232.N0720.N1279.d003959 N



def d003964 (N μ : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002682 N *
      _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003962 N) μ -
    2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003960 N) μ


def d003965 (N μ : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003936 N *
      _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003963 N) μ +
    _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003961 N) μ

theorem d003966 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003958 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003958
  exact mul_pos (_root_.GD.N0232.N0720.N1285.d002688 hN) _root_.GD.N0232.N0720.N1280.d003890

theorem d003967 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003959 N := by
  have he := _root_.GD.N0232.N0720.N1285.d002687 hN
  have hs : 0 < 1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N := by linarith
  unfold _root_.GD.N0232.N0720.N1279.d003959
  exact mul_pos hs _root_.GD.N0232.N0720.N1280.d003890

theorem d003968 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003960 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003960
  exact mul_pos (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)) _root_.GD.N0232.N0720.N1280.d003890

theorem d003969 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003961 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003961
  positivity [_root_.GD.N0232.N0720.N1285.d002686 (by linarith : 0 < N), _root_.GD.N0232.N0720.N1280.d003890]




theorem d003970 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003962 N =
      (_root_.GD.N0232.N0720.N1285.d002682 N / 2) ^ 2 *
        _root_.GD.N0232.N0720.N1279.d003960 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003962 _root_.GD.N0232.N0720.N1279.d003958
    _root_.GD.N0232.N0720.N1279.d003960 _root_.GD.N0232.N0720.N1280.d003879 _root_.GD.N0232.N0720.N1285.d002683
    _root_.GD.N0232.N0720.N1285.d002681 _root_.GD.N0232.N0720.N1280.d003878
  ring

theorem d003971 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003962 N := by
  rw [_root_.GD.N0232.N0720.N1279.d003970]
  have hc : 0 < _root_.GD.N0232.N0720.N1285.d002682 N / 2 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002692 hN]
  positivity [_root_.GD.N0232.N0720.N1279.d003968 hN]



theorem d003972 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003963 N =
      _root_.GD.N0232.N0720.N1279.d003962 N + _root_.GD.N0232.N0720.N1279.d003960 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003963 _root_.GD.N0232.N0720.N1279.d003962
    _root_.GD.N0232.N0720.N1279.d003959 _root_.GD.N0232.N0720.N1279.d003958 _root_.GD.N0232.N0720.N1279.d003960
    _root_.GD.N0232.N0720.N1285.d002681 _root_.GD.N0232.N0720.N1280.d003878
  ring

theorem d003973 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1279.d003963 N := by
  rw [_root_.GD.N0232.N0720.N1279.d003972]
  positivity [_root_.GD.N0232.N0720.N1279.d003971 hN,
    _root_.GD.N0232.N0720.N1279.d003968 hN]

theorem d003974 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003962 N + _root_.GD.N0232.N0720.N1279.d003958 N = _root_.GD.N0232.N0720.N1280.d003879 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003962
  ring

theorem d003975 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003960 N + _root_.GD.N0232.N0720.N1279.d003958 N = _root_.GD.N0232.N0720.N1280.d003878 := by
  unfold _root_.GD.N0232.N0720.N1279.d003960 _root_.GD.N0232.N0720.N1279.d003958 _root_.GD.N0232.N0720.N1285.d002681
  ring

theorem d003976 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003963 N + _root_.GD.N0232.N0720.N1279.d003959 N = _root_.GD.N0232.N0720.N1280.d003879 N := by
  unfold _root_.GD.N0232.N0720.N1279.d003963
  ring

theorem d003977 {N : ℝ} :
    _root_.GD.N0232.N0720.N1279.d003961 N + _root_.GD.N0232.N0720.N1279.d003959 N = _root_.GD.N0232.N0720.N1280.d003878 := by
  unfold _root_.GD.N0232.N0720.N1279.d003961 _root_.GD.N0232.N0720.N1279.d003959 _root_.GD.N0232.N0720.N1280.d003878
  ring


theorem d003978 {N : ℝ} (hN : 3 ≤ N) (μ : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1279.d003964 N μ := by
  unfold _root_.GD.N0232.N0720.N1279.d003964
  rw [_root_.GD.N0232.N0720.N1279.d003970]
  let c := _root_.GD.N0232.N0720.N1285.d002682 N
  let w := _root_.GD.N0232.N0720.N1279.d003960 N
  have hc4 : 4 ≤ c := _root_.GD.N0232.N0720.N1285.d002692 hN
  have hc0 : 0 ≤ c := by linarith
  have hc2 : 0 < c / 2 := by linarith
  have hw : 0 < w := _root_.GD.N0232.N0720.N1279.d003968 hN
  have hscale : 1 ≤ (c / 2) ^ 2 := by
    nlinarith [sq_nonneg (c / 2 - 1)]
  have hWU : w ≤ (c / 2) ^ 2 * w := by
    nlinarith [mul_le_mul_of_nonneg_right hscale hw.le]
  have hsqrt :
      Real.sqrt ((c / 2) ^ 2 * w) =
        (c / 2) * Real.sqrt w := by
    rw [Real.sqrt_mul (sq_nonneg (c / 2)), Real.sqrt_sq_eq_abs,
      abs_of_pos hc2]
  have hpeak :
      2 * Real.sqrt ((c / 2) ^ 2 * w) ≤ c * Real.sqrt w := by
    rw [hsqrt]
    ring_nf
    exact le_rfl
  exact _root_.GD.N0232.N0720.N1277.d002661
    hw hWU hc0 hpeak


theorem d003979 {N : ℝ} (hN : 3 ≤ N) (μ : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1279.d003965 N μ := by
  unfold _root_.GD.N0232.N0720.N1279.d003965
  exact add_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1280.d003943 hN)
      (_root_.GD.N0232.N0720.N1277.d002624 (_root_.GD.N0232.N0720.N1279.d003973 hN)).le)
    (_root_.GD.N0232.N0720.N1277.d002624 (_root_.GD.N0232.N0720.N1279.d003969 hN)).le

theorem d003980 {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1279.d003964 N) := by
  unfold _root_.GD.N0232.N0720.N1279.d003964
  exact
    (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003962 N)).const_mul
        (_root_.GD.N0232.N0720.N1285.d002682 N) |>.sub
      ((_root_.GD.N0232.N0720.N1277.d002625
        (_root_.GD.N0232.N0720.N1279.d003960 N)).const_mul 2)

theorem d003981 {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1279.d003965 N) := by
  unfold _root_.GD.N0232.N0720.N1279.d003965
  exact
    (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003963 N)).const_mul
        (_root_.GD.N0232.N0720.N1280.d003936 N) |>.add
      (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003961 N))


theorem d003982 {N : ℝ} (hN : 3 ≤ N) :
    ∫ μ : ℝ, _root_.GD.N0232.N0720.N1279.d003964 N μ =
      _root_.GD.N0232.N0720.N1285.d002682 N - 2 := by
  unfold _root_.GD.N0232.N0720.N1279.d003964
  rw [integral_sub,
    integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002626 (_root_.GD.N0232.N0720.N1279.d003971 hN),
    _root_.GD.N0232.N0720.N1277.d002626 (_root_.GD.N0232.N0720.N1279.d003968 hN)]
  · ring
  · exact
      (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003962 N)).const_mul _
  · exact
      (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003960 N)).const_mul _


theorem d003983 {N : ℝ} (hN : 3 ≤ N) :
    ∫ μ : ℝ, _root_.GD.N0232.N0720.N1279.d003965 N μ =
      _root_.GD.N0232.N0720.N1280.d003936 N + 1 := by
  unfold _root_.GD.N0232.N0720.N1279.d003965
  rw [integral_add,
    integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002626 (_root_.GD.N0232.N0720.N1279.d003973 hN),
    _root_.GD.N0232.N0720.N1277.d002626 (_root_.GD.N0232.N0720.N1279.d003969 hN)]
  · ring
  · exact
      (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1279.d003963 N)).const_mul _
  · exact _root_.GD.N0232.N0720.N1277.d002625 _



theorem d003984 {N x : ℝ} (hN : 3 ≤ N) :
    (∫ μ : ℝ, _root_.GD.N0232.N0720.N1279.d003964 N μ *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - μ)) =
      _root_.GD.N0232.N0720.N1280.d003937 N x := by
  unfold _root_.GD.N0232.N0720.N1279.d003964 _root_.GD.N0232.N0720.N1280.d003937 _root_.GD.N0232.N0720.N1280.d003887
    _root_.GD.N0232.N0720.N1280.d003886
  exact _root_.GD.N0232.N0720.N1277.d002643
    (_root_.GD.N0232.N0720.N1279.d003971 hN)
    (_root_.GD.N0232.N0720.N1279.d003968 hN)
    (_root_.GD.N0232.N0720.N1279.d003966 hN)
    _root_.GD.N0232.N0720.N1279.d003974 _root_.GD.N0232.N0720.N1279.d003975



theorem d003985 {N x : ℝ} (hN : 3 ≤ N) :
    (∫ μ : ℝ, _root_.GD.N0232.N0720.N1279.d003965 N μ *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - μ)) =
      _root_.GD.N0232.N0720.N1280.d003938 N x := by
  have h := _root_.GD.N0232.N0720.N1277.d002643
    (x := x)
    (U := _root_.GD.N0232.N0720.N1279.d003963 N)
    (w := _root_.GD.N0232.N0720.N1279.d003961 N)
    (v := _root_.GD.N0232.N0720.N1279.d003959 N)
    (V := _root_.GD.N0232.N0720.N1280.d003879 N) (v₀ := _root_.GD.N0232.N0720.N1280.d003878)
    (c := _root_.GD.N0232.N0720.N1280.d003936 N) (d := (-1 : ℝ))
    (_root_.GD.N0232.N0720.N1279.d003973 hN)
    (_root_.GD.N0232.N0720.N1279.d003969 hN)
    (_root_.GD.N0232.N0720.N1279.d003967 hN)
    _root_.GD.N0232.N0720.N1279.d003976 _root_.GD.N0232.N0720.N1279.d003977
  simpa [_root_.GD.N0232.N0720.N1279.d003965, _root_.GD.N0232.N0720.N1280.d003938, _root_.GD.N0232.N0720.N1280.d003887,
    _root_.GD.N0232.N0720.N1280.d003886] using h


theorem d003986 {N x : ℝ} (hN : 3 ≤ N) :
    (∫ μ : ℝ, μ * (_root_.GD.N0232.N0720.N1279.d003964 N μ *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - μ))) =
      _root_.GD.N0232.N0720.N1285.d002682 N *
          (_root_.GD.N0232.N0720.N1279.d003962 N / _root_.GD.N0232.N0720.N1280.d003879 N * x) *
            _root_.GD.N0232.N0720.N1280.d003887 N x -
        2 * (_root_.GD.N0232.N0720.N1279.d003960 N / _root_.GD.N0232.N0720.N1280.d003878 * x) *
          _root_.GD.N0232.N0720.N1280.d003886 x := by
  unfold _root_.GD.N0232.N0720.N1279.d003964 _root_.GD.N0232.N0720.N1280.d003887 _root_.GD.N0232.N0720.N1280.d003886
  exact _root_.GD.N0232.N0720.N1277.d002644
    (_root_.GD.N0232.N0720.N1279.d003971 hN)
    (_root_.GD.N0232.N0720.N1279.d003968 hN)
    (_root_.GD.N0232.N0720.N1279.d003966 hN)
    _root_.GD.N0232.N0720.N1279.d003974 _root_.GD.N0232.N0720.N1279.d003975


theorem d003987 {N x : ℝ} (hN : 3 ≤ N) :
    (∫ μ : ℝ, μ * (_root_.GD.N0232.N0720.N1279.d003965 N μ *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - μ))) =
      _root_.GD.N0232.N0720.N1280.d003936 N *
          (_root_.GD.N0232.N0720.N1279.d003963 N / _root_.GD.N0232.N0720.N1280.d003879 N * x) *
            _root_.GD.N0232.N0720.N1280.d003887 N x +
        _root_.GD.N0232.N0720.N1279.d003961 N / _root_.GD.N0232.N0720.N1280.d003878 * x *
          _root_.GD.N0232.N0720.N1280.d003886 x := by
  have h := _root_.GD.N0232.N0720.N1277.d002644
    (x := x)
    (U := _root_.GD.N0232.N0720.N1279.d003963 N)
    (w := _root_.GD.N0232.N0720.N1279.d003961 N)
    (v := _root_.GD.N0232.N0720.N1279.d003959 N)
    (V := _root_.GD.N0232.N0720.N1280.d003879 N) (v₀ := _root_.GD.N0232.N0720.N1280.d003878)
    (c := _root_.GD.N0232.N0720.N1280.d003936 N) (d := (-1 : ℝ))
    (_root_.GD.N0232.N0720.N1279.d003973 hN)
    (_root_.GD.N0232.N0720.N1279.d003969 hN)
    (_root_.GD.N0232.N0720.N1279.d003967 hN)
    _root_.GD.N0232.N0720.N1279.d003976 _root_.GD.N0232.N0720.N1279.d003977
  simpa [_root_.GD.N0232.N0720.N1279.d003965, _root_.GD.N0232.N0720.N1280.d003887,
    _root_.GD.N0232.N0720.N1280.d003886] using h

#print axioms _root_.GD.N0232.N0720.N1279.d003978
#print axioms _root_.GD.N0232.N0720.N1279.d003979
#print axioms _root_.GD.N0232.N0720.N1279.d003982
#print axioms _root_.GD.N0232.N0720.N1279.d003983
#print axioms _root_.GD.N0232.N0720.N1279.d003984
#print axioms _root_.GD.N0232.N0720.N1279.d003985
#print axioms _root_.GD.N0232.N0720.N1279.d003986
#print axioms _root_.GD.N0232.N0720.N1279.d003987

end

end GD.N0232.N0720.N1279

