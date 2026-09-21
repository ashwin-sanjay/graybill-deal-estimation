import GD.Module0269
import GD.Module1050
import GD.Module1010
import Mathlib.Tactic















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1364

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1277
open _root_.GD.N0232.N0720.N1280
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1281

noncomputable local instance d016788 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016789 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩

def d016790 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1285.d002679 N
def d016791 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1285.d002680 N
def d016792 (N : ℝ) : ℝ := 1 - _root_.GD.N0232.N0720.N1364.d016790 N
def d016793 (N : ℝ) : ℝ := 1 - 2 * _root_.GD.N0232.N0720.N1364.d016790 N
def d016794 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1285.d002682 N
def d016795 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1280.d003936 N

def d016796 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003878
def d016797 (N : ℝ) : ℝ := 2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003878
def d016798 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1364.d016792 N * _root_.GD.N0232.N0720.N1280.d003878
def d016799 (N : ℝ) : ℝ := _root_.GD.N0232.N0720.N1364.d016793 N * _root_.GD.N0232.N0720.N1280.d003878
def d016800 (N : ℝ) : ℝ := (_root_.GD.N0232.N0720.N1364.d016794 N / 2) ^ 2 * _root_.GD.N0232.N0720.N1364.d016796 N
def d016801 (N : ℝ) : ℝ := (1 + (_root_.GD.N0232.N0720.N1364.d016794 N / 2) ^ 2) * _root_.GD.N0232.N0720.N1364.d016796 N


def d016802 (N x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1364.d016794 N * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016800 N) x -
    2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016796 N) x


def d016803 (N x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1364.d016795 N * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016801 N) x +
    _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016797 N) x

theorem d016804
    {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1364.d016790 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016792 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016793 N ∧
      4 ≤ _root_.GD.N0232.N0720.N1364.d016794 N ∧ 0 ≤ _root_.GD.N0232.N0720.N1364.d016795 N := by
  have he := _root_.GD.N0232.N0720.N1285.d002686 (show 0 < N by linarith)
  have he9 := _root_.GD.N0232.N0720.N1285.d002687 hN
  constructor
  · exact he
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016792 _root_.GD.N0232.N0720.N1364.d016790
    linarith
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016793 _root_.GD.N0232.N0720.N1364.d016790
    linarith
  constructor
  · exact _root_.GD.N0232.N0720.N1285.d002692 hN
  · exact _root_.GD.N0232.N0720.N1280.d003943 hN

theorem d016805
    {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1364.d016796 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016797 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016798 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016799 N ∧
      0 < _root_.GD.N0232.N0720.N1364.d016800 N ∧ 0 < _root_.GD.N0232.N0720.N1364.d016801 N := by
  rcases _root_.GD.N0232.N0720.N1364.d016804 hN with ⟨he, hs1, hs2, hc1, hc2⟩
  have hv0 : 0 < _root_.GD.N0232.N0720.N1280.d003878 := _root_.GD.N0232.N0720.N1280.d003890
  have hw1 : 0 < _root_.GD.N0232.N0720.N1364.d016796 N := by unfold _root_.GD.N0232.N0720.N1364.d016796; positivity
  constructor
  · exact hw1
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016797
    positivity
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016798
    positivity
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016799
    positivity
  constructor
  · unfold _root_.GD.N0232.N0720.N1364.d016800
    positivity
  · unfold _root_.GD.N0232.N0720.N1364.d016801
    positivity

theorem d016806 (N : ℝ) : _root_.GD.N0232.N0720.N1364.d016800 N + _root_.GD.N0232.N0720.N1364.d016798 N = _root_.GD.N0232.N0720.N1280.d003879 N := by
  unfold _root_.GD.N0232.N0720.N1364.d016800 _root_.GD.N0232.N0720.N1364.d016796 _root_.GD.N0232.N0720.N1364.d016798 _root_.GD.N0232.N0720.N1364.d016794 _root_.GD.N0232.N0720.N1364.d016792 _root_.GD.N0232.N0720.N1364.d016790 _root_.GD.N0232.N0720.N1280.d003879 _root_.GD.N0232.N0720.N1280.d003878
    _root_.GD.N0232.N0720.N1285.d002683 _root_.GD.N0232.N0720.N1285.d002681
  ring

theorem d016807 (N : ℝ) : _root_.GD.N0232.N0720.N1364.d016796 N + _root_.GD.N0232.N0720.N1364.d016798 N = _root_.GD.N0232.N0720.N1280.d003878 := by
  unfold _root_.GD.N0232.N0720.N1364.d016796 _root_.GD.N0232.N0720.N1364.d016798 _root_.GD.N0232.N0720.N1364.d016792 _root_.GD.N0232.N0720.N1364.d016790
  ring

theorem d016808 (N : ℝ) : _root_.GD.N0232.N0720.N1364.d016801 N + _root_.GD.N0232.N0720.N1364.d016799 N = _root_.GD.N0232.N0720.N1280.d003879 N := by
  unfold _root_.GD.N0232.N0720.N1364.d016801 _root_.GD.N0232.N0720.N1364.d016796 _root_.GD.N0232.N0720.N1364.d016799 _root_.GD.N0232.N0720.N1364.d016794 _root_.GD.N0232.N0720.N1364.d016793 _root_.GD.N0232.N0720.N1364.d016790 _root_.GD.N0232.N0720.N1280.d003879 _root_.GD.N0232.N0720.N1280.d003878
    _root_.GD.N0232.N0720.N1285.d002683 _root_.GD.N0232.N0720.N1285.d002681
  ring

theorem d016809 (N : ℝ) : _root_.GD.N0232.N0720.N1364.d016797 N + _root_.GD.N0232.N0720.N1364.d016799 N = _root_.GD.N0232.N0720.N1280.d003878 := by
  unfold _root_.GD.N0232.N0720.N1364.d016797 _root_.GD.N0232.N0720.N1364.d016799 _root_.GD.N0232.N0720.N1364.d016793 _root_.GD.N0232.N0720.N1364.d016790
  ring

theorem d016810
    {N : ℝ} (hN : 3 ≤ N) :
    Real.sqrt (_root_.GD.N0232.N0720.N1364.d016800 N) = (_root_.GD.N0232.N0720.N1364.d016794 N / 2) * Real.sqrt (_root_.GD.N0232.N0720.N1364.d016796 N) := by
  have hw1 := (_root_.GD.N0232.N0720.N1364.d016805 hN).1
  have hc : 0 < _root_.GD.N0232.N0720.N1364.d016794 N / 2 := by
    rcases _root_.GD.N0232.N0720.N1364.d016804 hN with ⟨_, _, _, hc1, _⟩
    linarith
  unfold _root_.GD.N0232.N0720.N1364.d016800
  rw [Real.sqrt_mul (sq_nonneg (_root_.GD.N0232.N0720.N1364.d016794 N / 2)),
    Real.sqrt_sq_eq_abs, abs_of_pos hc]


theorem d016811
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1364.d016802 N x := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨hw1, _, _, _, hU1, _⟩
  rcases _root_.GD.N0232.N0720.N1364.d016804 hN with ⟨_, _, _, hc1, _⟩
  have hWU : _root_.GD.N0232.N0720.N1364.d016796 N ≤ _root_.GD.N0232.N0720.N1364.d016800 N := by
    unfold _root_.GD.N0232.N0720.N1364.d016800
    have hsquare : 1 ≤ (_root_.GD.N0232.N0720.N1364.d016794 N / 2) ^ 2 := by
      nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1364.d016794 N / 2 - 1)]
    nlinarith [mul_le_mul_of_nonneg_right hsquare hw1.le]
  have hpeak : 2 * Real.sqrt (_root_.GD.N0232.N0720.N1364.d016800 N) ≤
      _root_.GD.N0232.N0720.N1364.d016794 N * Real.sqrt (_root_.GD.N0232.N0720.N1364.d016796 N) := by
    rw [_root_.GD.N0232.N0720.N1364.d016810 hN]
    ring_nf
    exact le_rfl
  unfold _root_.GD.N0232.N0720.N1364.d016802
  exact _root_.GD.N0232.N0720.N1277.d002661
    hw1 hWU (by linarith) hpeak

theorem d016812
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1364.d016803 N x := by
  rcases _root_.GD.N0232.N0720.N1364.d016804 hN with ⟨_, _, _, _, hc2⟩
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨_, hw2, _, _, _, hU2⟩
  unfold _root_.GD.N0232.N0720.N1364.d016803
  exact add_nonneg
    (mul_nonneg hc2 (by
      exact (_root_.GD.N0232.N0720.N1277.d002624 (v := _root_.GD.N0232.N0720.N1364.d016801 N) (x := x) hU2).le))
    ((_root_.GD.N0232.N0720.N1277.d002624 (v := _root_.GD.N0232.N0720.N1364.d016797 N) (x := x) hw2).le)

theorem d016813 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1364.d016802 N) := by
  unfold _root_.GD.N0232.N0720.N1364.d016802 _root_.GD.N0232.N0720.N1277.d002621
  fun_prop

theorem d016814 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1364.d016803 N) := by
  unfold _root_.GD.N0232.N0720.N1364.d016803 _root_.GD.N0232.N0720.N1277.d002621
  fun_prop

theorem d016815
    {N : ℝ} (hN : 3 ≤ N) : Integrable (_root_.GD.N0232.N0720.N1364.d016802 N) := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨hw1, _, _, _, hU1, _⟩
  unfold _root_.GD.N0232.N0720.N1364.d016802
  exact ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016800 N)).const_mul (_root_.GD.N0232.N0720.N1364.d016794 N)).sub
    ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016796 N)).const_mul 2)

theorem d016816
    {N : ℝ} (_hN : 3 ≤ N) : Integrable (_root_.GD.N0232.N0720.N1364.d016803 N) := by
  unfold _root_.GD.N0232.N0720.N1364.d016803
  exact ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016801 N)).const_mul (_root_.GD.N0232.N0720.N1364.d016795 N)).add
    (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016797 N))

theorem d016817
    {N : ℝ} (hN : 3 ≤ N) :
    ∫ x, _root_.GD.N0232.N0720.N1364.d016802 N x = _root_.GD.N0232.N0720.N1364.d016794 N - 2 := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨hw1, _, _, _, hU1, _⟩
  unfold _root_.GD.N0232.N0720.N1364.d016802
  rw [integral_sub
      ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016800 N)).const_mul (_root_.GD.N0232.N0720.N1364.d016794 N))
      ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016796 N)).const_mul 2),
    integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002626 hU1,
    _root_.GD.N0232.N0720.N1277.d002626 hw1]
  ring

theorem d016818
    {N : ℝ} (hN : 3 ≤ N) :
    ∫ x, _root_.GD.N0232.N0720.N1364.d016803 N x = _root_.GD.N0232.N0720.N1364.d016795 N + 1 := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨_, hw2, _, _, _, hU2⟩
  unfold _root_.GD.N0232.N0720.N1364.d016803
  rw [integral_add
      ((_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016801 N)).const_mul (_root_.GD.N0232.N0720.N1364.d016795 N))
      (_root_.GD.N0232.N0720.N1277.d002625 (_root_.GD.N0232.N0720.N1364.d016797 N)),
    integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002626 hU2,
    _root_.GD.N0232.N0720.N1277.d002626 hw2]
  ring


theorem d016819
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    ∫ mu, _root_.GD.N0232.N0720.N1364.d016802 N mu * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016798 N) (x - mu) =
      _root_.GD.N0232.N0720.N1280.d003937 N x := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨hw1, _, hv1, _, hU1, _⟩
  unfold _root_.GD.N0232.N0720.N1364.d016802 _root_.GD.N0232.N0720.N1280.d003937
  simpa [_root_.GD.N0232.N0720.N1364.d016794, _root_.GD.N0232.N0720.N1280.d003887, _root_.GD.N0232.N0720.N1280.d003886] using
    _root_.GD.N0232.N0720.N1277.d002643
      hU1 hw1 hv1 (_root_.GD.N0232.N0720.N1364.d016806 N) (_root_.GD.N0232.N0720.N1364.d016807 N)
      (c := _root_.GD.N0232.N0720.N1364.d016794 N) (d := 2) (x := x)


theorem d016820
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    ∫ mu, _root_.GD.N0232.N0720.N1364.d016803 N mu * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016799 N) (x - mu) =
      _root_.GD.N0232.N0720.N1280.d003938 N x := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨_, hw2, _, hv2, _, hU2⟩
  unfold _root_.GD.N0232.N0720.N1364.d016803 _root_.GD.N0232.N0720.N1280.d003938
  simpa [_root_.GD.N0232.N0720.N1364.d016795, _root_.GD.N0232.N0720.N1280.d003887, _root_.GD.N0232.N0720.N1280.d003886] using
    _root_.GD.N0232.N0720.N1277.d002643
      hU2 hw2 hv2 (_root_.GD.N0232.N0720.N1364.d016808 N) (_root_.GD.N0232.N0720.N1364.d016809 N)
      (c := _root_.GD.N0232.N0720.N1364.d016795 N) (d := -1) (x := x)



theorem d016821
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1280.d003939 N z =
      _root_.GD.N0232.N0720.N1280.d003886 z.1 +
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 *
          (∫ mu, _root_.GD.N0232.N0720.N1364.d016802 N mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016798 N) (z.1 - mu)) +
        _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 *
          (∫ mu, _root_.GD.N0232.N0720.N1364.d016803 N mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016799 N) (z.1 - mu)) := by
  rw [_root_.GD.N0232.N0720.N1364.d016819 hN,
    _root_.GD.N0232.N0720.N1364.d016820 hN]
  rfl


theorem d016822
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016802 N mu *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016798 N) (x - mu))) =
      x * (_root_.GD.N0232.N0720.N1364.d016794 N * (1 - _root_.GD.N0232.N0720.N1364.d016792 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
          _root_.GD.N0232.N0720.N1280.d003887 N x -
        2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003886 x) := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨hw1, _, hv1, _, hU1, _⟩
  have hV : _root_.GD.N0232.N0720.N1280.d003879 N ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003892 hN).ne'
  have hv0 : _root_.GD.N0232.N0720.N1280.d003878 ≠ 0 := _root_.GD.N0232.N0720.N1280.d003890.ne'
  have h := _root_.GD.N0232.N0720.N1277.d002644
    hU1 hw1 hv1 (_root_.GD.N0232.N0720.N1364.d016806 N) (_root_.GD.N0232.N0720.N1364.d016807 N)
    (c := _root_.GD.N0232.N0720.N1364.d016794 N) (d := 2) (x := x)
  have h' :
      (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016802 N mu *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016798 N) (x - mu))) =
        _root_.GD.N0232.N0720.N1364.d016794 N * (_root_.GD.N0232.N0720.N1364.d016800 N / _root_.GD.N0232.N0720.N1280.d003879 N * x) *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x -
          2 * (_root_.GD.N0232.N0720.N1364.d016796 N / _root_.GD.N0232.N0720.N1280.d003878 * x) * _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x := by
    simpa [_root_.GD.N0232.N0720.N1364.d016802] using h
  rw [h']
  unfold _root_.GD.N0232.N0720.N1280.d003887 _root_.GD.N0232.N0720.N1280.d003886
  rw [show _root_.GD.N0232.N0720.N1364.d016800 N = _root_.GD.N0232.N0720.N1280.d003879 N - _root_.GD.N0232.N0720.N1364.d016792 N * _root_.GD.N0232.N0720.N1280.d003878 by
      have hu := _root_.GD.N0232.N0720.N1364.d016806 N
      unfold _root_.GD.N0232.N0720.N1364.d016798 at hu
      linarith,
    show _root_.GD.N0232.N0720.N1364.d016796 N = _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003878 by rfl]
  field_simp [hV, hv0]


theorem d016823
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016803 N mu *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016799 N) (x - mu))) =
      x * (_root_.GD.N0232.N0720.N1364.d016795 N * (1 - _root_.GD.N0232.N0720.N1364.d016793 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
          _root_.GD.N0232.N0720.N1280.d003887 N x +
        2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003886 x) := by
  rcases _root_.GD.N0232.N0720.N1364.d016805 hN with ⟨_, hw2, _, hv2, _, hU2⟩
  have hV : _root_.GD.N0232.N0720.N1280.d003879 N ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003892 hN).ne'
  have hv0 : _root_.GD.N0232.N0720.N1280.d003878 ≠ 0 := _root_.GD.N0232.N0720.N1280.d003890.ne'
  have h := _root_.GD.N0232.N0720.N1277.d002644
    hU2 hw2 hv2 (_root_.GD.N0232.N0720.N1364.d016808 N) (_root_.GD.N0232.N0720.N1364.d016809 N)
    (c := _root_.GD.N0232.N0720.N1364.d016795 N) (d := -1) (x := x)
  have h' :
      (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016803 N mu *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016799 N) (x - mu))) =
        _root_.GD.N0232.N0720.N1364.d016795 N * (_root_.GD.N0232.N0720.N1364.d016801 N / _root_.GD.N0232.N0720.N1280.d003879 N * x) *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x -
          (-1 : ℝ) * (_root_.GD.N0232.N0720.N1364.d016797 N / _root_.GD.N0232.N0720.N1280.d003878 * x) * _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x := by
    simpa [_root_.GD.N0232.N0720.N1364.d016803] using h
  rw [h']
  unfold _root_.GD.N0232.N0720.N1280.d003887 _root_.GD.N0232.N0720.N1280.d003886
  rw [show _root_.GD.N0232.N0720.N1364.d016801 N = _root_.GD.N0232.N0720.N1280.d003879 N - _root_.GD.N0232.N0720.N1364.d016793 N * _root_.GD.N0232.N0720.N1280.d003878 by
      have hu := _root_.GD.N0232.N0720.N1364.d016808 N
      unfold _root_.GD.N0232.N0720.N1364.d016799 at hu
      linarith,
    show _root_.GD.N0232.N0720.N1364.d016797 N = 2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003878 by rfl]
  field_simp [hV, hv0]
  ring

def d016824 (N : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016802 N x))

def d016825 (N : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016803 N x))

theorem d016826
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016824 N Set.univ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016794 N - 2) := by
  unfold _root_.GD.N0232.N0720.N1364.d016824
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0720.N1364.d016815 hN)
      (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1364.d016811 hN)),
    _root_.GD.N0232.N0720.N1364.d016817 hN]

theorem d016827
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016825 N Set.univ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016795 N + 1) := by
  unfold _root_.GD.N0232.N0720.N1364.d016825
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0720.N1364.d016816 hN)
      (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1364.d016812 hN)),
    _root_.GD.N0232.N0720.N1364.d016818 hN]

theorem d016828
    {N : ℝ} (hN : 3 ≤ N) : IsFiniteMeasure (_root_.GD.N0232.N0720.N1364.d016824 N) := by
  constructor
  rw [_root_.GD.N0232.N0720.N1364.d016826 hN]
  exact ENNReal.ofReal_lt_top

theorem d016829
    {N : ℝ} (hN : 3 ≤ N) : IsFiniteMeasure (_root_.GD.N0232.N0720.N1364.d016825 N) := by
  constructor
  rw [_root_.GD.N0232.N0720.N1364.d016827 hN]
  exact ENNReal.ofReal_lt_top



def d016830 (a : ℝ) (ha : 0 < a) (mu : ℝ) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := mu
  scale₁ := a
  scale₂ := a
  scale₁_pos := ha
  scale₂_pos := ha

theorem d016831 (a : ℝ) (ha : 0 < a) :
    Continuous (_root_.GD.N0232.N0720.N1364.d016830 a ha) := by
  apply (_root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff).mp
  change Continuous (fun mu : ℝ ↦ (mu, (a, a)))
  fun_prop

theorem d016832 (a : ℝ) (ha : 0 < a) :
    Measurable (_root_.GD.N0232.N0720.N1364.d016830 a ha) :=
  (_root_.GD.N0232.N0720.N1364.d016831 a ha).measurable

def d016833 (N : ℝ) (hN : 3 ≤ N) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  (_root_.GD.N0232.N0720.N1364.d016824 N).map
    (_root_.GD.N0232.N0720.N1364.d016830 (_root_.GD.N0232.N0720.N1281.d016761 (_root_.GD.N0232.N0720.N1364.d016790 N))
      (_root_.GD.N0232.N0720.N1281.d016763 (by
        have := _root_.GD.N0232.N0720.N1285.d002687 hN
        unfold _root_.GD.N0232.N0720.N1364.d016790
        linarith)))

def d016834 (N : ℝ) (hN : 3 ≤ N) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  (_root_.GD.N0232.N0720.N1364.d016825 N).map
    (_root_.GD.N0232.N0720.N1364.d016830 (_root_.GD.N0232.N0720.N1281.d016761 (2 * _root_.GD.N0232.N0720.N1364.d016790 N))
      (_root_.GD.N0232.N0720.N1281.d016763 (by
        have := _root_.GD.N0232.N0720.N1285.d002687 hN
        unfold _root_.GD.N0232.N0720.N1364.d016790
        linarith)))



def d016835 (N : ℝ) (hN : 3 ≤ N) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  Measure.dirac _root_.GD.N0232.N0720.N1080.d014169 + _root_.GD.N0232.N0720.N1364.d016833 N hN +
    _root_.GD.N0232.N0720.N1364.d016834 N hN

theorem d016836
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016833 N hN Set.univ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016794 N - 2) := by
  unfold _root_.GD.N0232.N0720.N1364.d016833
  rw [Measure.map_apply
      (_root_.GD.N0232.N0720.N1364.d016832 _ _) MeasurableSet.univ,
    Set.preimage_univ, _root_.GD.N0232.N0720.N1364.d016826 hN]

theorem d016837
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016834 N hN Set.univ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016795 N + 1) := by
  unfold _root_.GD.N0232.N0720.N1364.d016834
  rw [Measure.map_apply
      (_root_.GD.N0232.N0720.N1364.d016832 _ _) MeasurableSet.univ,
    Set.preimage_univ, _root_.GD.N0232.N0720.N1364.d016827 hN]

theorem d016838
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016835 N hN Set.univ =
      1 + ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016794 N - 2) + ENNReal.ofReal (_root_.GD.N0232.N0720.N1364.d016795 N + 1) := by
  simp [_root_.GD.N0232.N0720.N1364.d016835, _root_.GD.N0232.N0720.N1364.d016836 hN,
    _root_.GD.N0232.N0720.N1364.d016837 hN]

theorem d016839
    {N : ℝ} (hN : 3 ≤ N) : IsFiniteMeasure (_root_.GD.N0232.N0720.N1364.d016835 N hN) := by
  constructor
  rw [_root_.GD.N0232.N0720.N1364.d016838 hN]
  simp


theorem d016840
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1364.d016792 N * (_root_.GD.N0232.N0720.N1364.d016794 N - 2) + _root_.GD.N0232.N0720.N1364.d016793 N * (_root_.GD.N0232.N0720.N1364.d016795 N + 1) = _root_.GD.N0232.N0720.N1364.d016791 N := by
  apply _root_.GD.N0232.N0720.N1284.d002667
  unfold _root_.GD.N0232.N0720.N1364.d016794 _root_.GD.N0232.N0720.N1364.d016795 _root_.GD.N0232.N0720.N1364.d016791 _root_.GD.N0232.N0720.N1364.d016790
  have hs1 : 1 - _root_.GD.N0232.N0720.N1285.d002679 N ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  have hs2 : 1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1285.d002682 _root_.GD.N0232.N0720.N1280.d003936 _root_.GD.N0232.N0720.N1285.d002681
  rw [mul_div_cancel₀ _ hs1, mul_div_cancel₀ _ hs2]
  ring



def d016841
    (N : ℝ) (z : ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 * z.1 *
      (_root_.GD.N0232.N0720.N1364.d016794 N * (1 - _root_.GD.N0232.N0720.N1364.d016792 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
          _root_.GD.N0232.N0720.N1280.d003887 N z.1 -
        2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003886 z.1) +
    _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 * z.1 *
      (_root_.GD.N0232.N0720.N1364.d016795 N * (1 - _root_.GD.N0232.N0720.N1364.d016793 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
          _root_.GD.N0232.N0720.N1280.d003887 N z.1 +
        2 * _root_.GD.N0232.N0720.N1364.d016790 N * _root_.GD.N0232.N0720.N1280.d003886 z.1)



theorem d016842
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1364.d016841 N z =
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 *
          (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016802 N mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016798 N) (z.1 - mu))) +
        _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1364.d016790 N) z.2 *
          (∫ mu, mu * (_root_.GD.N0232.N0720.N1364.d016803 N mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1364.d016799 N) (z.1 - mu))) := by
  rw [_root_.GD.N0232.N0720.N1364.d016822 hN,
    _root_.GD.N0232.N0720.N1364.d016823 hN]
  unfold _root_.GD.N0232.N0720.N1364.d016841
  ring


theorem d016843
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1280.d003940 N z =
      z.1 * _root_.GD.N0232.N0720.N1280.d003939 N z - _root_.GD.N0232.N0720.N1364.d016841 N z := by
  have hV : _root_.GD.N0232.N0720.N1280.d003879 N ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003892 hN).ne'
  unfold _root_.GD.N0232.N0720.N1280.d003940 _root_.GD.N0232.N0720.N1280.d003939 _root_.GD.N0232.N0720.N1364.d016841
    _root_.GD.N0232.N0720.N1280.d003884 _root_.GD.N0232.N0720.N1280.d003885 _root_.GD.N0232.N0720.N1280.d003937
    _root_.GD.N0232.N0720.N1280.d003938 _root_.GD.N0232.N0720.N1364.d016794 _root_.GD.N0232.N0720.N1364.d016795 _root_.GD.N0232.N0720.N1364.d016792 _root_.GD.N0232.N0720.N1364.d016793 _root_.GD.N0232.N0720.N1364.d016790
  have hdecomp :=
    _root_.GD.N0232.N0720.N1284.d002669
      (epsilon := _root_.GD.N0232.N0720.N1285.d002679 N) (v0 := _root_.GD.N0232.N0720.N1280.d003878)
      (V := _root_.GD.N0232.N0720.N1280.d003879 N) (x := z.1)
      (p := _root_.GD.N0232.N0720.N1280.d003886 z.1)
      (h := _root_.GD.N0232.N0720.N1280.d003887 N z.1)
      (k1 := _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2)
      (k2 := _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2)
      (c1 := _root_.GD.N0232.N0720.N1285.d002682 N)
      (c2 := _root_.GD.N0232.N0720.N1280.d003936 N) hV
  have hs1 : 1 - _root_.GD.N0232.N0720.N1285.d002679 N ≠ 0 := by
    exact (_root_.GD.N0232.N0720.N1285.d002688 hN).ne'
  have hs2 : 1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  have hs2' : 1 - _root_.GD.N0232.N0720.N1285.d002679 N * 2 ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1285.d002682 _root_.GD.N0232.N0720.N1285.d002681 _root_.GD.N0232.N0720.N1280.d003936 at hdecomp ⊢
  field_simp [hs1, hs2, hs2'] at hdecomp ⊢
  linear_combination -hdecomp



theorem d016844
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1364.d016841 N z - z.1 * _root_.GD.N0232.N0720.N1280.d003939 N z =
      -_root_.GD.N0232.N0720.N1280.d003940 N z := by
  rw [_root_.GD.N0232.N0720.N1364.d016843 hN z]
  ring





def d016845
    (N : ℝ) (z : ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  2 * _root_.GD.N0232.N0720.N1364.d016841 N z / _root_.GD.N0232.N0720.N1280.d003939 N z - z.1

theorem d016846
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1364.d016841 N z -
        _root_.GD.N0232.N0720.N1364.d016845 N z * _root_.GD.N0232.N0720.N1280.d003939 N z =
      _root_.GD.N0232.N0720.N1280.d003940 N z := by
  have hD : _root_.GD.N0232.N0720.N1280.d003939 N z ≠ 0 :=
    (_root_.GD.N0232.N0720.N1282.d014833 hN z).ne'
  rw [_root_.GD.N0232.N0720.N1364.d016843 hN z]
  unfold _root_.GD.N0232.N0720.N1364.d016845
  field_simp [hD]
  ring


theorem d016847
    {N : ℝ} (hN : 3 ≤ N)
    (z : ℝ × (ℝ × (ℝ × ℝ))) :
    (_root_.GD.N0232.N0720.N1364.d016841 N z -
          z.1 * _root_.GD.N0232.N0720.N1280.d003939 N z) ^ 2 /
        _root_.GD.N0232.N0720.N1280.d003939 N z =
      (_root_.GD.N0232.N0720.N1364.d016841 N z -
          _root_.GD.N0232.N0720.N1364.d016845 N z *
            _root_.GD.N0232.N0720.N1280.d003939 N z) ^ 2 /
        _root_.GD.N0232.N0720.N1280.d003939 N z := by
  rw [_root_.GD.N0232.N0720.N1364.d016844 hN z,
    _root_.GD.N0232.N0720.N1364.d016846 hN z]
  ring

end


end GD.N0232.N0720.N1364

#print axioms _root_.GD.N0232.N0720.N1364.d016811
#print axioms _root_.GD.N0232.N0720.N1364.d016819
#print axioms _root_.GD.N0232.N0720.N1364.d016821
#print axioms _root_.GD.N0232.N0720.N1364.d016842
#print axioms _root_.GD.N0232.N0720.N1364.d016839
#print axioms _root_.GD.N0232.N0720.N1364.d016840
#print axioms _root_.GD.N0232.N0720.N1364.d016844
#print axioms _root_.GD.N0232.N0720.N1364.d016846
#print axioms _root_.GD.N0232.N0720.N1364.d016847

