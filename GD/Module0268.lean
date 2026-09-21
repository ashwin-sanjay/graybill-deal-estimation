import GD.Module0249
import GD.Module0253
import Mathlib.Tactic















namespace GD
namespace N0232
namespace N0720
namespace N1283

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open _root_.GD.N0232.N0719.N0887

def d003842 : ℝ≥0 := ⟨1, by norm_num⟩

theorem d003843 : _root_.GD.N0232.N0720.N1283.d003842 ≠ 0 := by
  change (1 : ℝ≥0) ≠ 0
  norm_num


def d003844 (epsilon x : ℝ) : ℝ :=
  Real.exp (epsilon * x ^ 2 / (2 * (1 - epsilon)))

def d003845 (epsilon : ℝ) : ℝ :=
  (1 - 2 * epsilon) / (1 - epsilon)

theorem d003846
    {epsilon : ℝ} (ht : 1 - epsilon ≠ 0) :
    _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0720.N1283.d003842
        (-epsilon / (2 * (1 - epsilon))) =
      _root_.GD.N0232.N0720.N1283.d003845 epsilon := by
  unfold _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0720.N1283.d003842 _root_.GD.N0232.N0720.N1283.d003845
  change 1 + 2 * (-epsilon / (2 * (1 - epsilon))) * (1 : ℝ) =
    (1 - 2 * epsilon) / (1 - epsilon)
  field_simp [ht]
  ring

theorem d003847
    {epsilon x : ℝ} (ht : 1 - epsilon ≠ 0) :
    -(-epsilon / (2 * (1 - epsilon))) * x ^ 2 + 0 * x =
      epsilon * x ^ 2 / (2 * (1 - epsilon)) := by
  field_simp [ht]
  ring


theorem d003848
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ∫ x : ℝ, _root_.GD.N0232.N0720.N1283.d003844 epsilon x
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹ := by
  have ht : 0 < 1 - epsilon := by linarith
  have hz : 0 < 1 - 2 * epsilon := by linarith
  have hp : 0 < _root_.GD.N0232.N0720.N1283.d003845 epsilon := div_pos hz ht
  unfold _root_.GD.N0232.N0720.N1283.d003844
  calc
    (∫ x : ℝ, Real.exp (epsilon * x ^ 2 / (2 * (1 - epsilon)))
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ,
        Real.exp (-(-epsilon / (2 * (1 - epsilon))) * x ^ 2 + 0 * x)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [_root_.GD.N0232.N0720.N1283.d003847 ht.ne']
    _ = _root_.GD.N0232.N0719.N0887.d003558 _root_.GD.N0232.N0720.N1283.d003842
        (-epsilon / (2 * (1 - epsilon))) 0 := by
          exact _root_.GD.N0232.N0719.N0887.d003568
            (v := _root_.GD.N0232.N0720.N1283.d003842)
            (a := -epsilon / (2 * (1 - epsilon))) (b := 0)
            _root_.GD.N0232.N0720.N1283.d003843
            (by simpa [_root_.GD.N0232.N0720.N1283.d003846 ht.ne'] using hp)
    _ = (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹ := by
          unfold _root_.GD.N0232.N0719.N0887.d003558
          rw [_root_.GD.N0232.N0720.N1283.d003846 ht.ne']
          simp




theorem d003849
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
        _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
        _root_.GD.N0232.N0720.N1283.d003844 epsilon z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) ^ 3 := by
  have hone := _root_.GD.N0232.N0720.N1283.d003848 he0 heHalf
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
          _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
          _root_.GD.N0232.N0720.N1283.d003844 epsilon z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ,
        _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
          _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
          (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          rw [show (fun z : ℝ ↦
              _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
                _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
                _root_.GD.N0232.N0720.N1283.d003844 epsilon z) =
              fun z : ℝ ↦
                (_root_.GD.N0232.N0720.N1283.d003844 epsilon x *
                  _root_.GD.N0232.N0720.N1283.d003844 epsilon y) *
                  _root_.GD.N0232.N0720.N1283.d003844 epsilon z by
                funext z; ring,
            integral_const_mul, hone]
    _ = ∫ x : ℝ,
        _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
          ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) ^ 2
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [show (fun y : ℝ ↦
              _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
                _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
                (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) =
              fun y : ℝ ↦
                (_root_.GD.N0232.N0720.N1283.d003844 epsilon x *
                  (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) *
                  _root_.GD.N0232.N0720.N1283.d003844 epsilon y by
                funext y; ring,
            integral_const_mul, hone]
          ring
    _ = ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) ^ 3 := by
          rw [show (fun x : ℝ ↦
              _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
                ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) ^ 2) =
              fun x : ℝ ↦
                ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon))⁻¹) ^ 2 *
                  _root_.GD.N0232.N0720.N1283.d003844 epsilon x by
                funext x; ring,
            integral_const_mul, hone]
          ring






theorem d003850
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    (Real.sqrt (1 - epsilon)) ^ 3 *
        (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon z
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      (1 - epsilon) ^ 3 /
        (Real.sqrt (1 - 2 * epsilon)) ^ 3 := by
  have ht : 0 < 1 - epsilon := by linarith
  have hz : 0 < 1 - 2 * epsilon := by linarith
  have hp : 0 < _root_.GD.N0232.N0720.N1283.d003845 epsilon := div_pos hz ht
  rw [_root_.GD.N0232.N0720.N1283.d003849 he0 heHalf]
  have hsqt : (Real.sqrt (1 - epsilon)) ^ 2 = 1 - epsilon :=
    Real.sq_sqrt ht.le
  have hsqz : (Real.sqrt (1 - 2 * epsilon)) ^ 2 = 1 - 2 * epsilon :=
    Real.sq_sqrt hz.le
  have hsqt6 : (Real.sqrt (1 - epsilon)) ^ 6 = (1 - epsilon) ^ 3 := by
    calc
      (Real.sqrt (1 - epsilon)) ^ 6 =
          ((Real.sqrt (1 - epsilon)) ^ 2) ^ 3 := by ring
      _ = (1 - epsilon) ^ 3 := by rw [hsqt]
  have hsqp :
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003845 epsilon) =
        Real.sqrt (1 - 2 * epsilon) / Real.sqrt (1 - epsilon) := by
    unfold _root_.GD.N0232.N0720.N1283.d003845
    rw [Real.sqrt_div hz.le]
  rw [hsqp]
  have hsqt0 : Real.sqrt (1 - epsilon) ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hsqz0 : Real.sqrt (1 - 2 * epsilon) ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  rw [inv_div]
  calc
    (Real.sqrt (1 - epsilon)) ^ 3 *
          (Real.sqrt (1 - epsilon) /
            Real.sqrt (1 - 2 * epsilon)) ^ 3 =
        (Real.sqrt (1 - epsilon)) ^ 6 /
          (Real.sqrt (1 - 2 * epsilon)) ^ 3 := by ring
    _ = (1 - epsilon) ^ 3 /
          (Real.sqrt (1 - 2 * epsilon)) ^ 3 := by rw [hsqt6]



def d003851 (a x : ℝ) : ℝ :=
  Real.exp (-a * x ^ 2 / 2)


theorem d003852
    {a : ℝ} (ha : 0 < 1 + a) :
    ∫ x : ℝ, _root_.GD.N0232.N0720.N1283.d003851 a x
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      (Real.sqrt (1 + a))⁻¹ := by
  have hprecision :
      _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0720.N1283.d003842 (a / 2) = 1 + a := by
    unfold _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0720.N1283.d003842
    change 1 + 2 * (a / 2) * (1 : ℝ) = 1 + a
    ring
  unfold _root_.GD.N0232.N0720.N1283.d003851
  calc
    (∫ x : ℝ, Real.exp (-a * x ^ 2 / 2)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, Real.exp (-(a / 2) * x ^ 2 + 0 * x)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          congr 1
          ring
    _ = _root_.GD.N0232.N0719.N0887.d003558 _root_.GD.N0232.N0720.N1283.d003842 (a / 2) 0 := by
      exact _root_.GD.N0232.N0719.N0887.d003568
        _root_.GD.N0232.N0720.N1283.d003843 (by simpa [hprecision] using ha)
    _ = (Real.sqrt (1 + a))⁻¹ := by
      unfold _root_.GD.N0232.N0719.N0887.d003558
      rw [hprecision]
      simp



theorem d003853
    {a : ℝ} (ha : 0 < 1 + a) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      _root_.GD.N0232.N0720.N1283.d003851 a x *
        _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      ((Real.sqrt (1 + a))⁻¹) ^ 3 := by
  have hone := _root_.GD.N0232.N0720.N1283.d003852 ha
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 a x * _root_.GD.N0232.N0720.N1283.d003851 a y *
          (Real.sqrt (1 + a))⁻¹
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          rw [show (fun z : ℝ ↦ _root_.GD.N0232.N0720.N1283.d003851 a x *
              _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z) =
            fun z : ℝ ↦
              (_root_.GD.N0232.N0720.N1283.d003851 a x * _root_.GD.N0232.N0720.N1283.d003851 a y) *
                _root_.GD.N0232.N0720.N1283.d003851 a z by funext z; ring,
            integral_const_mul, hone]
    _ = ∫ x : ℝ, _root_.GD.N0232.N0720.N1283.d003851 a x *
          ((Real.sqrt (1 + a))⁻¹) ^ 2
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [show (fun y : ℝ ↦ _root_.GD.N0232.N0720.N1283.d003851 a x *
              _root_.GD.N0232.N0720.N1283.d003851 a y * (Real.sqrt (1 + a))⁻¹) =
            fun y : ℝ ↦
              (_root_.GD.N0232.N0720.N1283.d003851 a x * (Real.sqrt (1 + a))⁻¹) *
                _root_.GD.N0232.N0720.N1283.d003851 a y by funext y; ring,
            integral_const_mul, hone]
          ring
    _ = ((Real.sqrt (1 + a))⁻¹) ^ 3 := by
          rw [show (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1283.d003851 a x *
              ((Real.sqrt (1 + a))⁻¹) ^ 2) =
            fun x : ℝ ↦ ((Real.sqrt (1 + a))⁻¹) ^ 2 *
              _root_.GD.N0232.N0720.N1283.d003851 a x by funext x; ring,
            integral_const_mul, hone]
          ring



def d003854 (epsilon : ℝ) : ℝ := 1 - epsilon
def d003855 (epsilon : ℝ) : ℝ := 1 - 2 * epsilon
def d003856 (epsilon : ℝ) : ℝ :=
  1 - 2 * epsilon + 2 * epsilon ^ 2



theorem d003857
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3) *
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851
            (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) x *
          _root_.GD.N0232.N0720.N1283.d003851
            (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) y *
          _root_.GD.N0232.N0720.N1283.d003851
            (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon)) ^ 3 := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1283.d003855 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003855; linarith
  have hmixed : 0 < _root_.GD.N0232.N0720.N1283.d003856 epsilon := by
    unfold _root_.GD.N0232.N0720.N1283.d003856
    nlinarith [sq_nonneg (epsilon - 1 / 2)]
  have hprecision :
      1 + epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) =
        _root_.GD.N0232.N0720.N1283.d003856 epsilon /
          (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by
    have hden : _root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon ≠ 0 :=
      mul_ne_zero hs1.ne' hs2.ne'
    calc
      1 + epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) =
          (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) /
              (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) +
            epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by
              rw [div_self hden]
      _ = (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon + epsilon) /
          (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by ring
      _ = _root_.GD.N0232.N0720.N1283.d003856 epsilon /
          (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by
            congr 1
            unfold _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003855 _root_.GD.N0232.N0720.N1283.d003856
            ring
  have ha :
      0 < 1 + epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by
    rw [hprecision]
    positivity
  rw [_root_.GD.N0232.N0720.N1283.d003853 ha, hprecision]
  have hsqrtRatio :
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon /
          (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) =
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon) /
          (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) := by
    rw [Real.sqrt_div hmixed.le, Real.sqrt_mul hs1.le]
  rw [hsqrtRatio, inv_div]
  have hs1sq : (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 epsilon :=
    Real.sq_sqrt hs1.le
  calc
    (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) /
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 *
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) /
              Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon))) ^ 3 =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 6 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon)) ^ 3 := by
          field_simp [(Real.sqrt_pos.2 hs2).ne',
            (Real.sqrt_pos.2 hmixed).ne']
    _ = _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon)) ^ 3 := by
      rw [show (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 6 =
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 2) ^ 3 by ring, hs1sq]


theorem d003858
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) /
        _root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 3) *
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851
            (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) x *
          _root_.GD.N0232.N0720.N1283.d003851
            (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) y *
          _root_.GD.N0232.N0720.N1283.d003851
            (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1283.d003855 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003855; linarith
  have ha : 0 < 1 +
      (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) := by
    rw [show 1 + (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) =
      1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) by ring]
    positivity
  rw [_root_.GD.N0232.N0720.N1283.d003853 ha]
  have hprecision :
      1 + (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) =
        1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) := by ring
  rw [hprecision]
  have hsqrtInv :
      Real.sqrt (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) =
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) *
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon))⁻¹ := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      one_div, Real.sqrt_mul hs1.le]
  rw [hsqrtInv, inv_inv]
  have hs1sq : (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 epsilon :=
    Real.sq_sqrt hs1.le
  have hs2sq : (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 2 = _root_.GD.N0232.N0720.N1283.d003855 epsilon :=
    Real.sq_sqrt hs2.le
  have hs2six : (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 6 =
      _root_.GD.N0232.N0720.N1283.d003855 epsilon ^ 3 := by
    calc
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 6 =
          ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 2) ^ 3 := by ring
      _ = _root_.GD.N0232.N0720.N1283.d003855 epsilon ^ 3 := by rw [hs2sq]
  calc
    (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) / _root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 3 *
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) *
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 6 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
          field_simp [hs2.ne', (Real.sqrt_pos.2 hs2).ne']
          nlinarith
    _ = _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
      rw [show (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 6 =
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 2) ^ 3 by ring, hs1sq]






def d003859 (epsilon x y z : ℝ) : ℝ :=
  ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon))⁻¹) ^ 3 *
    _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x *
    _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) y *
    _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) z

theorem d003860
    {epsilon : ℝ} (he : epsilon < 1) (x y z : ℝ) :
    0 < _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z := by
  have hs : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  unfold _root_.GD.N0232.N0720.N1283.d003859 _root_.GD.N0232.N0720.N1283.d003851
  positivity

private theorem d003861
    {epsilon x : ℝ} (hs1 : _root_.GD.N0232.N0720.N1283.d003854 epsilon ≠ 0) :
    (_root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x)⁻¹ =
      _root_.GD.N0232.N0720.N1283.d003844 epsilon x := by
  unfold _root_.GD.N0232.N0720.N1283.d003851 _root_.GD.N0232.N0720.N1283.d003844
  have hexp := (Real.exp_neg
    (-(epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) * x ^ 2 / 2)).symm
  rw [show -(-(epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) * x ^ 2 / 2) =
    epsilon * x ^ 2 / (2 * (1 - epsilon)) by
      unfold _root_.GD.N0232.N0720.N1283.d003854
      field_simp [hs1]
      ] at hexp
  simpa using hexp

private theorem d003862
    {epsilon x : ℝ}
    (hs1 : _root_.GD.N0232.N0720.N1283.d003854 epsilon ≠ 0)
    (hs2 : _root_.GD.N0232.N0720.N1283.d003855 epsilon ≠ 0) :
    _root_.GD.N0232.N0720.N1283.d003851 (2 * epsilon / _root_.GD.N0232.N0720.N1283.d003855 epsilon) x /
        _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x =
      _root_.GD.N0232.N0720.N1283.d003851
        (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) x := by
  unfold _root_.GD.N0232.N0720.N1283.d003851
  rw [← Real.exp_sub]
  congr 1
  field_simp [hs1, hs2]
  unfold _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003855
  ring

private theorem d003863
    {epsilon x : ℝ}
    (hs1 : _root_.GD.N0232.N0720.N1283.d003854 epsilon ≠ 0)
    (hs2 : _root_.GD.N0232.N0720.N1283.d003855 epsilon ≠ 0) :
    _root_.GD.N0232.N0720.N1283.d003851 (2 * epsilon / _root_.GD.N0232.N0720.N1283.d003855 epsilon) x ^ 2 /
        _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x =
      _root_.GD.N0232.N0720.N1283.d003851
        (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) x := by
  unfold _root_.GD.N0232.N0720.N1283.d003851
  rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  field_simp [hs1, hs2]
  unfold _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003855
  ring


theorem d003864
    {epsilon : ℝ} (heHalf : epsilon < 1 / 2) (x y z : ℝ) :
    1 / _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 3 *
        _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
        _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
        _root_.GD.N0232.N0720.N1283.d003844 epsilon z := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  have hqx : 0 < _root_.GD.N0232.N0720.N1283.d003851
      (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x := by
    unfold _root_.GD.N0232.N0720.N1283.d003851; positivity
  have hqy : 0 < _root_.GD.N0232.N0720.N1283.d003851
      (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) y := by
    unfold _root_.GD.N0232.N0720.N1283.d003851; positivity
  have hqz : 0 < _root_.GD.N0232.N0720.N1283.d003851
      (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) z := by
    unfold _root_.GD.N0232.N0720.N1283.d003851; positivity
  unfold _root_.GD.N0232.N0720.N1283.d003859
  rw [one_div, mul_inv_rev, mul_inv_rev, mul_inv_rev,
    inv_pow, inv_inv,
    _root_.GD.N0232.N0720.N1283.d003861 hs1.ne',
    _root_.GD.N0232.N0720.N1283.d003861 hs1.ne',
    _root_.GD.N0232.N0720.N1283.d003861 hs1.ne']
  ring


theorem d003865
    {epsilon : ℝ} (heHalf : epsilon < 1 / 2) (x y z : ℝ) :
    _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z /
        _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 *
        _root_.GD.N0232.N0720.N1283.d003851
          (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) x *
        _root_.GD.N0232.N0720.N1283.d003851
          (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) y *
        _root_.GD.N0232.N0720.N1283.d003851
          (epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)) z := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1283.d003855 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003855; linarith
  have hsqrt1 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) ≠ 0 :=
    (Real.sqrt_pos.2 hs1).ne'
  have hsqrt2 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ≠ 0 :=
    (Real.sqrt_pos.2 hs2).ne'
  unfold _root_.GD.N0232.N0720.N1283.d003859
  rw [show _root_.GD.N0232.N0720.N1283.d003854 (2 * epsilon) = _root_.GD.N0232.N0720.N1283.d003855 epsilon by
    unfold _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003855; ring]
  have hx := _root_.GD.N0232.N0720.N1283.d003862
    (epsilon := epsilon) (x := x) hs1.ne' hs2.ne'
  have hy := _root_.GD.N0232.N0720.N1283.d003862
    (epsilon := epsilon) (x := y) hs1.ne' hs2.ne'
  have hz := _root_.GD.N0232.N0720.N1283.d003862
    (epsilon := epsilon) (x := z) hs1.ne' hs2.ne'
  field_simp [hsqrt1, hsqrt2,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) y ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) z ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity] at hx hy hz ⊢
  rw [hx, hy, hz]
  ring


theorem d003866
    {epsilon : ℝ} (heHalf : epsilon < 1 / 2) (x y z : ℝ) :
    _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z ^ 2 /
        _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) / _root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 3 *
        _root_.GD.N0232.N0720.N1283.d003851
          (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) x *
        _root_.GD.N0232.N0720.N1283.d003851
          (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) y *
        _root_.GD.N0232.N0720.N1283.d003851
          (1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1) z := by
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003854; linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1283.d003855 epsilon := by unfold _root_.GD.N0232.N0720.N1283.d003855; linarith
  have hsqrt1 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) ≠ 0 :=
    (Real.sqrt_pos.2 hs1).ne'
  have hsqrt2 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ≠ 0 :=
    (Real.sqrt_pos.2 hs2).ne'
  have hsqrt2sq : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 2 = _root_.GD.N0232.N0720.N1283.d003855 epsilon :=
    Real.sq_sqrt hs2.le
  unfold _root_.GD.N0232.N0720.N1283.d003859
  rw [show _root_.GD.N0232.N0720.N1283.d003854 (2 * epsilon) = _root_.GD.N0232.N0720.N1283.d003855 epsilon by
    unfold _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003855; ring]
  have hx := _root_.GD.N0232.N0720.N1283.d003863
    (epsilon := epsilon) (x := x) hs1.ne' hs2.ne'
  have hy := _root_.GD.N0232.N0720.N1283.d003863
    (epsilon := epsilon) (x := y) hs1.ne' hs2.ne'
  have hz := _root_.GD.N0232.N0720.N1283.d003863
    (epsilon := epsilon) (x := z) hs1.ne' hs2.ne'
  field_simp [hsqrt1, hsqrt2,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) x ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) y ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (epsilon / _root_.GD.N0232.N0720.N1283.d003854 epsilon) z ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity] at hx hy hz ⊢
  rw [hx, hy, hz, show Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 6 =
    _root_.GD.N0232.N0720.N1283.d003855 epsilon ^ 3 by
      calc
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 6 =
            (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 2) ^ 3 := by ring
        _ = _root_.GD.N0232.N0720.N1283.d003855 epsilon ^ 3 := by rw [hsqrt2sq]]
  ring



private theorem d003867
    (c : ℝ) (f : ℝ → ℝ) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      c * (f x * f y * f z)
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      c * (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        f x * f y * f z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        c * (f x * f y * f z)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ,
        c * (∫ z : ℝ, f x * f y * f z
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          rw [show (fun z : ℝ ↦ c * (f x * f y * f z)) =
            fun z : ℝ ↦ c * (f x * f y * f z) by rfl,
            integral_const_mul]
    _ = ∫ x : ℝ, c *
        (∫ y : ℝ, ∫ z : ℝ, f x * f y * f z
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [integral_const_mul]
    _ = c * (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        f x * f y * f z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
          rw [integral_const_mul]



theorem d003868
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      1 / _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        1 / _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 3 *
          (_root_.GD.N0232.N0720.N1283.d003844 epsilon x *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon z)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          apply integral_congr_ae
          filter_upwards [] with z
          rw [_root_.GD.N0232.N0720.N1283.d003864 heHalf]
          ring
    _ = (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon)) ^ 3 *
        (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          _root_.GD.N0232.N0720.N1283.d003844 epsilon x *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon y *
            _root_.GD.N0232.N0720.N1283.d003844 epsilon z
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
          ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) :=
      _root_.GD.N0232.N0720.N1283.d003867 _ _
    _ = _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
          simpa only [_root_.GD.N0232.N0720.N1283.d003854, _root_.GD.N0232.N0720.N1283.d003855] using
            _root_.GD.N0232.N0720.N1283.d003850 he0 heHalf


theorem d003869
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z /
        _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon)) ^ 3 := by
  let a := epsilon / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon)
  let c := (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) /
    Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z /
          _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        c * (_root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [a, c]
          rw [_root_.GD.N0232.N0720.N1283.d003865 heHalf]
          ring
    _ = c * (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) :=
      _root_.GD.N0232.N0720.N1283.d003867 _ _
    _ = _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 epsilon)) ^ 3 := by
          dsimp [a, c]
          exact _root_.GD.N0232.N0720.N1283.d003857 he0 heHalf


theorem d003870
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (heHalf : epsilon < 1 / 2) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z ^ 2 /
        _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
  let a := 1 / (_root_.GD.N0232.N0720.N1283.d003854 epsilon * _root_.GD.N0232.N0720.N1283.d003855 epsilon) - 1
  let c := (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 epsilon) / _root_.GD.N0232.N0720.N1283.d003855 epsilon) ^ 3
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003859 (2 * epsilon) x y z ^ 2 /
          _root_.GD.N0232.N0720.N1283.d003859 epsilon x y z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        c * (_root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [a, c]
          rw [_root_.GD.N0232.N0720.N1283.d003866 heHalf]
          ring
    _ = c * (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) :=
      _root_.GD.N0232.N0720.N1283.d003867 _ _
    _ = _root_.GD.N0232.N0720.N1283.d003854 epsilon ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 epsilon)) ^ 3 := by
          dsimp [a, c]
          exact _root_.GD.N0232.N0720.N1283.d003858 he0 heHalf



def d003871 (base u v : ℝ) : ℝ :=
  u / _root_.GD.N0232.N0720.N1283.d003854 u + v / _root_.GD.N0232.N0720.N1283.d003854 v - base / _root_.GD.N0232.N0720.N1283.d003854 base

def d003872 (base u v : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1283.d003854 base * (_root_.GD.N0232.N0720.N1283.d003854 u + _root_.GD.N0232.N0720.N1283.d003854 v) -
    _root_.GD.N0232.N0720.N1283.d003854 u * _root_.GD.N0232.N0720.N1283.d003854 v



theorem d003873
    {base u v : ℝ}
    (hb : _root_.GD.N0232.N0720.N1283.d003854 base ≠ 0)
    (hu : _root_.GD.N0232.N0720.N1283.d003854 u ≠ 0)
    (hv : _root_.GD.N0232.N0720.N1283.d003854 v ≠ 0) :
    1 + _root_.GD.N0232.N0720.N1283.d003871 base u v =
      _root_.GD.N0232.N0720.N1283.d003872 base u v /
        (_root_.GD.N0232.N0720.N1283.d003854 base * _root_.GD.N0232.N0720.N1283.d003854 u * _root_.GD.N0232.N0720.N1283.d003854 v) := by
  have hbFrac : base / _root_.GD.N0232.N0720.N1283.d003854 base = 1 / _root_.GD.N0232.N0720.N1283.d003854 base - 1 := by
    field_simp [hb]
    unfold _root_.GD.N0232.N0720.N1283.d003854
    ring
  have huFrac : u / _root_.GD.N0232.N0720.N1283.d003854 u = 1 / _root_.GD.N0232.N0720.N1283.d003854 u - 1 := by
    field_simp [hu]
    unfold _root_.GD.N0232.N0720.N1283.d003854
    ring
  have hvFrac : v / _root_.GD.N0232.N0720.N1283.d003854 v = 1 / _root_.GD.N0232.N0720.N1283.d003854 v - 1 := by
    field_simp [hv]
    unfold _root_.GD.N0232.N0720.N1283.d003854
    ring
  unfold _root_.GD.N0232.N0720.N1283.d003871 _root_.GD.N0232.N0720.N1283.d003872
  rw [hbFrac, huFrac, hvFrac]
  field_simp [hb, hu, hv]
  ring

private theorem d003874
    {base u v x : ℝ}
    (hb : _root_.GD.N0232.N0720.N1283.d003854 base ≠ 0)
    (hu : _root_.GD.N0232.N0720.N1283.d003854 u ≠ 0)
    (hv : _root_.GD.N0232.N0720.N1283.d003854 v ≠ 0) :
    _root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) x *
          _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) x /
        _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) x =
      _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) x := by
  unfold _root_.GD.N0232.N0720.N1283.d003851 _root_.GD.N0232.N0720.N1283.d003871
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  field_simp [hb, hu, hv]
  ring


theorem d003875
    {base u v : ℝ}
    (hb : 0 < _root_.GD.N0232.N0720.N1283.d003854 base)
    (hu : 0 < _root_.GD.N0232.N0720.N1283.d003854 u)
    (hv : 0 < _root_.GD.N0232.N0720.N1283.d003854 v)
    (x y z : ℝ) :
    _root_.GD.N0232.N0720.N1283.d003859 u x y z * _root_.GD.N0232.N0720.N1283.d003859 v x y z /
        _root_.GD.N0232.N0720.N1283.d003859 base x y z =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) /
          (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v))) ^ 3 *
        _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) x *
        _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) y *
        _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) z := by
  have hsb : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) ≠ 0 :=
    (Real.sqrt_pos.2 hb).ne'
  have hsu : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) ≠ 0 :=
    (Real.sqrt_pos.2 hu).ne'
  have hsv : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v) ≠ 0 :=
    (Real.sqrt_pos.2 hv).ne'
  have hx := _root_.GD.N0232.N0720.N1283.d003874
    (base := base) (u := u) (v := v) (x := x) hb.ne' hu.ne' hv.ne'
  have hy := _root_.GD.N0232.N0720.N1283.d003874
    (base := base) (u := u) (v := v) (x := y) hb.ne' hu.ne' hv.ne'
  have hz := _root_.GD.N0232.N0720.N1283.d003874
    (base := base) (u := u) (v := v) (x := z) hb.ne' hu.ne' hv.ne'
  unfold _root_.GD.N0232.N0720.N1283.d003859
  field_simp [hsb, hsu, hsv,
    show _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) x ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) y ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity,
    show _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) z ≠ 0 by
      unfold _root_.GD.N0232.N0720.N1283.d003851; positivity] at hx hy hz ⊢
  calc
    _root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) x *
            _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) x *
          _root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) y *
        _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) y *
      _root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) z *
        _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) z =
        (_root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) x *
            _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) x) *
          (_root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) y *
            _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) y) *
          (_root_.GD.N0232.N0720.N1283.d003851 (u / _root_.GD.N0232.N0720.N1283.d003854 u) z *
            _root_.GD.N0232.N0720.N1283.d003851 (v / _root_.GD.N0232.N0720.N1283.d003854 v) z) := by ring
    _ = (_root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) x *
            _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) x) *
          (_root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) y *
            _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) y) *
          (_root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) z *
            _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) z) := by
          rw [hx, hy, hz]
    _ = _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) x *
              _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) x *
            _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) y *
          _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) y *
        _root_.GD.N0232.N0720.N1283.d003851 (base / _root_.GD.N0232.N0720.N1283.d003854 base) z *
      _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) z := by ring









theorem d003876
    {base u v : ℝ}
    (hb : 0 < _root_.GD.N0232.N0720.N1283.d003854 base)
    (hu : 0 < _root_.GD.N0232.N0720.N1283.d003854 u)
    (hv : 0 < _root_.GD.N0232.N0720.N1283.d003854 v)
    (hD : 0 < _root_.GD.N0232.N0720.N1283.d003872 base u v) :
    ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v))) ^ 3) *
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) x *
          _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) y *
          _root_.GD.N0232.N0720.N1283.d003851 (_root_.GD.N0232.N0720.N1283.d003871 base u v) z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      _root_.GD.N0232.N0720.N1283.d003854 base ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v)) ^ 3 := by
  have hprecision := _root_.GD.N0232.N0720.N1283.d003873 hb.ne' hu.ne' hv.ne'
  have ha : 0 < 1 + _root_.GD.N0232.N0720.N1283.d003871 base u v := by
    rw [hprecision]
    positivity
  rw [_root_.GD.N0232.N0720.N1283.d003853 ha, hprecision]
  have hsqrtDen :
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v /
          (_root_.GD.N0232.N0720.N1283.d003854 base * _root_.GD.N0232.N0720.N1283.d003854 u * _root_.GD.N0232.N0720.N1283.d003854 v)) =
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v) /
          (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v)) := by
    rw [Real.sqrt_div hD.le,
      Real.sqrt_mul (mul_nonneg hb.le hu.le), Real.sqrt_mul hb.le]
  rw [hsqrtDen, inv_div]
  have hbSq : (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base)) ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 base :=
    Real.sq_sqrt hb.le
  have hsu0 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  have hsv0 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have hD0 : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v) ≠ 0 :=
    (Real.sqrt_pos.2 hD).ne'
  calc
    (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) /
          (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v))) ^ 3 *
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v) /
              Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v))) ^ 3 =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base)) ^ 6 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v)) ^ 3 := by
          field_simp [hsu0, hsv0, hD0]
    _ = _root_.GD.N0232.N0720.N1283.d003854 base ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v)) ^ 3 := by
      rw [show (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base)) ^ 6 =
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base)) ^ 2) ^ 3 by ring, hbSq]


theorem d003877
    {base u v : ℝ}
    (hb : 0 < _root_.GD.N0232.N0720.N1283.d003854 base)
    (hu : 0 < _root_.GD.N0232.N0720.N1283.d003854 u)
    (hv : 0 < _root_.GD.N0232.N0720.N1283.d003854 v)
    (hD : 0 < _root_.GD.N0232.N0720.N1283.d003872 base u v) :
    ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      _root_.GD.N0232.N0720.N1283.d003859 u x y z * _root_.GD.N0232.N0720.N1283.d003859 v x y z /
        _root_.GD.N0232.N0720.N1283.d003859 base x y z
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
      ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 =
      _root_.GD.N0232.N0720.N1283.d003854 base ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v)) ^ 3 := by
  let a := _root_.GD.N0232.N0720.N1283.d003871 base u v
  let c := (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 base) /
    (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 u) * Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 v))) ^ 3
  calc
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003859 u x y z * _root_.GD.N0232.N0720.N1283.d003859 v x y z /
          _root_.GD.N0232.N0720.N1283.d003859 base x y z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        c * (_root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z)
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply integral_congr_ae
          filter_upwards [] with y
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [a, c]
          rw [_root_.GD.N0232.N0720.N1283.d003875 hb hu hv]
          ring
    _ = c * (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        _root_.GD.N0232.N0720.N1283.d003851 a x *
          _root_.GD.N0232.N0720.N1283.d003851 a y * _root_.GD.N0232.N0720.N1283.d003851 a z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) :=
      _root_.GD.N0232.N0720.N1283.d003867 _ _
    _ = _root_.GD.N0232.N0720.N1283.d003854 base ^ 3 /
        (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003872 base u v)) ^ 3 := by
          dsimp [a, c]
          exact _root_.GD.N0232.N0720.N1283.d003876 hb hu hv hD

end

end N1283
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1283.d003848
#print axioms _root_.GD.N0232.N0720.N1283.d003849
#print axioms _root_.GD.N0232.N0720.N1283.d003850
#print axioms _root_.GD.N0232.N0720.N1283.d003868
#print axioms _root_.GD.N0232.N0720.N1283.d003869
#print axioms _root_.GD.N0232.N0720.N1283.d003870
#print axioms _root_.GD.N0232.N0720.N1283.d003876
