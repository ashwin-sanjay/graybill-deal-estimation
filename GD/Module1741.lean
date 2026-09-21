import GD.Module1420
import GD.Module1314















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1677
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1528
open _root_.GD.N0106.N0428.N0765.N1527 _root_.GD.N0106.N0428.N0765.N1592 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521


def d028882 (z w : ℂ) : Prop :=
  ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi


def d028883 (e : ℝ) (z w : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1672.d021424 e z.re w.re z.im w.im / _root_.GD.N0106.N0428.N0765.N1672.d021423 e z.re w.re z.im w.im


theorem d028884 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) : _root_.GD.N0106.N0428.N0765.N1672.d021423 e z.re w.re z.im w.im ≠ 0 := by
  rcases eq_or_lt_of_le he with h | h
  · subst e
    exact _root_.GD.N0106.N0428.N0765.N1528.d021466 z.re w.re z.im w.im hw
  · have hn : _root_.GD.N0106.N0428.N0765.N1538.d021243 e z.re w.re z.im w.im ≠ 0 := by
      apply norm_pos_iff.mp
      exact (mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw) (_root_.GD.N0106.N0428.N0765.N1538.d021248 h z.re w.re)).trans_le
        (_root_.GD.N0106.N0428.N0765.N1538.d021250 h z.re w.re z.im w.im hw)
    intro hz
    apply hn
    rw [_root_.GD.N0106.N0428.N0765.N1672.d021427 h z.re w.re z.im w.im (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw), hz, mul_zero]


def d028885 (axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  (_root_.GD.N0106.N0428.N0765.N1592.d022713 true axis e w z *
      _root_.GD.N0106.N0428.N0765.N1672.d021423 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
        (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im -
    _root_.GD.N0106.N0428.N0765.N1672.d021424 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
        (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im *
      _root_.GD.N0106.N0428.N0765.N1592.d022713 false axis e w z) /
    _root_.GD.N0106.N0428.N0765.N1672.d021423 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im ^ 2

theorem d028886 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028883 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q))
      (_root_.GD.N0106.N0428.N0765.N1677.d028885 axis e w z) z := by
  exact (_root_.GD.N0106.N0428.N0765.N1592.d022730 axis he hz).div (_root_.GD.N0106.N0428.N0765.N1592.d022729 axis he hz)
    (_root_.GD.N0106.N0428.N0765.N1677.d028884 he hz)

theorem d028887 (axis : Bool) {e : ℝ} (he : 0 ≤ e) (w : ℂ) :
    DifferentiableOn ℂ (fun z => _root_.GD.N0106.N0428.N0765.N1677.d028883 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z))
      (_root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1677.d028886 axis he hz).differentiableAt.differentiableWithinAt

theorem d028888 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028883 e q w) (_root_.GD.N0106.N0428.N0765.N1677.d028885 true e w z) z :=
  _root_.GD.N0106.N0428.N0765.N1677.d028886 true he hw

theorem d028889 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028883 e z q) (_root_.GD.N0106.N0428.N0765.N1677.d028885 false e z w) w :=
  _root_.GD.N0106.N0428.N0765.N1677.d028886 false he hw


def d028890 (e : ℝ) (w : ℂ) : ℂ := Complex.exp w / (1 + (e : ℂ) * Complex.exp w)


def d028891 (e : ℝ) : ℂ := ((1 / (1 + e) : ℝ) : ℂ)

theorem d028892 {z w : ℂ} (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    |w.im| < Real.pi / 2 := by
  have h0 := abs_nonneg z.im
  have h1 := abs_nonneg w.im
  unfold _root_.GD.N0106.N0428.N0765.N1677.d028882 _root_.GD.N0106.N0428.N0765.N1538.d021192 at hw
  nlinarith [Real.pi_pos]

theorem d028893 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) : 1 + (e : ℂ) * Complex.exp w ≠ 0 := by
  have hcos : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo
    (abs_lt.mp (_root_.GD.N0106.N0428.N0765.N1677.d028892 hw))
  have hre : 0 < (1 + (e : ℂ) * Complex.exp w).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re]
    positivity
  exact fun h => (ne_of_gt hre) (by rw [h]; rfl)

theorem d028894 {e : ℝ} (he : 0 ≤ e) {z w : ℂ} (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1677.d028890 e)
      (Complex.exp w / (1 + (e : ℂ) * Complex.exp w) ^ 2) w := by
  have h : HasDerivAt (fun q : ℂ => Complex.exp q / (1 + (e : ℂ) * Complex.exp q))
      ((Complex.exp w * (1 + (e : ℂ) * Complex.exp w) -
        Complex.exp w * ((e : ℂ) * Complex.exp w)) /
          (1 + (e : ℂ) * Complex.exp w) ^ 2) w :=
    (Complex.hasDerivAt_exp w).div
      (((Complex.hasDerivAt_exp w).const_mul (e : ℂ)).const_add 1)
      (_root_.GD.N0106.N0428.N0765.N1677.d028893 he hw)
  have hn : Complex.exp w * (1 + (e : ℂ) * Complex.exp w) -
      Complex.exp w * ((e : ℂ) * Complex.exp w) = Complex.exp w := by ring
  change HasDerivAt (fun q => Complex.exp q / (1 + (e : ℂ) * Complex.exp q)) _ w
  simpa only [hn] using h

def d028895 (axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  if axis then 0 else Complex.exp z / (1 + (e : ℂ) * Complex.exp z) ^ 2

theorem d028896 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028890 e (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q)) (_root_.GD.N0106.N0428.N0765.N1677.d028895 axis e w z) z := by
  cases axis
  · exact _root_.GD.N0106.N0428.N0765.N1677.d028894 he hz
  · exact hasDerivAt_const z (_root_.GD.N0106.N0428.N0765.N1677.d028890 e w)



def d028897 (e : ℝ) (z w : ℂ) : ℂ :=
  (((1 + e) / 11 : ℝ) : ℂ) *
    ((_root_.GD.N0106.N0428.N0765.N1677.d028890 e w - _root_.GD.N0106.N0428.N0765.N1677.d028891 e) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1677.d028883 e z w - _root_.GD.N0106.N0428.N0765.N1677.d028891 e) ^ 2)

def d028898 (axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  (((1 + e) / 11 : ℝ) : ℂ) *
    (2 * (_root_.GD.N0106.N0428.N0765.N1677.d028890 e (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z) - _root_.GD.N0106.N0428.N0765.N1677.d028891 e) * _root_.GD.N0106.N0428.N0765.N1677.d028895 axis e w z -
      2 * (_root_.GD.N0106.N0428.N0765.N1677.d028883 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z) - _root_.GD.N0106.N0428.N0765.N1677.d028891 e) *
        _root_.GD.N0106.N0428.N0765.N1677.d028885 axis e w z)

theorem d028899 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028897 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q))
      (_root_.GD.N0106.N0428.N0765.N1677.d028898 axis e w z) z := by
  have hg := ((_root_.GD.N0106.N0428.N0765.N1677.d028896 axis he hz).sub_const (_root_.GD.N0106.N0428.N0765.N1677.d028891 e)).pow 2
  have hq := ((_root_.GD.N0106.N0428.N0765.N1677.d028886 axis he hz).sub_const (_root_.GD.N0106.N0428.N0765.N1677.d028891 e)).pow 2
  simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028897, _root_.GD.N0106.N0428.N0765.N1677.d028898, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    Pi.pow_apply, Pi.sub_apply] using
    (hg.sub hq).const_mul (((1 + e) / 11 : ℝ) : ℂ)

theorem d028900 (axis : Bool) {e : ℝ} (he : 0 ≤ e) (w : ℂ) :
    DifferentiableOn ℂ (fun z => _root_.GD.N0106.N0428.N0765.N1677.d028897 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z))
      (_root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1677.d028899 axis he hz).differentiableAt.differentiableWithinAt

theorem d028901 {e : ℝ} (he : 0 ≤ e) {z w : ℂ} (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028897 e q w) (_root_.GD.N0106.N0428.N0765.N1677.d028898 true e w z) z :=
  _root_.GD.N0106.N0428.N0765.N1677.d028899 true he hw

theorem d028902 {e : ℝ} (he : 0 ≤ e) {z w : ℂ} (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1677.d028897 e z q) (_root_.GD.N0106.N0428.N0765.N1677.d028898 false e z w) w :=
  _root_.GD.N0106.N0428.N0765.N1677.d028899 false he hw


theorem d028903 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1677.d028883 e (a : ℂ) (b : ℂ) =
      ((e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1677.d028883
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [← _root_.GD.N0106.N0428.N0765.N1672.d021429 he a b 0 0 (by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos)]
  exact _root_.GD.N0106.N0428.N0765.N1527.d021472 he a b


theorem d028904 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1677.d028883 0 (a : ℂ) (b : ℂ) =
      (((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
        (1 - _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) : ℝ) : ℂ) := by
  exact _root_.GD.N0106.N0428.N0765.N1527.d021476 a b

theorem d028905 (e b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1677.d028890 e (b : ℂ) = ((Real.exp b / (1 + e * Real.exp b) : ℝ) : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1677.d028890, ← Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_mul]

theorem d028906 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1677.d028897 e (a : ℂ) (b : ℂ) =
      (((1 + e) / 11 *
        ((Real.exp b / (1 + e * Real.exp b) - 1 / (1 + e)) ^ 2 -
          (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) - 1 / (1 + e)) ^ 2) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1677.d028897, _root_.GD.N0106.N0428.N0765.N1677.d028905, _root_.GD.N0106.N0428.N0765.N1677.d028903 he]
  simp only [_root_.GD.N0106.N0428.N0765.N1677.d028891, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]

theorem d028907 (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1677.d028897 0 (a : ℂ) (b : ℂ) =
      (((1 / 11 : ℝ) * ((Real.exp b - 1) ^ 2 -
        ((11 / 8 : ℝ) * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 /
          (1 - _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1) - 1) ^ 2) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1677.d028897, _root_.GD.N0106.N0428.N0765.N1677.d028905, _root_.GD.N0106.N0428.N0765.N1677.d028904]
  norm_num [_root_.GD.N0106.N0428.N0765.N1677.d028891]

end
end GD.N0106.N0428.N0765.N1677

#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028884
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028886
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028887
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028894
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028899
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028900
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028906
#print axioms _root_.GD.N0106.N0428.N0765.N1677.d028907
