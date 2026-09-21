import GD.Module1312
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1591
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1526

def d021497 (e x : ℝ) (z w : ℂ) : ℂ :=
  (Complex.exp w * (1 - (x : ℂ)) + (x : ℂ)) *
    ((1 - (x : ℂ)) + (e : ℂ) * (x : ℂ)) +
  (1 + (e : ℂ)) * Complex.exp z * (1 + Complex.exp w) *
    (x : ℂ) * (1 - (x : ℂ))

def d021498 (e x : ℝ) (z w : ℂ) : ℂ :=
  (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ) *
    _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w ^ (-((21 : ℂ) / 2))

def d021499 (e x : ℝ) (z w : ℂ) : ℂ :=
  (1 + (e : ℂ)) * Complex.exp z * (1 + Complex.exp w) *
    (x : ℂ) * (1 - (x : ℂ))

def d021500 (e x : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp w * (1 - (x : ℂ)) * ((1 - (x : ℂ)) + (e : ℂ) * (x : ℂ)) +
    (1 + (e : ℂ)) * Complex.exp z * Complex.exp w * (x : ℂ) * (1 - (x : ℂ))

theorem d021501 (e x : ℝ) (z w : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e z.re w.re z.im w.im x = _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021418 _root_.GD.N0106.N0428.N0765.N1591.d021497
  rw [Complex.re_add_im z, Complex.re_add_im w]

theorem d021502 (e x : ℝ) (z w : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1672.d021422 e z.re w.re z.im w.im x = _root_.GD.N0106.N0428.N0765.N1591.d021498 e x z w := by
  unfold _root_.GD.N0106.N0428.N0765.N1672.d021422 _root_.GD.N0106.N0428.N0765.N1591.d021498
  rw [_root_.GD.N0106.N0428.N0765.N1591.d021501]

theorem d021503 (e x : ℝ) (z w : ℂ) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1591.d021497 e x q w) (_root_.GD.N0106.N0428.N0765.N1591.d021499 e x z w) z := by
  unfold _root_.GD.N0106.N0428.N0765.N1591.d021497 _root_.GD.N0106.N0428.N0765.N1591.d021499
  exact (((((Complex.hasDerivAt_exp z).const_mul (1 + (e : ℂ))).mul_const
    (1 + Complex.exp w)).mul_const (x : ℂ)).mul_const (1 - (x : ℂ))).const_add _

theorem d021504 (e x : ℝ) (z w : ℂ) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z q) (_root_.GD.N0106.N0428.N0765.N1591.d021500 e x z w) w := by
  unfold _root_.GD.N0106.N0428.N0765.N1591.d021497 _root_.GD.N0106.N0428.N0765.N1591.d021500
  have h1 := (((Complex.hasDerivAt_exp w).mul_const (1 - (x : ℂ))).add_const
    (x : ℂ)).mul_const ((1 - (x : ℂ)) + (e : ℂ) * (x : ℂ))
  have h2 := (((((Complex.hasDerivAt_exp w).const_add 1).const_mul
    ((1 + (e : ℂ)) * Complex.exp z)).mul_const (x : ℂ)).mul_const (1 - (x : ℂ)))
  exact h1.add h2

theorem d021505 {e x : ℝ} (he : 0 ≤ e) (hx : x ∈ Ioo (0 : ℝ) 1)
    {z w : ℂ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w ∈ Complex.slitPlane := by
  rw [← _root_.GD.N0106.N0428.N0765.N1591.d021501]
  exact _root_.GD.N0106.N0428.N0765.N1526.d021446 he (Ioo_subset_Icc_self hx)
    ((sub_pos.mpr hx.2).trans_le (_root_.GD.N0106.N0428.N0765.N1526.d021436 he (Ioo_subset_Icc_self hx)))
    z.re w.re z.im w.im hw

def d021506 (e x : ℝ) (z w : ℂ) : ℂ :=
  (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ) *
    ((-((21 : ℂ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w) ^ (-((21 : ℂ) / 2) - 1) * _root_.GD.N0106.N0428.N0765.N1591.d021499 e x z w)

def d021507 (e x : ℝ) (z w : ℂ) : ℂ :=
  (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ) *
    ((-((21 : ℂ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w) ^ (-((21 : ℂ) / 2) - 1) * _root_.GD.N0106.N0428.N0765.N1591.d021500 e x z w)

theorem d021508 {e x : ℝ} (he : 0 ≤ e) (hx : x ∈ Ioo (0 : ℝ) 1)
    {z w : ℂ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1591.d021498 e x q w) (_root_.GD.N0106.N0428.N0765.N1591.d021506 e x z w) z := by
  exact ((_root_.GD.N0106.N0428.N0765.N1591.d021503 e x z w).cpow_const (_root_.GD.N0106.N0428.N0765.N1591.d021505 he hx hw)).const_mul _

theorem d021509 {e x : ℝ} (he : 0 ≤ e) (hx : x ∈ Ioo (0 : ℝ) 1)
    {z w : ℂ} (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1591.d021498 e x z q) (_root_.GD.N0106.N0428.N0765.N1591.d021507 e x z w) w := by
  exact ((_root_.GD.N0106.N0428.N0765.N1591.d021504 e x z w).cpow_const (_root_.GD.N0106.N0428.N0765.N1591.d021505 he hx hw)).const_mul _

end
end GD.N0106.N0428.N0765.N1591

#print axioms _root_.GD.N0106.N0428.N0765.N1591.d021508
#print axioms _root_.GD.N0106.N0428.N0765.N1591.d021509
