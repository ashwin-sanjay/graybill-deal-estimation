import GD.Module1765
import GD.Module1766
import GD.Module1773
import GD.Module1774
import GD.Module1777
import GD.Module0383





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Topology
open scoped FourierTransform BigOperators
namespace GD.N0106.N0428.N0765.N1598
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1653 _root_.GD.N0106.N0428.N0765.N1597 _root_.GD.N0106.N0428.N0765.N1596
open _root_.GD.N0106.N0428.N0765.N1600 _root_.GD.N0106.N0428.N0765.N1537

theorem d029608 {e h d0 d1 : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ)/2)*d0 < Real.pi)
    (hmixed : ((21 : ℝ)/2)*(d1+d1) < Real.pi) (x y : ℝ) :
    |(∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e (a,b)) -
      h^2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e (x+h*p.1,y+h*p.2))| ≤
      (2*_root_.GD.N0106.N0428.N0765.N1597.d029348 d0 0+2*_root_.GD.N0106.N0428.N0765.N1597.d029348 0 d0) /
        (Real.exp (2*Real.pi*d0/h)-1) +
      4*_root_.GD.N0106.N0428.N0765.N1597.d029348 d1 d1 / (Real.exp (2*Real.pi*d1/h)-1)^2 := by
  have heq : (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1600.d029604 e p : ℂ)) = _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 := by
    funext p
    exact _root_.GD.N0106.N0428.N0765.N1600.d029606 he p
  have hsmall : ((21 : ℝ)/2)*d1 < Real.pi := by nlinarith
  refine _root_.GD.N0106.N0428.N0765.N1653.d005827 hh hd0 hd1 ?_ ?_ x y ?_ ?_ ?_ ?_ ?_ ?_
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1596.d029358 he hh hd1 hsmall
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1596.d029359 he hh hd1 hmixed
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1596.d029361 he hh x y
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1596.d029362 he hh hd1 hsmall x
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1596.d029363 he hh hd1 hmixed
  · intro m _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1597.d029350 he hd0.le (le_refl (0 : ℝ))
      (by simpa only [add_zero] using haxis) (m/h) 0
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using hb
  · intro n _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1597.d029350 he (le_refl (0 : ℝ)) hd0.le
      (by simpa only [zero_add] using haxis) 0 (n/h)
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using hb
  · intro m n _ _
    rw [heq]
    simpa only [_root_.GD.N0106.N0428.N0765.N1596.d029356 hh] using _root_.GD.N0106.N0428.N0765.N1597.d029350 he hd1.le hd1.le hmixed (m/h) (n/h)



theorem d029609 {e : ℝ} (he : 0 ≤ e) :
    (_root_.GD.N0106.N0428.N0765.N1680.d021557 e 0 0).re =
      ((1+e)/11) * ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e (a,b) := by
  have heq : (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1600.d029604 e p : ℂ)) = _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 := by
    funext p
    exact _root_.GD.N0106.N0428.N0765.N1600.d029606 he p
  have hc : _root_.GD.N0106.N0428.N0765.N1680.d021557 e 0 0 =
      ((((1+e)/11) * ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e p : ℝ) : ℂ) := by
    unfold _root_.GD.N0106.N0428.N0765.N1680.d021557
    rw [← heq, integral_complex_ofReal, ← Complex.ofReal_mul]
  rw [hc, Complex.ofReal_re]
  congr 1
  exact integral_prod _ (_root_.GD.N0106.N0428.N0765.N1600.d029607 he)


theorem d029610 {e h d0 d1 : ℝ} (he : 0 ≤ e) (hh : 0 < h)
    (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ)/2)*d0 < Real.pi)
    (hmixed : ((21 : ℝ)/2)*(d1+d1) < Real.pi) (x y : ℝ) :
    |(_root_.GD.N0106.N0428.N0765.N1680.d021557 e 0 0).re -
      ((1+e)/11) * (h^2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e (x+h*p.1,y+h*p.2)))| ≤
      ((1+e)/11) * ((2*_root_.GD.N0106.N0428.N0765.N1597.d029348 d0 0+2*_root_.GD.N0106.N0428.N0765.N1597.d029348 0 d0) /
        (Real.exp (2*Real.pi*d0/h)-1) +
      4*_root_.GD.N0106.N0428.N0765.N1597.d029348 d1 d1 / (Real.exp (2*Real.pi*d1/h)-1)^2) := by
  rw [_root_.GD.N0106.N0428.N0765.N1598.d029609 he, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (1+e)/11)]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1598.d029608 he hh hd0 hd1 haxis hmixed x y)
    (by positivity)

end
end GD.N0106.N0428.N0765.N1598
#print axioms _root_.GD.N0106.N0428.N0765.N1598.d029608

#print axioms _root_.GD.N0106.N0428.N0765.N1598.d029610
