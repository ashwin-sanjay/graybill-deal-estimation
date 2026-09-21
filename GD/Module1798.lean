import GD.Module1778
import GD.Module1797



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter Topology Finset
open scoped BigOperators
namespace GD.N0106.N0428.N0765.N1588
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1598 _root_.GD.N0106.N0428.N0765.N1597 _root_.GD.N0106.N0428.N0765.N1600
open _root_.GD.N0106.N0428.N0765.N1678 _root_.GD.N0106.N0428.N0765.N1676 _root_.GD.N0106.N0428.N0765.N1629 _root_.GD.N0106.N0428.N0765.N1687

def d029951 (e h x y : ℝ) (NA NB : ℕ) : ℝ :=
  (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p).re

def d029952 (h d0 d1 : ℝ) : ℝ :=
  (2*_root_.GD.N0106.N0428.N0765.N1597.d029348 d0 0+2*_root_.GD.N0106.N0428.N0765.N1597.d029348 0 d0) /
    (Real.exp (2*Real.pi*d0/h)-1) +
  4*_root_.GD.N0106.N0428.N0765.N1597.d029348 d1 d1 / (Real.exp (2*Real.pi*d1/h)-1)^2

theorem d029953 {e : ℝ} (he : 0 ≤ e) (h x y : ℝ) (p : ℤ × ℤ) :
    _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p =
      ((((1+e)/11) * (h^2 * _root_.GD.N0106.N0428.N0765.N1600.d029604 e (x+h*p.1,y+h*p.2)) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1678.d029922, _root_.GD.N0106.N0428.N0765.N1676.d028932]
  have hp : (x+(p.1 : ℝ)*h,y+(p.2 : ℝ)*h) = (x+h*p.1,y+h*p.2) := by
    apply Prod.ext <;> dsimp <;> ring
  rw [hp, ← _root_.GD.N0106.N0428.N0765.N1600.d029606 he]
  push_cast
  ring

theorem d029954 {e : ℝ} (he : 0 ≤ e) (h x y : ℝ) :
    (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p).re =
      ((1+e)/11) * (h^2 * ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1600.d029604 e (x+h*p.1,y+h*p.2)) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1588.d029953 he]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [tsum_mul_left, tsum_mul_left]

theorem d029955 {e E h d0 d1 : ℝ} (he : 0 ≤ e) (heE : e ≤ E)
    (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ)/2)*d0 < Real.pi)
    (hmixed : ((21 : ℝ)/2)*(d1+d1) < Real.pi)
    (x y : ℝ) (NA NB : ℕ) (kA kB : ℤ) :
    |(_root_.GD.N0106.N0428.N0765.N1680.d021557 e 0 0).re - _root_.GD.N0106.N0428.N0765.N1588.d029951 e h x y NA NB| ≤
      ((1+e)/11)*_root_.GD.N0106.N0428.N0765.N1588.d029952 h d0 d1 +
        _root_.GD.N0106.N0428.N0765.N1678.d029932 E 0 0 h h x y NA NB kA kB := by
  have hp := _root_.GD.N0106.N0428.N0765.N1598.d029610 he hh hd0 hd1 haxis hmixed x y
  rw [← _root_.GD.N0106.N0428.N0765.N1588.d029954 he] at hp
  have hf := _root_.GD.N0106.N0428.N0765.N1678.d029947 (α := 0) (β := 0) he heE hh hh
    (by simp [_root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos]) x y NA NB kA kB
  have hr := Complex.abs_re_le_norm
    ((∑' p, _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p)
  simp only [Complex.sub_re] at hr
  exact (abs_sub_le _ (∑' p, _root_.GD.N0106.N0428.N0765.N1678.d029922 e 0 0 h h x y p).re _).trans
    (add_le_add hp (hr.trans hf))

end
end GD.N0106.N0428.N0765.N1588
#print axioms _root_.GD.N0106.N0428.N0765.N1588.d029955
