import GD.Module1739
import GD.Module1779
import GD.Module1293
import Mathlib.MeasureTheory.Group.Integral



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1668
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670 _root_.GD.N0106.N0428.N0765.N1665

def d029629 (d h : ℝ) : ℝ :=
  2*(Real.cos d)^(-21/2 : ℝ)/(Real.exp (2*Real.pi*d/h)-1)

theorem d029630 {f g : ℝ → ℝ} {s t h x eps : ℝ}
    (hs : 0 < s) (hf : ∀ c, f (t+c) = s*g c)
    (herr : |h*(∑' k : ℤ, f ((t+x)+h*k)) - ∫ c, f c| ≤ eps*∫ c, f c) :
    |h*(∑' k : ℤ, g (x+h*k)) - ∫ c, g c| ≤ eps*∫ c, g c := by
  have hi := integral_add_left_eq_self (μ := volume) f t
  simp_rw [hf] at hi
  rw [integral_const_mul] at hi
  have hgrid (k : ℤ) : f ((t+x)+h*k) = s*g (x+h*k) := by
    rw [add_assoc]
    exact hf _
  simp_rw [hgrid] at herr
  rw [tsum_mul_left, ← hi] at herr
  have heq : h*(s*∑' k : ℤ, g (x+h*k)) - s*(∫ c, g c) =
      s*(h*(∑' k : ℤ, g (x+h*k)) - ∫ c, g c) := by ring
  rw [heq, abs_mul, abs_of_pos hs] at herr
  exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith only [herr])

theorem d029631 {e u v w d h : ℝ}
    (he : 0 < e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h) (offset : ℝ) :
    |h*(∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w (offset+h*k)) - ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c| ≤
      _root_.GD.N0106.N0428.N0765.N1668.d029629 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c :=
  _root_.GD.N0106.N0428.N0765.N1668.d029630 (Real.exp_pos _) (_root_.GD.N0106.N0428.N0765.N1670.d028870 he u v w)
    (_root_.GD.N0106.N0428.N0765.N1561.d021034 (inv_pos.mpr he) hu hv hw hd hdpi hh
      (Real.log e+offset))

theorem d029632 {e u v w d h : ℝ}
    (he : 0 < e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h) (offset : ℝ) :
    |h*(∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w (offset+h*k)) - ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c| ≤
      _root_.GD.N0106.N0428.N0765.N1668.d029629 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c :=
  _root_.GD.N0106.N0428.N0765.N1668.d029630 (Real.exp_pos _) (_root_.GD.N0106.N0428.N0765.N1670.d028871 he u v w)
    (_root_.GD.N0106.N0428.N0765.N1561.d021035 (inv_pos.mpr he) hu hv hw hd hdpi hh
      (Real.log e+offset))



theorem d029633 {e u v w d h : ℝ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h) (offset : ℝ) :
    |h*(∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w (offset+h*k)) - ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c| ≤
      _root_.GD.N0106.N0428.N0765.N1668.d029629 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c := by
  rcases eq_or_lt_of_le he with heq | hepos
  · subst e
    have hi := _root_.GD.N0106.N0428.N0765.N1665.d029620 (a := 11/2) (p := 21/2) (n := 10)
      (by norm_num) (by norm_num) (by norm_num) hu hv hw
    have hs := _root_.GD.N0106.N0428.N0765.N1665.d029621 (a := 11/2) (p := 21/2) (n := 10)
      (by norm_num) (by norm_num) (by norm_num) hu hv hw hh offset
    apply le_of_tendsto_of_tendsto ((hs.const_mul h).sub hi).abs (hi.const_mul (_root_.GD.N0106.N0428.N0765.N1668.d029629 d h))
    filter_upwards [self_mem_nhdsWithin] with e he
    exact _root_.GD.N0106.N0428.N0765.N1668.d029631 he hu hv hw hd hdpi hh offset
  · exact _root_.GD.N0106.N0428.N0765.N1668.d029631 hepos hu hv hw hd hdpi hh offset

theorem d029634 {e u v w d h : ℝ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi/2) (hh : 0 < h) (offset : ℝ) :
    |h*(∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w (offset+h*k)) - ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c| ≤
      _root_.GD.N0106.N0428.N0765.N1668.d029629 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c := by
  rcases eq_or_lt_of_le he with heq | hepos
  · subst e
    have hi := _root_.GD.N0106.N0428.N0765.N1665.d029620 (a := 13/2) (p := 21/2) (n := 9)
      (by norm_num) (by norm_num) (by norm_num) hu hv hw
    have hs := _root_.GD.N0106.N0428.N0765.N1665.d029621 (a := 13/2) (p := 21/2) (n := 9)
      (by norm_num) (by norm_num) (by norm_num) hu hv hw hh offset
    apply le_of_tendsto_of_tendsto ((hs.const_mul h).sub hi).abs (hi.const_mul (_root_.GD.N0106.N0428.N0765.N1668.d029629 d h))
    filter_upwards [self_mem_nhdsWithin] with e he
    exact _root_.GD.N0106.N0428.N0765.N1668.d029632 he hu hv hw hd hdpi hh offset
  · exact _root_.GD.N0106.N0428.N0765.N1668.d029632 hepos hu hv hw hd hdpi hh offset

end
end GD.N0106.N0428.N0765.N1668
#print axioms _root_.GD.N0106.N0428.N0765.N1668.d029633
#print axioms _root_.GD.N0106.N0428.N0765.N1668.d029634
