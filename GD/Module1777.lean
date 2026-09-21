import GD.Module1319
import GD.Module1772



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1600
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1680

def d029604 (e : ℝ) (p : ℝ × ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 p).re

theorem d029605 {e : ℝ} (he : 0 ≤ e) (p : ℝ × ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 p).im = 0 := by
  rcases he.eq_or_lt with h | h
  · subst e
    have hlim := (Complex.continuous_im.tendsto (_root_.GD.N0106.N0428.N0765.N1537.d021532 0 0 0 p)).comp
      (_root_.GD.N0106.N0428.N0765.N1537.d021555 0 0 (by simp [_root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos]) p)
    have hzero : Tendsto (fun e : ℝ => (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 p).im) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with e he
      change 0 < e at he
      simp only [_root_.GD.N0106.N0428.N0765.N1680.d021566 he, Complex.ofReal_im]
    exact tendsto_nhds_unique hlim hzero
  · simp only [_root_.GD.N0106.N0428.N0765.N1680.d021566 h, Complex.ofReal_im]

theorem d029606 {e : ℝ} (he : 0 ≤ e) (p : ℝ × ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1600.d029604 e p : ℂ) = _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 p := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, _root_.GD.N0106.N0428.N0765.N1600.d029604]
  · simp only [Complex.ofReal_im, _root_.GD.N0106.N0428.N0765.N1600.d029605 he p]

theorem d029607 {e : ℝ} (he : 0 ≤ e) : Integrable (_root_.GD.N0106.N0428.N0765.N1600.d029604 e) :=
  (_root_.GD.N0106.N0428.N0765.N1537.d021550 he (by simp [_root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos])).re

end
end GD.N0106.N0428.N0765.N1600
#print axioms _root_.GD.N0106.N0428.N0765.N1600.d029606
