import GD.Module1770
import GD.Module1760
import GD.Module0467
import GD.Module1769



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1594
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1595 _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1602
open _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1589


theorem d029340 (e β xi : ℝ) (z : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1595.d029326 e β xi z = 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e z.im β (z.re,y)) xi := by
  rw [_root_.GD.N0106.N0428.N0765.N1595.d029326, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [_root_.GD.N0106.N0428.N0765.N1595.d029324, _root_.GD.N0106.N0428.N0765.N1595.d029328, smul_eq_mul]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1595.d029323
  congr 1
  push_cast
  ring

theorem d029341 {e β xi : ℝ} (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1595.d029334 β) : Integrable (_root_.GD.N0106.N0428.N0765.N1595.d029324 e β xi z) := by
  exact ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3)).const_mul
    (_root_.GD.N0106.N0428.N0765.N1595.d029335 β z)).mono' (_root_.GD.N0106.N0428.N0765.N1595.d029329 e β xi z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => _root_.GD.N0106.N0428.N0765.N1595.d029338 he hz y)


theorem d029342 {e β xi : ℝ} (he : 0 ≤ e) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1595.d029334 β) :
    ‖_root_.GD.N0106.N0428.N0765.N1595.d029326 e β xi z‖ ≤ _root_.GD.N0106.N0428.N0765.N1595.d029335 β z * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
  calc ‖_root_.GD.N0106.N0428.N0765.N1595.d029326 e β xi z‖ ≤ ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1595.d029324 e β xi z y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1595.d029335 β z * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := integral_mono_ae
      (_root_.GD.N0106.N0428.N0765.N1594.d029341 he hz).norm
      ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3)).const_mul _)
      (Filter.Eventually.of_forall fun y => _root_.GD.N0106.N0428.N0765.N1595.d029338 he hz y)
    _ = _root_.GD.N0106.N0428.N0765.N1595.d029335 β z * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := integral_const_mul _ _


theorem d029343 {e dA dB : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) {z : ℂ} (hz : |z.im| ≤ dA) (xi : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 xi z‖ ≤ Real.exp (-2*Real.pi*dB*|xi|) *
      ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e z.im (if 0 ≤ xi then -dB else dB) (z.re,y)‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1594.d029340]
  exact _root_.GD.N0106.N0428.N0765.N1589.d029322 he hdA hdB hd hz z.re xi

end
end GD.N0106.N0428.N0765.N1594
#print axioms _root_.GD.N0106.N0428.N0765.N1594.d029340
#print axioms _root_.GD.N0106.N0428.N0765.N1594.d029342
#print axioms _root_.GD.N0106.N0428.N0765.N1594.d029343
