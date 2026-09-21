import GD.Module1739
import GD.Module1779
import GD.Module1314
import Mathlib.MeasureTheory.Group.Integral



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1667
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670 _root_.GD.N0106.N0428.N0765.N1665 _root_.GD.N0106.N0428.N0765.N1534

def d029622 (e u v w : ℝ) : ℝ := (∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028857 e u v w c) / ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028856 e u v w c

theorem d029623 {f g : ℝ → ℝ} (s t : ℝ)
    (hf : ∀ c, f (t+c) = s*g c) : (∫ c, f c) = s*∫ c, g c := by
  have hi := integral_add_left_eq_self (μ := volume) f t
  simp_rw [hf] at hi
  rw [integral_const_mul] at hi
  exact hi.symm

theorem d029624 {e u v w : ℝ} (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) : 0 < _root_.GD.N0106.N0428.N0765.N1667.d029622 e u v w :=
  div_pos
    (_root_.GD.N0106.N0428.N0765.N1665.d029616 (a := 13/2) (p := 21/2) (n := 9)
      (by norm_num) (by norm_num) (by norm_num) he hu hv hw)
    (_root_.GD.N0106.N0428.N0765.N1665.d029616 (a := 11/2) (p := 21/2) (n := 10)
      (by norm_num) (by norm_num) (by norm_num) he hu hv hw)

theorem d029625 {e u v w : ℝ} (he : 0 < e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) : e⁻¹*_root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ u v w = _root_.GD.N0106.N0428.N0765.N1667.d029622 e u v w := by
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020964 (inv_pos.mpr he) hu hv hw,
    _root_.GD.N0106.N0428.N0765.N1667.d029623 _ _ (_root_.GD.N0106.N0428.N0765.N1670.d028870 he u v w),
    _root_.GD.N0106.N0428.N0765.N1667.d029623 _ _ (_root_.GD.N0106.N0428.N0765.N1670.d028871 he u v w)]
  have hs : Real.exp (13*Real.log e/2) = e*Real.exp (11*Real.log e/2) := by
    rw [show 13*Real.log e/2 = Real.log e + 11*Real.log e/2 by ring,
      Real.exp_add, Real.exp_log he]
  rw [hs]
  unfold _root_.GD.N0106.N0428.N0765.N1667.d029622
  field_simp

theorem d029626 {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1667.d029622 e u v w) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1667.d029622 0 u v w)) := by
  exact (_root_.GD.N0106.N0428.N0765.N1665.d029620 (a := 13/2) (p := 21/2) (n := 9)
    (by norm_num) (by norm_num) (by norm_num) hu hv hw).div
    (_root_.GD.N0106.N0428.N0765.N1665.d029620 (a := 11/2) (p := 21/2) (n := 10)
      (by norm_num) (by norm_num) (by norm_num) hu hv hw)
    (_root_.GD.N0106.N0428.N0765.N1665.d029616 (a := 11/2) (p := 21/2) (n := 10)
      (by norm_num) (by norm_num) (by norm_num) (e := 0) le_rfl hu hv hw).ne'

theorem d029627 {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1667.d029622 0 u v w = (11/8 : ℝ)*v/(u+w) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1673.d005866 hu hv hw).comp tendsto_inv_nhdsGT_zero
  apply tendsto_nhds_unique (_root_.GD.N0106.N0428.N0765.N1667.d029626 hu hv hw)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  exact _root_.GD.N0106.N0428.N0765.N1667.d029625 he hu hv hw


theorem d029628 {e : ℝ} (he : 0 ≤ e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b 0 0 / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b 0 0 =
      (_root_.GD.N0106.N0428.N0765.N1667.d029622 e (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 0)
        (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 1) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a,b) 2) : ℂ) := by
  obtain ⟨hu,hv,hw⟩ := _root_.GD.N0106.N0428.N0765.N1527.d021473 a b
  rcases eq_or_lt_of_le he with heq | hepos
  · subst e
    rw [_root_.GD.N0106.N0428.N0765.N1527.d021475, _root_.GD.N0106.N0428.N0765.N1667.d029627 hu hv hw]
  · rw [← _root_.GD.N0106.N0428.N0765.N1672.d021429 hepos a b 0 0
      (by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos),
      _root_.GD.N0106.N0428.N0765.N1527.d021472 hepos a b]
    congr 1
    exact _root_.GD.N0106.N0428.N0765.N1667.d029625 hepos hu hv hw

end
end GD.N0106.N0428.N0765.N1667
#print axioms _root_.GD.N0106.N0428.N0765.N1667.d029628
#print axioms _root_.GD.N0106.N0428.N0765.N1667.d029627
