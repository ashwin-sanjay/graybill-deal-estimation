import GD.Module1530
import GD.Module1426
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0088
noncomputable section
open _root_.GD.N0051

def d023931 (r : ℝ) (u : _root_.GD.N0051.d023832) : ℝ :=
  2 ^ r * (u.2.2 + _root_.GD.N0051.d022793 r u.1 * (u.2.1 ^ (-r) * u.2.2))

theorem d023932 {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 ≤ r) (hra : r < a) :
    Integrable (_root_.GD.N0088.d023931 r) (_root_.GD.N0051.d023833 a b) := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  have hy : Integrable (fun y : ℝ => y) (gammaMeasure b b) := by
    simpa only [Real.rpow_one] using _root_.GD.N0051.d022782 hb hb
      (show 0 < b + 1 by linarith)
  have hx : Integrable (fun x : ℝ => x ^ (-r)) (gammaMeasure a a) :=
    _root_.GD.N0051.d022782 ha ha (by linarith)
  exact ((hy.comp_snd (gammaMeasure a a)).comp_snd _root_.GD.N0051.d022792 |>.add
    ((_root_.GD.N0051.d022797 hr).mul_prod (hx.mul_prod hy))).const_mul _

theorem d023933 {p q w : ℝ} (hq : 0 < q)
    (hw : 0 < w) (hw1 : w ≤ 1) (hr : 0 ≤ p / q)
    (u : _root_.GD.N0051.d023832) (hx : 0 < u.2.1) (hy : 0 < u.2.2) :
    (_root_.GD.N0051.d022763 p q u.1.1 (Real.sqrt w * u.1.2) u.2.1 (w * u.2.2) -
      Real.sqrt w * u.1.2) ^ 2 / w ≤ _root_.GD.N0088.d023931 (p / q) u := by
  have hsel := _root_.GD.N0051.d022770 (p := p) hq hx (mul_pos hw hy)
    (y := u.1.1) (z := Real.sqrt w * u.1.2)
  have he := _root_.GD.N0051.d022786 (v := w) (w := 1) (x := u.2.2)
    (y := u.2.1) (d := Real.sqrt w * u.1.2 - u.1.1) hw (by norm_num) hy hx hr
  simp only [one_mul, div_one] at he
  have hg := _root_.GD.N0051.d022799 hw (by norm_num : (0 : ℝ) < 1) hw1 hr
    (u.1.2, u.1.1)
  simp only [Real.sqrt_one, one_mul, div_one] at hg
  have hg' : ((Real.sqrt w * u.1.2 - u.1.1) ^ 2) ^ (p / q) ≤
      _root_.GD.N0051.d022793 (p / q) u.1 := by
    simpa only [sub_sq_comm, _root_.GD.N0051.d022793, add_comm] using hg
  apply (div_le_iff₀ hw).mpr
  calc
    _ ≤ (w * u.2.2) * (1 + (Real.sqrt w * u.1.2 - u.1.1) ^ 2 / u.2.1) ^ (p / q) := hsel
    _ ≤ w * 2 ^ (p / q) *
        (u.2.2 + ((Real.sqrt w * u.1.2 - u.1.1) ^ 2) ^ (p / q) *
          (u.2.2 * u.2.1 ^ (-(p / q)))) := he
    _ ≤ w * 2 ^ (p / q) *
        (u.2.2 + _root_.GD.N0051.d022793 (p / q) u.1 *
          (u.2.2 * u.2.1 ^ (-(p / q)))) := by gcongr
    _ = _ := by unfold _root_.GD.N0088.d023931; ring

theorem d023934 {p q x y z₁ z₂ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hz : z₁ ≠ 0) :
    ∀ᶠ w in 𝓝[>] (0 : ℝ),
      _root_.GD.N0051.d022763 p q z₁ (Real.sqrt w * z₂) x (w * y) = Real.sqrt w * z₂ := by
  have hd : Tendsto (fun w : ℝ => Real.sqrt w * z₂ - z₁)
      (𝓝[>] 0) (𝓝 (-z₁)) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
      |>.mul_const z₂).sub_const z₁
  have hleft : Tendsto (fun w : ℝ => _root_.GD.N0051.d022762 x (Real.sqrt w * z₂ - z₁) ^ p)
      (𝓝[>] 0) (𝓝 (_root_.GD.N0051.d022762 x (-z₁) ^ p)) := by
    apply Tendsto.rpow_const _ (Or.inr hp.le)
    unfold _root_.GD.N0051.d022762
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (hd.pow 2)) (by positivity)
  have hright : Tendsto (fun w : ℝ => _root_.GD.N0051.d022762 (w * y) (Real.sqrt w * z₂ - z₁) ^ q)
      (𝓝[>] 0) (𝓝 0) := by
    apply Tendsto.rpow_const_nhds_zero _ hq
    unfold _root_.GD.N0051.d022762
    simpa only [Pi.div_def, id_eq, zero_mul, zero_add, zero_div] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const y).div
      (((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const y).add (hd.pow 2))
      (by simpa using pow_ne_zero 2 (neg_ne_zero.mpr hz))
  filter_upwards [hright.eventually_lt hleft
    (Real.rpow_pos_of_pos (_root_.GD.N0051.d022764 hx) _)] with w hw
  exact if_neg (not_le.mpr hw)

#print axioms _root_.GD.N0088.d023932
#print axioms _root_.GD.N0088.d023933
#print axioms _root_.GD.N0088.d023934
end
end GD.N0088
