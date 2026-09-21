import GD.Module0439
import GD.Module0460







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0106.N0428.N0770.N1702
noncomputable section


theorem d007152 (x : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
  congr 1
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  ring


theorem d007153 (b x : ℝ) : ‖_root_.GD.N0106.N0428.N0770.N1702.d006767 b x‖ ≤ _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x := by
  rw [Real.norm_eq_abs]
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  linarith


theorem d007154 (b x : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1702.d006767 b x = _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x *
      Real.exp (-((b ^ 2 / 2) * (1 / x ^ 2))) := by
  rw [_root_.GD.N0106.N0428.N0770.N1702.d007152, ← Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
  congr 1
  simp only [div_eq_mul_inv]
  ring



theorem d007155 {lo b : ℝ} (hlo : 0 < lo) (hlb : lo ≤ b)
    (x : ℝ) :
    (1 / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x ≤ (1 / (lo ^ 2 / 2)) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x := by
  have hb : 0 < b := lt_of_lt_of_le hlo hlb
  have hcut : lo ^ 2 / 2 ≤ b ^ 2 / 2 := by nlinarith
  have h := _root_.GD.N0106.N0428.N0770.N1744.d007146
    (a := 1 / x ^ 2) (c := lo ^ 2 / 2) (s := b ^ 2 / 2)
    (by positivity) (by positivity) hcut 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  rw [_root_.GD.N0106.N0428.N0770.N1702.d007154]
  calc
    (1 / x ^ 2) * (_root_.GD.N0106.N0428.N0770.N1702.d006767 0 x * Real.exp (-((b ^ 2 / 2) * (1 / x ^ 2)))) =
        ((1 / x ^ 2) * Real.exp (-((b ^ 2 / 2) * (1 / x ^ 2)))) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x := by ring
    _ ≤ (1 / (lo ^ 2 / 2)) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le



theorem d007156 {lo hi b : ℝ}
    (hlo : 0 < lo) (hlb : lo ≤ b) (hbh : b ≤ hi) (x : ℝ) :
    ‖-(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x‖ ≤
      (hi * (1 / (lo ^ 2 / 2))) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x := by
  have hb : 0 < b := lt_of_lt_of_le hlo hlb
  have hx : 0 ≤ (1 / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by unfold _root_.GD.N0106.N0428.N0770.N1702.d006767; positivity
  have hnorm : ‖-(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x‖ =
      b * ((1 / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) := by
    have hk : 0 < _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by unfold _root_.GD.N0106.N0428.N0770.N1702.d006767; exact Real.exp_pos _
    rw [norm_mul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hb.le (sq_nonneg x)), Real.norm_eq_abs, abs_of_pos hk]
    ring
  rw [hnorm]
  calc
    b * ((1 / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) ≤
        hi * ((1 / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) := mul_le_mul_of_nonneg_right hbh hx
    _ ≤ hi * ((1 / (lo ^ 2 / 2)) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0770.N1702.d007155 hlo hlb x)
        (le_trans hb.le hbh)
    _ = _ := by ring



theorem d007157 (b x : ℝ) :
    HasDerivAt (fun u : ℝ => _root_.GD.N0106.N0428.N0770.N1702.d006767 u x) (-(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) b := by
  have hd := (((((hasDerivAt_pow 2 b).div_const (x ^ 2)).const_add (x ^ 2)).neg.div_const 2).exp)
  refine hd.congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
  norm_num
  ring



theorem d007158 {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => -(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) (Ioi 0) ∧
    HasDerivAt (fun u : ℝ => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 u x)
      (∫ x in Ioi 0, -(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) b := by
  have hs : Ioo (b / 2) (2 * b) ∈ 𝓝 b :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hm : ∀ᶠ u in 𝓝 b,
      AEStronglyMeasurable (_root_.GD.N0106.N0428.N0770.N1702.d006767 u) (volume.restrict (Ioi 0)) := by
    filter_upwards with u
    unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
    fun_prop
  have hdm : AEStronglyMeasurable (fun x => -(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x)
      (volume.restrict (Ioi 0)) := by unfold _root_.GD.N0106.N0428.N0770.N1702.d006767; fun_prop
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ Ioo (b / 2) (2 * b),
      ‖-(u / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 u x‖ ≤
        (2 * b * (1 / ((b / 2) ^ 2 / 2))) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x := by
    filter_upwards with x u hu
    exact _root_.GD.N0106.N0428.N0770.N1702.d007156 (by positivity) hu.1.le hu.2.le x
  have hi : Integrable (fun x =>
      (2 * b * (1 / ((b / 2) ^ 2 / 2))) * _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x)
      (volume.restrict (Ioi 0)) := (_root_.GD.N0106.N0428.N0770.N1702.d006770 0).const_mul _
  have hd : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ u ∈ Ioo (b / 2) (2 * b),
      HasDerivAt (fun v : ℝ => _root_.GD.N0106.N0428.N0770.N1702.d006767 v x) (-(u / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 u x) u := by
    filter_upwards with x u _
    exact _root_.GD.N0106.N0428.N0770.N1702.d007157 u x
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm
    (_root_.GD.N0106.N0428.N0770.N1702.d006770 b) hdm hbound hi hd



theorem d007159 {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun u : ℝ => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 u x)
      (-(∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x)) b := by
  have hd := (_root_.GD.N0106.N0428.N0770.N1702.d007158 hb).2
  have hneg : (∫ x in Ioi 0, -(b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) =
      -(∫ x in Ioi 0, (b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) := by
    simp only [neg_mul, integral_neg]
  rw [hneg, (_root_.GD.N0106.N0428.N0770.N1702.d006779 hb).2] at hd
  exact hd



theorem d007160 (b : ℝ) :
    ContinuousAt (fun u : ℝ => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 u x) b := by
  apply continuousAt_of_dominated (bound := _root_.GD.N0106.N0428.N0770.N1702.d006767 0)
  · filter_upwards with u
    unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
    fun_prop
  · filter_upwards with u
    exact ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1702.d007153 u)
  · exact _root_.GD.N0106.N0428.N0770.N1702.d006770 0
  · filter_upwards with x
    unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
    fun_prop


theorem d007161 :
    (∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 0 x) = Real.sqrt (Real.pi / 2) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1702.d007152]
  rw [integral_gaussian_Ioi]
  rw [show Real.pi / (1 / 2 : ℝ) = 4 * (Real.pi / 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num



theorem d007162 :
    Tendsto (fun b : ℝ => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) (𝓝 0)
      (𝓝 (Real.sqrt (Real.pi / 2))) := by
  simpa only [_root_.GD.N0106.N0428.N0770.N1702.d007161] using (_root_.GD.N0106.N0428.N0770.N1702.d007160 0).tendsto

end
end GD.N0106.N0428.N0770.N1702

#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007152
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007153
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007154
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007155
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007156
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007157
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007158
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007159
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007160
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007161
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d007162
