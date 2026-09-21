import GD.Module0531
import GD.Module0535
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0221
noncomputable section
open _root_.GD.N0208.N0455
open _root_.GD.N0208.N0456
open _root_.GD.N0213.N0493



theorem d008100 (f : ℝ → ℝ) (hf : Measurable f)
    (heven : ∀ x, f (-x) = f x) (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ, k (v + w) * ENNReal.ofReal ((f v - f w) ^ 2)) =
      ∫⁻ a : ℝ, k a * ∫⁻ v : ℝ, ENNReal.ofReal ((f (v - a) - f v) ^ 2) := by
  have hinner (v : ℝ) :
      (∫⁻ w : ℝ, k (v + w) * ENNReal.ofReal ((f v - f w) ^ 2)) =
        ∫⁻ a : ℝ, k a * ENNReal.ofReal ((f (v - a) - f v) ^ 2) := by
    calc
      _ = ∫⁻ a : ℝ, k (v + (a - v)) * ENNReal.ofReal ((f v - f (a - v)) ^ 2) :=
        (lintegral_sub_right_eq_self
          (fun w => k (v + w) * ENNReal.ofReal ((f v - f w) ^ 2)) v).symm
      _ = _ := by
        apply lintegral_congr
        intro a
        rw [show v + (a - v) = a by ring, show a - v = -(v - a) by ring,
          heven (v - a), sub_sq_comm]
  simp_rw [hinner]
  have hm : Measurable (fun p : ℝ × ℝ =>
      k p.2 * ENNReal.ofReal ((f (p.1 - p.2) - f p.1) ^ 2)) := by fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro a
  exact lintegral_const_mul _ (by fun_prop)

theorem d008101 (N : ℝ) (hN : 0 < N)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ,
      k (v + w) * ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (8 / N) * ∫⁻ a : ℝ, k a * ENNReal.ofReal (a ^ 2) := by
  rw [_root_.GD.N0221.d008100 (_root_.GD.N0208.N0455.d007937 N) (_root_.GD.N0208.N0455.d007938 N)
    (_root_.GD.N0208.N0455.d007939 hN).2.1 k hk]
  calc
    _ ≤ ∫⁻ a : ℝ, k a * ENNReal.ofReal (8 * a ^ 2 / N) := by
      apply lintegral_mono
      intro a
      have h : (∫⁻ v : ℝ, ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N (v - a) - _root_.GD.N0208.N0455.d007937 N v) ^ 2)) ≤
          ENNReal.ofReal (8 * a ^ 2 / N) := by
        simpa only [sub_eq_add_neg, neg_sq] using _root_.GD.N0208.N0455.d007942 hN (-a)
      exact mul_le_mul_right h (k a)
    _ = ∫⁻ a : ℝ, ENNReal.ofReal (8 / N) * (k a * ENNReal.ofReal (a ^ 2)) := by
      apply lintegral_congr
      intro a
      rw [show 8 * a ^ 2 / N = (8 / N) * a ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 / N)]
      ring
    _ = _ := lintegral_const_mul _ (hk.mul (by fun_prop))

theorem d008102 :
    (∫⁻ a : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 a) * ENNReal.ofReal (a ^ 2)) ≤
      ENNReal.ofReal (32 / Real.pi) := by
  calc
    _ ≤ ∫⁻ a : ℝ, ENNReal.ofReal (Real.pi⁻¹) *
        ENNReal.ofReal (a ^ 2 * Real.exp (-|a| / 2)) := by
      apply lintegral_mono
      intro a
      dsimp only
      rw [← ENNReal.ofReal_mul (_root_.GD.N0213.N0493.d007994 a).le,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)]
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_right (_root_.GD.N0213.N0493.d007995 a) (sq_nonneg a)).trans_eq
        (by ring)
    _ = ENNReal.ofReal (Real.pi⁻¹) * 32 := by
      rw [lintegral_const_mul _ (by fun_prop), _root_.GD.N0208.N0456.d007936]
    _ = _ := by
      rw [show (32 : ℝ≥0∞) = ENNReal.ofReal (32 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)]
      congr 1
      ring



theorem d008103 (N : ℝ) (hN : 0 < N) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 (v + w)) *
      ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
        ENNReal.ofReal (256 / (Real.pi * N)) := by
  have hk : Measurable (fun a => ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 a)) := by
    unfold _root_.GD.N0213.N0493.d007990
    fun_prop
  have h := _root_.GD.N0221.d008101 N hN _ hk
  calc
    _ ≤ ENNReal.ofReal (8 / N) * ENNReal.ofReal (32 / Real.pi) :=
      h.trans (mul_le_mul_right _root_.GD.N0221.d008102 _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 / N)]
      congr 1
      ring

theorem d008104 (N : ℝ) (hN : 0 < N)
    (F : ℝ) (hF : 0 ≤ F) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (256 * F / (Real.pi * N)) := by
  have hkernel (v w : ℝ) :
      ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((v + w) / 2))) =
        ENNReal.ofReal F * ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 (v + w)) := by
    rw [← ENNReal.ofReal_mul hF]
    rfl
  have hinner (v : ℝ) :
      (∫⁻ w : ℝ, ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) =
      ENNReal.ofReal F * ∫⁻ w : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 (v + w)) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
    simp_rw [hkernel, mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal F * ENNReal.ofReal (256 / (Real.pi * N)) :=
      mul_le_mul_right (_root_.GD.N0221.d008103 N hN) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hF]
      congr 1
      ring

theorem d008105 (N : ℝ) (hN : 0 < N) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ, ENNReal.ofReal (_root_.GD.N0208.N0456.d007929 v w) *
      ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
        ENNReal.ofReal (128 / (Real.pi * N)) := by
  have h := _root_.GD.N0221.d008104 N hN (1 / 2) (by norm_num)
  have he (v w : ℝ) : (1 / 2 : ℝ) / (2 * Real.pi * Real.cosh ((v + w) / 2)) =
      _root_.GD.N0208.N0456.d007929 v w := by
    unfold _root_.GD.N0208.N0456.d007929
    ring
  simpa only [he, show (256 : ℝ) * (1 / 2) / (Real.pi * N) =
    128 / (Real.pi * N) by ring] using h


theorem d008106 (F v w : ℝ) :
    _root_.GD.N0213.N0493.d007991 F v w = (2 * F) * _root_.GD.N0208.N0456.d007928 v w := by
  unfold _root_.GD.N0213.N0493.d007991 _root_.GD.N0213.N0493.d007990 _root_.GD.N0208.N0456.d007928
  rw [_root_.GD.N0213.N0493.d007987, show (w - v) / 2 = -((v - w) / 2) by ring, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring



theorem d008107 (N : ℝ) (hN : 0 < N)
    (F : ℝ → ℝ) (hFm : Measurable F) (hF : ∀ s, 0 ≤ F s)
    (hmass : (∫⁻ s : ℝ, ENNReal.ofReal (F s)) ≤ 1) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (F s / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (256 / (Real.pi * N)) := by
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (256 * F s / (Real.pi * N)) :=
      lintegral_mono (fun s => _root_.GD.N0221.d008104 N hN (F s) (hF s))
    _ = ∫⁻ s : ℝ, ENNReal.ofReal (256 / (Real.pi * N)) * ENNReal.ofReal (F s) := by
      apply lintegral_congr
      intro s
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 256 / (Real.pi * N))]
      congr 1
      ring
    _ = ENNReal.ofReal (256 / (Real.pi * N)) * ∫⁻ s : ℝ, ENNReal.ofReal (F s) :=
      lintegral_const_mul _ hFm.ennreal_ofReal
    _ ≤ ENNReal.ofReal (256 / (Real.pi * N)) * 1 := mul_le_mul_right hmass _
    _ = _ := mul_one _

theorem d008108
    (F : ℝ → ℝ) (hFm : Measurable F) (hF : ∀ s, 0 ≤ F s)
    (hmass : (∫⁻ s : ℝ, ENNReal.ofReal (F s)) ≤ 1) :
    Tendsto (fun N : ℝ => ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (F s / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℝ => (256 / Real.pi) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun N : ℝ => ENNReal.ofReal (256 / (Real.pi * N)))
      atTop (𝓝 0) := by
    have heq (N : ℝ) : 256 / (Real.pi * N) = (256 / Real.pi) / N := by
      ring
    simpa only [heq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  exact _root_.GD.N0221.d008107 N hN F hFm hF hmass

end
end GD.N0221

#print axioms _root_.GD.N0221.d008100
#print axioms _root_.GD.N0221.d008101
#print axioms _root_.GD.N0221.d008102
#print axioms _root_.GD.N0221.d008103
#print axioms _root_.GD.N0221.d008104
#print axioms _root_.GD.N0221.d008105
#print axioms _root_.GD.N0221.d008106
#print axioms _root_.GD.N0221.d008107
#print axioms _root_.GD.N0221.d008108
