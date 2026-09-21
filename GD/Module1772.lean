import GD.Module1771
import GD.Module1770
import GD.Module1760
import GD.Module0467
import GD.Module1769
import Mathlib.MeasureTheory.Integral.Prod



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1593
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1594 _root_.GD.N0106.N0428.N0765.N1595 _root_.GD.N0106.N0428.N0765.N1587
open _root_.GD.N0106.N0428.N0765.N1602 _root_.GD.N0106.N0428.N0765.N1589 _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1550

theorem d029344 (e eta s x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) s x = _root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta (_root_.GD.N0106.N0428.N0765.N1537.d021524 x s) := rfl


theorem d029345 {dA dB : ℝ} (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) :
    ∃ C : ℝ, ∀ e : ℝ, 0 ≤ e → ∀ eta : ℝ, ∀ z : ℂ, |z.im| ≤ dA →
      ‖_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta z‖ ≤ C * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 z.re := by
  obtain ⟨K, _, hK⟩ := _root_.GD.N0106.N0428.N0765.N1602.d029274 hdA hdB hd
  refine ⟨K * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y, ?_⟩
  intro e he eta z hz
  have hphase : z ∈ _root_.GD.N0106.N0428.N0765.N1595.d029334 0 := by
    change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 z.im 0 < Real.pi
    simp only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, add_zero]
    nlinarith
  have hbound : ∀ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1595.d029324 e 0 eta z y‖ ≤
      (K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 z.re) * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
    intro y
    rw [_root_.GD.N0106.N0428.N0765.N1595.d029324, norm_mul, _root_.GD.N0106.N0428.N0765.N1595.d029327, one_mul, _root_.GD.N0106.N0428.N0765.N1595.d029328]
    exact hK e he z.im 0 hz (by simpa using hdB) z.re y
  calc ‖_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta z‖ ≤ ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1595.d029324 e 0 eta z y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 z.re) * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y :=
      integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1594.d029341 he hphase).norm
        ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3)).const_mul _)
        (Filter.Eventually.of_forall hbound)
    _ = (K * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y) * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 z.re := by
      rw [integral_const_mul]
      ring

theorem d029346 {e dA dB : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) (eta s : ℝ) (hs : |s| ≤ dA) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) s) := by
  have hp (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1537.d021524 x s ∈ _root_.GD.N0106.N0428.N0765.N1595.d029334 0 := by
    change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1537.d021524 x s).im 0 < Real.pi
    simp only [_root_.GD.N0106.N0428.N0765.N1537.d021526, _root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, add_zero]
    nlinarith
  have hc : Continuous (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) s) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021524 t s) (x := x)
      (_root_.GD.N0106.N0428.N0765.N1595.d029339 he (hp x)).2.continuousAt (by unfold _root_.GD.N0106.N0428.N0765.N1537.d021524; fun_prop)
  obtain ⟨C, hC⟩ := _root_.GD.N0106.N0428.N0765.N1593.d029345 hdA hdB hd
  apply Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 10)).const_mul C) hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [_root_.GD.N0106.N0428.N0765.N1593.d029344, _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526] using
      hC e he eta (_root_.GD.N0106.N0428.N0765.N1537.d021524 x s) (by simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021526] using hs)


theorem d029347 {e dA dB : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) (xi eta : ℝ) :
    ‖𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x,y)) eta) xi‖ ≤
      _root_.GD.N0106.N0428.N0765.N1537.d021534 (if 0 ≤ xi then -dA else dA) (if 0 ≤ eta then -dB else dB) *
        Real.exp (-2*Real.pi*dA*|xi|) * Real.exp (-2*Real.pi*dB*|eta|) := by
  let α : ℝ := if 0 ≤ xi then -dA else dA
  let β : ℝ := if 0 ≤ eta then -dB else dB
  have hα : |α| ≤ dA := by simp only [α]; split <;> simp [abs_of_nonneg hdA]
  have hβ : |β| ≤ dB := by simp only [β]; split <;> simp [abs_of_nonneg hdB]
  have hphase : ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dA → DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) z := by
    intro z hz
    apply (_root_.GD.N0106.N0428.N0765.N1595.d029339 he ?_).2.differentiableAt
    change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 z.im 0 < Real.pi
    simp only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, add_zero]
    nlinarith
  obtain ⟨C, hC⟩ := _root_.GD.N0106.N0428.N0765.N1593.d029345 hdA hdB hd
  have hint := _root_.GD.N0106.N0428.N0765.N1593.d029346 he hdA hdB hd eta
  have hFourier := _root_.GD.N0106.N0428.N0765.N1550.d005490 (f := _root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) (AL := C) (AR := C)
    hdA hf (hint 0 (by simpa using hdA))
    (hint (-dA) (by simp only [abs_neg, abs_of_nonneg hdA, le_refl]))
    (hint dA (by simp only [abs_of_nonneg hdA, le_refl]))
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 10)
    (by intro z hz hx; simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx] using hC e he eta z hz)
    (by
      intro z hz hx
      by_cases heq : z.re = 0
      · simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, heq, le_refl, if_true, mul_zero, Real.exp_zero, mul_one] using hC e he eta z hz
      · have hp : ¬ z.re ≤ 0 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm heq))
        simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hp] using hC e he eta z hz) xi
  have hi := _root_.GD.N0106.N0428.N0765.N1537.d021550 he hphase
  have hB : (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) α x‖) ≤
      Real.exp (-2*Real.pi*dB*|eta|) * _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
    calc (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) α x‖)
        ≤ ∫ x : ℝ, Real.exp (-2*Real.pi*dB*|eta|) * ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)‖ := by
          apply integral_mono_ae (hint α hα).norm (hi.integral_norm_prod_left.const_mul _)
          exact Filter.Eventually.of_forall fun x => by
            simpa only [_root_.GD.N0106.N0428.N0765.N1593.d029344, _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526, β] using
              _root_.GD.N0106.N0428.N0765.N1594.d029343 he hdA hdB hd
                (z := _root_.GD.N0106.N0428.N0765.N1537.d021524 x α) (by simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021526] using hα) eta
      _ = Real.exp (-2*Real.pi*dB*|eta|) * ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p‖ := by
        rw [integral_const_mul, ← integral_prod _ hi.norm]
        rfl
      _ ≤ Real.exp (-2*Real.pi*dB*|eta|) * _root_.GD.N0106.N0428.N0765.N1537.d021534 α β :=
        mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1537.d021551 he hphase) (Real.exp_nonneg _)
  have h := hFourier.trans (mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _))
  have hfun : _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1595.d029326 e 0 eta) 0 =
      fun x : ℝ => 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x,y)) eta := by
    funext x
    rw [_root_.GD.N0106.N0428.N0765.N1593.d029344, _root_.GD.N0106.N0428.N0765.N1594.d029340]
    simp only [_root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526]
  rw [hfun] at h
  simpa only [α, β, mul_assoc, mul_left_comm, mul_comm] using h

end
end GD.N0106.N0428.N0765.N1593
#print axioms _root_.GD.N0106.N0428.N0765.N1593.d029347
