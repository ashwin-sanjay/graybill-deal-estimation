import GD.Module0494
import GD.Module0443
import GD.Module0493
import GD.Module0442
















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1554
noncomputable section

open MeasureTheory Set Complex TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1531
open scoped Topology FourierTransform

def d007592 (f : ℂ → ℂ) (h : ℝ) (z : ℂ) : ℂ := f ((h : ℂ) * z)



theorem d007593 (f : ℂ → ℂ) (h y : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1530.d005194 (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) y = fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1530.d005194 f (h * y) (h * x) := by
  funext x
  unfold _root_.GD.N0106.N0428.N0765.N1530.d005194 _root_.GD.N0106.N0428.N0765.N1554.d007592
  congr 1
  push_cast
  ring

theorem d007594 {d h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h)) : (h : ℂ) * z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
  change |z.im| ≤ d / h at hz
  change |((h : ℂ) * z).im| ≤ d
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, zero_add, abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hz

theorem d007595 {d h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 (d / h)) : (h : ℂ) * z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := by
  change |z.im| < d / h at hz
  change |((h : ℂ) * z).im| < d
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, zero_add, abs_mul, abs_of_pos hh, mul_comm] using (lt_div_iff₀ hh).mp hz

theorem d007596 {f : ℂ → ℂ} {d h : ℝ} (hh : 0 < h)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) (_root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h)) := by
  exact hc.comp (continuous_const.mul continuous_id).continuousOn
    (fun _ hz => _root_.GD.N0106.N0428.N0765.N1554.d007594 hh hz)

theorem d007597 {f : ℂ → ℂ} {d h : ℝ} (hh : 0 < h)
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) (_root_.GD.N0106.N0428.N0765.N1533.d005163 (d / h)) := by
  have hlin : Differentiable ℂ (fun z : ℂ => (h : ℂ) * z) := by fun_prop
  exact hf.comp hlin.differentiableOn (fun _ hz => _root_.GD.N0106.N0428.N0765.N1554.d007595 hh hz)



theorem d007598 {f : ℂ → ℂ} {d M h : ℝ}
    (hd : 0 < d) (hh : 0 < h)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1530.d005194 f 0 (h * x),
          (_root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)).comp
            (continuous_const.mul continuous_id)⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  have hwidth : 0 < d / h := div_pos hd hh
  have hcF := _root_.GD.N0106.N0428.N0765.N1554.d007596 hh hc
  have hfF := _root_.GD.N0106.N0428.N0765.N1554.d007597 hh hf
  have hMF : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h), ‖_root_.GD.N0106.N0428.N0765.N1554.d007592 f h z‖ ≤ M :=
    fun z hz => hM _ (_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hz)
  have hminusF : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) (-(d / h))) := by
    rw [_root_.GD.N0106.N0428.N0765.N1554.d007593]
    have heq : h * (-(d / h)) = -d := by field_simp [hh.ne'] <;> ring
    rw [heq]
    exact hminus.comp_mul_left' hh.ne'
  have hplusF : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) (d / h)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1554.d007593]
    have heq : h * (d / h) = d := by field_simp [hh.ne'] <;> ring
    rw [heq]
    exact hplus.comp_mul_left' hh.ne'
  have hs := _root_.GD.N0106.N0428.N0765.N1532.d007590
    hwidth hcF hfF hMF hminusF hplusF K
  have hmap :
      (⟨_root_.GD.N0106.N0428.N0765.N1530.d005194 (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) 0,
          _root_.GD.N0106.N0428.N0765.N1531.d007567 hcF (by simpa using hwidth.le)⟩ : C(ℝ, ℂ)) =
        (⟨fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1530.d005194 f 0 (h * x),
          (_root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)).comp
            (continuous_const.mul continuous_id)⟩ : C(ℝ, ℂ)) := by
    ext x
    change _root_.GD.N0106.N0428.N0765.N1530.d005194 (_root_.GD.N0106.N0428.N0765.N1554.d007592 f h) 0 x = _root_.GD.N0106.N0428.N0765.N1530.d005194 f 0 (h * x)
    rw [_root_.GD.N0106.N0428.N0765.N1554.d007593, mul_zero]
  rw [hmap] at hs
  exact hs



theorem d007599 {f : ℂ → ℂ} {d : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε) :
    (∀ ξ : ℝ, 0 < ξ → ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) ξ‖ ≤
      _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) * Real.exp (-(2 * Real.pi * d) * ξ)) ∧
    (∀ ξ : ℝ, 0 < ξ → ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) (-ξ)‖ ≤
      _root_.GD.N0106.N0428.N0765.N1530.d005195 f d * Real.exp (-(2 * Real.pi * d) * ξ)) := by
  constructor
  · intro ξ _hξ
    have hb := _root_.GD.N0106.N0428.N0765.N1551.d006792
      (y := -d) hd (by simpa only [abs_neg, abs_of_pos hd] using le_refl d)
      hc hf h0 hminus hdecay ξ
    have heq : 2 * Real.pi * ξ * (-d) = -(2 * Real.pi * d) * ξ := by ring
    rw [heq] at hb
    change ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) ξ‖ ≤ _ at hb
    simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005195, _root_.GD.N0106.N0428.N0765.N1530.d005194, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005473,
      mul_comm] using hb
  · intro ξ _hξ
    have hb := _root_.GD.N0106.N0428.N0765.N1551.d006792
      (y := d) hd (by simpa only [abs_of_pos hd] using le_refl d)
      hc hf h0 hplus hdecay (-ξ)
    have heq : 2 * Real.pi * (-ξ) * d = -(2 * Real.pi * d) * ξ := by ring
    rw [heq] at hb
    change ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) (-ξ)‖ ≤ _ at hb
    simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005195, _root_.GD.N0106.N0428.N0765.N1530.d005194, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005473,
      mul_comm] using hb





theorem d007600 {f : ℂ → ℂ} {d h : ℝ}
    (hd : 0 < d) (hh : 0 < h)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (offset : ℝ) :
    ‖(∫ t : ℝ, f (t : ℂ)) -
        (h : ℂ) * (∑' n : ℤ, f ((offset + h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      ((∫ t : ℝ, ‖f ((t : ℂ) + ((-d : ℝ) : ℂ) * Complex.I)‖) +
        ∫ t : ℝ, ‖f ((t : ℂ) + (d : ℂ) * Complex.I)‖) /
      (Real.exp (2 * Real.pi * d / h) - 1) := by
  obtain ⟨M, _hMpos, hM⟩ := _root_.GD.N0106.N0428.N0765.N1551.d006791 hc hdecay
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) :=
    (_root_.GD.N0106.N0428.N0765.N1531.d007569 hd (by simpa using hd.le)
      hc hf hM hminus hplus).1
  have hc0 : Continuous (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) :=
    _root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)
  have hnorm : ∀ K : Compacts ℝ, Summable (fun n : ℤ =>
      ‖((⟨fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1530.d005194 f 0 (h * x),
        hc0.comp (continuous_const.mul continuous_id)⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight (n : ℝ))).restrict K‖) :=
    _root_.GD.N0106.N0428.N0765.N1554.d007598 hd hh hc hf hM hminus hplus
  obtain ⟨hpos, hneg⟩ := _root_.GD.N0106.N0428.N0765.N1554.d007599 hd hc hf h0 hminus hplus hdecay
  have herror := _root_.GD.N0106.N0428.N0765.N1553.d006797 hc0
    (mul_pos Real.two_pi_pos hd) hh hnorm hpos hneg offset
  rw [norm_sub_rev] at herror
  simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005195, _root_.GD.N0106.N0428.N0765.N1530.d005194, Complex.ofReal_zero, zero_mul, add_zero] using herror

end
end GD.N0106.N0428.N0765.N1554

#print axioms _root_.GD.N0106.N0428.N0765.N1554.d007598
#print axioms _root_.GD.N0106.N0428.N0765.N1554.d007599
#print axioms _root_.GD.N0106.N0428.N0765.N1554.d007600
