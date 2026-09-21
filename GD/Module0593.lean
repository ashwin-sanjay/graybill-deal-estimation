import GD.Module0589
import GD.Module0590




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1660
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533
open scoped Topology FourierTransform BigOperators

theorem d008565 (F : ℂ → ℂ → ℂ) (d : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d := by
  have hm : 0 ≤ _root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) (-d) :=
    integral_nonneg (fun _ => norm_nonneg _)
  unfold _root_.GD.N0106.N0428.N0765.N1650.d008510
  exact hm.trans ((le_max_left _ _).trans (le_max_left _ _))

theorem d008566 {k : ℝ} (hk : 0 < k) :
    Summable (fun n : ℤ => Real.exp (-k * |(n : ℝ)|)) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1613.d005630
    (s := fun n : ℤ => ((Real.exp (-k * |(n : ℝ)|) : ℝ) : ℂ)) (C := 1) hk (by
      intro n
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        one_mul, le_refl])
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs.norm



theorem d008567 {f : ℝ × ℝ → ℂ} {C k : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C)
    (hb : ∀ ξ ν : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 f ξ ν‖ ≤
      C * Real.exp (-k * |ξ|) * Real.exp (-k * |ν|)) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 f p.1 p.2) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1660.d008566 hk
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819 (hs.mul_left C) hs
    (fun n => mul_nonneg hC (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  intro p
  exact hb p.1 p.2



theorem d008568 {F : ℂ → ℂ → ℂ} {d M : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z w‖ ≤ M)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume))
    (hdecayA : ∀ β : ℝ, |β| ≤ d → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ,
        R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x y : ℝ) :
    (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x + (p.1 : ℝ), y + (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) p.1 p.2 *
        fourier p.1 (x : UnitAddCircle) * fourier p.2 (y : UnitAddCircle) := by
  have hdecayB' : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005478] using hdecayB
  have hrows := _root_.GD.N0106.N0428.N0765.N1654.d008558
    hd hc hfA hfB hM hmm hmp hpm hpp hdecayB
  have hcolumns (n : ℤ) := _root_.GD.N0106.N0428.N0765.N1651.d008556
    hd hc hfA hfB hM hmm hmp hpm hpp hdecayA hdecayB' (n : ℝ)
  have hsamples : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x + (p.1 : ℝ), y + (p.2 : ℝ))) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466, Complex.ofReal_zero,
      zero_mul, add_zero] using _root_.GD.N0106.N0428.N0765.N1650.d008513
      hd hc hfA hfB hM hmm hmp hpm hpp x y
  have hcross := _root_.GD.N0106.N0428.N0765.N1641.d008522
    hd hc hfA hfB hM hmm hmp hpm hpp hdecayB x
  have hbound := _root_.GD.N0106.N0428.N0765.N1644.d008532
    hd hc hfA hfB hM hmm hmp hpm hpp hdecayA hdecayB'
  have hcoeff := _root_.GD.N0106.N0428.N0765.N1660.d008567
    (by positivity : 0 < 2 * Real.pi * d) (_root_.GD.N0106.N0428.N0765.N1660.d008565 F d) hbound
  exact _root_.GD.N0106.N0428.N0765.N1652.d005820 hrows hcolumns x y hsamples hcross hcoeff

end
end GD.N0106.N0428.N0765.N1660

#print axioms _root_.GD.N0106.N0428.N0765.N1660.d008567
#print axioms _root_.GD.N0106.N0428.N0765.N1660.d008568
