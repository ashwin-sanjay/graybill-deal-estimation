import GD.Module0495










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1552
noncomputable section
open MeasureTheory Set Complex Filter Topology
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530
open scoped Topology


theorem d007605 {f : ℂ → ℂ} {d r : ℝ} (hr : r < d)
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 r) := by
  apply hf.continuousOn.mono
  intro z hz
  exact lt_of_le_of_lt (show |z.im| ≤ r from hz) hr



theorem d007606 {f : ℂ → ℂ} {d r h : ℝ}
    (hr : 0 < r) (hrd : r < d) (hh : 0 < h)
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-r)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f r))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| < d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (offset : ℝ) :
    ‖(∫ t : ℝ, f (t : ℂ)) -
      (h : ℂ) * (∑' n : ℤ, f ((offset + h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-r) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f r) /
        (Real.exp (2 * Real.pi * r / h) - 1) := by
  have hfr : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 r) := hf.mono (by
    intro z hz
    exact lt_trans (show |z.im| < r from hz) hrd)
  have hdr : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ r → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hdecay ε hε
    exact ⟨R, fun x s hx hs => hR x s hx (lt_of_le_of_lt hs hrd)⟩
  simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005195, _root_.GD.N0106.N0428.N0765.N1530.d005194] using
    _root_.GD.N0106.N0428.N0765.N1554.d007600 hr hh
      (_root_.GD.N0106.N0428.N0765.N1552.d007605 hrd hf) hfr hminus hplus hdr offset



theorem d007607 {f : ℂ → ℂ} {d h B : ℝ}
    {r : ℕ → ℝ} (hd : 0 < d) (hh : 0 < h)
    (hrpos : ∀ n, 0 < r n) (hrlt : ∀ n, r n < d)
    (hr : Tendsto r atTop (𝓝 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : ∀ n, Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-r n)))
    (hplus : ∀ n, Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (r n)))
    (hbudget : ∀ n, _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-r n) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f (r n) ≤ B)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| < d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (offset : ℝ) :
    ‖(∫ t : ℝ, f (t : ℂ)) -
      (h : ℂ) * (∑' n : ℤ, f ((offset + h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      B / (Real.exp (2 * Real.pi * d / h) - 1) := by
  have hb : ∀ n, ‖(∫ t : ℝ, f (t : ℂ)) -
      (h : ℂ) * (∑' k : ℤ, f ((offset + h * (k : ℝ) : ℝ) : ℂ))‖ ≤
      (B + 0) / (Real.exp (2 * Real.pi * r n / h) - 1) := by
    intro n
    have he := _root_.GD.N0106.N0428.N0765.N1552.d007606 (hrpos n) (hrlt n) hh hf
      (hminus n) (hplus n) hdecay offset
    apply he.trans
    rw [add_zero]
    exact div_le_div_of_nonneg_right (hbudget n) (by
      apply sub_nonneg.mpr
      apply Real.one_le_exp_iff.mpr
      exact (div_pos (mul_pos Real.two_pi_pos (hrpos n)) hh).le)
  simpa only [add_zero] using
    _root_.GD.N0106.N0428.N0765.N1553.d006798
      (Bplus := B) (Bminus := 0) hh hd hr hb




theorem d007608 {f : ℂ → ℂ} {d h Bminus Bplus : ℝ}
    {r : ℕ → ℝ} (hd : 0 < d) (hh : 0 < h)
    (hrpos : ∀ n, 0 < r n) (hrlt : ∀ n, r n < d)
    (hr : Tendsto r atTop (𝓝 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : ∀ n, Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-r n)))
    (hplus : ∀ n, Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (r n)))
    (hm : Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-r n)) atTop (𝓝 Bminus))
    (hp : Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (r n)) atTop (𝓝 Bplus))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| < d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (offset : ℝ) :
    ‖(∫ t : ℝ, f (t : ℂ)) -
      (h : ℂ) * (∑' n : ℤ, f ((offset + h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      (Bminus + Bplus) / (Real.exp (2 * Real.pi * d / h) - 1) := by
  exact _root_.GD.N0106.N0428.N0765.N1551.d006796 hh hd hr hm hp
    (fun n => _root_.GD.N0106.N0428.N0765.N1552.d007606 (hrpos n) (hrlt n) hh hf
      (hminus n) (hplus n) hdecay offset)

end
end GD.N0106.N0428.N0765.N1552

#print axioms _root_.GD.N0106.N0428.N0765.N1552.d007606
#print axioms _root_.GD.N0106.N0428.N0765.N1552.d007607
#print axioms _root_.GD.N0106.N0428.N0765.N1552.d007608
