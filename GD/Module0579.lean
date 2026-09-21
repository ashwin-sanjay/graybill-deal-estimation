import GD.Module0495
import GD.Module0382
















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1655
noncomputable section

open MeasureTheory Set Complex TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1531
open _root_.GD.N0106.N0428.N0765.N1551 _root_.GD.N0106.N0428.N0765.N1554 _root_.GD.N0106.N0428.N0765.N1652
open scoped FourierTransform Topology

theorem d008461 {f : ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) := by
  obtain ⟨M, _hMpos, hM⟩ := _root_.GD.N0106.N0428.N0765.N1551.d006791 hc hdecay
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) :=
    (_root_.GD.N0106.N0428.N0765.N1531.d007569 hd (by simpa using hd.le)
      hc hf hM hminus hplus).1
  obtain ⟨hpos, hneg⟩ := _root_.GD.N0106.N0428.N0765.N1554.d007599 hd hc hf h0 hminus hplus hdecay
  refine ⟨_root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le),
    _root_.GD.N0106.N0428.N0765.N1532.d007590
      hd hc hf hM hminus hplus, ?_⟩
  apply _root_.GD.N0106.N0428.N0765.N1551.d006793 (k := 2 * Real.pi * d) (by positivity)
  · intro n
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      hpos ((n : ℝ) + 1) (by positivity)
  · intro n
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      hneg ((n : ℝ) + 1) (by positivity)

end
end GD.N0106.N0428.N0765.N1655

#print axioms _root_.GD.N0106.N0428.N0765.N1655.d008461
