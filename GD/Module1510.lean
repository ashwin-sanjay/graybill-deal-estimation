import GD.Module0444
import GD.Module0658

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0047
noncomputable section
open _root_.GD.N0033.N0285
open _root_.GD.N0232.N0719.N0960

def d023527 (a B x : ℝ) : ℝ := 1 / (a + B * x)

theorem d023528 (s : ℝ) (hs : 0 < s) : ∀ᵐ x ∂gammaMeasure s s, 0 < x := by
  have hne : ∀ᵐ x ∂gammaMeasure s s, x ≠ 0 := by
    rw [gammaMeasure]
    exact (withDensity_absolutelyContinuous volume (gammaPDF s s)).ae_le (volume.ae_ne 0)
  filter_upwards [_root_.GD.N0232.N0719.N0960.d009681 hs hs, hne] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)

theorem d023529 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) :
    (0 ≤ _root_.GD.N0047.d023527 a B x ∧ _root_.GD.N0047.d023527 a B x ≤ 1 / a) ∧
    (0 ≤ _root_.GD.N0033.N0285.d006801 a B x ∧ _root_.GD.N0033.N0285.d006801 a B x ≤ 1 / a) ∧
    (0 ≤ _root_.GD.N0033.N0285.d006800 a B x ∧ _root_.GD.N0033.N0285.d006800 a B x ≤ x / a) := by
  have hd : 0 < a + B * x := add_pos_of_pos_of_nonneg ha (mul_nonneg hB hx)
  have had : a ≤ a + B * x := le_add_of_nonneg_right (mul_nonneg hB hx)
  refine ⟨⟨by unfold _root_.GD.N0047.d023527; positivity, ?_⟩,
    ⟨by unfold _root_.GD.N0033.N0285.d006801; positivity, ?_⟩,
    ⟨by unfold _root_.GD.N0033.N0285.d006800; positivity, ?_⟩⟩
  · exact div_le_div_of_nonneg_left (by norm_num) ha had
  · unfold _root_.GD.N0033.N0285.d006801
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) ha).mpr
    have hh := pow_le_pow_left₀ ha.le had 2
    nlinarith
  · exact div_le_div_of_nonneg_left hx ha had

theorem d023530 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 0 < s) :
    Integrable (_root_.GD.N0047.d023527 a B) (gammaMeasure s s) ∧
    Integrable (_root_.GD.N0033.N0285.d006801 a B) (gammaMeasure s s) ∧
    Integrable (_root_.GD.N0033.N0285.d006800 a B) (gammaMeasure s s) := by
  letI := isProbabilityMeasure_gammaMeasure hs hs
  have hp := _root_.GD.N0047.d023528 s hs
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_const (1 / a)).mono'
    · exact (show Measurable (_root_.GD.N0047.d023527 a B) by unfold _root_.GD.N0047.d023527; fun_prop).aestronglyMeasurable
    · filter_upwards [hp] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0047.d023529 a B ha hB x hx.le).1.1]
      exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).1.2
  · apply (integrable_const (1 / a)).mono'
    · exact (show Measurable (_root_.GD.N0033.N0285.d006801 a B) by unfold _root_.GD.N0033.N0285.d006801; fun_prop).aestronglyMeasurable
    · filter_upwards [hp] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.1.1]
      exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.1.2
  · apply ((_root_.GD.N0232.N0719.N0960.d009683 hs hs).div_const a).mono'
    · exact (show Measurable (_root_.GD.N0033.N0285.d006800 a B) by unfold _root_.GD.N0033.N0285.d006800; fun_prop).aestronglyMeasurable
    · filter_upwards [hp] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.2.1]
      exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.2.2


theorem d023531 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) :
    _root_.GD.N0033.N0285.d006800 a B x - _root_.GD.N0047.d023527 a B x ≤ (x - 1) / (a + B) := by
  have hd : 0 < a + B * x := add_pos_of_pos_of_nonneg ha (mul_nonneg hB hx)
  have hab : 0 < a + B := add_pos_of_pos_of_nonneg ha hB
  rw [_root_.GD.N0033.N0285.d006800, _root_.GD.N0047.d023527, ← sub_div, div_le_div_iff₀ hd hab]
  nlinarith [mul_nonneg hB (sq_nonneg (x - 1))]


theorem d023532
    (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 0 < s) :
    (∫ x, _root_.GD.N0033.N0285.d006800 a B x ∂gammaMeasure s s) ≤
      ∫ x, _root_.GD.N0047.d023527 a B x ∂gammaMeasure s s := by
  letI := isProbabilityMeasure_gammaMeasure hs hs
  obtain ⟨hH, _hD, hF⟩ := _root_.GD.N0047.d023530 a B s ha hB hs
  have hi := (_root_.GD.N0232.N0719.N0960.d009683 hs hs).sub (integrable_const 1)
  have hh := integral_mono_ae (hF.sub hH) (hi.div_const (a + B))
    (show (fun x => _root_.GD.N0033.N0285.d006800 a B x - _root_.GD.N0047.d023527 a B x) ≤ᵐ[gammaMeasure s s]
      (fun x => (x - 1) / (a + B)) from by
        filter_upwards [_root_.GD.N0047.d023528 s hs] with x hx
        exact _root_.GD.N0047.d023531 a B ha hB x hx.le)
  change (∫ x, _root_.GD.N0033.N0285.d006800 a B x - _root_.GD.N0047.d023527 a B x ∂gammaMeasure s s) ≤
    ∫ x, (x - 1) / (a + B) ∂gammaMeasure s s at hh
  simp only [div_eq_mul_inv] at hh
  rw [integral_sub hF hH, integral_mul_const,
    integral_sub (_root_.GD.N0232.N0719.N0960.d009683 hs hs) (integrable_const 1),
    _root_.GD.N0232.N0719.N0960.d009682 hs hs, div_self hs.ne'] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self] at hh
  linarith

end
end GD.N0047

#print axioms _root_.GD.N0047.d023530
#print axioms _root_.GD.N0047.d023532
