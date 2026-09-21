import GD.Module0432

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace GD.N0043
noncomputable section



theorem d006969 {a r C : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r) (hC : 0 ≤ C)
    (f : ℝ → ℝ≥0∞)
    (hcap : ∀ M : ℝ, 1 ≤ M →
      ENNReal.ofReal M * (∫⁻ x, f x ∂gammaMeasure a (r / M)) ≤ ENNReal.ofReal C) :
    (∫⁻ x, f x ∂gammaMeasure a r) = 0 := by
  by_contra hzero
  have hpos : 0 < ∫⁻ x, f x ∂gammaMeasure a r := pos_iff_ne_zero.mpr hzero
  obtain ⟨b, hb0, hbt⟩ := exists_between hpos
  have hbfin : b ≠ ⊤ := ne_top_of_lt hbt
  let p := b.toReal
  have hp : 0 < p := ENNReal.toReal_pos hb0.ne' hbfin
  have hpb : ENNReal.ofReal p = b := ENNReal.ofReal_toReal hbfin
  have ht : Tendsto (fun M : ℝ => M ^ (1 - a) * p) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hp (tendsto_rpow_atTop (by linarith : 0 < 1 - a))
  obtain ⟨M, hM, hMC⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (ht.eventually (eventually_gt_atTop C))).exists
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hl : ENNReal.ofReal (M ^ (1 - a) * p) ≤ ENNReal.ofReal C := by
    calc
      ENNReal.ofReal (M ^ (1 - a) * p) =
          ENNReal.ofReal (M ^ (1 - a)) * ENNReal.ofReal p :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hMp.le _)
      _ ≤ ENNReal.ofReal (M ^ (1 - a)) * (∫⁻ x, f x ∂gammaMeasure a r) := by
        rw [hpb]
        exact mul_le_mul_right hbt.le _
      _ ≤ ENNReal.ofReal M * (∫⁻ x, f x ∂gammaMeasure a (r / M)) :=
        _root_.GD.N0043.d006731 ha hr hM f
      _ ≤ ENNReal.ofReal C := hcap M hM
  exact (not_le_of_gt hMC) ((ENNReal.ofReal_le_ofReal_iff hC).mp hl)

theorem d006970 {a r C : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r) (hC : 0 ≤ C)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hcap : ∀ M : ℝ, 1 ≤ M →
      ENNReal.ofReal M * (∫⁻ x, f x ∂gammaMeasure a (r / M)) ≤ ENNReal.ofReal C) :
    f =ᵐ[gammaMeasure a r] 0 := by
  exact (lintegral_eq_zero_iff hf).mp
    (_root_.GD.N0043.d006969 ha ha1 hr hC f hcap)

end
end GD.N0043

#print axioms _root_.GD.N0043.d006969
#print axioms _root_.GD.N0043.d006970
