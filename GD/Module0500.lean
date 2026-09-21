import GD.Module0452

set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped ENNReal

namespace GD.N0043
noncomputable section


theorem d007627 {a C : ℝ}
    (ha1 : a < 1) (hC : 0 ≤ C) (L : ℝ≥0∞)
    (hcap : ∀ M : ℝ, 1 ≤ M → ENNReal.ofReal (M ^ (1 - a)) * L ≤ ENNReal.ofReal C) :
    L = 0 := by
  by_contra hzero
  obtain ⟨b, hb0, hbL⟩ := exists_between (pos_iff_ne_zero.mpr hzero)
  have hbfin : b ≠ ⊤ := ne_top_of_lt hbL
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
      _ ≤ ENNReal.ofReal (M ^ (1 - a)) * L := by
        rw [hpb]
        exact mul_le_mul_right hbL.le _
      _ ≤ ENNReal.ofReal C := hcap M hM
  exact (not_le_of_gt hMC) ((ENNReal.ofReal_le_ofReal_iff hC).mp hl)

end
end GD.N0043

#print axioms _root_.GD.N0043.d007627
