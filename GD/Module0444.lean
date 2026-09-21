import Mathlib.Tactic
import GD.Module0155
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0033.N0285
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0878

private theorem d006799 (s : ℝ) : ∀ᵐ x ∂gammaMeasure s s, 0 < x := by
  have hnonneg : ∀ᵐ x ∂gammaMeasure s s, 0 ≤ x := by
    rw [gammaMeasure]
    refine (ae_withDensity_iff (μ := volume) ((measurable_gammaPDFReal s s).ennreal_ofReal)).2 ?_
    filter_upwards with x
    intro hpdf
    by_contra hx
    exact hpdf (gammaPDF_of_neg (lt_of_not_ge hx))
  have hne : ∀ᵐ x ∂gammaMeasure s s, x ≠ 0 := by
    rw [gammaMeasure]
    exact (withDensity_absolutelyContinuous volume (gammaPDF s s)).ae_le (volume.ae_ne 0)
  filter_upwards [hnonneg, hne] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)

def d006800 (a B x : ℝ) : ℝ := x / (a + B * x)
def d006801 (a B x : ℝ) : ℝ := a / (a + B * x) ^ 2

theorem d006802 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) : HasDerivAt (_root_.GD.N0033.N0285.d006800 a B) (_root_.GD.N0033.N0285.d006801 a B x) x := by
  have hd : 0 < a + B * x := add_pos_of_pos_of_nonneg ha (mul_nonneg hB hx)
  have hh := (hasDerivAt_id x).div
    ((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul B)) hd.ne'
  convert hh using 1 <;> first | rfl | (dsimp [_root_.GD.N0033.N0285.d006801]; ring)

theorem d006803 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) : ContinuousOn (_root_.GD.N0033.N0285.d006801 a B) (Icc 0 x) := by
  unfold _root_.GD.N0033.N0285.d006801
  apply continuousOn_const.div ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
  intro u hu
  exact pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg ha (mul_nonneg hB hu.1)))

theorem d006804 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫ u in Ioc 0 x, _root_.GD.N0033.N0285.d006801 a B u) = _root_.GD.N0033.N0285.d006800 a B x := by
  have hc : ContinuousOn (_root_.GD.N0033.N0285.d006801 a B) (uIcc 0 x) := by
    simpa only [uIcc_of_le hx] using _root_.GD.N0033.N0285.d006803 a B ha hB x
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := _root_.GD.N0033.N0285.d006800 a B) (f' := _root_.GD.N0033.N0285.d006801 a B)
    (fun u hu => _root_.GD.N0033.N0285.d006802 a B ha hB u
      (show u ∈ Icc 0 x by simpa only [uIcc_of_le hx] using hu).1)
    hc.intervalIntegrable
  rw [intervalIntegral.integral_of_le hx] at hh
  simpa [_root_.GD.N0033.N0285.d006800] using hh

theorem d006805 (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ u in Ioc 0 x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B u)) =
      ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) := by
  have hc : ContinuousOn (_root_.GD.N0033.N0285.d006801 a B) (uIcc 0 x) := by
    simpa only [uIcc_of_le hx] using _root_.GD.N0033.N0285.d006803 a B ha hB x
  rw [← ofReal_integral_eq_lintegral_ofReal hc.intervalIntegrable.1
    (ae_of_all _ fun u => by unfold _root_.GD.N0033.N0285.d006801; positivity)]
  rw [_root_.GD.N0033.N0285.d006804 a B ha hB x hx]

theorem d006806
    (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    (∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B x) ∂gammaMeasure 1 1) =
      ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure 1 1 := by
  let action : ℝ → ℝ := fun x => Real.sqrt a / (a + B * x)
  have hm : Measurable action := by unfold action; fun_prop
  have ha2 : ∀ x, action x ^ 2 = _root_.GD.N0033.N0285.d006801 a B x := by
    intro x
    dsimp [action]
    rw [div_pow, Real.sq_sqrt ha.le]
    rfl
  have hv := _root_.GD.N0232.N0719.N0878.d001774 1 1 action hm (by norm_num) (by norm_num)
  have hleft : (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 1 action x ∂gammaMeasure 1 1) =
      ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure 1 1 := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.N0285.d006799 1] with x hx
    rw [_root_.GD.N0232.N0719.N0878.d001766 action hx]
    simp only [sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul, ha2]
    exact _root_.GD.N0033.N0285.d006805 a B ha hB x hx.le
  rw [hleft] at hv
  simpa only [_root_.GD.N0232.N0719.N0878.d001750, ha2, ENNReal.ofReal_one, inv_one, one_mul] using hv.symm

theorem d006807
    (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (x : ℝ) (hx : 0 < x) :
    _root_.GD.N0232.N0719.N0878.d001761 s (fun u => Real.sqrt a / (a + B * u)) x ≤
      ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) := by
  have ha2 : ∀ u, (Real.sqrt a / (a + B * u)) ^ 2 = _root_.GD.N0033.N0285.d006801 a B u := by
    intro u
    rw [div_pow, Real.sq_sqrt ha.le]
    rfl
  rw [_root_.GD.N0232.N0719.N0878.d001766 _ hx]
  simp only [ha2]
  have hh : (∫⁻ u in Ioc 0 x, ENNReal.ofReal (u ^ (s - 1)) * ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B u)) ≤
      ENNReal.ofReal (x ^ (s - 1)) * ∫⁻ u in Ioc 0 x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B u) := by
    calc
      _ ≤ ∫⁻ u in Ioc 0 x, ENNReal.ofReal (x ^ (s - 1)) * ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B u) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hu.1.le hu.2 (by linarith))) _
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hcancel : ENNReal.ofReal (x ^ (1 - s)) * ENNReal.ofReal (x ^ (s - 1)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _), ← Real.rpow_add hx,
      show (1 - s) + (s - 1) = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]
  calc
    _ ≤ ENNReal.ofReal (x ^ (1 - s)) * (ENNReal.ofReal (x ^ (s - 1)) *
        ∫⁻ u in Ioc 0 x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B u)) := mul_le_mul_right hh _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul, _root_.GD.N0033.N0285.d006805 a B ha hB x hx.le]



theorem d006808
    (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s) :
    (∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B x) ∂gammaMeasure s s) ≤
      ENNReal.ofReal s * ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure s s := by
  have hs0 : 0 < s := by linarith
  let action : ℝ → ℝ := fun u => Real.sqrt a / (a + B * u)
  have hm : Measurable action := by unfold action; fun_prop
  have ha2 : ∀ x, action x ^ 2 = _root_.GD.N0033.N0285.d006801 a B x := by
    intro x
    dsimp [action]
    rw [div_pow, Real.sq_sqrt ha.le]
    rfl
  have hv := _root_.GD.N0232.N0719.N0878.d001774 s s action hm hs0 hs0
  have heq : (∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B x) ∂gammaMeasure s s) =
      ENNReal.ofReal s * ∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 s action x ∂gammaMeasure s s := by
    rw [hv, ← mul_assoc, ENNReal.mul_inv_cancel (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hs0])
      ENNReal.ofReal_ne_top, one_mul]
    simp only [_root_.GD.N0232.N0719.N0878.d001750, ha2]
  rw [heq]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [_root_.GD.N0033.N0285.d006799 s] with x hx
  exact _root_.GD.N0033.N0285.d006807 a B s ha hB hs x hx

end
end GD.N0033.N0285

#print axioms _root_.GD.N0033.N0285.d006804
#print axioms _root_.GD.N0033.N0285.d006806
#print axioms _root_.GD.N0033.N0285.d006808
