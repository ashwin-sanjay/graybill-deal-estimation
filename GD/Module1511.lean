import GD.Module1510
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0047
noncomputable section
open _root_.GD.N0033.N0285
open _root_.GD.N0232.N0719.N0878

def d023533 (a B s x : ℝ) : ℝ :=
  _root_.GD.N0033.N0285.d006801 a B x + (s - 1) * _root_.GD.N0047.d023527 a B x

def d023534 (a B s x : ℝ) : ℝ := x ^ (s - 1) * _root_.GD.N0047.d023533 a B s x
def d023535 (a B s x : ℝ) : ℝ := x ^ s / (a + B * x)

theorem d023536 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ _root_.GD.N0047.d023533 a B s x :=
  add_nonneg (_root_.GD.N0047.d023529 a B ha hB x hx).2.1.1
    (mul_nonneg (sub_nonneg.mpr hs) (_root_.GD.N0047.d023529 a B ha hB x hx).1.1)

theorem d023537 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ _root_.GD.N0047.d023534 a B s x :=
  mul_nonneg (Real.rpow_nonneg hx _) (_root_.GD.N0047.d023536 a B s ha hB hs x hx)

theorem d023538 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0047.d023535 a B s) (_root_.GD.N0047.d023534 a B s x) x := by
  have hd : 0 < a + B * x := add_pos_of_pos_of_nonneg ha (mul_nonneg hB hx.le)
  have hpow : x ^ (s - 1) * x = x ^ s := by
    calc
      _ = x ^ (s - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((s - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by rw [sub_add_cancel]
  have hh := (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := s)).div
    ((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul B)) hd.ne'
  convert hh using 1 <;> first | rfl | (dsimp [_root_.GD.N0047.d023534, _root_.GD.N0047.d023533,
    _root_.GD.N0033.N0285.d006801, _root_.GD.N0047.d023527]; rw [← hpow]; field_simp [hd.ne']; ring)

theorem d023539 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (x : ℝ) : ContinuousOn (_root_.GD.N0047.d023534 a B s) (Icc 0 x) := by
  have hH : ContinuousOn (_root_.GD.N0047.d023527 a B) (Icc 0 x) := by
    unfold _root_.GD.N0047.d023527
    apply continuousOn_const.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro u hu
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (mul_nonneg hB hu.1))
  have hpow : ContinuousOn (fun u : ℝ => u ^ (s - 1)) (Icc 0 x) :=
    continuousOn_id.rpow_const (fun _ _ => Or.inr (sub_nonneg.mpr hs))
  exact hpow.mul ((_root_.GD.N0033.N0285.d006803 a B ha hB x).add (hH.const_mul (s - 1)))


theorem d023540 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (x : ℝ) (hx : 0 ≤ x) :
    (∫ u in Ioc 0 x, _root_.GD.N0047.d023534 a B s u) = _root_.GD.N0047.d023535 a B s x := by
  have hc : ContinuousOn (_root_.GD.N0047.d023535 a B s) (Icc 0 x) := by
    unfold _root_.GD.N0047.d023535
    apply (continuousOn_id.rpow_const (fun _ _ => Or.inr (zero_le_one.trans hs))).div
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro u hu
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (mul_nonneg hB hu.1))
  have hcD : ContinuousOn (_root_.GD.N0047.d023534 a B s) (uIcc 0 x) := by
    simpa only [uIcc_of_le hx] using _root_.GD.N0047.d023539 a B s ha hB hs x
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hc
    (fun u hu => _root_.GD.N0047.d023538 a B s ha hB u hu.1) hcD.intervalIntegrable
  rw [intervalIntegral.integral_of_le hx] at hh
  simpa [_root_.GD.N0047.d023535, Real.zero_rpow (show s ≠ 0 by linarith)] using hh

theorem d023541 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ u in Ioc 0 x, ENNReal.ofReal (_root_.GD.N0047.d023534 a B s u)) =
      ENNReal.ofReal (_root_.GD.N0047.d023535 a B s x) := by
  have hcD : ContinuousOn (_root_.GD.N0047.d023534 a B s) (uIcc 0 x) := by
    simpa only [uIcc_of_le hx] using _root_.GD.N0047.d023539 a B s ha hB hs x
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioc 0 x), 0 ≤ _root_.GD.N0047.d023534 a B s u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact _root_.GD.N0047.d023537 a B s ha hB hs u hu.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hcD.intervalIntegrable.1 hnonneg,
    _root_.GD.N0047.d023540 a B s ha hB hs x hx]

theorem d023542 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (x : ℝ) (hx : 0 < x) :
    _root_.GD.N0232.N0719.N0878.d001761 s (fun u => Real.sqrt (_root_.GD.N0047.d023533 a B s u)) x =
      ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) := by
  rw [_root_.GD.N0232.N0719.N0878.d001766 _ hx]
  have hinner : (∫⁻ u in Ioc 0 x, ENNReal.ofReal (u ^ (s - 1)) *
      ENNReal.ofReal (Real.sqrt (_root_.GD.N0047.d023533 a B s u) ^ 2)) =
      ENNReal.ofReal (_root_.GD.N0047.d023535 a B s x) := by
    calc
      _ = ∫⁻ u in Ioc 0 x, ENNReal.ofReal (_root_.GD.N0047.d023534 a B s u) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [Real.sq_sqrt (_root_.GD.N0047.d023536 a B s ha hB hs u hu.1.le),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hu.1.le _)]
        rfl
      _ = _ := _root_.GD.N0047.d023541 a B s ha hB hs x hx.le
  rw [hinner, ← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _)]
  congr 1
  unfold _root_.GD.N0047.d023535 _root_.GD.N0033.N0285.d006800
  rw [← mul_div_assoc, ← Real.rpow_add hx,
    show (1 - s) + s = 1 by ring, Real.rpow_one]


theorem d023543 (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s) :
    (∫ x, _root_.GD.N0033.N0285.d006801 a B x ∂gammaMeasure s s) +
      (s - 1) * (∫ x, _root_.GD.N0047.d023527 a B x ∂gammaMeasure s s) =
      s * (∫ x, _root_.GD.N0033.N0285.d006800 a B x ∂gammaMeasure s s) := by
  have hs0 : 0 < s := by linarith
  let action : ℝ → ℝ := fun u => Real.sqrt (_root_.GD.N0047.d023533 a B s u)
  have hm : Measurable action := by
    unfold action _root_.GD.N0047.d023533 _root_.GD.N0033.N0285.d006801 _root_.GD.N0047.d023527
    fun_prop
  have hv := _root_.GD.N0232.N0719.N0878.d001774 s s action hm hs0 hs0
  have hV : (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001761 s action x ∂gammaMeasure s s) =
      ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure s s := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    exact _root_.GD.N0047.d023542 a B s ha hB hs x hx
  have hA : (∫⁻ x, _root_.GD.N0232.N0719.N0878.d001750 action x ∂gammaMeasure s s) =
      ∫⁻ x, ENNReal.ofReal (_root_.GD.N0047.d023533 a B s x) ∂gammaMeasure s s := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    simp only [_root_.GD.N0232.N0719.N0878.d001750, action, Real.sq_sqrt (_root_.GD.N0047.d023536 a B s ha hB hs x hx.le)]
  rw [hV, hA] at hv
  have heq : (∫⁻ x, ENNReal.ofReal (_root_.GD.N0047.d023533 a B s x) ∂gammaMeasure s s) =
      ENNReal.ofReal s * ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure s s := by
    rw [hv, ← mul_assoc, ENNReal.mul_inv_cancel
      (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hs0]) ENNReal.ofReal_ne_top, one_mul]
  obtain ⟨hH, hD, hF⟩ := _root_.GD.N0047.d023530 a B s ha hB hs0
  have hC := hD.add (hH.const_mul (s - 1))
  change Integrable (_root_.GD.N0047.d023533 a B s) (gammaMeasure s s) at hC
  have hCN : ∀ᵐ x ∂gammaMeasure s s, 0 ≤ _root_.GD.N0047.d023533 a B s x := by
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    exact _root_.GD.N0047.d023536 a B s ha hB hs x hx.le
  have hFN : ∀ᵐ x ∂gammaMeasure s s, 0 ≤ _root_.GD.N0033.N0285.d006800 a B x := by
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.2.1
  rw [← ofReal_integral_eq_lintegral_ofReal hC hCN,
    ← ofReal_integral_eq_lintegral_ofReal hF hFN, ← ENNReal.ofReal_mul hs0.le] at heq
  have hr := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hCN),
    ENNReal.toReal_ofReal (mul_nonneg hs0.le (integral_nonneg_of_ae hFN))] at hr
  change (∫ x, _root_.GD.N0033.N0285.d006801 a B x + (s - 1) * _root_.GD.N0047.d023527 a B x ∂gammaMeasure s s) = _ at hr
  rw [integral_add hD (hH.const_mul (s - 1)), integral_const_mul] at hr
  exact hr


theorem d023544
    (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s) :
    (∫ x, _root_.GD.N0033.N0285.d006801 a B x ∂gammaMeasure s s) ≤
      ∫ x, _root_.GD.N0033.N0285.d006800 a B x ∂gammaMeasure s s := by
  have heq := _root_.GD.N0047.d023543 a B s ha hB hs
  have hle := _root_.GD.N0047.d023532 a B s ha hB (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hs)]



theorem d023545
    (a B s : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (hs : 1 ≤ s) :
    (∫⁻ x, ENNReal.ofReal (a / (a + B * x) ^ 2) ∂gammaMeasure s s) ≤
      ∫⁻ x, ENNReal.ofReal (x / (a + B * x)) ∂gammaMeasure s s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨_hH, hD, hF⟩ := _root_.GD.N0047.d023530 a B s ha hB hs0
  have hDN : ∀ᵐ x ∂gammaMeasure s s, 0 ≤ _root_.GD.N0033.N0285.d006801 a B x := by
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.1.1
  have hFN : ∀ᵐ x ∂gammaMeasure s s, 0 ≤ _root_.GD.N0033.N0285.d006800 a B x := by
    filter_upwards [_root_.GD.N0047.d023528 s hs0] with x hx
    exact (_root_.GD.N0047.d023529 a B ha hB x hx.le).2.2.1
  change (∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006801 a B x) ∂gammaMeasure s s) ≤
    ∫⁻ x, ENNReal.ofReal (_root_.GD.N0033.N0285.d006800 a B x) ∂gammaMeasure s s
  rw [← ofReal_integral_eq_lintegral_ofReal hD hDN,
    ← ofReal_integral_eq_lintegral_ofReal hF hFN]
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0047.d023544 a B s ha hB hs)

end
end GD.N0047

#print axioms _root_.GD.N0047.d023540
#print axioms _root_.GD.N0047.d023543
#print axioms _root_.GD.N0047.d023544
#print axioms _root_.GD.N0047.d023545
