import GD.Module1333
import GD.Module1332

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0387
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1236
open _root_.GD.N0101.N0376 _root_.GD.N0101.N0374

def d021709 (u : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) * (u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ)))

def d021710 (u s t : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, s) * t ^ (-(3 / 2 : ℝ))

theorem d021711 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0101.N0387.d021709 u := by
  unfold _root_.GD.N0101.N0387.d021709
  exact mul_pos (by positivity) (mul_pos (Real.rpow_pos_of_pos hu.1 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hu.2) _))

theorem d021712 {u a b R : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : b * R < 1) :
    ContinuousOn (fun x => _root_.GD.N0101.N0376.d021693 u (a * x) (b * x)) (Icc (0 : ℝ) R) := by
  have hQ : ∀ x ∈ Icc (0 : ℝ) R, 0 < _root_.GD.N0101.N0376.d021692 u (a * x) (b * x) := by
    intro x hx
    have ht0 : 0 ≤ b * x := mul_nonneg hb hx.1
    have ht1 : b * x < 1 := (mul_le_mul_of_nonneg_left hx.2 hb).trans_lt hR
    have hr0 : 0 ≤ a * x := mul_nonneg ha hx.1
    have heq : _root_.GD.N0101.N0376.d021692 u (a * x) (b * x) =
        (u + a * x) * (1 - b * x) + (b * x) * (1 - u) := by
      unfold _root_.GD.N0101.N0376.d021692
      ring
    rw [heq]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (add_pos_of_pos_of_nonneg hu.1 hr0) (sub_pos.mpr ht1))
      (mul_nonneg ht0 (sub_pos.mpr hu.2).le)
  have hp : Continuous (fun x : ℝ => (a * x) ^ (1 / 2 : ℝ) * (1 - b * x) ^ 2) := by
    apply Continuous.mul
    · exact (continuous_const.mul continuous_id).rpow_const (fun _ => Or.inr (by norm_num))
    · fun_prop
  have hqc : Continuous (fun x => _root_.GD.N0101.N0376.d021692 u (a * x) (b * x)) := by
    unfold _root_.GD.N0101.N0376.d021692
    fun_prop
  exact hp.continuousOn.mul (hqc.continuousOn.rpow_const
    (fun x hx => Or.inl (hQ x hx).ne'))

theorem d021713 {u s ε : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (he : ε < 1) :
    IntegrableOn (_root_.GD.N0101.N0387.d021710 u s) (Ioo (0 : ℝ) ε) := by
  have hc := _root_.GD.N0101.N0387.d021712 hu hs.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_mul] using he)
  have hi0 : IntegrableOn (fun t => _root_.GD.N0101.N0376.d021693 u (s * t) t)
      (Icc (0 : ℝ) ε) (volume : Measure ℝ) := by
    simpa only [one_mul] using (hc.integrableOn_Icc (μ := volume))
  have hi : IntegrableOn (fun t => _root_.GD.N0101.N0387.d021709 u * _root_.GD.N0101.N0376.d021693 u (s * t) t)
      (Ioo (0 : ℝ) ε) := by
    exact (hi0.mono_set Ioo_subset_Icc_self).const_mul (_root_.GD.N0101.N0387.d021709 u)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioo
  intro t ht
  exact (_root_.GD.N0101.N0376.d021696 ⟨ht.1, ht.2.trans he⟩ hu hs).symm

theorem d021714 {u s R : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hR : R / s < 1) :
    IntegrableOn (fun r => _root_.GD.N0101.N0376.d021693 u r (r / s)) (Ioo (0 : ℝ) R) := by
  have hc := _root_.GD.N0101.N0387.d021712 hu (by norm_num : (0 : ℝ) ≤ 1)
    (inv_nonneg.mpr hs.le) (by simpa only [div_eq_mul_inv, mul_comm] using hR)
  have hi0 : IntegrableOn (fun r => _root_.GD.N0101.N0376.d021693 u r (r / s))
      (Icc (0 : ℝ) R) (volume : Measure ℝ) := by
    simpa only [one_mul, mul_one, div_eq_mul_inv, mul_comm] using (hc.integrableOn_Icc (μ := volume))
  exact hi0.mono_set Ioo_subset_Icc_self



theorem d021715 {u s R δ ε c : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hR : 0 < R)
    (hδu : δ ≤ u) (he : ε < 1) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (hRs : R ≤ s * ε) :
    _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) *
        (2 / (3 * u) - 1 / R) ≤
      s * ∫ t in Ioo (0 : ℝ) ε, _root_.GD.N0101.N0387.d021710 u s t := by
  have hRe : R / s ≤ ε := (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hRs)
  have hR1 : R / s < 1 := hRe.trans_lt he
  have hi := _root_.GD.N0101.N0387.d021714 hu hs hR1
  let K : ℝ := (1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
    (zero_le_one.trans hc) _)
  have hbase : IntegrableOn (_root_.GD.N0232.N0720.N1236.d016213 u 1) (Ioo (0 : ℝ) R) :=
    (_root_.GD.N0232.N0720.N1236.d016216 hu.1 (by norm_num)).mono_set
      (fun _ hx => hx.1)
  have hb := setIntegral_mono_on (hbase.const_mul K) hi measurableSet_Ioo
    (fun r hr => _root_.GD.N0101.N0376.d021697 hu hr.1
      ⟨div_pos hr.1 hs, ((div_lt_div_of_pos_right hr.2 hs).trans_le hRe).trans he⟩
      hδu ((div_lt_div_of_pos_right hr.2 hs).le.trans hRe) he hc hec)
  rw [integral_const_mul] at hb
  have hmass : K * (2 / (3 * u) - 1 / R) ≤
      ∫ r in Ioo (0 : ℝ) R, _root_.GD.N0101.N0376.d021693 u r (r / s) :=
    (mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0374.d021691 hu.1 hR) hK).trans hb
  have hweighted : (∫ r in Ioo (0 : ℝ) R, _root_.GD.N0101.N0387.d021710 u s (r / s)) =
      _root_.GD.N0101.N0387.d021709 u * ∫ r in Ioo (0 : ℝ) R, _root_.GD.N0101.N0376.d021693 u r (r / s) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have ht : r / s ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hr.1 hs, (div_lt_div_of_pos_right hr.2 hs).trans hR1⟩
    simpa only [_root_.GD.N0101.N0387.d021710, _root_.GD.N0101.N0387.d021709, mul_div_cancel₀ _ hs.ne'] using
      _root_.GD.N0101.N0376.d021696 ht hu hs
  have hchange := intervalIntegral.integral_comp_div
    (_root_.GD.N0101.N0387.d021710 u s) (a := 0) (b := R) hs.ne'
  rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo,
    zero_div, intervalIntegral.integral_of_le (div_pos hR hs).le,
    integral_Ioc_eq_integral_Ioo, smul_eq_mul] at hchange
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) ε)] _root_.GD.N0101.N0387.d021710 u s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    unfold _root_.GD.N0101.N0387.d021710
    exact mul_nonneg (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (x := (u, s))
      (by norm_num) (by norm_num)
      ht.1 (ht.2.trans he) ⟨hu, hs⟩).le (Real.rpow_nonneg ht.1.le _)
  have hsubset : Ioo (0 : ℝ) (R / s) ≤ᵐ[volume] Ioo (0 : ℝ) ε :=
    ae_of_all _ (fun _ ht => ⟨ht.1, ht.2.trans_le hRe⟩)
  have hmono := setIntegral_mono_set (_root_.GD.N0101.N0387.d021713 hu hs he) hnonneg hsubset
  calc
    _ = _root_.GD.N0101.N0387.d021709 u * (K * (2 / (3 * u) - 1 / R)) := by dsimp [K]; ring
    _ ≤ _root_.GD.N0101.N0387.d021709 u * ∫ r in Ioo (0 : ℝ) R, _root_.GD.N0101.N0376.d021693 u r (r / s) :=
      mul_le_mul_of_nonneg_left hmass (_root_.GD.N0101.N0387.d021711 hu).le
    _ = s * ∫ t in Ioo (0 : ℝ) (R / s), _root_.GD.N0101.N0387.d021710 u s t := by
      rw [← hweighted, hchange]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hs.le



theorem d021716 {u s H R a δ ε c : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hH : 0 < H) (hHR : H ≤ R)
    (ha : 0 ≤ a) (hδu : δ ≤ u) (he : ε < 1) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (haH : s * a ≤ H) (hRs : R ≤ s * ε) :
    _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) *
        (∫ r in Ioo H R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r) ≤
      s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t := by
  have hR : 0 < R := hH.trans_le hHR
  have hRe : R / s ≤ ε := (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hRs)
  have hR1 : R / s < 1 := hRe.trans_lt he
  have haHs : a ≤ H / s := (le_div_iff₀ hs).mpr (by simpa [mul_comm] using haH)
  have hset : Ioo H R ⊆ Ioo (0 : ℝ) R := fun _ hx => ⟨hH.trans hx.1, hx.2⟩
  have hi := (_root_.GD.N0101.N0387.d021714 hu hs hR1).mono_set hset
  let K : ℝ := (1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))
  have hbase : IntegrableOn (_root_.GD.N0232.N0720.N1236.d016213 u 1) (Ioo H R) :=
    (_root_.GD.N0232.N0720.N1236.d016216 hu.1 (by norm_num)).mono_set
      (fun _ hx => hH.trans hx.1)
  have hb := setIntegral_mono_on (hbase.const_mul K) hi measurableSet_Ioo
    (fun r hr => _root_.GD.N0101.N0376.d021697 hu (hH.trans hr.1)
      ⟨div_pos (hH.trans hr.1) hs,
        ((div_lt_div_of_pos_right hr.2 hs).trans_le hRe).trans he⟩
      hδu ((div_lt_div_of_pos_right hr.2 hs).le.trans hRe) he hc hec)
  rw [integral_const_mul] at hb
  have hweighted : (∫ r in Ioo H R, _root_.GD.N0101.N0387.d021710 u s (r / s)) =
      _root_.GD.N0101.N0387.d021709 u * ∫ r in Ioo H R, _root_.GD.N0101.N0376.d021693 u r (r / s) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have ht : r / s ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (hH.trans hr.1) hs, (div_lt_div_of_pos_right hr.2 hs).trans hR1⟩
    simpa only [_root_.GD.N0101.N0387.d021710, _root_.GD.N0101.N0387.d021709, mul_div_cancel₀ _ hs.ne'] using
      _root_.GD.N0101.N0376.d021696 ht hu hs
  have hchange := intervalIntegral.integral_comp_div
    (_root_.GD.N0101.N0387.d021710 u s) (a := H) (b := R) hs.ne'
  rw [intervalIntegral.integral_of_le hHR, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (div_le_div_of_nonneg_right hHR hs.le),
    integral_Ioc_eq_integral_Ioo, smul_eq_mul] at hchange
  have hW : IntegrableOn (_root_.GD.N0101.N0387.d021710 u s) (Ioo a ε) :=
    (_root_.GD.N0101.N0387.d021713 hu hs he).mono_set
      (fun _ ht => ⟨ha.trans_lt ht.1, ht.2⟩)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo a ε)] _root_.GD.N0101.N0387.d021710 u s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    unfold _root_.GD.N0101.N0387.d021710
    exact mul_nonneg (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (x := (u, s))
      (by norm_num) (by norm_num)
      (ha.trans_lt ht.1) (ht.2.trans he) ⟨hu, hs⟩).le
      (Real.rpow_nonneg (ha.trans_lt ht.1).le _)
  have hsubset : Ioo (H / s) (R / s) ≤ᵐ[volume] Ioo a ε :=
    ae_of_all _ (fun _ ht => ⟨haHs.trans_lt ht.1, ht.2.trans_le hRe⟩)
  have hmono := setIntegral_mono_set hW hnonneg hsubset
  calc
    _ = _root_.GD.N0101.N0387.d021709 u * (K * ∫ r in Ioo H R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r) := by
      dsimp [K]
      ring
    _ ≤ _root_.GD.N0101.N0387.d021709 u * ∫ r in Ioo H R, _root_.GD.N0101.N0376.d021693 u r (r / s) :=
      mul_le_mul_of_nonneg_left hb (_root_.GD.N0101.N0387.d021711 hu).le
    _ = s * ∫ t in Ioo (H / s) (R / s), _root_.GD.N0101.N0387.d021710 u s t := by
      rw [← hweighted, hchange]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hs.le

end
end GD.N0101.N0387

#print axioms _root_.GD.N0101.N0387.d021712
#print axioms _root_.GD.N0101.N0387.d021713
#print axioms _root_.GD.N0101.N0387.d021715
#print axioms _root_.GD.N0101.N0387.d021716
