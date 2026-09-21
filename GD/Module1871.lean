import GD.Module1870

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0379
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1287
open _root_.GD.N0101.N0368 _root_.GD.N0101.N0371

def d030644 (F : ℝ → ℝ≥0∞) (a ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a ε, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) * (F t + F (1 - t))




theorem d030645 (F : ℝ → ℝ≥0∞) {q a ε : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hae : a ≤ ε) (he : ε < 1)
    (hcap : ∀ t ∈ Ioo (0 : ℝ) 1, F t ≤ ENNReal.ofReal (q * _root_.GD.N0101.N0368.d021679 t)) :
    _root_.GD.N0101.N0379.d030644 F a ε ≤
      ENNReal.ofReal (q * (Real.log (ε / a) + 2 * (ε - a))) := by
  have hnon (t : ℝ) : 0 ≤ _root_.GD.N0101.N0368.d021679 t := ENNReal.toReal_nonneg
  have hi := (_root_.GD.N0101.N0368.d021686 ha he).const_mul (q * 2)
  have hinon : 0 ≤ᵐ[volume.restrict (Ioo a ε)] (fun t => q * 2 * _root_.GD.N0101.N0368.d021683 t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (mul_nonneg hq (by norm_num))
      (mul_nonneg (hnon t) (Real.rpow_nonneg (ha.trans ht.1).le _))
  calc
    _ ≤ ∫⁻ t in Ioo a ε, ENNReal.ofReal (q * 2 * _root_.GD.N0101.N0368.d021683 t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans ht.1, ht.2.trans he⟩
      have hr := hcap (1 - t) ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
      rw [_root_.GD.N0101.N0371.d030642 ht'] at hr
      have hqB := mul_nonneg hq (hnon t)
      calc
        _ ≤ ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
            (ENNReal.ofReal (q * _root_.GD.N0101.N0368.d021679 t) + ENNReal.ofReal (q * _root_.GD.N0101.N0368.d021679 t)) :=
          mul_le_mul_right (add_le_add (hcap t ht') hr) _
        _ = _ := by
          rw [← ENNReal.ofReal_add hqB hqB,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg ht'.1.le _)]
          congr 1
          unfold _root_.GD.N0101.N0368.d021683
          ring
    _ = ENNReal.ofReal (∫ t in Ioo a ε, q * 2 * _root_.GD.N0101.N0368.d021683 t) :=
      (ofReal_integral_eq_lintegral_ofReal hi hinon).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul]
      have hb := mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0368.d021687 ha hae he)
        (mul_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith



theorem d030646
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) {q a ε : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hae : a ≤ ε) (he : ε < 1)
    (hcap : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) ≤ q * _root_.GD.N0101.N0368.d021679 t.1) :
    _root_.GD.N0101.N0379.d030644 (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) a ε ≤
      ENNReal.ofReal (q * (Real.log (ε / a) + 2 * (ε - a))) := by
  apply _root_.GD.N0101.N0379.d030645 _ hq ha hae he
  intro t ht
  have hi := _root_.GD.N0232.N0720.N1287.d019523 2 2 (by decide) (by decide)
    ⟨t, ht⟩ g hg hgb
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => sq_nonneg (g z - t)))]
  exact ENNReal.ofReal_le_ofReal (hcap ⟨t, ht⟩)

end
end GD.N0101.N0379

#print axioms _root_.GD.N0101.N0379.d030645
#print axioms _root_.GD.N0101.N0379.d030646
