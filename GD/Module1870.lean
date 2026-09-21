import GD.Module1869
import GD.Module1331
import GD.Module1185





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0371
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1287
open _root_.GD.N0076.N0313


theorem d030640 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0101.N0368.d021679 t.1 =
      ∫ z, (z.1 - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 := by
  have hint : Integrable (fun z : _root_.GD.N0232.N0720.N1436.d013217 => (z.1 - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) := by
    simpa only [_root_.GD.N0232.N0720.N1424.d014839] using
      _root_.GD.N0232.N0720.N1287.d019524 2 2 (by decide) (by decide) t
  have hnon : 0 ≤ ∫ z : _root_.GD.N0232.N0720.N1436.d013217, (z.1 - t.1) ^ 2
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 := integral_nonneg (fun z => sq_nonneg (z.1 - t.1))
  rw [_root_.GD.N0101.N0368.d021680 t.2,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (fun z => sq_nonneg (z.1 - t.1))),
    ENNReal.toReal_ofReal hnon]



theorem d030641 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0076.N0313.d030565 2 2 (by decide) (by decide)
        (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) t) =
      t.1 * (1 - t.1) + _root_.GD.N0101.N0368.d021679 t.1 := by
  have h := _root_.GD.N0232.N0720.N1287.d019529 2 2 (by decide) (by decide)
    (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) t)
  have ho := _root_.GD.N0232.N0720.N1396.d014795 2 2
    (by decide) (by decide)
    (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) t)
  unfold _root_.GD.N0232.N0720.N1396.d014778 at ho
  rw [ho] at h
  simp only [_root_.GD.N0045.d023065,
    _root_.GD.N0045.d023066, one_mul, _root_.GD.N0232.N0720.N1424.d014839] at h
  unfold _root_.GD.N0076.N0313.d030565 _root_.GD.N0232.N0720.N1066.d014320
  have hnon : 0 ≤ ∫ z : _root_.GD.N0232.N0720.N1436.d013217, (z.1 - t.1) ^ 2
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 := integral_nonneg (fun z => sq_nonneg (z.1 - t.1))
  rw [h, ENNReal.toReal_ofReal
    (add_nonneg (mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le))
      hnon),
    ← _root_.GD.N0101.N0371.d030640 t]



theorem d030642 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0101.N0368.d021679 (1 - t) =
      _root_.GD.N0101.N0368.d021679 t := by
  let q : _root_.GD.N0232.N0720.N1441.d013676 := ⟨t, ht⟩
  let s : _root_.GD.N0232.N0720.N1441.d013676 := ⟨1 - t, by constructor <;> linarith [ht.1, ht.2]⟩
  have hparam :
      _root_.GD.N0045.d023064 2 2 (by decide) (by decide) s =
        _root_.GD.N0232.N0720.N1043.d019058
          (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) q) := by
    apply _root_.GD.N0232.N0720.N1215.d014277
    · rfl
    · change Real.sqrt ((2 : ℝ) * (1 - (1 - t))) = Real.sqrt ((2 : ℝ) * t)
      congr 1
      ring
    · rfl
  have hbudget :
      _root_.GD.N0076.N0313.d030565 2 2 (by decide) (by decide)
          (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) s) =
        _root_.GD.N0076.N0313.d030565 2 2 (by decide) (by decide)
          (_root_.GD.N0045.d023064 2 2 (by decide) (by decide) q) := by
    unfold _root_.GD.N0076.N0313.d030565 _root_.GD.N0232.N0720.N1066.d014320
    rw [hparam, _root_.GD.N0232.N0720.N1043.d019080 2 (by decide)]
  rw [_root_.GD.N0101.N0371.d030641 s, _root_.GD.N0101.N0371.d030641 q] at hbudget
  change (1 - t) * (1 - (1 - t)) + _root_.GD.N0101.N0368.d021679 (1 - t) =
    t * (1 - t) + _root_.GD.N0101.N0368.d021679 t at hbudget
  nlinarith




theorem d030643
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d)
    (hbound : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
      ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 2 2 (by decide) (by decide) θ)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) ≤
          c * _root_.GD.N0101.N0368.d021679 t.1 := by
  obtain ⟨g, hg, hgb, hcap⟩ := _root_.GD.N0101.N0384.d030639
    2 2 (by decide) (by decide) c hc d hd hbound
  refine ⟨g, hg, hgb, fun t => ?_⟩
  have ht := hcap t
  rw [_root_.GD.N0101.N0371.d030641 t] at ht
  change (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) ≤ _ at ht
  have horacle := mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc1) horacle]

end
end GD.N0101.N0371

#print axioms _root_.GD.N0101.N0371.d030640
#print axioms _root_.GD.N0101.N0371.d030641
#print axioms _root_.GD.N0101.N0371.d030642
#print axioms _root_.GD.N0101.N0371.d030643
