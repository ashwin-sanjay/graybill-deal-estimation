import GD.Module0433
import GD.Module0465
import GD.Module1465
import GD.Module1323
import GD.Module0699

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0402
noncomputable section

open _root_.GD.N0213.N0495
open _root_.GD.N0213.N0520
open _root_.GD.N0213.N0519
open _root_.GD.N0101.N0407
open _root_.GD.N0232.N0719.N0876
open _root_.GD.N0232.N0719.N0910

variable {k : ℕ}

def d023083 (s r : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun i => gammaMeasure (s i + 1) (r i))

def d023084 (z : Fin k → ℝ) : ℝ := ∑ i, z i

@[fun_prop] theorem d023085 : Measurable (_root_.GD.N0101.N0402.d023084 (k := k)) := by
  unfold _root_.GD.N0101.N0402.d023084
  fun_prop

theorem d023086 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) :
    IsProbabilityMeasure (_root_.GD.N0101.N0402.d023083 s r) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (s i + 1) (r i)) :=
    isProbabilityMeasure_gammaMeasure (by linarith [hs i]) (hr i)
  unfold _root_.GD.N0101.N0402.d023083
  infer_instance

theorem d023087 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) :
    Integrable (fun z => _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2) (_root_.GD.N0101.N0402.d023083 s r) := by
  letI := _root_.GD.N0101.N0402.d023086 s r hs hr
  apply (integrable_const (1 : ℝ)).mono'
    (((_root_.GD.N0101.N0407.d007203 L).comp _root_.GD.N0101.N0402.d023085).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun z => _root_.GD.N0213.N0519.d007983 L (_root_.GD.N0101.N0402.d023084 z))

theorem d023088 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) (i : Fin k) :
    Integrable (fun z => (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2) (_root_.GD.N0101.N0402.d023083 s r) := by
  let μ : Fin k → Measure ℝ := fun j => gammaMeasure (s j + 1) (r j)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) :=
    isProbabilityMeasure_gammaMeasure (by linarith [hs j]) (hr j)
  have hi : Integrable (fun z : Fin k → ℝ => (z i)⁻¹) (_root_.GD.N0101.N0402.d023083 s r) :=
    integrable_comp_eval (μ := μ)
      (_root_.GD.N0232.N0719.N0876.d020682 (by linarith [hs i]) (hr i))
  apply hi.norm.mono' (by unfold _root_.GD.N0213.N0495.d007174 _root_.GD.N0101.N0402.d023084; fun_prop)
  filter_upwards with z
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (_root_.GD.N0213.N0519.d007983 L (_root_.GD.N0101.N0402.d023084 z))

theorem d023089 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) {L : ℝ} (hL : 0 < L) :
    Integrable (fun z => _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) * _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z))
      (_root_.GD.N0101.N0402.d023083 s r) := by
  letI := _root_.GD.N0101.N0402.d023086 s r hs hr
  exact _root_.GD.N0101.N0407.d007210 hL _root_.GD.N0101.N0402.d023085

theorem d023090 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) {L : ℝ} (hL : 0 < L) :
    Integrable (fun z => _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ^ 2) (_root_.GD.N0101.N0402.d023083 s r) := by
  letI := _root_.GD.N0101.N0402.d023086 s r hs hr
  exact _root_.GD.N0101.N0407.d007208 hL _root_.GD.N0101.N0402.d023085

theorem d023091 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) :
    0 < ∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r := by
  letI := _root_.GD.N0101.N0402.d023086 s r hs hr
  apply (integral_pos_iff_support_of_nonneg (fun z => sq_nonneg _)
    (_root_.GD.N0101.N0402.d023087 s r hs hr L)).mpr
  have hsupport : Function.support (fun z : Fin k → ℝ => _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2) = univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sq_pos_of_pos (_root_.GD.N0213.N0495.d007176 L (_root_.GD.N0101.N0402.d023084 z))).ne'
  rw [hsupport, measure_univ]
  exact zero_lt_one



theorem d023092 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) {L : ℝ} (hL : 0 < L) :
    (∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) * _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ∂_root_.GD.N0101.N0402.d023083 s r) ^ 2 ≤
      (∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) *
        (∫ z, _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) := by
  let f : (Fin k → ℝ) → ℝ := fun z => _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z)
  let g : (Fin k → ℝ) → ℝ := fun z => _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z)
  let m := ∫ z, f z ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r
  let e := ∫ z, f z * g z ∂_root_.GD.N0101.N0402.d023083 s r
  let D := ∫ z, g z ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r
  have hm : 0 < m := _root_.GD.N0101.N0402.d023091 s r hs hr L
  have hff : Integrable (fun z => f z ^ 2) (_root_.GD.N0101.N0402.d023083 s r) :=
    _root_.GD.N0101.N0402.d023087 s r hs hr L
  have hfg : Integrable (fun z => f z * g z) (_root_.GD.N0101.N0402.d023083 s r) :=
    _root_.GD.N0101.N0402.d023089 s r hs hr hL
  have hgg : Integrable (fun z => g z ^ 2) (_root_.GD.N0101.N0402.d023083 s r) :=
    _root_.GD.N0101.N0402.d023090 s r hs hr hL
  have hnonneg : 0 ≤ ∫ z, (m * g z - e * f z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r :=
    integral_nonneg (fun z => sq_nonneg _)
  have hexpand : (∫ z, (m * g z - e * f z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) =
      m ^ 2 * D - (2 * m * e) * e + e ^ 2 * m := by
    have heq : (fun z => (m * g z - e * f z) ^ 2) =
        (fun z => m ^ 2 * g z ^ 2 - (2 * m * e) * (f z * g z) + e ^ 2 * f z ^ 2) := by
      funext z
      ring
    rw [heq, integral_add
      (f := fun z => m ^ 2 * g z ^ 2 - (2 * m * e) * (f z * g z))
      (g := fun z => e ^ 2 * f z ^ 2)
      ((hgg.const_mul _).sub (hfg.const_mul _)) (hff.const_mul _),
      integral_sub (f := fun z => m ^ 2 * g z ^ 2)
        (g := fun z => (2 * m * e) * (f z * g z))
        (hgg.const_mul _) (hfg.const_mul _)]
    simp only [integral_const_mul, m, e, D]
  rw [hexpand] at hnonneg
  change e ^ 2 ≤ m * D
  by_contra h
  have hneg := mul_neg_of_pos_of_neg hm (sub_neg.mpr (lt_of_not_ge h))
  nlinarith




theorem d023093 {n : ℕ}
    (s r : Fin (n + 1) → ℝ) (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    {L : ℝ} (hL : 0 < L) (i : Fin (n + 1)) :
    (∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) =
      (r i / s i) * (∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) -
        (2 / s i) * (∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) * _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z)
          ∂_root_.GD.N0101.N0402.d023083 s r) := by
  let μ : Fin (n + 1) → Measure ℝ := fun j => gammaMeasure (s j + 1) (r j)
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun j => μ (i.succAbove j))
  letI (j : Fin (n + 1)) : IsProbabilityMeasure (μ j) :=
    isProbabilityMeasure_gammaMeasure (by linarith [hs j]) (hr j)
  have hsplit (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F (_root_.GD.N0101.N0402.d023083 s r)) :
      (∫ z, F z ∂_root_.GD.N0101.N0402.d023083 s r) = ∫ y, ∫ x, F (i.insertNth x y) ∂μ i ∂ν :=
    _root_.GD.N0101.N0352.d006732 μ i F hF
  have hsum (x : ℝ) (y : Fin n → ℝ) : _root_.GD.N0101.N0402.d023084 (i.insertNth x y) = x + ∑ j, y j := by
    exact Fin.sum_insertNth i x y
  have hm := hsplit _ (_root_.GD.N0101.N0402.d023087 s r hs hr L)
  have he := hsplit _ (_root_.GD.N0101.N0402.d023089 s r hs hr hL)
  have hi := hsplit _ (_root_.GD.N0101.N0402.d023088 s r hs hr L i)
  simp only [hsum, Fin.insertNth_apply_same] at hm he hi
  rw [hi, hm, he]
  have hmass : Integrable
      (fun y => ∫ x, _root_.GD.N0213.N0495.d007174 L (x + ∑ j, y j) ^ 2 ∂μ i) ν := by
    have h := (_root_.GD.N0101.N0402.d023087 s r hs hr L)
    have hp := (measurePreserving_piFinSuccAbove μ i).symm
    have hi' := (hp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurableEmbedding).mpr h
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, hsum] using hi'.integral_prod_right
  have hscore : Integrable
      (fun y => ∫ x, _root_.GD.N0213.N0495.d007174 L (x + ∑ j, y j) *
        _root_.GD.N0213.N0495.d007175 L (x + ∑ j, y j) ∂μ i) ν := by
    have h := (_root_.GD.N0101.N0402.d023089 s r hs hr hL)
    have hp := (measurePreserving_piFinSuccAbove μ i).symm
    have hi' := (hp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurableEmbedding).mpr h
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, hsum] using hi'.integral_prod_right
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hmass.const_mul _) (hscore.const_mul _)]
  apply integral_congr_ae
  have hpos : ∀ᵐ y ∂ν, ∀ j, 0 < y j := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun j => μ (i.succAbove j)) j).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0910.d010286 (by linarith [hs (i.succAbove j)]) (hr (i.succAbove j)))
  filter_upwards [hpos] with y hy
  exact _root_.GD.N0213.N0520.d023082 (hs i) (hr i) hL
    (Finset.sum_nonneg fun j _ => (hy j).le)

end
end GD.N0101.N0402

#print axioms _root_.GD.N0101.N0402.d023087
#print axioms _root_.GD.N0101.N0402.d023088
#print axioms _root_.GD.N0101.N0402.d023089
#print axioms _root_.GD.N0101.N0402.d023090
#print axioms _root_.GD.N0101.N0402.d023091
#print axioms _root_.GD.N0101.N0402.d023092
#print axioms _root_.GD.N0101.N0402.d023093
