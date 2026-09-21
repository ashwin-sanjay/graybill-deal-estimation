import Mathlib.MeasureTheory.Function.Jacobian
import GD.Module0415
import GD.Module0419

















namespace GD.N0123

open MeasureTheory Set
open _root_.GD.N0124
open scoped ENNReal


theorem d006491 : MeasurableSet _root_.GD.N0124.d006388 := by
  have h :
      _root_.GD.N0124.d006388 = Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext p
    simp [_root_.GD.N0124.d006388]
  rw [h]
  exact measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi)


theorem d006492 : MeasurableSet _root_.GD.N0124.d006389 := by
  have h :
      _root_.GD.N0124.d006389 = Ioo (0 : ℝ) 1 ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext p
    simp [_root_.GD.N0124.d006389, and_assoc]
  rw [h]
  exact measurableSet_Ioo.prod (measurableSet_Ioi.prod measurableSet_Ioi)



theorem d006493 {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    _root_.GD.N0124.d006392 e '' _root_.GD.N0124.d006389 = _root_.GD.N0124.d006388 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact _root_.GD.N0124.d006395 he0 he1 hq
  · intro hp
    refine ⟨_root_.GD.N0124.d006391 e p, _root_.GD.N0124.d006394 he0 he1 hp, ?_⟩
    exact _root_.GD.N0124.d006396 he0 he1 hp


theorem d006494 {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    Set.InjOn (_root_.GD.N0124.d006392 e) _root_.GD.N0124.d006389 := by
  intro p hp q hq hpq
  rw [← _root_.GD.N0124.d006397 he0 he1 hp, ← _root_.GD.N0124.d006397 he0 he1 hq, hpq]



theorem d006495 {e : ℝ} (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    (_root_.GD.N0124.d006409 e p).det = p.2.2 ^ 2 / (e * (1 - e)) := by
  rw [ContinuousLinearMap.det]
  change LinearMap.det (_root_.GD.N0124.d006408 e p) =
    p.2.2 ^ 2 / (e * (1 - e))
  have hconj :
      LinearMap.det (_root_.GD.N0124.d006414 e p) =
        LinearMap.det (_root_.GD.N0124.d006408 e p) := by
    exact LinearMap.det_conj (_root_.GD.N0124.d006408 e p) _root_.GD.N0124.d006407
  rw [← hconj, ← LinearMap.det_toMatrix']
  exact _root_.GD.N0124.d006417 p he h1e



theorem d006496 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    |(_root_.GD.N0124.d006409 e p).det| = p.2.2 ^ 2 / (e * (1 - e)) := by
  rw [_root_.GD.N0123.d006495 p (ne_of_gt he0) (ne_of_gt (sub_pos.mpr he1)),
    abs_of_pos]
  exact div_pos (sq_pos_of_pos hp.2.2.2)
    (mul_pos he0 (sub_pos.mpr he1))






theorem d006497
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (g : _root_.GD.N0124.d006387 → E) :
    (∫ p in _root_.GD.N0124.d006388, g p)
      =
    ∫ p in _root_.GD.N0124.d006389,
      (p.2.2 ^ 2 / (e * (1 - e))) • g (_root_.GD.N0124.d006392 e p) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure (volume : Measure _root_.GD.N0124.d006387) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [← _root_.GD.N0123.d006493 he0 he1]
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    volume _root_.GD.N0123.d006492
    (fun p _ ↦ (_root_.GD.N0124.d006411 e p).hasFDerivWithinAt)
    (_root_.GD.N0123.d006494 he0 he1) g]
  apply setIntegral_congr_fun _root_.GD.N0123.d006492
  intro p hp
  change |(_root_.GD.N0124.d006409 e p).det| • g (_root_.GD.N0124.d006392 e p) =
    (p.2.2 ^ 2 / (e * (1 - e))) • g (_root_.GD.N0124.d006392 e p)
  rw [_root_.GD.N0123.d006496 he0 he1 hp]



theorem d006498
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (g : _root_.GD.N0124.d006387 → ℝ≥0∞) :
    (∫⁻ p in _root_.GD.N0124.d006388, g p)
      =
    ∫⁻ p in _root_.GD.N0124.d006389,
      ENNReal.ofReal (p.2.2 ^ 2 / (e * (1 - e))) * g (_root_.GD.N0124.d006392 e p) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure (volume : Measure _root_.GD.N0124.d006387) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [← _root_.GD.N0123.d006493 he0 he1]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    volume _root_.GD.N0123.d006492
    (fun p _ ↦ (_root_.GD.N0124.d006411 e p).hasFDerivWithinAt)
    (_root_.GD.N0123.d006494 he0 he1) g]
  apply setLIntegral_congr_fun _root_.GD.N0123.d006492
  intro p hp
  change ENNReal.ofReal |(_root_.GD.N0124.d006409 e p).det| * g (_root_.GD.N0124.d006392 e p) =
    ENNReal.ofReal (p.2.2 ^ 2 / (e * (1 - e))) * g (_root_.GD.N0124.d006392 e p)
  rw [_root_.GD.N0123.d006496 he0 he1 hp]






noncomputable def d006499 (α β : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  p.1 ^ (α - 1) * p.2.1 ^ (β - 1) * p.2.2 ^ ((1 : ℝ) / 2) *
    Real.exp (-(α * p.1 + β * p.2.1 + p.2.2 / 2))


noncomputable def d006500 (α β : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  p.1 ^ (β - 1) * (1 - p.1) ^ (α - 1) *
    p.2.1 ^ ((1 : ℝ) / 2)


noncomputable def d006501 (α β e : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  α * e * (1 - p.1) + β * (1 - e) * p.1 +
    p.2.1 * e * (1 - e) / 2


theorem d006502 {e : ℝ} (α β : ℝ) (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    α * (_root_.GD.N0124.d006392 e p).1 + β * (_root_.GD.N0124.d006392 e p).2.1 +
        (_root_.GD.N0124.d006392 e p).2.2 / 2
      =
    _root_.GD.N0123.d006501 α β e p / (e * (1 - e)) * p.2.2 := by
  simp only [_root_.GD.N0124.d006392, _root_.GD.N0123.d006501]
  field_simp [he, h1e]



theorem d006503 {e : ℝ} (α β : ℝ) (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    Real.exp (-(α * (_root_.GD.N0124.d006392 e p).1 + β * (_root_.GD.N0124.d006392 e p).2.1 +
        (_root_.GD.N0124.d006392 e p).2.2 / 2))
      =
    Real.exp (-(_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) * p.2.2)) := by
  rw [_root_.GD.N0123.d006502 α β p he h1e]



theorem d006504 {α β e : ℝ} {p : _root_.GD.N0124.d006387}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    0 < _root_.GD.N0123.d006501 α β e p := by
  unfold _root_.GD.N0123.d006501
  have h1e : 0 < 1 - e := sub_pos.mpr he1
  have h1l : 0 < 1 - p.1 := sub_pos.mpr hp.2.1
  exact add_pos
    (add_pos (mul_pos (mul_pos hα he0) h1l)
      (mul_pos (mul_pos hβ h1e) hp.1))
    (div_pos (mul_pos (mul_pos hp.2.2.1 he0) h1e) (by norm_num))




theorem d006505 {α β e C : ℝ} {p : _root_.GD.N0124.d006387}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    ∫ H : ℝ in Ioi 0,
        C * (H ^ ((α + β + (3 : ℝ) / 2) - 1) *
          Real.exp (-
            ((_root_.GD.N0123.d006501 α β e p / (e * (1 - e))) * H)))
      =
    C * Real.Gamma (α + β + (3 : ℝ) / 2) *
      (_root_.GD.N0123.d006501 α β e p / (e * (1 - e))) ^
        (-(α + β + (3 : ℝ) / 2)) := by
  apply _root_.GD.N0133.d006490 hα hβ
  exact div_pos (_root_.GD.N0123.d006504 hα hβ he0 he1 hp)
    (mul_pos he0 (sub_pos.mpr he1))

end GD.N0123
