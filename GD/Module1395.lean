import GD.Module1394














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0158
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0163 _root_.GD.N0179 _root_.GD.N0203
open _root_.GD.N0165 _root_.GD.N0168
open _root_.GD.N0174 _root_.GD.N0198
open _root_.GD.N0176 _root_.GD.N0175

local instance d022458 (eta a b : ℝ) : SFinite (_root_.GD.N0198.d022440 eta a b) := by
  unfold _root_.GD.N0198.d022440
  infer_instance

private theorem d022459 {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    ContinuousAt (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 p.1 p.2) (u, x) := by
  have hD : 0 < x + 2 * u := by linarith
  unfold _root_.GD.N0179.d006018
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact (mul_pos (pow_pos hD 3) (Real.sqrt_pos.mpr hD)).ne'


theorem d022460 {eta a b : ℝ} (heta : 0 < eta) (ha : 0 < a) :
    Integrable (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 p.1 p.2) (_root_.GD.N0198.d022440 eta a b) ∧
      Integrable (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 (1 - p.1) p.2) (_root_.GD.N0198.d022440 eta a b) := by
  let K : Set _root_.GD.N0232.N0720.N1436.d013217 := Icc eta (1 - eta) ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc0 : ContinuousOn (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 p.1 p.2) K := by
    intro p hp
    exact (_root_.GD.N0158.d022459 (heta.trans_le hp.1.1)
      (ha.trans_le hp.2.1)).continuousWithinAt
  have hc1 : ContinuousOn (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 (1 - p.1) p.2) K := by
    intro p hp
    have hu : 0 < 1 - p.1 := by linarith [hp.1.2]
    have hmap : Continuous (fun p : _root_.GD.N0232.N0720.N1436.d013217 => (1 - p.1, p.2)) := by fun_prop
    have hk : ContinuousAt
        (fun q : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 q.1 q.2) (1 - p.1, p.2) :=
      _root_.GD.N0158.d022459 hu (ha.trans_le hp.2.1)
    exact (hk.comp (f := fun q : _root_.GD.N0232.N0720.N1436.d013217 => (1 - q.1, q.2))
      (x := p) hmap.continuousAt).continuousWithinAt
  have hsub : Ioc eta (1 - eta) ×ˢ Ioc a b ⊆ K :=
    fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
  have hi0 : IntegrableOn (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 p.1 p.2) K volume :=
    hc0.integrableOn_compact hK
  have hi1 : IntegrableOn (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0179.d006018 (1 - p.1) p.2) K volume :=
    hc1.integrableOn_compact hK
  have h0 := IntegrableOn.mono_set hi0 hsub
  have h1 := IntegrableOn.mono_set hi1 hsub
  constructor
  · simpa only [IntegrableOn, _root_.GD.N0198.d022440, Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod] using h0
  · simpa only [IntegrableOn, _root_.GD.N0198.d022440, Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod] using h1

private theorem d022461 {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ‖v ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v)]
  simpa only [one_pow] using pow_le_pow_left₀ hv.1 hv.2 2


theorem d022462 {eta a b : ℝ} (heta : 0 < eta) (ha : 0 < a)
    (d l r : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × ℝ => _root_.GD.N0168.d022367 d z.1.1 z.1.2 g z.2)
      ((_root_.GD.N0198.d022440 eta a b).prod (volume.restrict (Ioc l r))) := by
  have hk := _root_.GD.N0158.d022460 (b := b) heta ha
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc l r) volume :=
    (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume l r from intervalIntegral.intervalIntegrable_const).1
  have hb0 := hk.1.mul_prod hc
  have hb1 := hk.2.mul_prod hc
  have hv : Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
      _root_.GD.N0163.d022211 g (z.1.1, Real.exp z.2)) :=
    (_root_.GD.N0163.d022213 g hg).comp (by fun_prop)
  have hv01 := fun z : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
    _root_.GD.N0163.d022214 g h01 (z.1.1, Real.exp z.2)
  have h0 := Integrable.mul_bdd hb0
    (show Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
      _root_.GD.N0163.d022211 g (z.1.1, Real.exp z.2) ^ 2) by fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun z => _root_.GD.N0158.d022461 (hv01 z)))
  have h1 := Integrable.mul_bdd hb1
    (show Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
      (1 - _root_.GD.N0163.d022211 g (z.1.1, Real.exp z.2)) ^ 2) by fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun z => _root_.GD.N0158.d022461
      ⟨by linarith [(hv01 z).2], by linarith [(hv01 z).1]⟩))
  apply ((h0.add h1).sub ((hb0.add hb1).const_mul (2 * d))).congr
  exact ae_of_all _ (fun z => by simp [_root_.GD.N0168.d022367])


theorem d022463 {eta a b A T : ℝ}
    (heta : 0 < eta) (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a / (2 * T) *
      (∫ u in eta..(1 - eta), ∫ x in a..b,
        ∫ y in (A + Real.log b)..(A + T + Real.log a), _root_.GD.N0168.d022367 (Real.exp (-A)) u x g y) ≤
      _root_.GD.N0174.d022397 A T g := by
  have hA0 : 0 < A := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hA
  have hT : 0 < T := (Real.log_pos ((one_lt_div ha).mpr hab)).trans hwindow
  have hAB : A ≤ A + T := by linarith
  have hU : eta ≤ 1 - eta := by linarith
  have hW := (_root_.GD.N0176.d022350 ha (ha.trans hab) hwindow A).le
  have hc := _root_.GD.N0158.d022462 (b := b) heta ha (Real.exp (-A))
    (A + Real.log b) (A + T + Real.log a) g hg h01
  have he := _root_.GD.N0198.d022456 (B := A + T) (b := b) hA0 heta ha g hg h01
  have hcy : Integrable (fun p : _root_.GD.N0232.N0720.N1436.d013217 =>
      ∫ y in (A + Real.log b)..(A + T + Real.log a), _root_.GD.N0168.d022367 (Real.exp (-A)) p.1 p.2 g y)
      (_root_.GD.N0198.d022440 eta a b) := by
    simpa only [intervalIntegral.integral_of_le hW] using hc.integral_prod_left
  have her : Integrable (fun p : _root_.GD.N0232.N0720.N1436.d013217 =>
      ∫ r in A..(A + T), _root_.GD.N0168.d022365 p.1 p.2 g r) (_root_.GD.N0198.d022440 eta a b) := by
    simpa only [intervalIntegral.integral_of_le hAB] using he.integral_prod_right
  have hpoint : (∫ p, (∫ y in (A + Real.log b)..(A + T + Real.log a),
      _root_.GD.N0168.d022367 (Real.exp (-A)) p.1 p.2 g y) ∂_root_.GD.N0198.d022440 eta a b) ≤
      ∫ p, (∫ r in A..(A + T), _root_.GD.N0168.d022365 p.1 p.2 g r) ∂_root_.GD.N0198.d022440 eta a b := by
    apply integral_mono_ae hcy her
    have hmem : ∀ᵐ p : _root_.GD.N0232.N0720.N1436.d013217 ∂_root_.GD.N0198.d022440 eta a b,
        p ∈ Ioc eta (1 - eta) ×ˢ Ioc a b := by
      simpa only [_root_.GD.N0198.d022440, Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod] using
        (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc) :
          ∀ᵐ p : _root_.GD.N0232.N0720.N1436.d013217 ∂volume.restrict (Ioc eta (1 - eta) ×ˢ Ioc a b),
            p ∈ Ioc eta (1 - eta) ×ˢ Ioc a b)
    filter_upwards [hmem] with p hp
    exact _root_.GD.N0168.d022380 ha hab hp.2.1.le hp.2.2
      (heta.trans hp.1.1) (by linarith [hp.1.2]) hwindow A g hg h01
  have hceq : (∫ p, (∫ y in (A + Real.log b)..(A + T + Real.log a),
      _root_.GD.N0168.d022367 (Real.exp (-A)) p.1 p.2 g y) ∂_root_.GD.N0198.d022440 eta a b) =
      ∫ u in eta..(1 - eta), ∫ x in a..b,
        ∫ y in (A + Real.log b)..(A + T + Real.log a), _root_.GD.N0168.d022367 (Real.exp (-A)) u x g y := by
    simpa only [_root_.GD.N0198.d022440, intervalIntegral.integral_of_le hU,
      intervalIntegral.integral_of_le hab.le] using
        (MeasureTheory.integral_prod (fun p : _root_.GD.N0232.N0720.N1436.d013217 =>
          ∫ y in (A + Real.log b)..(A + T + Real.log a),
            _root_.GD.N0168.d022367 (Real.exp (-A)) p.1 p.2 g y) hcy)
  have heeq : (∫ p, (∫ r in A..(A + T), _root_.GD.N0168.d022365 p.1 p.2 g r) ∂_root_.GD.N0198.d022440 eta a b) =
      ∫ u in eta..(1 - eta), ∫ x in a..b, ∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r := by
    simpa only [_root_.GD.N0198.d022440, intervalIntegral.integral_of_le hU,
      intervalIntegral.integral_of_le hab.le] using
        (MeasureTheory.integral_prod (fun p : _root_.GD.N0232.N0720.N1436.d013217 => ∫ r in A..(A + T), _root_.GD.N0168.d022365 p.1 p.2 g r) her)
  rw [hceq, heeq] at hpoint
  have hcoef : 0 ≤ _root_.GD.N0165.d007234 (Real.exp (-A)) eta a / (2 * T) :=
    div_nonneg (_root_.GD.N0198.d022454 hA0 heta ha).le (by positivity)
  exact (mul_le_mul_of_nonneg_left hpoint hcoef).trans
    (_root_.GD.N0198.d022457 hA0 hT heta hhalf ha hab.le g hg h01)


theorem d022464 {eta a b A T : ℝ}
    (heta : 0 < eta) (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0176.d022339 eta (Real.exp (-A)) a b A T g ≤ _root_.GD.N0174.d022397 A T g := by
  rw [← _root_.GD.N0175.d022392 heta hhalf ha hab hwindow (Real.exp (-A)) A g hg h01]
  exact _root_.GD.N0158.d022463 heta hhalf ha hab hA hwindow g hg h01


theorem d022465 {eta a b A T : ℝ}
    (heta : 0 < eta) (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a * (1 - Real.log (b / a) / T) *
      (_root_.GD.N0203.d007249 eta a b - Real.exp (-A) * _root_.GD.N0203.d007250 eta a b) ≤ _root_.GD.N0174.d022397 A T g :=
  (_root_.GD.N0175.d022393 heta hhalf ha hab hA hwindow g hg h01).trans
    (_root_.GD.N0158.d022463 heta hhalf ha hab hA hwindow g hg h01)

end
end GD.N0158

#print axioms _root_.GD.N0158.d022460
#print axioms _root_.GD.N0158.d022462
#print axioms _root_.GD.N0158.d022463
#print axioms _root_.GD.N0158.d022464
#print axioms _root_.GD.N0158.d022465
