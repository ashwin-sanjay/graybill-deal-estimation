import GD.Module1389










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0175
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0163 _root_.GD.N0203 _root_.GD.N0205
open _root_.GD.N0168 _root_.GD.N0202
open _root_.GD.N0176 _root_.GD.N0165

private theorem d022388 {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖v ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v)]
  simpa only [one_pow] using pow_le_pow_left₀ hv.1 hv.2 2


theorem d022389 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (d l r : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × ℝ => _root_.GD.N0205.d022323 d a b
      (fun u => _root_.GD.N0163.d022211 g (u, Real.exp z.2)) z.1)
      ((volume.restrict (Ioc eta (1 - eta))).prod (volume.restrict (Ioc l r))) := by
  have hu : eta ≤ 1 - eta := by linarith
  have hc0 : ContinuousOn (_root_.GD.N0203.d007246 a b) (Icc eta (1 - eta)) :=
    (_root_.GD.N0203.d007255 ha hab).mono (fun u hu => heta.trans_le hu.1)
  have hc1 : ContinuousOn (fun u => _root_.GD.N0203.d007246 a b (1 - u)) (Icc eta (1 - eta)) := by
    apply (_root_.GD.N0203.d007255 ha hab).comp (by fun_prop)
    intro u hu
    show 0 < 1 - u
    linarith [hu.2]
  have h0 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hu hc0
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hu hc1
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc l r) volume :=
    (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume l r from
      intervalIntegral.intervalIntegrable_const).1
  have hb0 := h0.1.mul_prod hc
  have hb1 := h1.1.mul_prod hc
  have hv : Measurable (fun z : ℝ × ℝ => _root_.GD.N0163.d022211 g (z.1, Real.exp z.2)) :=
    (_root_.GD.N0163.d022213 g hg).comp
      (measurable_fst.prodMk (Real.measurable_exp.comp measurable_snd))
  have hv01 := fun z : ℝ × ℝ => _root_.GD.N0163.d022214 g h01 (z.1, Real.exp z.2)
  have hs0 := Integrable.mul_bdd hb0
    (show Measurable (fun z : ℝ × ℝ =>
      _root_.GD.N0163.d022211 g (z.1, Real.exp z.2) ^ 2) by fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun z => _root_.GD.N0175.d022388 (hv01 z)))
  have hs1 := Integrable.mul_bdd hb1
    (show Measurable (fun z : ℝ × ℝ =>
      (1 - _root_.GD.N0163.d022211 g (z.1, Real.exp z.2)) ^ 2) by fun_prop).aestronglyMeasurable
    (ae_of_all _ (fun z => _root_.GD.N0175.d022388
      ⟨by linarith [(hv01 z).2], by linarith [(hv01 z).1]⟩))
  have hprod := (hs0.add hs1).sub ((hb0.add hb1).const_mul (2 * d))
  apply hprod.congr
  exact ae_of_all _ (fun z => by simp [_root_.GD.N0205.d022323, _root_.GD.N0205.d022322])


theorem d022390 {eta a b l r : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b) (hlr : l ≤ r)
    (d : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ u in eta..(1 - eta), ∫ y in l..r,
      _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u) =
    ∫ y in l..r, ∫ u in eta..(1 - eta),
      _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
  have hu : eta ≤ 1 - eta := by linarith
  have h := MeasureTheory.integral_integral_swap
    (f := fun u y => _root_.GD.N0205.d022323 d a b
      (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u)
    (_root_.GD.N0175.d022389 heta hhalf ha hab d l r g hg h01)
  simpa only [intervalIntegral.integral_of_le hu,
    intervalIntegral.integral_of_le hlr] using h


theorem d022391 {eta a b l r : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b) (hlr : l ≤ r)
    (d : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ u in eta..(1 - eta), ∫ x in a..b, ∫ y in l..r,
      _root_.GD.N0168.d022367 d u x g y) =
    ∫ y in l..r, ∫ u in eta..(1 - eta),
      _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
  calc
    _ = ∫ u in eta..(1 - eta), ∫ y in l..r,
        _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (show eta ≤ 1 - eta by linarith)] at hu
      exact _root_.GD.N0202.d022386 (heta.trans_le hu.1)
        (by linarith [hu.2]) ha hab hlr d g hg h01
    _ = _ := _root_.GD.N0175.d022390 heta hhalf ha hab hlr d g hg h01


theorem d022392 {eta a b T : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hwindow : Real.log (b / a) < T) (d A : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 d eta a / (2 * T) *
      (∫ u in eta..(1 - eta), ∫ x in a..b,
        ∫ y in (A + Real.log b)..(A + T + Real.log a), _root_.GD.N0168.d022367 d u x g y) =
      _root_.GD.N0176.d022339 eta d a b A T g := by
  rw [_root_.GD.N0175.d022391 heta hhalf ha hab.le
    (_root_.GD.N0176.d022350 ha (ha.trans hab) hwindow A).le d g hg h01]
  exact (_root_.GD.N0176.d022348 eta d a b A T g).symm


theorem d022393 {eta a b A T : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b)
    (hA : Real.log 2 < A) (hwindow : Real.log (b / a) < T)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0165.d007234 (Real.exp (-A)) eta a * (1 - Real.log (b / a) / T) *
        (_root_.GD.N0203.d007249 eta a b - Real.exp (-A) * _root_.GD.N0203.d007250 eta a b) ≤
      _root_.GD.N0165.d007234 (Real.exp (-A)) eta a / (2 * T) *
        (∫ u in eta..(1 - eta), ∫ x in a..b,
          ∫ y in (A + Real.log b)..(A + T + Real.log a),
            _root_.GD.N0168.d022367 (Real.exp (-A)) u x g y) := by
  rw [_root_.GD.N0175.d022392 heta hhalf ha hab hwindow (Real.exp (-A)) A g hg h01]
  exact _root_.GD.N0176.d022353 heta hhalf ha hab hA hwindow g hg h01

end
end GD.N0175

#print axioms _root_.GD.N0175.d022389
#print axioms _root_.GD.N0175.d022390
#print axioms _root_.GD.N0175.d022391
#print axioms _root_.GD.N0175.d022392
#print axioms _root_.GD.N0175.d022393
