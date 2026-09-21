import GD.Module1388
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0202
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0163 _root_.GD.N0179 _root_.GD.N0203
open _root_.GD.N0168 _root_.GD.N0205


theorem d022381 {a b u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b)
    (d y : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    IntervalIntegrable (fun x => _root_.GD.N0168.d022367 d u x g y) volume a b := by
  have h0 := _root_.GD.N0179.d006038 hu ha hab
  have h1 := _root_.GD.N0179.d006038 (sub_pos.mpr hu1) ha hab
  exact ((h0.mul_const (_root_.GD.N0163.d022211 g (u, Real.exp y) ^ 2)).add
    (h1.mul_const ((1 - _root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2))).sub
      ((h0.add h1).const_mul (2 * d))


theorem d022382 {a b u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b)
    (d y : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    (∫ x in a..b, _root_.GD.N0168.d022367 d u x g y) =
      _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
  have hk0 := _root_.GD.N0179.d006038 hu ha hab
  have hk1 := _root_.GD.N0179.d006038 (sub_pos.mpr hu1) ha hab
  have h0 := hk0.mul_const (_root_.GD.N0163.d022211 g (u, Real.exp y) ^ 2)
  have h1 := hk1.mul_const ((1 - _root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2)
  have he := (hk0.add hk1).const_mul (2 * d)
  unfold _root_.GD.N0168.d022367
  rw [intervalIntegral.integral_sub (h0.add h1) he,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hk0 hk1,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const] <;> rfl

private theorem d022383 {v : ℝ → ℝ}
    (hv : Measurable v) (h01 : ∀ y, v y ∈ Icc (0 : ℝ) 1) (l r : ℝ) :
    IntegrableOn (fun y => v y ^ 2) (Ioc l r) volume := by
  apply IntegrableOn.of_bound (by simp [Real.volume_Ioc])
    (show Measurable (fun y => v y ^ 2) by fun_prop).aestronglyMeasurable 1
  exact ae_of_all _ (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [one_pow] using pow_le_pow_left₀ (h01 y).1 (h01 y).2 2)


theorem d022384 {a b u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b)
    (d l r : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : ℝ × ℝ => _root_.GD.N0168.d022367 d u z.1 g z.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc l r))) := by
  have hk0 := (_root_.GD.N0179.d006038 hu ha hab).1
  have hk1 := (_root_.GD.N0179.d006038 (sub_pos.mpr hu1) ha hab).1
  have hv := _root_.GD.N0168.d022370 u g hg
  have hv01 := fun y => _root_.GD.N0163.d022214 g h01 (u, Real.exp y)
  have hv2 := _root_.GD.N0202.d022383 hv hv01 l r
  have hw2 := _root_.GD.N0202.d022383
    (show Measurable (fun y => 1 - _root_.GD.N0163.d022211 g (u, Real.exp y)) by fun_prop)
    (fun y => ⟨by linarith [(hv01 y).2], by linarith [(hv01 y).1]⟩) l r
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc l r) volume :=
    (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume l r from
      intervalIntegral.intervalIntegrable_const).1
  have he := ((hk0.add hk1).mul_prod hc).const_mul (2 * d)
  have hprod := ((hk0.mul_prod hv2).add (hk1.mul_prod hw2)).sub he
  apply hprod.congr
  exact ae_of_all _ (fun z => by simp [_root_.GD.N0168.d022367])


theorem d022385 {a b u l r : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b) (hlr : l ≤ r)
    (d : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, ∫ y in l..r, _root_.GD.N0168.d022367 d u x g y) =
      ∫ y in l..r, ∫ x in a..b, _root_.GD.N0168.d022367 d u x g y := by
  have h := MeasureTheory.integral_integral_swap
    (f := fun x y => _root_.GD.N0168.d022367 d u x g y)
    (_root_.GD.N0202.d022384 hu hu1 ha hab d l r g hg h01)
  simpa only [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hlr] using h


theorem d022386 {a b u l r : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b) (hlr : l ≤ r)
    (d : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, ∫ y in l..r, _root_.GD.N0168.d022367 d u x g y) =
      ∫ y in l..r,
        _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u := by
  rw [_root_.GD.N0202.d022385 hu hu1 ha hab hlr d g hg h01]
  exact intervalIntegral.integral_congr (fun y _ =>
    _root_.GD.N0202.d022382 hu hu1 ha hab d y g)


theorem d022387 {a b u T : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a < b)
    (hT : Real.log (b / a) < T) (d A : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, ∫ y in (A + Real.log b)..(A + T + Real.log a),
      _root_.GD.N0168.d022367 d u x g y) =
        ∫ y in (A + Real.log b)..(A + T + Real.log a),
          _root_.GD.N0205.d022323 d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) u :=
  _root_.GD.N0202.d022386 hu hu1 ha hab.le
    (_root_.GD.N0176.d022350 ha (ha.trans hab) hT A).le d g hg h01

end
end GD.N0202

#print axioms _root_.GD.N0202.d022381
#print axioms _root_.GD.N0202.d022382
#print axioms _root_.GD.N0202.d022384
#print axioms _root_.GD.N0202.d022385
#print axioms _root_.GD.N0202.d022386
#print axioms _root_.GD.N0202.d022387
