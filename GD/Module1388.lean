import GD.Module1387















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0168
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0163 _root_.GD.N0179


def d022365 (u x : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (r : ℝ) : ℝ :=
  _root_.GD.N0179.d006018 u x * (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - Real.exp (-r)) ^ 2 +
    _root_.GD.N0179.d006018 (1 - u) x *
      (_root_.GD.N0163.d022211 g (u, x / Real.exp (-r)) - 1 + Real.exp (-r)) ^ 2


def d022366 (u x : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (y : ℝ) : ℝ :=
  _root_.GD.N0179.d006018 u x *
      (_root_.GD.N0163.d022211 g (u, Real.exp y) - Real.exp (-(y - Real.log x))) ^ 2 +
    _root_.GD.N0179.d006018 (1 - u) x *
      (_root_.GD.N0163.d022211 g (u, Real.exp y) - 1 + Real.exp (-(y - Real.log x))) ^ 2


def d022367 (d u x : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (y : ℝ) : ℝ :=
  _root_.GD.N0179.d006018 u x * (_root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2 +
    _root_.GD.N0179.d006018 (1 - u) x * (1 - _root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2 -
      2 * d * (_root_.GD.N0179.d006018 u x + _root_.GD.N0179.d006018 (1 - u) x)

private theorem d022368 {v : ℝ → ℝ}
    (hv : Measurable v) (C : ℝ) (hC : ∀ y, ‖v y‖ ≤ C) (l r : ℝ) :
    IntervalIntegrable v volume l r := by
  apply intervalIntegrable_iff.mpr
  exact IntegrableOn.of_bound (by simp [uIoc, Real.volume_Ioc])
    hv.aestronglyMeasurable C (ae_of_all _ hC)

private theorem d022369 {v f : ℝ → ℝ}
    (hv : Measurable v) (h01 : ∀ y, v y ∈ Icc (0 : ℝ) 1)
    (hf : Continuous f) (l r : ℝ) :
    IntervalIntegrable (fun y => (v y - f y) ^ 2) volume l r := by
  have hi : IntervalIntegrable v volume l r :=
    _root_.GD.N0168.d022368 hv 1 (by
      intro y
      simpa only [Real.norm_eq_abs, abs_of_nonneg (h01 y).1] using (h01 y).2) l r
  have hi2 : IntervalIntegrable (fun y => v y ^ 2) volume l r :=
    _root_.GD.N0168.d022368 (by fun_prop) 1 (by
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [one_pow] using pow_le_pow_left₀ (h01 y).1 (h01 y).2 2) l r
  have hif2 : IntervalIntegrable (fun y => f y ^ 2) volume l r :=
    (hf.pow 2).intervalIntegrable l r
  have hcross := (hi.mul_continuousOn hf.continuousOn).const_mul (2 : ℝ)
  convert (hi2.sub hcross).add hif2 using 1 <;> ext y <;> ring

theorem d022370 (u : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (hg : Measurable g) :
    Measurable (fun y => _root_.GD.N0163.d022211 g (u, Real.exp y)) :=
  (_root_.GD.N0163.d022213 g hg).comp (measurable_const.prodMk Real.measurable_exp)


theorem d022371 (u x l r : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0168.d022366 u x g) volume l r := by
  have hv := _root_.GD.N0168.d022370 u g hg
  have hv01 := fun y => _root_.GD.N0163.d022214 g h01 (u, Real.exp y)
  have h0 := _root_.GD.N0168.d022369 hv hv01
    (show Continuous (fun y => Real.exp (-(y - Real.log x))) by fun_prop) l r
  have h1 := _root_.GD.N0168.d022369 hv hv01
    (show Continuous (fun y => 1 - Real.exp (-(y - Real.log x))) by fun_prop) l r
  convert (h0.const_mul (_root_.GD.N0179.d006018 u x)).add
    (h1.const_mul (_root_.GD.N0179.d006018 (1 - u) x)) using 1 <;>
      ext y <;> simp only [_root_.GD.N0168.d022366] <;> ring

theorem d022372 (d u x l r : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0168.d022367 d u x g) volume l r := by
  have hv := _root_.GD.N0168.d022370 u g hg
  have hv01 := fun y => _root_.GD.N0163.d022214 g h01 (u, Real.exp y)
  have h0 := _root_.GD.N0168.d022369 hv hv01
    (show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const) l r
  have h1 := _root_.GD.N0168.d022369 hv hv01
    (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const) l r
  have hc : IntervalIntegrable
      (fun _ : ℝ => 2 * d * (_root_.GD.N0179.d006018 u x + _root_.GD.N0179.d006018 (1 - u) x))
      volume l r := intervalIntegral.intervalIntegrable_const
  convert ((h0.const_mul (_root_.GD.N0179.d006018 u x)).add
    (h1.const_mul (_root_.GD.N0179.d006018 (1 - u) x))).sub hc using 1 <;>
      ext y <;> simp only [_root_.GD.N0168.d022367] <;> ring

theorem d022373 {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x / Real.exp (-r) = Real.exp (r + Real.log x) := by
  rw [Real.exp_add, Real.exp_log hx, Real.exp_neg, div_eq_mul_inv, inv_inv]
  ring


theorem d022374 {x : ℝ} (hx : 0 < x)
    (u A T : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    (∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r) =
      ∫ y in (A + Real.log x)..(A + T + Real.log x), _root_.GD.N0168.d022366 u x g y := by
  calc
    _ = ∫ r in A..(A + T), _root_.GD.N0168.d022366 u x g (r + Real.log x) := by
      apply intervalIntegral.integral_congr
      intro r _
      simp only [_root_.GD.N0168.d022365, _root_.GD.N0168.d022366, _root_.GD.N0168.d022373 hx,
        add_sub_cancel_right]
    _ = _ := intervalIntegral.integral_comp_add_right
      (a := A) (b := A + T) (_root_.GD.N0168.d022366 u x g) (Real.log x)

theorem d022375 {x : ℝ} (hx : 0 < x) (u l r : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0168.d022365 u x g) volume l r := by
  have hi := _root_.GD.N0168.d022371 u x
    (l + Real.log x) (r + Real.log x) g hg h01
  have heq : _root_.GD.N0168.d022365 u x g =
      (fun s => _root_.GD.N0168.d022366 u x g (s + Real.log x)) := by
    funext s
    simp only [_root_.GD.N0168.d022365, _root_.GD.N0168.d022366, _root_.GD.N0168.d022373 hx,
      add_sub_cancel_right]
  rw [heq]
  simpa only [add_sub_cancel_right] using hi.comp_add_right (Real.log x)

theorem d022376 {a b x : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) (A T : ℝ) :
    Ioc (A + Real.log b) (A + T + Real.log a) ⊆
      Ioc (A + Real.log x) (A + T + Real.log x) := by
  have hlogax := Real.log_le_log ha hax
  have hlogxb := Real.log_le_log (ha.trans_le hax) hxb
  intro y hy
  constructor <;> linarith [hy.1, hy.2]

theorem d022377 {u x : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hx : 0 < x) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (y : ℝ) :
    0 ≤ _root_.GD.N0168.d022366 u x g y := by
  have hk0 : 0 ≤ _root_.GD.N0179.d006018 u x := by unfold _root_.GD.N0179.d006018; positivity
  have hk1 : 0 ≤ _root_.GD.N0179.d006018 (1 - u) x := by
    have : 0 < 1 - u := sub_pos.mpr hu1
    unfold _root_.GD.N0179.d006018
    positivity
  exact add_nonneg (mul_nonneg hk0 (sq_nonneg _)) (mul_nonneg hk1 (sq_nonneg _))


theorem d022378 {a b x u T : ℝ}
    (ha : 0 < a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hu : 0 < u) (hu1 : u < 1) (hT : Real.log (b / a) < T) (A : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ y in (A + Real.log b)..(A + T + Real.log a), _root_.GD.N0168.d022366 u x g y) ≤
      ∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r := by
  have hx := ha.trans_le hax
  have ht : 0 < T := (Real.log_pos ((one_lt_div ha).mpr hab)).trans hT
  have hw := (_root_.GD.N0176.d022350 ha (ha.trans hab) hT A).le
  have hshift : A + Real.log x ≤ A + T + Real.log x := by linarith
  have hi := _root_.GD.N0168.d022371 u x
    (A + Real.log x) (A + T + Real.log x) g hg h01
  rw [_root_.GD.N0168.d022374 hx,
    intervalIntegral.integral_of_le hw, intervalIntegral.integral_of_le hshift]
  exact setIntegral_mono_set hi.1
    (ae_of_all _ (fun y => _root_.GD.N0168.d022377 hu hu1 hx g y))
    (ae_of_all _ (fun y hy => _root_.GD.N0168.d022376 ha hax hxb A T hy))


theorem d022379 {a b x u A T y : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hu : 0 < u) (hu1 : u < 1)
    (hy : y ∈ Icc (A + Real.log b) (A + T + Real.log a))
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0168.d022367 (Real.exp (-A)) u x g y ≤ _root_.GD.N0168.d022366 u x g y := by
  have hx := ha.trans_le hax
  have hlogxb := Real.log_le_log hx hxb
  have ht0 : 0 ≤ Real.exp (-(y - Real.log x)) := (Real.exp_pos _).le
  have htd : Real.exp (-(y - Real.log x)) ≤ Real.exp (-A) :=
    Real.exp_le_exp_of_le (by linarith [hy.1])
  have hv := _root_.GD.N0163.d022214 g h01 (u, Real.exp y)
  have h0 := _root_.GD.N0178.d007142 hv.2
    (le_refl (0 : ℝ)) ht0
  have h1 := _root_.GD.N0178.d007142
    (show 1 - _root_.GD.N0163.d022211 g (u, Real.exp y) ≤ 1 by linarith [hv.1])
    (le_refl (0 : ℝ)) ht0
  simp only [sub_zero] at h0 h1
  have he0 : (_root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2 - 2 * Real.exp (-A) ≤
      (_root_.GD.N0163.d022211 g (u, Real.exp y) - Real.exp (-(y - Real.log x))) ^ 2 := by
    linarith
  have he1 : (1 - _root_.GD.N0163.d022211 g (u, Real.exp y)) ^ 2 - 2 * Real.exp (-A) ≤
      (_root_.GD.N0163.d022211 g (u, Real.exp y) - 1 + Real.exp (-(y - Real.log x))) ^ 2 := by
    nlinarith [h1]
  have hk0 : 0 ≤ _root_.GD.N0179.d006018 u x := by unfold _root_.GD.N0179.d006018; positivity
  have hk1 : 0 ≤ _root_.GD.N0179.d006018 (1 - u) x := by
    have : 0 < 1 - u := sub_pos.mpr hu1
    unfold _root_.GD.N0179.d006018
    positivity
  have h := add_le_add (mul_le_mul_of_nonneg_left he0 hk0)
    (mul_le_mul_of_nonneg_left he1 hk1)
  dsimp [_root_.GD.N0168.d022367, _root_.GD.N0168.d022366]
  nlinarith [h]


theorem d022380 {a b x u T : ℝ}
    (ha : 0 < a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hu : 0 < u) (hu1 : u < 1) (hT : Real.log (b / a) < T) (A : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ y in (A + Real.log b)..(A + T + Real.log a),
      _root_.GD.N0168.d022367 (Real.exp (-A)) u x g y) ≤
        ∫ r in A..(A + T), _root_.GD.N0168.d022365 u x g r := by
  have hw := (_root_.GD.N0176.d022350 ha (ha.trans hab) hT A).le
  have h := intervalIntegral.integral_mono_on hw
    (_root_.GD.N0168.d022372 (Real.exp (-A)) u x
      (A + Real.log b) (A + T + Real.log a) g hg h01)
    (_root_.GD.N0168.d022371 u x
      (A + Real.log b) (A + T + Real.log a) g hg h01)
    (fun y hy => _root_.GD.N0168.d022379 ha hax hxb hu hu1 hy g h01)
  exact h.trans (_root_.GD.N0168.d022378 ha hab hax hxb hu hu1 hT A g hg h01)

end
end GD.N0168

#print axioms _root_.GD.N0168.d022370
#print axioms _root_.GD.N0168.d022371
#print axioms _root_.GD.N0168.d022372
#print axioms _root_.GD.N0168.d022373
#print axioms _root_.GD.N0168.d022374
#print axioms _root_.GD.N0168.d022375
#print axioms _root_.GD.N0168.d022376
#print axioms _root_.GD.N0168.d022377
#print axioms _root_.GD.N0168.d022378
#print axioms _root_.GD.N0168.d022379
#print axioms _root_.GD.N0168.d022380
