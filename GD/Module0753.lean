import GD.Module0752
import GD.Module0002

set_option autoImplicit false
set_option warningAsError true











open Set
open scoped BigOperators ContDiff

namespace GD.N0232.N0719.N0873

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

abbrev d011295 (I : Type*) := (I → ℝ) × (I → ℝ)

def d011296 (i : I) : _root_.GD.N0232.N0719.N0873.d011295 I := (Pi.single i 1, 0)
def d011297 (i : I) : _root_.GD.N0232.N0719.N0873.d011295 I := (0, Pi.single i 1)

def d011298 (i : I) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ))

def d011299 (i : I) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ))

omit [Fintype I] [DecidableEq I] in
@[simp] theorem d011300 (i : I) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011298 i x = x.1 i := rfl
omit [Fintype I] [DecidableEq I] in
@[simp] theorem d011301 (i : I) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0873.d011299 i x = x.2 i := rfl

def d011302 (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ i, precision i * ((x.1 i - location) ^ 2 / 2 + x.2 i)

def d011303 (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ :=
  ∑ i, precision i • ((x.1 i - location) • _root_.GD.N0232.N0719.N0873.d011298 i + _root_.GD.N0232.N0719.N0873.d011299 i)

omit [DecidableEq I] in
theorem d011304 (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0873.d011302 location precision) (_root_.GD.N0232.N0719.N0873.d011303 location precision x) x := by
  unfold _root_.GD.N0232.N0719.N0873.d011302 _root_.GD.N0232.N0719.N0873.d011303
  apply HasFDerivAt.fun_sum
  intro i _hi
  have hmean := ((_root_.GD.N0232.N0719.N0873.d011298 i).hasFDerivAt (x := x)).sub_const location
  have hres := (_root_.GD.N0232.N0719.N0873.d011299 i).hasFDerivAt (x := x)
  apply ((((hmean.pow 2).mul_const (2 : ℝ)⁻¹).add hres).const_mul (precision i)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [smul_eq_mul]
  ring_nf
  simp

omit [DecidableEq I] in
theorem d011305 (location : ℝ) (precision : I → ℝ) :
    ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0873.d011302 location precision) := by
  unfold _root_.GD.N0232.N0719.N0873.d011302
  fun_prop

def d011306 (amplitude location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  amplitude * Real.exp (-_root_.GD.N0232.N0719.N0873.d011302 location precision x)

omit [DecidableEq I] in
theorem d011307 (amplitude location : ℝ) (precision : I → ℝ) :
    ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0873.d011306 amplitude location precision) := by
  exact contDiff_const.mul ((_root_.GD.N0232.N0719.N0873.d011305 location precision).neg.exp)

omit [DecidableEq I] in
theorem d011308 (amplitude location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0873.d011306 amplitude location precision)
      (-(_root_.GD.N0232.N0719.N0873.d011306 amplitude location precision x) • _root_.GD.N0232.N0719.N0873.d011303 location precision x) x := by
  apply (((_root_.GD.N0232.N0719.N0873.d011304 location precision x).neg.exp).const_mul amplitude).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [_root_.GD.N0232.N0719.N0873.d011306]
  ring

theorem d011309 (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) (i : I) :
    _root_.GD.N0232.N0719.N0873.d011303 location precision x (_root_.GD.N0232.N0719.N0873.d011296 i) = precision i * (x.1 i - location) := by
  classical
  simp [_root_.GD.N0232.N0719.N0873.d011303, _root_.GD.N0232.N0719.N0873.d011296, _root_.GD.N0232.N0719.N0873.d011298, _root_.GD.N0232.N0719.N0873.d011299, Pi.single_apply]

theorem d011310 (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) (i : I) :
    _root_.GD.N0232.N0719.N0873.d011303 location precision x (_root_.GD.N0232.N0719.N0873.d011297 i) = precision i := by
  classical
  simp [_root_.GD.N0232.N0719.N0873.d011303, _root_.GD.N0232.N0719.N0873.d011297, _root_.GD.N0232.N0719.N0873.d011298, _root_.GD.N0232.N0719.N0873.d011299, Pi.single_apply]

theorem d011311 (amplitude location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011306 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011296 i) =
      -precision i * (x.1 i - location) * _root_.GD.N0232.N0719.N0873.d011306 amplitude location precision x := by
  rw [(_root_.GD.N0232.N0719.N0873.d011308 amplitude location precision x).fderiv]
  simp only [smul_apply, smul_eq_mul, _root_.GD.N0232.N0719.N0873.d011309]
  ring

theorem d011312 (amplitude location : ℝ) (precision : I → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 I) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011306 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
      -precision i * _root_.GD.N0232.N0719.N0873.d011306 amplitude location precision x := by
  rw [(_root_.GD.N0232.N0719.N0873.d011308 amplitude location precision x).fderiv]
  simp only [smul_apply, smul_eq_mul, _root_.GD.N0232.N0719.N0873.d011310]
  ring

def d011313 (amplitude location : J → ℝ) (precision : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ j, _root_.GD.N0232.N0719.N0873.d011306 (amplitude j) (location j) (precision j) x

def d011314 (amplitude location : J → ℝ) (precision : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ j, location j * _root_.GD.N0232.N0719.N0873.d011306 (amplitude j) (location j) (precision j) x

omit [DecidableEq I] in
theorem d011315 (amplitude location : J → ℝ) (precision : J → I → ℝ) :
    ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0873.d011313 amplitude location precision) := by
  exact ContDiff.sum fun j _ => _root_.GD.N0232.N0719.N0873.d011307 (amplitude j) (location j) (precision j)

omit [DecidableEq I] in
theorem d011316 (amplitude location : J → ℝ) (precision : J → I → ℝ) :
    ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0873.d011314 amplitude location precision) := by
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (_root_.GD.N0232.N0719.N0873.d011307 (amplitude j) (location j) (precision j))



theorem d011317 (amplitude location : J → ℝ) (precision : J → I → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 I) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011314 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
      x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011313 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
        fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011313 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011296 i) := by
  have hd j : DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0873.d011306 (amplitude j) (location j) (precision j)) x :=
    (_root_.GD.N0232.N0719.N0873.d011308 (amplitude j) (location j) (precision j) x).differentiableAt
  unfold _root_.GD.N0232.N0719.N0873.d011314 _root_.GD.N0232.N0719.N0873.d011313
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (location j)),
    fderiv_fun_sum (fun j _ => hd j)]
  simp only [sum_apply, fderiv_const_mul (hd _), smul_apply, smul_eq_mul]
  simp only [_root_.GD.N0232.N0719.N0873.d011312, _root_.GD.N0232.N0719.N0873.d011311]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

def d011318 (f : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ) (i : I) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011295 I :=
  _root_.GD.N0232.N0719.N0873.d011296 i + (f x - x.1 i) • _root_.GD.N0232.N0719.N0873.d011297 i

def d011319 (f : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ) (amplitude location : J → ℝ)
    (precision : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  f x * _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x - _root_.GD.N0232.N0719.N0873.d011314 amplitude location precision x



theorem d011320 (f : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ)
    (amplitude location : J → ℝ) (precision : J → I → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hf : DifferentiableAt ℝ f x) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011313 amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011318 f i x) =
      -(fderiv ℝ f x (_root_.GD.N0232.N0719.N0873.d011297 i)) * _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x +
        fderiv ℝ (_root_.GD.N0232.N0719.N0873.d011319 f amplitude location precision) x (_root_.GD.N0232.N0719.N0873.d011297 i) := by
  have hM : DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0873.d011313 amplitude location precision) x :=
    ((_root_.GD.N0232.N0719.N0873.d011315 amplitude location precision).contDiffAt).differentiableAt
    (by simp)
  have hN : DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0873.d011314 amplitude location precision) x :=
    ((_root_.GD.N0232.N0719.N0873.d011316 amplitude location precision).contDiffAt).differentiableAt
    (by simp)
  have hpde := _root_.GD.N0232.N0719.N0873.d011317 amplitude location precision x i
  unfold _root_.GD.N0232.N0719.N0873.d011319
  rw [fderiv_fun_sub (hf.fun_mul hM) hN, fderiv_fun_mul hf hM]
  simp only [_root_.GD.N0232.N0719.N0873.d011318, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [hpde]
  ring

omit [DecidableEq I] in
theorem d011321 {amplitude : ℝ} (ha : 0 ≤ amplitude)
    (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    0 ≤ _root_.GD.N0232.N0719.N0873.d011306 amplitude location precision x :=
  mul_nonneg ha (Real.exp_pos _).le

omit [DecidableEq I] in
theorem d011322 {amplitude : ℝ} (ha : 0 < amplitude)
    (location : ℝ) (precision : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    0 < _root_.GD.N0232.N0719.N0873.d011306 amplitude location precision x :=
  mul_pos ha (Real.exp_pos _)

omit [DecidableEq I] in


theorem d011323 (amplitude location : J → ℝ) (precision : J → I → ℝ)
    (ha : ∀ j, 0 ≤ amplitude j) (j : J) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0873.d011306 (amplitude j) (location j) (precision j) x ≤
      _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x := by
  exact Finset.single_le_sum (fun q _ => _root_.GD.N0232.N0719.N0873.d011321 (ha q) _ _ _) (Finset.mem_univ j)

omit [DecidableEq I] in


theorem d011324 (f : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ)
    (amplitude location : J → ℝ) (precision : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I)
    (hM : _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x ≠ 0) :
    _root_.GD.N0232.N0719.N0873.d011319 f amplitude location precision x ^ 2 /
        _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x =
      _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x *
        (f x - _root_.GD.N0232.N0719.N0873.d011314 amplitude location precision x /
          _root_.GD.N0232.N0719.N0873.d011313 amplitude location precision x) ^ 2 := by
  unfold _root_.GD.N0232.N0719.N0873.d011319
  field_simp

section LiteralNormalization

open _root_.GD.N0232.N0719.N1011

def d011325 {k : ℕ} (sizes : Fin k → ℕ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) :=
  (s.mean, fun i => ((sizes i - 1 : ℕ) : ℝ) * s.meanVariance i / 2)

def d011326 (n : ℕ) (scale : ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ / (Real.sqrt (2 * Real.pi))⁻¹) ^ n

def d011327 {k : ℕ} (sizes : Fin k → ℕ) (scale : Fin k → ℝ) : ℝ :=
  ∏ i, _root_.GD.N0232.N0719.N0873.d011326 (sizes i) (scale i)

def d011328 {k : ℕ} (sizes : Fin k → ℕ) (scale : Fin k → ℝ) : Fin k → ℝ :=
  fun i => (sizes i : ℝ) / scale i ^ 2

def d011329 {k : ℕ} (sizes : Fin k → ℕ) (location : ℝ) (scale : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ :=
  _root_.GD.N0232.N0719.N0873.d011306 (_root_.GD.N0232.N0719.N0873.d011327 sizes scale) location (_root_.GD.N0232.N0719.N0873.d011328 sizes scale)

def d011330 {k : ℕ} (sizes : Fin k → ℕ) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ :=
  _root_.GD.N0232.N0719.N0873.d011306 1 0 (fun i => (sizes i : ℝ))

theorem d011331 (n : ℕ) {scale : ℝ} (hscale : scale ≠ 0) :
    0 < _root_.GD.N0232.N0719.N0873.d011326 n scale := by
  apply pow_pos
  apply div_pos
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (by positivity) (sq_pos_of_ne_zero hscale)))
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem d011332 {k : ℕ} (sizes : Fin k → ℕ) (scale : Fin k → ℝ)
    (hscale : ∀ i, scale i ≠ 0) : 0 < _root_.GD.N0232.N0719.N0873.d011327 sizes scale := by
  exact Finset.prod_pos fun i _ => _root_.GD.N0232.N0719.N0873.d011331 (sizes i) (hscale i)

theorem d011333 {k : ℕ} (sizes : Fin k → ℕ) (scale : Fin k → ℝ)
    (hsizes : ∀ i, 0 < sizes i) (hscale : ∀ i, scale i ≠ 0) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0873.d011328 sizes scale i :=
  div_pos (Nat.cast_pos.mpr (hsizes i)) (sq_pos_of_ne_zero (hscale i))

theorem d011334 (n : ℕ)
    (location scale mean meanVariance : ℝ) :
    _root_.GD.N0232.N0719.N1011.d011284 n location scale mean meanVariance =
      _root_.GD.N0232.N0719.N0873.d011326 n scale * Real.exp
        ((n : ℝ) * (mean ^ 2 / 2 + ((n - 1 : ℕ) : ℝ) * meanVariance / 2) -
          ((n : ℝ) / scale ^ 2) *
            ((mean - location) ^ 2 / 2 + ((n - 1 : ℕ) : ℝ) * meanVariance / 2)) := by
  unfold _root_.GD.N0232.N0719.N1011.d011284 _root_.GD.N0232.N0719.N0873.d011326 _root_.GD.N0232.N0719.N1011.d011283
  congr 2
  ring




theorem d011335 {k : ℕ}
    (sizes : Fin k → ℕ) (location : ℝ) (scale : Fin k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0873.d011329 sizes location scale (_root_.GD.N0232.N0719.N0873.d011325 sizes s) =
      _root_.GD.N0232.N0719.N0873.d011330 sizes (_root_.GD.N0232.N0719.N0873.d011325 sizes s) *
        _root_.GD.N0232.N0719.N1011.d011288 k sizes location scale s := by
  unfold _root_.GD.N0232.N0719.N1011.d011288
  simp_rw [_root_.GD.N0232.N0719.N0873.d011334]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  unfold _root_.GD.N0232.N0719.N0873.d011329 _root_.GD.N0232.N0719.N0873.d011330 _root_.GD.N0232.N0719.N0873.d011306 _root_.GD.N0232.N0719.N0873.d011327 _root_.GD.N0232.N0719.N0873.d011328 _root_.GD.N0232.N0719.N0873.d011302 _root_.GD.N0232.N0719.N0873.d011325
  simp only [sub_zero, one_mul]
  rw [mul_left_comm (Real.exp _) (∏ i, _root_.GD.N0232.N0719.N0873.d011326 (sizes i) (scale i)), ← Real.exp_add]
  congr 2
  rw [Finset.sum_sub_distrib]
  ring

theorem d011336 {k : ℕ} (sizes : Fin k → ℕ) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    0 < _root_.GD.N0232.N0719.N0873.d011330 sizes x := _root_.GD.N0232.N0719.N0873.d011322 (by norm_num) _ _ _



theorem d011337 {k : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N0873.d011329 sizes theta.location theta.scale
        (_root_.GD.N0232.N0719.N0873.d011325 sizes (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) =
      _root_.GD.N0232.N0719.N0873.d011330 sizes (_root_.GD.N0232.N0719.N0873.d011325 sizes (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) *
        _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega := by
  rw [_root_.GD.N0232.N0719.N1011.d011293 k sizes hsizes theta]
  exact _root_.GD.N0232.N0719.N0873.d011335 sizes theta.location theta.scale _

end LiteralNormalization

end
end GD.N0232.N0719.N0873

#print axioms _root_.GD.N0232.N0719.N0873.d011311
#print axioms _root_.GD.N0232.N0719.N0873.d011317
#print axioms _root_.GD.N0232.N0719.N0873.d011320
#print axioms _root_.GD.N0232.N0719.N0873.d011324
#print axioms _root_.GD.N0232.N0719.N0873.d011335
#print axioms _root_.GD.N0232.N0719.N0873.d011337
