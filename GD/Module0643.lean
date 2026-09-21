import GD.Module0018
import GD.Module0640
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


































open MeasureTheory Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0928

noncomputable section

variable {I : Type*} [Fintype I]


def d009405 (p y : I → ℝ) : ℝ :=
  ∑ i, p i * y i


def d009406 (p y : I → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, p i * (y i - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2


def d009407 (shape p y t : I → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009406 p y + ∑ i, shape i * p i * t i


def d009408 (shape : I → ℝ) : ℝ :=
  ∑ i, shape i + (Fintype.card I : ℝ) / 2



def d009409 (shape p : I → ℝ) : ℝ :=
  ∏ i, p i ^ (shape i + 1 / 2)





def d009410
    (shape p y t : I → ℝ) (mu q : ℝ) (i : I) : ℝ :=
  (p i / q) ^ (shape i + 1 / 2) *
    Real.exp
      (-((p i / q) *
        (shape i * t i + (y i - mu) ^ 2 / 2)))




def d009411
    (shape p y t : I → ℝ) (mu q : ℝ) : ℝ :=
  ∏ i, _root_.GD.N0232.N0719.N0928.d009410 shape p y t mu q i



def d009412
    (shape p y t : I → ℝ) (mu q : ℝ) : ℝ :=
  q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p *
    Real.exp
      (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
          (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q))


def d009413
    (shape p y t : I → ℝ) (s mu q : ℝ) : ℝ :=
  q ^ (-s) * _root_.GD.N0232.N0719.N0928.d009412 shape p y t mu q


def d009414 (shape : I → ℝ) (s : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009408 shape + s


def d009415 (shape : I → ℝ) (s : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009408 shape + s - 3 / 2

theorem d009416
    (shape : I → ℝ) (s : ℝ) :
    _root_.GD.N0232.N0719.N0928.d009415 shape s =
      (∑ i, shape i) + (Fintype.card I : ℝ) / 2 + s - 3 / 2 := by
  unfold _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0928.d009408
  ring



theorem d009417 (shape : I → ℝ) :
    (∑ i, (shape i + 1 / 2)) = _root_.GD.N0232.N0719.N0928.d009408 shape := by
  unfold _root_.GD.N0232.N0719.N0928.d009408
  rw [Finset.sum_add_distrib]
  simp [div_eq_mul_inv]





theorem d009418
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0928.d009408
        (_root_.GD.N0232.N0719.N0954.d009355 sizes) =
      ∑ i, (sizes i : ℝ) / 2 := by
  unfold _root_.GD.N0232.N0719.N0928.d009408 _root_.GD.N0232.N0719.N0954.d009355
  rw [show (Fintype.card (Fin k) : ℝ) / 2 =
      ∑ _i : Fin k, (1 : ℝ) / 2 by
        simp [div_eq_mul_inv]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hcast : (((sizes i - 1 : ℕ) : ℝ) + 1) = sizes i := by
    exact_mod_cast Nat.sub_add_cancel (hsizes i)
  linarith





theorem d009419
    (p y : I → ℝ) (mu : ℝ)
    (hsum : ∑ i, p i = 1) :
    (1 / 2 : ℝ) * ∑ i, p i * (y i - mu) ^ 2 =
      _root_.GD.N0232.N0719.N0928.d009406 p y +
        (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2 := by
  have hcompletion :=
    _root_.GD.N0230.N0615.d000158
      p y mu (by
        simpa [_root_.GD.N0230.N0615.d000151, hsum] using
          one_ne_zero)
  have hcenter :
      _root_.GD.N0230.N0615.d000152 p y =
        _root_.GD.N0232.N0719.N0928.d009405 p y := by
    unfold _root_.GD.N0230.N0615.d000152
      _root_.GD.N0230.N0615.d000151 _root_.GD.N0232.N0719.N0928.d009405
    rw [hsum, div_one]
  rw [hcenter] at hcompletion
  unfold _root_.GD.N0230.N0615.d000151 at hcompletion
  rw [hsum] at hcompletion
  unfold _root_.GD.N0232.N0719.N0928.d009406
  nlinarith



theorem d009420
    (shape p y t : I → ℝ) (mu : ℝ)
    (hsum : ∑ i, p i = 1) :
    (1 / 2 : ℝ) * ∑ i, p i * (y i - mu) ^ 2 +
        ∑ i, shape i * p i * t i =
      _root_.GD.N0232.N0719.N0928.d009407 shape p y t +
        (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2 := by
  rw [_root_.GD.N0232.N0719.N0928.d009419 p y mu hsum]
  unfold _root_.GD.N0232.N0719.N0928.d009407
  ring





theorem d009421
    (shape p : I → ℝ) {q : ℝ}
    (hp : ∀ i, 0 < p i) (hq : 0 < q) :
    (∏ i, (p i / q) ^ (shape i + 1 / 2)) =
      q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p := by
  calc
    (∏ i, (p i / q) ^ (shape i + 1 / 2)) =
        ∏ i, p i ^ (shape i + 1 / 2) /
          q ^ (shape i + 1 / 2) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.div_rpow (hp i).le hq.le]
    _ = (∏ i, p i ^ (shape i + 1 / 2)) /
          (∏ i, q ^ (shape i + 1 / 2)) := by
      rw [Finset.prod_div_distrib]
    _ = _root_.GD.N0232.N0719.N0928.d009409 shape p /
          q ^ _root_.GD.N0232.N0719.N0928.d009408 shape := by
      unfold _root_.GD.N0232.N0719.N0928.d009409
      rw [← Real.rpow_sum_of_pos hq
        (fun i ↦ shape i + 1 / 2) Finset.univ,
        _root_.GD.N0232.N0719.N0928.d009417]
    _ = q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
          _root_.GD.N0232.N0719.N0928.d009409 shape p := by
      rw [Real.rpow_neg hq.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hq (_root_.GD.N0232.N0719.N0928.d009408 shape))]
      <;> ring


theorem d009422
    (shape p y t : I → ℝ) (mu q : ℝ) :
    (∏ i, Real.exp
        (-((p i / q) *
          (shape i * t i + (y i - mu) ^ 2 / 2)))) =
      Real.exp
        (-(∑ i, (p i / q) *
          (shape i * t i + (y i - mu) ^ 2 / 2))) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]





theorem d009423
    (shape p y t : I → ℝ) (mu : ℝ) {q : ℝ}
    (hp : ∀ i, 0 < p i) (hq : 0 < q)
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009411 shape p y t mu q =
      _root_.GD.N0232.N0719.N0928.d009412 shape p y t mu q := by
  unfold _root_.GD.N0232.N0719.N0928.d009411 _root_.GD.N0232.N0719.N0928.d009410
  rw [Finset.prod_mul_distrib, _root_.GD.N0232.N0719.N0928.d009421 shape p hp hq,
    _root_.GD.N0232.N0719.N0928.d009422]
  unfold _root_.GD.N0232.N0719.N0928.d009412
  have henergy :
      ∑ i, (p i / q) *
          (shape i * t i + (y i - mu) ^ 2 / 2) =
        (_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
          (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q := by
    rw [show (∑ i, (p i / q) *
          (shape i * t i + (y i - mu) ^ 2 / 2)) =
        ((1 / 2 : ℝ) * ∑ i, p i * (y i - mu) ^ 2 +
          ∑ i, shape i * p i * t i) / q by
      calc
        (∑ i, (p i / q) *
            (shape i * t i + (y i - mu) ^ 2 / 2)) =
            ∑ i, (shape i * p i * t i +
              (1 / 2 : ℝ) * p i * (y i - mu) ^ 2) / q := by
          apply Finset.sum_congr rfl
          intro i _
          field_simp [hq.ne']
        _ = (∑ i, (shape i * p i * t i +
              (1 / 2 : ℝ) * p i * (y i - mu) ^ 2)) / q := by
          rw [Finset.sum_div]
        _ = _ := by
          have hhalf :
              (∑ i, (1 / 2 : ℝ) * p i * (y i - mu) ^ 2) =
                (1 / 2 : ℝ) * ∑ i, p i * (y i - mu) ^ 2 := by
            calc
              (∑ i, (1 / 2 : ℝ) * p i * (y i - mu) ^ 2) =
                  ∑ i, (1 / 2 : ℝ) *
                    (p i * (y i - mu) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
              _ = _ := by rw [Finset.mul_sum]
          rw [Finset.sum_add_distrib, hhalf]
          ring]
    rw [_root_.GD.N0232.N0719.N0928.d009420 shape p y t mu hsum]
  rw [henergy]




theorem d009424
    (b center : ℝ) :
    (∫ mu : ℝ, Real.exp (-b * (mu - center) ^ 2)) =
      Real.sqrt (Real.pi / b) := by
  rw [show (∫ mu : ℝ, Real.exp (-b * (mu - center) ^ 2)) =
      ∫ x : ℝ, Real.exp (-b * x ^ 2) by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (fun x : ℝ ↦ Real.exp (-b * x ^ 2)) (-center))]
  exact integral_gaussian b


theorem d009425
    {q : ℝ} (hq : 0 < q) (center : ℝ) :
    (∫ mu : ℝ,
        Real.exp (-((mu - center) ^ 2 / 2) / q)) =
      Real.sqrt (2 * Real.pi * q) := by
  have hb : 0 < (1 / (2 * q) : ℝ) := by positivity
  rw [show (fun mu : ℝ ↦ Real.exp (-((mu - center) ^ 2 / 2) / q)) =
      fun mu ↦ Real.exp (-(1 / (2 * q)) * (mu - center) ^ 2) by
    funext mu
    congr 1
    field_simp [hq.ne']]
  rw [_root_.GD.N0232.N0719.N0928.d009424]
  congr 1
  have htwoq : 0 < 2 * q := by positivity
  rw [show Real.pi / (1 / (2 * q)) = 2 * Real.pi * q by
    field_simp [hq.ne'] <;> ring]



theorem d009426
    (shape p y t : I → ℝ) (s : ℝ)
    {q : ℝ} (hq : 0 < q) :
    (∫ mu : ℝ, _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p *
        Real.exp
          (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
        Real.sqrt (2 * Real.pi * q) := by
  let C := _root_.GD.N0232.N0719.N0928.d009407 shape p y t
  let m := _root_.GD.N0232.N0719.N0928.d009405 p y
  let A := q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p * Real.exp (-(C / q))
  have hsplit :
      (fun mu ↦ _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        fun mu ↦ A * Real.exp (-((mu - m) ^ 2 / 2) / q) := by
    funext mu
    unfold _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0719.N0928.d009412 A C m
    have hexp :
        Real.exp
            (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
              (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q)) =
          Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
            Real.exp (-((mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hq.ne']
      ring
    rw [hexp]
    ring
  rw [hsplit, integral_const_mul,
    _root_.GD.N0232.N0719.N0928.d009425 hq m]




theorem d009427
    (shape p y t : I → ℝ) (s : ℝ)
    {q : ℝ} (hq : 0 < q) :
    q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p *
        Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
        Real.sqrt (2 * Real.pi * q) =
      Real.sqrt (2 * Real.pi) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p *
        (q ^ (-(_root_.GD.N0232.N0719.N0928.d009415 shape s + 1)) *
          Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q))) := by
  have hsqrt :
      Real.sqrt (2 * Real.pi * q) =
        Real.sqrt (2 * Real.pi) * q ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hqpow :
      q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) * q ^ (1 / 2 : ℝ) =
        q ^ (-(_root_.GD.N0232.N0719.N0928.d009415 shape s + 1)) := by
    rw [← Real.rpow_add hq, ← Real.rpow_add hq]
    congr 1
    unfold _root_.GD.N0232.N0719.N0928.d009415
    ring
  rw [hsqrt]
  calc
    q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
          _root_.GD.N0232.N0719.N0928.d009409 shape p *
          Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
          (Real.sqrt (2 * Real.pi) * q ^ (1 / 2 : ℝ)) =
        Real.sqrt (2 * Real.pi) *
          _root_.GD.N0232.N0719.N0928.d009409 shape p *
          ((q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
              q ^ (1 / 2 : ℝ)) *
            Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q))) := by ring
    _ = _ := by rw [hqpow]




def d009428 (C x : ℝ) : ℝ := C / x


def d009429 (C x : ℝ) : ℝ := C / x ^ 2

theorem d009430 {C : ℝ} (hC : 0 < C) :
    _root_.GD.N0232.N0719.N0928.d009428 C '' Ioi (0 : ℝ) = Ioi 0 := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hC hx
  · intro hq
    have hq0 : 0 < q := hq
    refine ⟨C / q, div_pos hC hq0, ?_⟩
    unfold _root_.GD.N0232.N0719.N0928.d009428
    field_simp [hC.ne', hq0.ne']

theorem d009431 {C : ℝ} (hC : 0 < C) :
    Set.InjOn (_root_.GD.N0232.N0719.N0928.d009428 C) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hinv : x⁻¹ = y⁻¹ := by
    apply mul_left_cancel₀ hC.ne'
    simpa [_root_.GD.N0232.N0719.N0928.d009428, div_eq_mul_inv] using hxy
  exact inv_injective hinv

theorem d009432
    {C x : ℝ} (hC : 0 < C) (hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (_root_.GD.N0232.N0719.N0928.d009428 C) (-(_root_.GD.N0232.N0719.N0928.d009429 C x))
      (Ioi 0) x := by
  have hx0 : 0 < x := hx
  have h := (hasDerivAt_const x C).div (hasDerivAt_id x) hx0.ne'
  have hcoef : (0 * x - C * 1) / x ^ 2 = -(_root_.GD.N0232.N0719.N0928.d009429 C x) := by
    unfold _root_.GD.N0232.N0719.N0928.d009429
    ring
  exact (h.congr_deriv hcoef).hasDerivWithinAt

theorem d009433
    {C alpha x : ℝ} (hC : 0 < C) (hx : 0 < x) :
    |-(_root_.GD.N0232.N0719.N0928.d009429 C x)| *
        ((_root_.GD.N0232.N0719.N0928.d009428 C x) ^ (-alpha) *
          Real.exp (-(C / _root_.GD.N0232.N0719.N0928.d009428 C x))) =
      C ^ (1 - alpha) *
        (x ^ (alpha - 2) * Real.exp (-x)) := by
  have hjac : 0 < _root_.GD.N0232.N0719.N0928.d009429 C x := by
    unfold _root_.GD.N0232.N0719.N0928.d009429
    positivity
  rw [abs_neg, abs_of_pos hjac]
  unfold _root_.GD.N0232.N0719.N0928.d009429 _root_.GD.N0232.N0719.N0928.d009428
  have hquot : C / (C / x) = x := by field_simp [hC.ne', hx.ne']
  rw [hquot]
  rw [Real.div_rpow hC.le hx.le]
  have hCpow : C * C ^ (-alpha) = C ^ (1 - alpha) := by
    calc
      C * C ^ (-alpha) = C ^ (1 : ℝ) * C ^ (-alpha) := by
        rw [Real.rpow_one]
      _ = C ^ ((1 : ℝ) + (-alpha)) := by
        rw [Real.rpow_add hC]
      _ = C ^ (1 - alpha) := by congr 1 <;> ring
  have hxpow : (x ^ 2)⁻¹ * (x ^ (-alpha))⁻¹ =
      x ^ (alpha - 2) := by
    have hsquare : (x ^ 2)⁻¹ = x ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hx.le, Real.rpow_two]
    have hinvNeg : (x ^ (-alpha))⁻¹ = x ^ alpha := by
      rw [Real.rpow_neg hx.le, inv_inv]
    rw [hsquare, hinvNeg, ← Real.rpow_add hx]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    C * (x ^ 2)⁻¹ *
          (C ^ (-alpha) * (x ^ (-alpha))⁻¹ * Real.exp (-x)) =
        (C * C ^ (-alpha)) *
          ((x ^ 2)⁻¹ * (x ^ (-alpha))⁻¹) * Real.exp (-x) := by ring
    _ = C ^ (1 - alpha) * x ^ (alpha - 2) * Real.exp (-x) := by
      rw [hCpow, hxpow]
    _ = _ := by ring



theorem d009434
    {C alpha : ℝ} (hC : 0 < C) (halpha : 1 < alpha) :
    (∫ q in Ioi (0 : ℝ),
        q ^ (-alpha) * Real.exp (-(C / q))) =
      C ^ (1 - alpha) * Real.Gamma (alpha - 1) := by
  let g : ℝ → ℝ := fun q ↦
    q ^ (-alpha) * Real.exp (-(C / q))
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x hx ↦ _root_.GD.N0232.N0719.N0928.d009432 hC hx)
    (_root_.GD.N0232.N0719.N0928.d009431 hC) g
  rw [_root_.GD.N0232.N0719.N0928.d009430 hC] at hcov
  change (∫ q in Ioi (0 : ℝ), g q) = _
  rw [hcov]
  calc
    (∫ x in Ioi (0 : ℝ),
        |-(_root_.GD.N0232.N0719.N0928.d009429 C x)| • g (_root_.GD.N0232.N0719.N0928.d009428 C x)) =
      ∫ x in Ioi (0 : ℝ),
        C ^ (1 - alpha) *
          (x ^ (alpha - 2) * Real.exp (-x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simpa [g, smul_eq_mul] using
        _root_.GD.N0232.N0719.N0928.d009433 hC hx
    _ = C ^ (1 - alpha) *
        (∫ x in Ioi (0 : ℝ),
          x ^ ((alpha - 1) - 1) * Real.exp (-(x * 1))) := by
      rw [integral_const_mul]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      congr 2 <;> ring
    _ = C ^ (1 - alpha) * Real.Gamma (alpha - 1) := by
      congr 1
      simpa [mul_one] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi
          (by linarith : 0 < alpha - 1)
          (by norm_num : 0 < (1 : ℝ)))





theorem d009435
    (shape : I → ℝ) (s : ℝ) :
    _root_.GD.N0232.N0719.N0928.d009414 shape s - 1 / 2 =
      _root_.GD.N0232.N0719.N0928.d009415 shape s + 1 := by
  unfold _root_.GD.N0232.N0719.N0928.d009414 _root_.GD.N0232.N0719.N0928.d009415
  ring




theorem d009436
    (shape : I → ℝ) (s C : ℝ)
    (hC : 0 < C)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    (∫ q in Ioi (0 : ℝ),
        q ^ (-(_root_.GD.N0232.N0719.N0928.d009415 shape s + 1)) *
          Real.exp (-(C / q))) =
      C ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s) := by
  convert _root_.GD.N0232.N0719.N0928.d009434 hC
      (show 1 < _root_.GD.N0232.N0719.N0928.d009415 shape s + 1 by linarith) using 1 <;>
    ring



def d009437
    (shape p y t : I → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p *
    _root_.GD.N0232.N0719.N0928.d009407 shape p y t ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
    Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s)



theorem d009438
    (shape p : I → ℝ) (hp : ∀ i, 0 < p i) :
    0 < _root_.GD.N0232.N0719.N0928.d009409 shape p := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  exact Finset.prod_pos fun i _ ↦
    Real.rpow_pos_of_pos (hp i) (shape i + 1 / 2)





theorem d009439
    (shape p : I → ℝ) (i : I)
    (hexponent : 0 < shape i + 1 / 2)
    (hzero : p i = 0) :
    _root_.GD.N0232.N0719.N0928.d009409 shape p = 0 := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hzero, Real.zero_rpow hexponent.ne']




theorem d009440
    (shape p y t : I → ℝ) (s : ℝ)
    (hp : ∀ i, 0 < p i)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    0 < _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
  unfold _root_.GD.N0232.N0719.N0928.d009437
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (by positivity)
  exact mul_pos
    (mul_pos
      (mul_pos hsqrt (_root_.GD.N0232.N0719.N0928.d009438 shape p hp))
      (Real.rpow_pos_of_pos henergy (-_root_.GD.N0232.N0719.N0928.d009415 shape s)))
    (Real.Gamma_pos_of_pos hpower)



theorem d009441
    (p y : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ _root_.GD.N0232.N0719.N0928.d009406 p y := by
  unfold _root_.GD.N0232.N0719.N0928.d009406
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hp i) (sq_nonneg (y i - _root_.GD.N0232.N0719.N0928.d009405 p y)))





theorem d009442
    (shape p y t : I → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hfloor : ∀ i, c ≤ shape i * t i) :
    c ≤ _root_.GD.N0232.N0719.N0928.d009407 shape p y t := by
  have hweighted :
      ∑ i, p i * c ≤ ∑ i, shape i * p i * t i := by
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_left (hfloor i) (hp i)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
  have hc_eq : c = ∑ i, p i * c := by
    calc
      c = 1 * c := by ring
      _ = (∑ i, p i) * c := by rw [hsum]
      _ = ∑ i, p i * c := by rw [Finset.sum_mul]
  rw [hc_eq]
  unfold _root_.GD.N0232.N0719.N0928.d009407
  linarith [_root_.GD.N0232.N0719.N0928.d009441 p y hp]







theorem d009443
    (shape p y t : I → ℝ) (s c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hc : 0 < c) (hfloor : ∀ i, c ≤ shape i * t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0928.d009437 shape p y t s ≤
      Real.sqrt (2 * Real.pi) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p *
        c ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s) := by
  have henergyFloor : c ≤ _root_.GD.N0232.N0719.N0928.d009407 shape p y t :=
    _root_.GD.N0232.N0719.N0928.d009442 shape p y t c hp hsum hfloor
  have hpow :
      _root_.GD.N0232.N0719.N0928.d009407 shape p y t ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) ≤
        c ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) :=
    Real.rpow_le_rpow_of_nonpos hc henergyFloor
      (neg_nonpos.mpr hpower.le)
  have hmono : 0 ≤ _root_.GD.N0232.N0719.N0928.d009409 shape p := by
    unfold _root_.GD.N0232.N0719.N0928.d009409
    exact Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hp i) _
  have hfront :
      0 ≤ Real.sqrt (2 * Real.pi) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p :=
    mul_nonneg (Real.sqrt_nonneg _) hmono
  have hgamma : 0 ≤ Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s) :=
    (Real.Gamma_pos_of_pos hpower).le
  unfold _root_.GD.N0232.N0719.N0928.d009437
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hfront) hgamma






theorem d009444
    (shape p y t : I → ℝ) (s : ℝ)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    (∫ q in Ioi (0 : ℝ),
        ∫ mu : ℝ,
          _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
  calc
    (∫ q in Ioi (0 : ℝ),
        ∫ mu : ℝ,
          _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        ∫ q in Ioi (0 : ℝ),
          Real.sqrt (2 * Real.pi) *
            _root_.GD.N0232.N0719.N0928.d009409 shape p *
            (q ^ (-(_root_.GD.N0232.N0719.N0928.d009415 shape s + 1)) *
              Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      change (∫ mu : ℝ,
        _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) = _
      rw [_root_.GD.N0232.N0719.N0928.d009426
        shape p y t s hq]
      exact _root_.GD.N0232.N0719.N0928.d009427 shape p y t s hq
    _ = Real.sqrt (2 * Real.pi) *
          _root_.GD.N0232.N0719.N0928.d009409 shape p *
          (∫ q in Ioi (0 : ℝ),
            q ^ (-(_root_.GD.N0232.N0719.N0928.d009415 shape s + 1)) *
              Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q))) := by
      rw [integral_const_mul]
    _ = _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
      rw [_root_.GD.N0232.N0719.N0928.d009436 shape s
        (_root_.GD.N0232.N0719.N0928.d009407 shape p y t) henergy hpower]
      unfold _root_.GD.N0232.N0719.N0928.d009437
      ring

end

end N0928
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0928.d009418
#print axioms _root_.GD.N0232.N0719.N0928.d009420
#print axioms _root_.GD.N0232.N0719.N0928.d009423
#print axioms _root_.GD.N0232.N0719.N0928.d009425
#print axioms _root_.GD.N0232.N0719.N0928.d009434
#print axioms _root_.GD.N0232.N0719.N0928.d009436
#print axioms _root_.GD.N0232.N0719.N0928.d009438
#print axioms _root_.GD.N0232.N0719.N0928.d009439
#print axioms _root_.GD.N0232.N0719.N0928.d009440
#print axioms _root_.GD.N0232.N0719.N0928.d009443
#print axioms _root_.GD.N0232.N0719.N0928.d009444
