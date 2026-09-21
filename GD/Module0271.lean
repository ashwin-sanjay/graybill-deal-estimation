import GD.Module0232
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real












open Set
open scoped Interval

namespace GD.N0232.N0720.N1358

noncomputable section

def d003988 (a : ℝ) : ℝ := 2 * a / (1 + a ^ 2)

def d003989 (a x : ℝ) : ℝ := 1 + a ^ 2 - 2 * a * x

def d003990 (a x : ℝ) : ℝ :=
  (2 * a - (1 + a ^ 2) * x) / _root_.GD.N0232.N0720.N1358.d003989 a x

def d003991 (a x : ℝ) : ℝ :=
  -(1 - a ^ 2) ^ 2 / (_root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2

def d003992 (a x : ℝ) : ℝ := 1 - _root_.GD.N0232.N0720.N1358.d003988 a * x

theorem d003993 {a : ℝ} (ha : |a| < 1) : 0 < 1 - a ^ 2 := by
  have hsq := (sq_lt_one_iff_abs_lt_one a).2 ha
  linarith

theorem d003994 {a x : ℝ} (ha : |a| < 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1358.d003989 a x := by
  have habsx : |x| ≤ 1 := abs_le.mpr hx
  have hprod : a * x ≤ |a| := by
    calc
      a * x ≤ |a * x| := le_abs_self _
      _ = |a| * |x| := abs_mul _ _
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left habsx (abs_nonneg a)
      _ = |a| := mul_one _
  have hsq : 0 < (1 - |a|) ^ 2 := sq_pos_of_pos (sub_pos.mpr ha)
  have habsSq : |a| ^ 2 = a ^ 2 := sq_abs a
  unfold _root_.GD.N0232.N0720.N1358.d003989
  nlinarith

theorem d003995 (a x : ℝ) :
    _root_.GD.N0232.N0720.N1358.d003992 a x = _root_.GD.N0232.N0720.N1358.d003989 a x / (1 + a ^ 2) := by
  have hA : 1 + a ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + a ^ 2)
  unfold _root_.GD.N0232.N0720.N1358.d003992 _root_.GD.N0232.N0720.N1358.d003988 _root_.GD.N0232.N0720.N1358.d003989
  field_simp [hA]

theorem d003996 {a x : ℝ} (ha : |a| < 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1358.d003992 a x := by
  rw [_root_.GD.N0232.N0720.N1358.d003995]
  exact div_pos (_root_.GD.N0232.N0720.N1358.d003994 ha hx) (by positivity)

theorem d003997 (a x : ℝ) (hd : _root_.GD.N0232.N0720.N1358.d003989 a x ≠ 0) :
    _root_.GD.N0232.N0720.N1358.d003990 a x - a = -(1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x * (x - a) := by
  unfold _root_.GD.N0232.N0720.N1358.d003990 _root_.GD.N0232.N0720.N1358.d003989 at *
  field_simp [hd]
  ring

theorem d003998 (a x : ℝ) (hd : _root_.GD.N0232.N0720.N1358.d003989 a x ≠ 0) :
    1 - (_root_.GD.N0232.N0720.N1358.d003990 a x) ^ 2 =
      ((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2 * (1 - x ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1358.d003990 _root_.GD.N0232.N0720.N1358.d003989 at *
  field_simp [hd]
  ring

theorem d003999 (a x : ℝ) (hd : _root_.GD.N0232.N0720.N1358.d003989 a x ≠ 0) :
    _root_.GD.N0232.N0720.N1358.d003992 a (_root_.GD.N0232.N0720.N1358.d003990 a x) =
      ((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2 * _root_.GD.N0232.N0720.N1358.d003992 a x := by
  have hA : 1 + a ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + a ^ 2)
  unfold _root_.GD.N0232.N0720.N1358.d003992 _root_.GD.N0232.N0720.N1358.d003988 _root_.GD.N0232.N0720.N1358.d003990 _root_.GD.N0232.N0720.N1358.d003989 at *
  field_simp [hA, hd]
  ring

theorem d004000 {a x : ℝ} (ha : |a| < 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a (_root_.GD.N0232.N0720.N1358.d003990 a x)) =
      ((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) * Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x) := by
  have hd := _root_.GD.N0232.N0720.N1358.d003994 ha hx
  rw [_root_.GD.N0232.N0720.N1358.d003999 a x (ne_of_gt hd), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (div_nonneg (_root_.GD.N0232.N0720.N1358.d003993 ha).le hd.le)]

theorem d004001 {a x : ℝ} (hd : _root_.GD.N0232.N0720.N1358.d003989 a x ≠ 0) :
    HasDerivAt (_root_.GD.N0232.N0720.N1358.d003990 a) (_root_.GD.N0232.N0720.N1358.d003991 a x) x := by
  have hN : HasDerivAt (fun y : ℝ ↦ 2 * a - (1 + a ^ 2) * y)
      (-(1 + a ^ 2)) x := by
    simpa only [mul_one] using
      ((hasDerivAt_id' x).const_mul (1 + a ^ 2)).const_sub (2 * a)
  have hD : HasDerivAt (_root_.GD.N0232.N0720.N1358.d003989 a) (-(2 * a)) x := by
    convert ((hasDerivAt_id' x).const_mul (2 * a)).const_sub (1 + a ^ 2)
      using 1
    · ext <;> rfl
    · ext <;> rfl
    · funext y
      rfl
    · simp only [mul_one]
  have hraw := hN.div hD hd
  change HasDerivAt (_root_.GD.N0232.N0720.N1358.d003990 a) _ x at hraw
  convert hraw using 1
  unfold _root_.GD.N0232.N0720.N1358.d003991 _root_.GD.N0232.N0720.N1358.d003989
  ring

theorem d004002 {a : ℝ} (ha : |a| < 1) : _root_.GD.N0232.N0720.N1358.d003990 a (-1) = 1 := by
  have hd := ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha (by constructor <;> norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1))
  unfold _root_.GD.N0232.N0720.N1358.d003990
  apply (div_eq_one_iff_eq hd).2
  unfold _root_.GD.N0232.N0720.N1358.d003989
  ring

theorem d004003 {a : ℝ} (ha : |a| < 1) : _root_.GD.N0232.N0720.N1358.d003990 a 1 = -1 := by
  have hd := ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1))
  unfold _root_.GD.N0232.N0720.N1358.d003990
  apply (div_eq_iff hd).2
  unfold _root_.GD.N0232.N0720.N1358.d003989
  ring

theorem d004004 {a x : ℝ} (ha : |a| < 1) (hx : x ∈ Icc (-1 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1358.d003990 a x ∈ Icc (-1 : ℝ) 1 := by
  have hd := _root_.GD.N0232.N0720.N1358.d003994 ha hx
  have hleft : 0 ≤ (1 + a) ^ 2 * (1 - x) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hx.2)
  have hright : 0 ≤ (1 - a) ^ 2 * (1 + x) :=
    mul_nonneg (sq_nonneg _) (by linarith [hx.1])
  constructor
  · unfold _root_.GD.N0232.N0720.N1358.d003990
    apply (le_div_iff₀ hd).2
    unfold _root_.GD.N0232.N0720.N1358.d003989
    nlinarith
  · unfold _root_.GD.N0232.N0720.N1358.d003990
    apply (div_le_iff₀ hd).2
    unfold _root_.GD.N0232.N0720.N1358.d003989
    nlinarith



def d004005 (k : ℕ) (a x : ℝ) : ℝ :=
  (x - a) ^ k * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ (k + 4)

private theorem d004006 (k : ℕ) (r y v s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    ((-r * y) ^ k * (r ^ 2 * v) / (r * s) ^ (k + 4)) * (-r ^ 2) =
      (-1 : ℝ) ^ (k + 1) * (y ^ k * v / s ^ (k + 4)) := by
  rw [show -r * y = (-1 : ℝ) * (r * y) by ring, mul_pow, mul_pow, mul_pow,
    pow_add r k 4, pow_succ (-1 : ℝ) k]
  field_simp [hr, hs]


theorem d004007 (k : ℕ) {a x : ℝ} (ha : |a| < 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1358.d004005 k a (_root_.GD.N0232.N0720.N1358.d003990 a x) * _root_.GD.N0232.N0720.N1358.d003991 a x =
      (-1 : ℝ) ^ (k + 1) * _root_.GD.N0232.N0720.N1358.d004005 k a x := by
  have hd := _root_.GD.N0232.N0720.N1358.d003994 ha hx
  have hc := _root_.GD.N0232.N0720.N1358.d003993 ha
  have hs := Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1358.d003996 ha hx)
  unfold _root_.GD.N0232.N0720.N1358.d004005
  rw [_root_.GD.N0232.N0720.N1358.d003997 a x (ne_of_gt hd), _root_.GD.N0232.N0720.N1358.d003998 a x (ne_of_gt hd),
    _root_.GD.N0232.N0720.N1358.d004000 ha hx]
  have hderiv : _root_.GD.N0232.N0720.N1358.d003991 a x = -((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1358.d003991
    rw [div_pow, neg_div]
  rw [hderiv]
  have hshift : -(1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x = -((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) := by
    rw [neg_div]
  rw [hshift]
  exact _root_.GD.N0232.N0720.N1358.d004006 k _ _ _ _ (div_ne_zero (ne_of_gt hc) (ne_of_gt hd)) (ne_of_gt hs)

private theorem d004008 (k : ℕ) {a : ℝ} (ha : |a| < 1) :
    ContinuousOn (_root_.GD.N0232.N0720.N1358.d004005 k a) (Icc (-1 : ℝ) 1) := by
  unfold _root_.GD.N0232.N0720.N1358.d004005
  apply ContinuousOn.div
  · fun_prop
  · unfold _root_.GD.N0232.N0720.N1358.d003992
    fun_prop
  · intro x hx
    exact pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1358.d003996 ha hx)))



theorem d004009 (k : ℕ) (hk : Odd k) {a : ℝ} (ha : |a| < 1) :
    (∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1358.d004005 k a x) = 0 := by
  have hinterval : uIcc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by norm_num [uIcc]
  have hderiv : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (_root_.GD.N0232.N0720.N1358.d003990 a) (_root_.GD.N0232.N0720.N1358.d003991 a x) x := by
    intro x hx
    rw [hinterval] at hx
    exact _root_.GD.N0232.N0720.N1358.d004001 (ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha hx))
  have hderivCont : ContinuousOn (_root_.GD.N0232.N0720.N1358.d003991 a) (uIcc (-1 : ℝ) 1) := by
    rw [hinterval]
    unfold _root_.GD.N0232.N0720.N1358.d003991
    apply ContinuousOn.div
    · fun_prop
    · unfold _root_.GD.N0232.N0720.N1358.d003989
      fun_prop
    · intro x hx
      exact pow_ne_zero _ (ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha hx))
  have hkernelCont : ContinuousOn (_root_.GD.N0232.N0720.N1358.d004005 k a)
      ((_root_.GD.N0232.N0720.N1358.d003990 a) '' uIcc (-1 : ℝ) 1) := by
    apply (_root_.GD.N0232.N0720.N1358.d004008 k ha).mono
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.GD.N0232.N0720.N1358.d004004 ha (by rwa [hinterval] at hx)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hderivCont hkernelCont
  have heven : Even (k + 1) := hk.add_odd (by decide : Odd 1)
  have hsign : (-1 : ℝ) ^ (k + 1) = 1 := heven.neg_one_pow
  have hsame :
      (∫ x in (-1 : ℝ)..1, (_root_.GD.N0232.N0720.N1358.d004005 k a ∘ _root_.GD.N0232.N0720.N1358.d003990 a) x * _root_.GD.N0232.N0720.N1358.d003991 a x) =
        ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1358.d004005 k a x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simpa only [Function.comp_apply, hsign, one_mul] using
      _root_.GD.N0232.N0720.N1358.d004007 k ha (by rwa [hinterval] at hx)
  rw [hsame, _root_.GD.N0232.N0720.N1358.d004002 ha, _root_.GD.N0232.N0720.N1358.d004003 ha,
    intervalIntegral.integral_symm (-1 : ℝ) 1] at hsub
  linarith

theorem d004010 {a : ℝ} (ha : |a| < 1) :
    (∫ x in (-1 : ℝ)..1,
      (x - a) * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 5) = 0 := by
  simpa [_root_.GD.N0232.N0720.N1358.d004005] using _root_.GD.N0232.N0720.N1358.d004009 1 (by decide) ha

theorem d004011 {a : ℝ} (ha : |a| < 1) :
    (∫ x in (-1 : ℝ)..1,
      (x - a) ^ 3 * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 7) = 0 := by
  simpa [_root_.GD.N0232.N0720.N1358.d004005] using _root_.GD.N0232.N0720.N1358.d004009 3 (by decide) ha

theorem d004012 (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-(n : ℝ) / 2) = ((Real.sqrt x) ^ n)⁻¹ := by
  rw [Real.rpow_div_two_eq_sqrt (-(n : ℝ)) hx,
    Real.rpow_neg (Real.sqrt_nonneg x), Real.rpow_natCast]


theorem d004013 {a : ℝ} (ha : |a| < 1) :
    (∫ x in (-1 : ℝ)..1,
      (x - a) * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(5 / 2 : ℝ))) = 0 := by
  calc
    _ = ∫ x in (-1 : ℝ)..1,
        (x - a) * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 5 := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by simpa [uIcc] using hx
      change (x - a) * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(5 / 2 : ℝ)) =
        (x - a) * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 5
      have hp : (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(5 / 2 : ℝ)) =
          ((Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 5)⁻¹ := by
        convert _root_.GD.N0232.N0720.N1358.d004012 _ (_root_.GD.N0232.N0720.N1358.d003996 ha hx').le 5 using 1 <;> norm_num
      rw [hp, div_eq_mul_inv]
    _ = 0 := _root_.GD.N0232.N0720.N1358.d004010 ha


theorem d004014 {a : ℝ} (ha : |a| < 1) :
    (∫ x in (-1 : ℝ)..1,
      (x - a) ^ 3 * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(7 / 2 : ℝ))) = 0 := by
  calc
    _ = ∫ x in (-1 : ℝ)..1,
        (x - a) ^ 3 * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 7 := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by simpa [uIcc] using hx
      change (x - a) ^ 3 * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(7 / 2 : ℝ)) =
        (x - a) ^ 3 * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 7
      have hp : (_root_.GD.N0232.N0720.N1358.d003992 a x) ^ (-(7 / 2 : ℝ)) =
          ((Real.sqrt (_root_.GD.N0232.N0720.N1358.d003992 a x)) ^ 7)⁻¹ := by
        convert _root_.GD.N0232.N0720.N1358.d004012 _ (_root_.GD.N0232.N0720.N1358.d003996 ha hx').le 7 using 1 <;> norm_num
      rw [hp, div_eq_mul_inv]
    _ = 0 := _root_.GD.N0232.N0720.N1358.d004011 ha

def d004015 (epsilon : ℝ) : ℝ :=
  epsilon / (1 + Real.sqrt (1 - epsilon ^ 2))

theorem d004016 {epsilon : ℝ} (he : |epsilon| < 1) :
    |_root_.GD.N0232.N0720.N1358.d004015 epsilon| < 1 := by
  have hs : 0 < Real.sqrt (1 - epsilon ^ 2) :=
    Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1358.d003993 he)
  have hden : 0 < 1 + Real.sqrt (1 - epsilon ^ 2) := by linarith
  unfold _root_.GD.N0232.N0720.N1358.d004015
  rw [abs_div, abs_of_pos hden]
  apply (div_lt_one hden).2
  linarith

theorem d004017 {epsilon : ℝ} (he : |epsilon| < 1) :
    _root_.GD.N0232.N0720.N1358.d003988 (_root_.GD.N0232.N0720.N1358.d004015 epsilon) = epsilon := by
  let s := Real.sqrt (1 - epsilon ^ 2)
  have hs : 0 < s := Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1358.d003993 he)
  have hsq : s ^ 2 = 1 - epsilon ^ 2 := Real.sq_sqrt (_root_.GD.N0232.N0720.N1358.d003993 he).le
  have hden : 1 + s ≠ 0 := ne_of_gt (by linarith : 0 < 1 + s)
  have hA : 1 + (epsilon / (1 + s)) ^ 2 ≠ 0 :=
    ne_of_gt (by positivity : 0 < 1 + (epsilon / (1 + s)) ^ 2)
  have hpoly : 2 * epsilon * (1 + s) = epsilon * ((1 + s) ^ 2 + epsilon ^ 2) := by
    linear_combination -epsilon * hsq
  change 2 * (epsilon / (1 + s)) / (1 + (epsilon / (1 + s)) ^ 2) = epsilon
  apply (div_eq_iff hA).2
  field_simp [hden]
  linear_combination hpoly



theorem d004018 {epsilon : ℝ} (he : |epsilon| < 1) :
    (∫ x in (-1 : ℝ)..1,
      (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - x ^ 2) *
        (1 - epsilon * x) ^ (-(5 / 2 : ℝ))) = 0 ∧
    (∫ x in (-1 : ℝ)..1,
      (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - x ^ 2) *
        (1 - epsilon * x) ^ (-(7 / 2 : ℝ))) = 0 := by
  have ha := _root_.GD.N0232.N0720.N1358.d004016 he
  constructor
  · simpa only [_root_.GD.N0232.N0720.N1358.d003992, _root_.GD.N0232.N0720.N1358.d004017 he] using _root_.GD.N0232.N0720.N1358.d004013 ha
  · simpa only [_root_.GD.N0232.N0720.N1358.d003992, _root_.GD.N0232.N0720.N1358.d004017 he] using _root_.GD.N0232.N0720.N1358.d004014 ha

end

end GD.N0232.N0720.N1358

#print axioms _root_.GD.N0232.N0720.N1358.d004007
#print axioms _root_.GD.N0232.N0720.N1358.d004009
#print axioms _root_.GD.N0232.N0720.N1358.d004010
#print axioms _root_.GD.N0232.N0720.N1358.d004011
#print axioms _root_.GD.N0232.N0720.N1358.d004018
