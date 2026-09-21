import GD.Module0284
import GD.Module0860
import Mathlib.Probability.Distributions.Beta













open MeasureTheory Set
open scoped Interval

namespace GD.N0232.N0720.N1338

open _root_.GD.N0232.N0720.N1358 _root_.GD.N0232.N0720.N1357

noncomputable section


def d013295 (q : ℝ) : Measure ℝ :=
  ProbabilityTheory.betaMeasure (q - 1 / 2) (q - 1 / 2)

theorem d013296 {q : ℝ} (hq : 1 / 2 < q) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1338.d013295 q) :=
  ProbabilityTheory.isProbabilityMeasureBeta (sub_pos.mpr hq) (sub_pos.mpr hq)



theorem d013297 {q t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.betaPDFReal (q - 1 / 2) (q - 1 / 2) t =
      (1 / ProbabilityTheory.beta (q - 1 / 2) (q - 1 / 2)) *
        (t * (1 - t)) ^ (q - 3 / 2) := by
  rw [ProbabilityTheory.betaPDFReal, if_pos (show 0 < t ∧ t < 1 from ht),
    show q - 1 / 2 - 1 = q - 3 / 2 by ring,
    Real.mul_rpow ht.1.le (sub_nonneg.mpr ht.2.le)]
  ring



theorem d013298 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1436.d013210 m n =
      ((m : ℝ) + (n : ℝ) + 1) / 2 := by
  unfold _root_.GD.N0232.N0720.N1436.d013210
    _root_.GD.N0232.N0720.N1436.d013207
    _root_.GD.N0232.N0720.N1436.d013208
    _root_.GD.N0232.N0720.N1436.d013209
  rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num
  ring

theorem d013299 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (5 / 2 : ℝ) ≤ _root_.GD.N0232.N0720.N1436.d013210 m n := by
  rw [_root_.GD.N0232.N0720.N1338.d013298 hm hn]
  have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith



def d013300 (q : ℝ) (k : ℕ) (a v x : ℝ) : ℝ :=
  (x - a) ^ k * (1 - x ^ 2) ^ (q - 3 / 2) *
    (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(q + ((k : ℝ) - 1) / 2))

private theorem d013301 (q : ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    c ^ (k + 2) * ((c ^ 2) ^ (q - 3 / 2) *
      (c ^ 2) ^ (-(q + ((k : ℝ) - 1) / 2))) = 1 := by
  rw [← Real.rpow_add (sq_pos_of_pos hc)]
  have hexponent : q - 3 / 2 + -(q + ((k : ℝ) - 1) / 2) =
      -((k + 2 : ℕ) : ℝ) / 2 := by
    push_cast
    ring
  rw [hexponent, _root_.GD.N0232.N0720.N1358.d004012 (c ^ 2) (sq_nonneg c) (k + 2),
    Real.sqrt_sq hc.le]
  exact mul_inv_cancel₀ (pow_ne_zero _ hc.ne')

private theorem d013302 (q : ℝ) (k : ℕ)
    {c y w b : ℝ} (hc : 0 < c) (hw : 0 ≤ w) (hb : 0 ≤ b) :
    ((-c * y) ^ k * (c ^ 2 * w) ^ (q - 3 / 2) *
      (c ^ 2 * b) ^ (-(q + ((k : ℝ) - 1) / 2))) * (-c ^ 2) =
        (-1 : ℝ) ^ (k + 1) *
          (y ^ k * w ^ (q - 3 / 2) * b ^ (-(q + ((k : ℝ) - 1) / 2))) := by
  rw [Real.mul_rpow (sq_nonneg c) hw, Real.mul_rpow (sq_nonneg c) hb]
  calc
    _ = ((-1 : ℝ) ^ (k + 1) *
        (y ^ k * w ^ (q - 3 / 2) * b ^ (-(q + ((k : ℝ) - 1) / 2)))) *
          (c ^ (k + 2) * ((c ^ 2) ^ (q - 3 / 2) *
            (c ^ 2) ^ (-(q + ((k : ℝ) - 1) / 2)))) := by
      rw [show -c * y = (-1 : ℝ) * (c * y) by ring,
        mul_pow, mul_pow, pow_succ (-1 : ℝ) k, pow_add c k 2]
      ring
    _ = _ := by rw [_root_.GD.N0232.N0720.N1338.d013301 q k hc, mul_one]


theorem d013303 (q : ℝ) (k : ℕ) {a v x : ℝ}
    (ha : |a| < 1) (hv : 0 ≤ v) (hx : x ∈ Icc (-1 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1338.d013300 q k a v (_root_.GD.N0232.N0720.N1358.d003990 a x) * _root_.GD.N0232.N0720.N1358.d003991 a x =
      (-1 : ℝ) ^ (k + 1) * _root_.GD.N0232.N0720.N1338.d013300 q k a v x := by
  have hd := _root_.GD.N0232.N0720.N1358.d003994 ha hx
  have hc := div_pos (_root_.GD.N0232.N0720.N1358.d003993 ha) hd
  have hw : 0 ≤ 1 - x ^ 2 := by
    have hs := (sq_le_one_iff_abs_le_one x).2 (abs_le.mpr hx)
    linarith
  unfold _root_.GD.N0232.N0720.N1338.d013300
  rw [_root_.GD.N0232.N0720.N1358.d003997 a x hd.ne', _root_.GD.N0232.N0720.N1358.d003998 a x hd.ne',
    _root_.GD.N0232.N0720.N1357.d004220 a v x hd.ne']
  have hderiv : _root_.GD.N0232.N0720.N1358.d003991 a x = -((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1358.d003991
    rw [div_pow, neg_div]
  have hshift : -(1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x =
      -((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) := by rw [neg_div]
  rw [hderiv, hshift]
  exact _root_.GD.N0232.N0720.N1338.d013302 q k hc hw (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx).le

theorem d013304 {q : ℝ} (hq : 3 / 2 ≤ q) (k : ℕ)
    {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    ContinuousOn (_root_.GD.N0232.N0720.N1338.d013300 q k a v) (Icc (-1 : ℝ) 1) := by
  have hweight : ContinuousOn (fun x : ℝ ↦ (1 - x ^ 2) ^ (q - 3 / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    exact Or.inr (sub_nonneg.mpr hq)
  have hbase : ContinuousOn
      (fun x : ℝ ↦ (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(q + ((k : ℝ) - 1) / 2)))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.rpow_const
    · unfold _root_.GD.N0232.N0720.N1357.d004218 _root_.GD.N0232.N0720.N1358.d003992
      fun_prop
    · intro x hx
      exact Or.inl (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx).ne'
  exact ((show ContinuousOn (fun x : ℝ ↦ (x - a) ^ k)
    (Icc (-1 : ℝ) 1) by fun_prop).mul hweight).mul hbase



theorem d013305 {q : ℝ} (hq : 3 / 2 ≤ q)
    (k : ℕ) (hk : Odd k) {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1338.d013300 q k a v x) = 0 := by
  have hinterval : uIcc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by norm_num [uIcc]
  have hderiv : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (_root_.GD.N0232.N0720.N1358.d003990 a) (_root_.GD.N0232.N0720.N1358.d003991 a x) x := by
    intro x hx
    exact _root_.GD.N0232.N0720.N1358.d004001 (_root_.GD.N0232.N0720.N1358.d003994 ha (by rwa [hinterval] at hx)).ne'
  have hderivCont : ContinuousOn (_root_.GD.N0232.N0720.N1358.d003991 a) (uIcc (-1 : ℝ) 1) := by
    rw [hinterval]
    unfold _root_.GD.N0232.N0720.N1358.d003991
    apply ContinuousOn.div
    · fun_prop
    · unfold _root_.GD.N0232.N0720.N1358.d003989
      fun_prop
    · intro x hx
      exact pow_ne_zero _ (_root_.GD.N0232.N0720.N1358.d003994 ha hx).ne'
  have hkernelCont : ContinuousOn (_root_.GD.N0232.N0720.N1338.d013300 q k a v)
      ((_root_.GD.N0232.N0720.N1358.d003990 a) '' uIcc (-1 : ℝ) 1) := by
    apply (_root_.GD.N0232.N0720.N1338.d013304 hq k ha hv).mono
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.GD.N0232.N0720.N1358.d004004 ha (by rwa [hinterval] at hx)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hderivCont hkernelCont
  have heven : Even (k + 1) := hk.add_odd (by decide : Odd 1)
  have hsign : (-1 : ℝ) ^ (k + 1) = 1 := heven.neg_one_pow
  have heq :
      (∫ x in (-1 : ℝ)..1,
        (_root_.GD.N0232.N0720.N1338.d013300 q k a v ∘ _root_.GD.N0232.N0720.N1358.d003990 a) x * _root_.GD.N0232.N0720.N1358.d003991 a x) =
          ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1338.d013300 q k a v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simpa only [Function.comp_apply, hsign, one_mul] using
      _root_.GD.N0232.N0720.N1338.d013303 q k ha hv (by rwa [hinterval] at hx)
  rw [heq, _root_.GD.N0232.N0720.N1358.d004002 ha, _root_.GD.N0232.N0720.N1358.d004003 ha,
    intervalIntegral.integral_symm (-1 : ℝ) 1] at hsub
  linarith

theorem d013306 {q : ℝ} (hq : 3 / 2 ≤ q)
    {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x in (-1 : ℝ)..1, (x - a) * (1 - x ^ 2) ^ (q - 3 / 2) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-q)) = 0 := by
  simpa only [_root_.GD.N0232.N0720.N1338.d013300, Nat.cast_one, sub_self, zero_div, add_zero, pow_one] using
    _root_.GD.N0232.N0720.N1338.d013305 hq 1 (by decide) ha hv

theorem d013307 {q : ℝ} (hq : 3 / 2 ≤ q)
    {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x in (-1 : ℝ)..1, (x - a) ^ 3 * (1 - x ^ 2) ^ (q - 3 / 2) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(q + 1))) = 0 := by
  convert _root_.GD.N0232.N0720.N1338.d013305 hq 3 (by decide) ha hv using 1
  norm_num [_root_.GD.N0232.N0720.N1338.d013300]




theorem d013308 {q p r u : ℝ} (hq : 3 / 2 ≤ q)
    (hp : 0 < p) (hr : 0 < r) (hu : 0 ≤ u) :
    (∫ x in (-1 : ℝ)..1, ((1 + x) / 2) * (1 - x ^ 2) ^ (q - 3 / 2) *
      (_root_.GD.N0232.N0720.N1357.d004229 p r u ((1 + x) / 2)) ^ (-q)) /
      (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (q - 3 / 2) *
        (_root_.GD.N0232.N0720.N1357.d004229 p r u ((1 + x) / 2)) ^ (-q)) = p / (p + r) := by
  let K : ℝ → ℝ := fun x ↦ (1 - x ^ 2) ^ (q - 3 / 2) *
    (_root_.GD.N0232.N0720.N1357.d004229 p r u ((1 + x) / 2)) ^ (-q)
  have ha := _root_.GD.N0232.N0720.N1357.d004233 hp hr
  have hA : 0 < _root_.GD.N0232.N0720.N1357.d004231 p r := by unfold _root_.GD.N0232.N0720.N1357.d004231; positivity
  have hv : 0 ≤ _root_.GD.N0232.N0720.N1357.d004232 p r u := by unfold _root_.GD.N0232.N0720.N1357.d004232; positivity
  have hpoint {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
      (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hKc : ContinuousOn K (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro x hx
      exact Or.inr (sub_nonneg.mpr hq)
    · apply ContinuousOn.rpow_const
      · unfold _root_.GD.N0232.N0720.N1357.d004229
        fun_prop
      · intro x hx
        exact Or.inl (_root_.GD.N0232.N0720.N1357.d004236 hp hr hu (hpoint hx)).ne'
  have hKi : IntervalIntegrable K volume (-1) 1 :=
    hKc.intervalIntegrable_of_Icc (by norm_num)
  have hTKi : IntervalIntegrable (fun x : ℝ ↦ ((1 + x) / 2) * K x) volume (-1) 1 :=
    ((show ContinuousOn (fun x : ℝ ↦ (1 + x) / 2) (Icc (-1 : ℝ) 1) by
      fun_prop).mul hKc).intervalIntegrable_of_Icc (by norm_num)
  have hmass : 0 < ∫ x in (-1 : ℝ)..1, K x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hKi _ (by norm_num)
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hw : 0 < 1 - x ^ 2 := by
      have hxx : |x| < 1 := abs_lt.mpr hx
      exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr hxx)
    exact mul_pos (Real.rpow_pos_of_pos hw _) (Real.rpow_pos_of_pos
      (_root_.GD.N0232.N0720.N1357.d004236 hp hr hu (hpoint hx')) _)
  have hzero : (∫ x in (-1 : ℝ)..1, (((1 + x) / 2) - p / (p + r)) * K x) = 0 := by
    calc
      _ = ((_root_.GD.N0232.N0720.N1357.d004231 p r) ^ (-q) / 2) *
          ∫ x in (-1 : ℝ)..1, (x - _root_.GD.N0232.N0720.N1357.d004230 p r) * (1 - x ^ 2) ^ (q - 3 / 2) *
            (_root_.GD.N0232.N0720.N1357.d004218 (_root_.GD.N0232.N0720.N1357.d004230 p r) (_root_.GD.N0232.N0720.N1357.d004232 p r u) x) ^ (-q) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (-1 : ℝ) 1 := by
          simpa only [uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using hx
        dsimp only [K]
        rw [_root_.GD.N0232.N0720.N1357.d004235 hp hr,
          _root_.GD.N0232.N0720.N1357.d004234 hp hr,
          Real.mul_rpow hA.le (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx').le]
        ring
      _ = 0 := by rw [_root_.GD.N0232.N0720.N1338.d013306 hq ha hv, mul_zero]
  have hmoment : (∫ x in (-1 : ℝ)..1, ((1 + x) / 2) * K x) =
      (p / (p + r)) * ∫ x in (-1 : ℝ)..1, K x := by
    simp_rw [sub_mul] at hzero
    rw [intervalIntegral.integral_sub hTKi (hKi.const_mul _),
      intervalIntegral.integral_const_mul] at hzero
    exact sub_eq_zero.mp hzero
  have hratio := (div_eq_iff hmass.ne').2 hmoment
  simpa only [K, mul_assoc] using hratio

end
end GD.N0232.N0720.N1338

#print axioms _root_.GD.N0232.N0720.N1338.d013296
#print axioms _root_.GD.N0232.N0720.N1338.d013298
#print axioms _root_.GD.N0232.N0720.N1338.d013305
#print axioms _root_.GD.N0232.N0720.N1338.d013306
#print axioms _root_.GD.N0232.N0720.N1338.d013307
#print axioms _root_.GD.N0232.N0720.N1338.d013308
