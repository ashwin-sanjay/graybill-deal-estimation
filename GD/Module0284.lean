import GD.Module0283
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic












open MeasureTheory Set
open scoped Interval

namespace GD.N0232.N0720.N1357

open _root_.GD.N0232.N0720.N1358 _root_.GD.N0232.N0720.N1353
open _root_.GD.N0232.N0720.N1414 _root_.GD.N0232.N0720.N1290

noncomputable section

def d004218 (a v x : ℝ) : ℝ := _root_.GD.N0232.N0720.N1358.d003992 a x + v * (1 - x ^ 2)

theorem d004219 {a v x : ℝ} (ha : |a| < 1) (hv : 0 ≤ v)
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 < _root_.GD.N0232.N0720.N1357.d004218 a v x := by
  have hsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 (abs_le.mpr hx)
  exact add_pos_of_pos_of_nonneg (_root_.GD.N0232.N0720.N1358.d003996 ha hx) (mul_nonneg hv (by linarith))

theorem d004220 (a v x : ℝ) (hd : _root_.GD.N0232.N0720.N1358.d003989 a x ≠ 0) :
    _root_.GD.N0232.N0720.N1357.d004218 a v (_root_.GD.N0232.N0720.N1358.d003990 a x) =
      ((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) ^ 2 * _root_.GD.N0232.N0720.N1357.d004218 a v x := by
  unfold _root_.GD.N0232.N0720.N1357.d004218
  rw [_root_.GD.N0232.N0720.N1358.d003999 a x hd, _root_.GD.N0232.N0720.N1358.d003998 a x hd]
  ring

theorem d004221 {a v x : ℝ} (ha : |a| < 1) (hv : 0 ≤ v)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.sqrt (_root_.GD.N0232.N0720.N1357.d004218 a v (_root_.GD.N0232.N0720.N1358.d003990 a x)) =
      ((1 - a ^ 2) / _root_.GD.N0232.N0720.N1358.d003989 a x) * Real.sqrt (_root_.GD.N0232.N0720.N1357.d004218 a v x) := by
  have hd := _root_.GD.N0232.N0720.N1358.d003994 ha hx
  rw [_root_.GD.N0232.N0720.N1357.d004220 a v x (ne_of_gt hd), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (div_nonneg (_root_.GD.N0232.N0720.N1358.d003993 ha).le hd.le)]

def d004222 (a v x : ℝ) : ℝ :=
  (x - a) * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1357.d004218 a v x)) ^ 5

theorem d004223 {a v x : ℝ} (ha : |a| < 1) (hv : 0 ≤ v)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1357.d004222 a v (_root_.GD.N0232.N0720.N1358.d003990 a x) * _root_.GD.N0232.N0720.N1358.d003991 a x =
      _root_.GD.N0232.N0720.N1357.d004222 a v x := by
  have hd := ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha hx)
  have hc := ne_of_gt (_root_.GD.N0232.N0720.N1358.d003993 ha)
  have hs := ne_of_gt (Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx))
  unfold _root_.GD.N0232.N0720.N1357.d004222
  rw [_root_.GD.N0232.N0720.N1358.d003997 a x hd, _root_.GD.N0232.N0720.N1358.d003998 a x hd,
    _root_.GD.N0232.N0720.N1357.d004221 ha hv hx]
  unfold _root_.GD.N0232.N0720.N1358.d003991
  field_simp [hd, hc, hs] <;> ring

theorem d004224 {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    ContinuousOn (_root_.GD.N0232.N0720.N1357.d004222 a v) (Icc (-1 : ℝ) 1) := by
  unfold _root_.GD.N0232.N0720.N1357.d004222
  apply ContinuousOn.div
  · fun_prop
  · unfold _root_.GD.N0232.N0720.N1357.d004218 _root_.GD.N0232.N0720.N1358.d003992
    fun_prop
  · intro x hx
    exact pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx)))


theorem d004225 {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1357.d004222 a v x) = 0 := by
  have hinterval : uIcc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by norm_num [uIcc]
  have hderiv : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (_root_.GD.N0232.N0720.N1358.d003990 a) (_root_.GD.N0232.N0720.N1358.d003991 a x) x := by
    intro x hx
    exact _root_.GD.N0232.N0720.N1358.d004001 (ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha (by rwa [hinterval] at hx)))
  have hderivCont : ContinuousOn (_root_.GD.N0232.N0720.N1358.d003991 a) (uIcc (-1 : ℝ) 1) := by
    rw [hinterval]
    unfold _root_.GD.N0232.N0720.N1358.d003991
    apply ContinuousOn.div
    · fun_prop
    · unfold _root_.GD.N0232.N0720.N1358.d003989
      fun_prop
    · intro x hx
      exact pow_ne_zero _ (ne_of_gt (_root_.GD.N0232.N0720.N1358.d003994 ha hx))
  have hkernelCont : ContinuousOn (_root_.GD.N0232.N0720.N1357.d004222 a v)
      ((_root_.GD.N0232.N0720.N1358.d003990 a) '' uIcc (-1 : ℝ) 1) := by
    apply (_root_.GD.N0232.N0720.N1357.d004224 ha hv).mono
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.GD.N0232.N0720.N1358.d004004 ha (by rwa [hinterval] at hx)
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hderivCont hkernelCont
  have heq :
      (∫ x in (-1 : ℝ)..1,
        (_root_.GD.N0232.N0720.N1357.d004222 a v ∘ _root_.GD.N0232.N0720.N1358.d003990 a) x * _root_.GD.N0232.N0720.N1358.d003991 a x) =
          ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1357.d004222 a v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact _root_.GD.N0232.N0720.N1357.d004223 ha hv (by rwa [hinterval] at hx)
  rw [heq, _root_.GD.N0232.N0720.N1358.d004002 ha, _root_.GD.N0232.N0720.N1358.d004003 ha,
    intervalIntegral.integral_symm (-1 : ℝ) 1] at hsub
  linarith

theorem d004226 {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x in (-1 : ℝ)..1,
      (x - a) * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ))) = 0 := by
  calc
    _ = ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1357.d004222 a v x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by simpa [uIcc] using hx
      change (x - a) * (1 - x ^ 2) * (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) =
        (x - a) * (1 - x ^ 2) / (Real.sqrt (_root_.GD.N0232.N0720.N1357.d004218 a v x)) ^ 5
      have hp : (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) =
          ((Real.sqrt (_root_.GD.N0232.N0720.N1357.d004218 a v x)) ^ 5)⁻¹ := by
        convert _root_.GD.N0232.N0720.N1358.d004012 _ (_root_.GD.N0232.N0720.N1357.d004219 ha hv hx').le 5 using 1 <;> norm_num
      rw [hp, div_eq_mul_inv]
    _ = 0 := _root_.GD.N0232.N0720.N1357.d004225 ha hv

theorem d004227 {a v : ℝ}
    (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 := by
  rw [_root_.GD.N0232.N0720.N1353.d004183
    (fun x : ℝ ↦ (x - a) * (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)))]
  have heq :
      (fun x : ℝ ↦ (1 - x ^ 2) * ((x - a) *
        (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)))) =
      fun x ↦ (x - a) * (1 - x ^ 2) *
        (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) := by
    funext x
    ring
  rw [heq, _root_.GD.N0232.N0720.N1357.d004226 ha hv, mul_zero]

theorem d004228 {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, (x : ℝ) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) =
      a * ∫ x : _root_.GD.N0232.N0720.N1353.d004179,
        (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182 := by
  let K : _root_.GD.N0232.N0720.N1353.d004179 → ℝ := fun x ↦ (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-(5 / 2 : ℝ))
  have hKc : Continuous K := by
    apply Continuous.rpow_const
    · unfold _root_.GD.N0232.N0720.N1357.d004218 _root_.GD.N0232.N0720.N1358.d003992
      fun_prop
    · intro x
      exact Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1357.d004219 ha hv x.2))
  have hK : Integrable K _root_.GD.N0232.N0720.N1353.d004182 :=
    hKc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hXK : Integrable (fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ (x : ℝ) * K x) _root_.GD.N0232.N0720.N1353.d004182 :=
    (continuous_subtype_val.mul hKc).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hzero := _root_.GD.N0232.N0720.N1357.d004227 ha hv
  have heq :
      (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) * K x ∂_root_.GD.N0232.N0720.N1353.d004182) =
        (∫ x : _root_.GD.N0232.N0720.N1353.d004179, (x : ℝ) * K x ∂_root_.GD.N0232.N0720.N1353.d004182) -
          a * ∫ x : _root_.GD.N0232.N0720.N1353.d004179, K x ∂_root_.GD.N0232.N0720.N1353.d004182 := by
    simp_rw [sub_mul]
    rw [integral_sub hXK (hK.const_mul a), integral_const_mul]
  change (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) * K x ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 at hzero
  rw [heq] at hzero
  exact sub_eq_zero.mp hzero


def d004229 (p q u t : ℝ) : ℝ :=
  p ^ 2 * (1 - t) + q ^ 2 * t + u * t * (1 - t)

def d004230 (p q : ℝ) : ℝ := (p - q) / (p + q)

def d004231 (p q : ℝ) : ℝ := (p ^ 2 + q ^ 2) / 2

def d004232 (p q u : ℝ) : ℝ := u / (2 * (p ^ 2 + q ^ 2))

theorem d004233 {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |_root_.GD.N0232.N0720.N1357.d004230 p q| < 1 := by
  have hsum : 0 < p + q := add_pos hp hq
  rw [_root_.GD.N0232.N0720.N1357.d004230, abs_lt]
  constructor
  · apply (lt_div_iff₀ hsum).2
    linarith
  · apply (div_lt_iff₀ hsum).2
    linarith

theorem d004234 {p q u : ℝ}
    (hp : 0 < p) (hq : 0 < q) (x : ℝ) :
    _root_.GD.N0232.N0720.N1357.d004229 p q u ((1 + x) / 2) =
      _root_.GD.N0232.N0720.N1357.d004231 p q * _root_.GD.N0232.N0720.N1357.d004218 (_root_.GD.N0232.N0720.N1357.d004230 p q) (_root_.GD.N0232.N0720.N1357.d004232 p q u) x := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  have hss : p ^ 2 + q ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < p ^ 2 + q ^ 2)
  have ha : 1 + ((p - q) / (p + q)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold _root_.GD.N0232.N0720.N1357.d004229 _root_.GD.N0232.N0720.N1357.d004231 _root_.GD.N0232.N0720.N1357.d004218 _root_.GD.N0232.N0720.N1358.d003992 _root_.GD.N0232.N0720.N1358.d003988 _root_.GD.N0232.N0720.N1357.d004230 _root_.GD.N0232.N0720.N1357.d004232
  field_simp [hs, hss, ha] <;> ring

theorem d004235 {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : ℝ) :
    (1 + x) / 2 - p / (p + q) = (x - _root_.GD.N0232.N0720.N1357.d004230 p q) / 2 := by
  unfold _root_.GD.N0232.N0720.N1357.d004230
  field_simp [ne_of_gt (add_pos hp hq)] <;> ring

theorem d004236 {p q u t : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hu : 0 ≤ u) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < _root_.GD.N0232.N0720.N1357.d004229 p q u t := by
  have hnonneg : 0 ≤ u * t * (1 - t) :=
    mul_nonneg (mul_nonneg hu ht.1) (sub_nonneg.mpr ht.2)
  have hl : 0 ≤ p ^ 2 * (1 - t) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht.2)
  have hr : 0 ≤ q ^ 2 * t := mul_nonneg (sq_nonneg _) ht.1
  unfold _root_.GD.N0232.N0720.N1357.d004229
  by_cases ht0 : t = 0
  · subst t
    simpa using sq_pos_of_pos hp
  · have hrt : 0 < q ^ 2 * t :=
      mul_pos (sq_pos_of_pos hq) (lt_of_le_of_ne ht.1 (Ne.symm ht0))
    linarith



theorem d004237 {p q u : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 ≤ u) :
    (∫ t : ℝ, (t - p / (p + q)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p q u t) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1414.d004209 (1 / 2) (1 / 2)) = 0 := by
  have ha := _root_.GD.N0232.N0720.N1357.d004233 hp hq
  have hA : 0 < _root_.GD.N0232.N0720.N1357.d004231 p q := by unfold _root_.GD.N0232.N0720.N1357.d004231; positivity
  have hv : 0 ≤ _root_.GD.N0232.N0720.N1357.d004232 p q u := by unfold _root_.GD.N0232.N0720.N1357.d004232; positivity
  have hmeas : Measurable (fun t : ℝ ↦ (t - p / (p + q)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p q u t) ^ (-(5 / 2 : ℝ))) := by
    unfold _root_.GD.N0232.N0720.N1357.d004229
    fun_prop
  rw [_root_.GD.N0232.N0720.N1414.d004209, integral_map
    (f := fun t : ℝ ↦ (t - p / (p + q)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p q u t) ^ (-(5 / 2 : ℝ)))
    (by fun_prop) hmeas.aestronglyMeasurable]
  have heq :
      (∫ x : _root_.GD.N0232.N0720.N1353.d004179, (1 / 2 + 1 / 2 * (x : ℝ) - p / (p + q)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p q u (1 / 2 + 1 / 2 * (x : ℝ))) ^ (-(5 / 2 : ℝ))
        ∂_root_.GD.N0232.N0720.N1353.d004182) =
      ((_root_.GD.N0232.N0720.N1357.d004231 p q) ^ (-(5 / 2 : ℝ)) / 2) *
        ∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - _root_.GD.N0232.N0720.N1357.d004230 p q) *
          (_root_.GD.N0232.N0720.N1357.d004218 (_root_.GD.N0232.N0720.N1357.d004230 p q) (_root_.GD.N0232.N0720.N1357.d004232 p q u) x) ^ (-(5 / 2 : ℝ))
          ∂_root_.GD.N0232.N0720.N1353.d004182 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (1 / 2 : ℝ) + 1 / 2 * (x : ℝ) = (1 + (x : ℝ)) / 2 by ring,
      _root_.GD.N0232.N0720.N1357.d004234 hp hq,
      _root_.GD.N0232.N0720.N1357.d004235 hp hq,
      Real.mul_rpow hA.le (_root_.GD.N0232.N0720.N1357.d004219 ha hv x.2).le]
    ring
  rw [heq, _root_.GD.N0232.N0720.N1357.d004227 ha hv, mul_zero]





theorem d004238
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 (1 / 2) (1 / 2))
    {p q u : ℝ} (hp : 0 < p) (hq : 0 < q) (hu : 0 ≤ u) :
    _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1357.d004229 p q u t) mu = p / (p + q) := by
  let P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ _root_.GD.N0232.N0720.N1357.d004229 p q u t
  let K : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ (P t) ^ (-(5 / 2 : ℝ))
  have hP : Continuous P := by unfold P _root_.GD.N0232.N0720.N1357.d004229; fun_prop
  have hpos (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < P t := _root_.GD.N0232.N0720.N1357.d004236 hp hq hu t.2
  have hK : Integrable K mu := by
    simpa [K] using _root_.GD.N0232.N0720.N1290.d004135 (5 / 2) (phi := fun _ ↦ 1)
      continuous_const hP hpos mu
  have hTK : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * K t) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 (5 / 2) continuous_subtype_val hP hpos mu
  have hzero : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, ((t : ℝ) - p / (p + q)) * K t ∂mu) = 0 := by
    have h := _root_.GD.N0232.N0720.N1357.d004237 hp hq hu
    have hmeas : Measurable (fun t : ℝ ↦ (t - p / (p + q)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p q u t) ^ (-(5 / 2 : ℝ))) := by
      unfold _root_.GD.N0232.N0720.N1357.d004229
      fun_prop
    rw [← hclass, integral_map
      (f := fun t : ℝ ↦ (t - p / (p + q)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p q u t) ^ (-(5 / 2 : ℝ)))
      measurable_subtype_coe.aemeasurable hmeas.aestronglyMeasurable] at h
    exact h
  have hmoment : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * K t ∂mu) =
      (p / (p + q)) * ∫ t : _root_.GD.N0232.N0720.N1290.d004131, K t ∂mu := by
    simp_rw [sub_mul] at hzero
    rw [integral_sub hTK (hK.const_mul _), integral_const_mul] at hzero
    exact sub_eq_zero.mp hzero
  change (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * K t ∂mu) / _root_.GD.N0232.N0720.N1290.d004139 (5 / 2) P mu = _
  apply (div_eq_iff (ne_of_gt (_root_.GD.N0232.N0720.N1290.d004146 (5 / 2) P hP hpos mu))).2
  exact hmoment

end
end GD.N0232.N0720.N1357

#print axioms _root_.GD.N0232.N0720.N1357.d004227
#print axioms _root_.GD.N0232.N0720.N1357.d004228
#print axioms _root_.GD.N0232.N0720.N1357.d004238
