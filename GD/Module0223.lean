import GD.Module0222
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper











open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1050

noncomputable section

open _root_.GD.N0232.N0720.N1463
open _root_.GD.N0232.N0720.N1462
open _root_.GD.N0232.N0720.N1049


def d003157 (x : ℝ) : ℝ := x / (1 - x)

def d003158 (x : ℝ) : ℝ := 1 / (1 - x) ^ 2

theorem d003159 :
    _root_.GD.N0232.N0720.N1050.d003157 '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro hy
    have hy0 : 0 < y := hy
    let x := y / (1 + y)
    have hden : 0 < 1 + y := by linarith
    have hx0 : 0 < x := div_pos hy0 hden
    have hx1 : x < 1 := (div_lt_one hden).mpr (by linarith)
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    dsimp [_root_.GD.N0232.N0720.N1050.d003157, x]
    field_simp [ne_of_gt hden]
    ring

theorem d003160
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt _root_.GD.N0232.N0720.N1050.d003157 (_root_.GD.N0232.N0720.N1050.d003158 x)
      (Ioo 0 1) x := by
  have hden : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have h := (hasDerivAt_id x).div
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) hden
  have hcoef :
      (1 * (1 - x) - x * (0 - 1)) / (1 - x) ^ 2 =
        _root_.GD.N0232.N0720.N1050.d003158 x := by
    dsimp [_root_.GD.N0232.N0720.N1050.d003158]
    field_simp [hden]
    ring
  exact (h.congr_deriv hcoef).hasDerivWithinAt

theorem d003161 :
    InjOn _root_.GD.N0232.N0720.N1050.d003157 (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxden : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hyden : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy.2)
  dsimp [_root_.GD.N0232.N0720.N1050.d003157] at hxy
  field_simp [hxden, hyden] at hxy
  linarith


theorem d003162
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioo (0 : ℝ) 1,
        x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      ProbabilityTheory.beta a b := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb,
    Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow,
      RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith [hx.1, hx.2]
  convert! Complex.betaIntegral_convergent
    (u := a) (v := b) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

private theorem d003163
    (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1050.d003158 x| *
        ((_root_.GD.N0232.N0720.N1050.d003157 x) ^ (a - 1) *
          (1 + _root_.GD.N0232.N0720.N1050.d003157 x) ^ (-(a + b))) =
      x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x := sub_pos.mpr hx.2
  have hone : 1 + _root_.GD.N0232.N0720.N1050.d003157 x = (1 - x)⁻¹ := by
    dsimp [_root_.GD.N0232.N0720.N1050.d003157]
    field_simp [ne_of_gt h1x]
    ring
  have hderiv : 0 < _root_.GD.N0232.N0720.N1050.d003158 x := by
    dsimp [_root_.GD.N0232.N0720.N1050.d003158]
    positivity
  rw [abs_of_pos hderiv, hone]
  dsimp [_root_.GD.N0232.N0720.N1050.d003157, _root_.GD.N0232.N0720.N1050.d003158]
  rw [Real.div_rpow hx0.le h1x.le,
    Real.inv_rpow h1x.le, ← Real.rpow_neg h1x.le]
  rw [div_eq_mul_inv]
  have hsquare : ((1 - x) ^ 2 : ℝ)⁻¹ = (1 - x) ^ (-2 : ℝ) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_neg h1x.le (2 : ℝ)).symm
  rw [hsquare, div_eq_mul_inv, ← Real.rpow_neg h1x.le]
  have hcollect :
      (1 - x) ^ (-2 : ℝ) * (1 - x) ^ (-(a - 1)) *
          (1 - x) ^ (-(-(a + b))) =
        (1 - x) ^ (b - 1) := by
    rw [← Real.rpow_add h1x, ← Real.rpow_add h1x]
    congr 1
    ring
  calc
    _ = x ^ (a - 1) *
        ((1 - x) ^ (-2 : ℝ) * (1 - x) ^ (-(a - 1)) *
          (1 - x) ^ (-(-(a + b)))) := by ring
    _ = _ := by rw [hcollect]



theorem d003164
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (a - 1) * (1 + x) ^ (-(a + b))) =
      ProbabilityTheory.beta a b := by
  let g : ℝ → ℝ := fun x ↦
    x ^ (a - 1) * (1 + x) ^ (-(a + b))
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo _root_.GD.N0232.N0720.N1050.d003160
      _root_.GD.N0232.N0720.N1050.d003161 g
  rw [_root_.GD.N0232.N0720.N1050.d003159] at hcov
  change (∫ x in Ioi (0 : ℝ), g x) = ProbabilityTheory.beta a b
  rw [hcov, ← _root_.GD.N0232.N0720.N1050.d003162 a b ha hb]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simpa [g, smul_eq_mul] using _root_.GD.N0232.N0720.N1050.d003163 a b x hx


def d003165 (r c s : ℝ) : ℝ :=
  s ^ (1 / 2 : ℝ) * (c + s / 2) ^ (-(r + 3 / 2))

private theorem d003166
    (r c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1050.d003165 r c ((2 * c) * x) =
      (2 * c) ^ (1 / 2 : ℝ) * c ^ (-(r + 3 / 2)) *
        (x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(r + 3 / 2))) := by
  have h2c : 0 < 2 * c := mul_pos (by norm_num) hc
  have h1x : 0 < 1 + x := by linarith
  unfold _root_.GD.N0232.N0720.N1050.d003165
  rw [Real.mul_rpow h2c.le hx.le]
  have hden : c + 2 * c * x / 2 = c * (1 + x) := by ring
  rw [hden, Real.mul_rpow hc.le h1x.le]
  ring


theorem d003167
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 r c s) =
      2 ^ (3 / 2 : ℝ) * c ^ (-r) *
        ProbabilityTheory.beta (3 / 2) r := by
  let A : ℝ := (2 * c) ^ (1 / 2 : ℝ) * c ^ (-(r + 3 / 2))
  let g : ℝ → ℝ := fun x ↦
    x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(r + 3 / 2))
  have h2c : 0 < 2 * c := mul_pos (by norm_num) hc
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (g := _root_.GD.N0232.N0720.N1050.d003165 r c) 0 h2c
  simp only [mul_zero, smul_eq_mul] at hscale
  have hscaled :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 r c ((2 * c) * x)) =
        A * ProbabilityTheory.beta (3 / 2) r := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), A * g x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simpa [A, g] using _root_.GD.N0232.N0720.N1050.d003166 r c x hc hx
      _ = A * ∫ x in Ioi (0 : ℝ), g x := by rw [integral_const_mul]
      _ = A * ProbabilityTheory.beta (3 / 2) r := by
        congr 1
        dsimp [g]
        convert _root_.GD.N0232.N0720.N1050.d003164 (3 / 2) r (by norm_num) hr using 1 <;> ring
  have hrecover :
      (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 r c s) =
        (2 * c) *
          (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 r c ((2 * c) * x)) := by
    rw [hscale]
    field_simp [h2c.ne']
  rw [hrecover, hscaled]
  dsimp [A]
  have hcollect2c :
      (2 * c) * (2 * c) ^ (1 / 2 : ℝ) =
        (2 * c) ^ (3 / 2 : ℝ) := by
    calc
      _ = (2 * c) ^ (1 : ℝ) * (2 * c) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = (2 * c) ^ (1 + 1 / 2 : ℝ) :=
        (Real.rpow_add h2c 1 (1 / 2)).symm
      _ = _ := by congr 1 <;> ring
  calc
    2 * c * ((2 * c) ^ (1 / 2 : ℝ) * c ^ (-(r + 3 / 2)) *
        ProbabilityTheory.beta (3 / 2) r) =
      ((2 * c) * (2 * c) ^ (1 / 2 : ℝ)) * c ^ (-(r + 3 / 2)) *
        ProbabilityTheory.beta (3 / 2) r := by ring
    _ = (2 * c) ^ (3 / 2 : ℝ) * c ^ (-(r + 3 / 2)) *
        ProbabilityTheory.beta (3 / 2) r := by rw [hcollect2c]
    _ = (2 ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ)) *
        c ^ (-(r + 3 / 2)) * ProbabilityTheory.beta (3 / 2) r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hc.le]
    _ = 2 ^ (3 / 2 : ℝ) * c ^ (-r) *
        ProbabilityTheory.beta (3 / 2) r := by
      have hcCollect :
          c ^ (3 / 2 : ℝ) * c ^ (-(r + 3 / 2)) = c ^ (-r) := by
        rw [← Real.rpow_add hc]
        congr 1
        ring
      calc
        _ = 2 ^ (3 / 2 : ℝ) *
            (c ^ (3 / 2 : ℝ) * c ^ (-(r + 3 / 2))) *
              ProbabilityTheory.beta (3 / 2) r := by ring
        _ = _ := by rw [hcCollect]


theorem d003168
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 r c s) =
      2 ^ (3 / 2 : ℝ) * Real.Gamma (3 / 2) * Real.Gamma r /
        Real.Gamma (r + 3 / 2) * c ^ (-r) := by
  rw [_root_.GD.N0232.N0720.N1050.d003167 r c hr hc]
  unfold ProbabilityTheory.beta
  ring


theorem d003169
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s) =
      _root_.GD.N0232.N0720.N1049.d003147 alpha beta l := by
  have hr : 0 < alpha + beta := add_pos halpha hbeta
  have hc : 0 < beta * l := mul_pos hbeta hl.1
  let projective : ℝ := l ^ (beta - 1) * (1 - l) ^ (alpha - 1)
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        projective * _root_.GD.N0232.N0720.N1050.d003165 (alpha + beta) (beta * l) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      simp only [_root_.GD.N0232.N0720.N1462.d003122, _root_.GD.N0232.N0720.N1462.d003121,
        _root_.GD.N0232.N0720.N1462.d003113, _root_.GD.N0232.N0720.N1462.d003109, _root_.GD.N0232.N0720.N1050.d003165,
        projective]
      ring
    _ = projective *
        ∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1050.d003165 (alpha + beta) (beta * l) s := by
      rw [integral_const_mul]
    _ = projective *
        (_root_.GD.N0232.N0720.N1049.d003146 alpha beta * (beta * l) ^ (-(alpha + beta))) := by
      rw [_root_.GD.N0232.N0720.N1050.d003168 (alpha + beta) (beta * l) hr hc]
      rfl
    _ = _root_.GD.N0232.N0720.N1049.d003147 alpha beta l := by
      unfold _root_.GD.N0232.N0720.N1049.d003147 projective
      ring


theorem d003170
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) =
      _root_.GD.N0232.N0720.N1049.d003148 alpha beta l := by
  have hr : 0 < alpha + beta := add_pos halpha hbeta
  have hc : 0 < alpha * (1 - l) :=
    mul_pos halpha (sub_pos.mpr hl.2)
  let projective : ℝ := l ^ (beta - 1) * (1 - l) ^ (alpha - 1)
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        projective * _root_.GD.N0232.N0720.N1050.d003165 (alpha + beta) (alpha * (1 - l)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      simp only [_root_.GD.N0232.N0720.N1462.d003123, _root_.GD.N0232.N0720.N1462.d003121,
        _root_.GD.N0232.N0720.N1462.d003118, _root_.GD.N0232.N0720.N1462.d003109, _root_.GD.N0232.N0720.N1050.d003165,
        projective]
      ring
    _ = projective *
        ∫ s in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1050.d003165 (alpha + beta) (alpha * (1 - l)) s := by
      rw [integral_const_mul]
    _ = projective *
        (_root_.GD.N0232.N0720.N1049.d003146 alpha beta *
          (alpha * (1 - l)) ^ (-(alpha + beta))) := by
      rw [_root_.GD.N0232.N0720.N1050.d003168
        (alpha + beta) (alpha * (1 - l)) hr hc]
      rfl
    _ = _root_.GD.N0232.N0720.N1049.d003148 alpha beta l := by
      unfold _root_.GD.N0232.N0720.N1049.d003148 projective
      ring



theorem d003171
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s) =
      _root_.GD.N0232.N0720.N1049.d003149 alpha beta l *
        (_root_.GD.N0232.N0720.N1463.d003059 alpha beta * (1 - l) ^ (alpha + beta)) := by
  rw [_root_.GD.N0232.N0720.N1050.d003169 halpha hbeta hl,
    _root_.GD.N0232.N0720.N1049.d003154 halpha hbeta hl]



theorem d003172
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) =
      _root_.GD.N0232.N0720.N1049.d003149 alpha beta l *
        (_root_.GD.N0232.N0720.N1463.d003060 alpha beta * l ^ (alpha + beta)) := by
  rw [_root_.GD.N0232.N0720.N1050.d003170 halpha hbeta hl,
    _root_.GD.N0232.N0720.N1049.d003155 halpha hbeta hl]



theorem d003173
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) /
        ((∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003122 alpha beta l s) +
          ∫ s in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1462.d003123 alpha beta l s) =
      _root_.GD.N0232.N0720.N1463.d003066 alpha beta l := by
  rw [_root_.GD.N0232.N0720.N1050.d003169 halpha hbeta hl,
    _root_.GD.N0232.N0720.N1050.d003170 halpha hbeta hl]
  exact _root_.GD.N0232.N0720.N1049.d003156 halpha hbeta hl

end

end N1050
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1050.d003168
#print axioms _root_.GD.N0232.N0720.N1050.d003169
#print axioms _root_.GD.N0232.N0720.N1050.d003170
#print axioms _root_.GD.N0232.N0720.N1050.d003173
