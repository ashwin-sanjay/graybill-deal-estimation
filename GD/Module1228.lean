import GD.Module1223
import GD.Module1227
import GD.Module0744

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0719.N0996

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1326
  (d019885)
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0999 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0900 (d009095)
open _root_.GD.N0107

noncomputable section

variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)

abbrev d019929 := _root_.GD.N0232.N0720.N1341.d004414 d
abbrev d019930 := _root_.GD.N0232.N0719.N0859.d010809 k

def d019931 (h : _root_.GD.N0232.N0720.N1341.d004417 d) (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) : ℝ :=
  _root_.GD.N0232.N0720.N1341.d004418 h (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)

@[fun_prop] theorem d019932 (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Measurable (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h) :=
  (_root_.GD.N0232.N0720.N1326.d019885 h).comp (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurable

private theorem d019933 (q : _root_.GD.N0232.N0720.N1316.d004440 d) (x : _root_.GD.N0232.N0719.N0996.d019929) :
    0 ≤ _root_.GD.N0232.N0720.N1316.d004445 q x := mul_nonneg (_root_.GD.N0232.N0720.N1316.d004446 q).le (Real.exp_pos _).le

@[fun_prop] private theorem d019934 (q : _root_.GD.N0232.N0720.N1316.d004440 d) :
    Measurable (_root_.GD.N0232.N0720.N1316.d004445 q) := by unfold _root_.GD.N0232.N0720.N1316.d004445; fun_prop

def d019935 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : _root_.GD.N0232.N0719.N0996.d019930 (k := k) where
  location := q.1
  scale := _root_.GD.N0232.N0719.N0997.d019811 q
  scale_pos := _root_.GD.N0232.N0719.N0997.d019812 q

theorem d019936 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0996.d019935 q)
        (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q h) := by
  let p := _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q
  have hm : Measurable (fun x : _root_.GD.N0232.N0719.N0996.d019929 =>
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2)) :=
    ((_root_.GD.N0232.N0720.N1326.d019885 h).sub measurable_const).pow_const 2 |>.ennreal_ofReal
  change (∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h omega - q.1) ^ 2)
    ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)) = _
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2)
        ∂volume.withDensity (fun x => ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 p x)) :=
      _root_.GD.N0232.N0719.N0997.d019815 sizes hdim q _ (_root_.GD.N0232.N0720.N1326.d019885 h)
    _ = ∫⁻ x, ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 p x) *
        ENNReal.ofReal ((_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2) :=
      lintegral_withDensity_eq_lintegral_mul volume
        (_root_.GD.N0232.N0719.N0996.d019934 p).ennreal_ofReal hm
    _ = ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q h) := by
      change _ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004469 p h)
      rw [_root_.GD.N0232.N0720.N1316.d004469,
        ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0232.N0720.N1316.d004468 p h)
          (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0719.N0996.d019933 p x))]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (_root_.GD.N0232.N0719.N0996.d019933 p x), mul_comm]
      rfl

theorem d019937 (c : ℝ) (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0232.N0719.N0997.d019807 sizes hdim (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 c omega) =
      c • _root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega := by
  apply (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm.injective
  rw [(_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm_apply_apply, _root_.GD.N0232.N0719.N0997.d019810,
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm_apply_apply]
  funext i j
  simp [_root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]

theorem d019938 (h : _root_.GD.N0232.N0720.N1341.d004417 d) {c : ℝ} (hc : 0 < c)
    (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0232.N0719.N0996.d019931 sizes hdim h (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 c omega) =
      c * _root_.GD.N0232.N0719.N0996.d019931 sizes hdim h omega := by
  unfold _root_.GD.N0232.N0719.N0996.d019931
  rw [_root_.GD.N0232.N0719.N0996.d019937]
  simpa only [smul_eq_mul] using
    _root_.GD.N0232.N0720.N1341.d004419 h c hc (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)

theorem d019939 (h : _root_.GD.N0232.N0720.N1341.d004417 d) (mu : ℝ) (sigma : Fin k → ℝ)
    {c : ℝ} (hc : 0 < c) :
    (∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h omega - c * mu) ^ 2)
      ∂_root_.GD.N0232.N0719.d009176 k sizes (c * mu) (fun i => c * sigma i)) =
    ENNReal.ofReal (c ^ 2) *
      ∫⁻ omega, ENNReal.ofReal ((_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h omega - mu) ^ 2)
        ∂_root_.GD.N0232.N0719.d009176 k sizes mu sigma := by
  have hmap := _root_.GD.N0232.N0719.d009188 k sizes 0 c mu sigma
  simp only [zero_add] at hmap
  rw [← hmap, lintegral_map (by fun_prop) (by fun_prop)]
  simp_rw [_root_.GD.N0232.N0719.N0996.d019938 sizes hdim h hc,
    ← mul_sub, mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul _ (by fun_prop)

theorem d019940 (theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k)) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019796 theta.scale ^ 2) * ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)
          (_root_.GD.N0232.N0719.N0988.d019799 theta.location theta.scale theta.scale_pos) h) := by
  let q := _root_.GD.N0232.N0719.N0988.d019799 theta.location theta.scale theta.scale_pos
  have hr := _root_.GD.N0232.N0719.N0996.d019939 sizes hdim h q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)
    (_root_.GD.N0232.N0719.N0988.d019797 theta.scale)
  have hloc : _root_.GD.N0232.N0719.N0988.d019796 theta.scale * q.1 = theta.location :=
    _root_.GD.N0232.N0719.N0988.d019800 _ _ _
  have hscale : (fun i => _root_.GD.N0232.N0719.N0988.d019796 theta.scale * _root_.GD.N0232.N0719.N0997.d019811 q i) = theta.scale := by
    funext i
    exact _root_.GD.N0232.N0719.N0988.d019802 _ _ _ i
  rw [hloc, hscale] at hr
  change _ = ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019796 theta.scale ^ 2) *
    _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0996.d019935 q)
      (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h) at hr
  rw [_root_.GD.N0232.N0719.N0996.d019936] at hr
  exact hr

theorem d019941 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    0 ≤ _root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q h := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0719.N0996.d019933 _ x)


theorem d019942 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hraw : ¬ ∃ f : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ, Measurable f ∧
      (∀ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k),
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h)) ∧
      ∃ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k),
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h)) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)) h := by
  rintro ⟨g, hweak, q, hstrict⟩
  apply hraw
  refine ⟨_root_.GD.N0232.N0719.N0996.d019931 sizes hdim g, _root_.GD.N0232.N0719.N0996.d019932 sizes hdim g, ?_, ?_⟩
  · intro theta
    rw [_root_.GD.N0232.N0719.N0996.d019940, _root_.GD.N0232.N0719.N0996.d019940]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hweak _)) _
  · refine ⟨_root_.GD.N0232.N0719.N0996.d019935 q, ?_⟩
    rw [_root_.GD.N0232.N0719.N0996.d019936, _root_.GD.N0232.N0719.N0996.d019936]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (_root_.GD.N0232.N0719.N0996.d019941 sizes hdim q g)).2 hstrict

theorem d019943 {f g : _root_.GD.N0232.N0719.N0996.d019929 → ℝ}
    (hfg : f =ᵐ[volume] g) (theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k)) :
    f ∘ _root_.GD.N0232.N0719.N0997.d019807 sizes hdim =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
      g ∘ _root_.GD.N0232.N0719.N0997.d019807 sizes hdim := by
  let q := _root_.GD.N0232.N0719.N0988.d019778 k
  have hq : Measure.QuasiMeasurePreserving (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim)
      (_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)) volume := by
    refine ⟨(_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurable, ?_⟩
    rw [_root_.GD.N0232.N0719.N0997.d019814]
    exact withDensity_absolutelyContinuous _ _
  have hac : _root_.GD.N0232.N0719.N0859.d010812 k sizes theta ≪
      _root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q) :=
    _root_.GD.N0232.N0719.d009181 k sizes theta.location q.1 theta.scale
      (_root_.GD.N0232.N0719.N0997.d019811 q) (fun i => (theta.scale_pos i).ne') (fun i => (_root_.GD.N0232.N0719.N0997.d019812 q i).ne')
  exact hac.ae_le (hq.ae_eq_comp hfg)


theorem d019944
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    Integrable (fun x : _root_.GD.N0232.N0719.N0996.d019929 =>
      (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x) := by
  let q := _root_.GD.N0232.N0719.N0988.d019778 k
  let f : _root_.GD.N0232.N0719.N0996.d019929 → ℝ := s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm
  have hint : Integrable (fun omega => s omega ^ 2)
      (_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hs.1.pow_const 2).aestronglyMeasurable (ae_of_all _ fun _ => sq_nonneg _)).mp
    simpa only [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0996.d019935, q, _root_.GD.N0232.N0719.N0988.d019778, sub_zero] using
      ne_top_of_lt (hs.2.2.1 (_root_.GD.N0232.N0719.N0996.d019935 q))
  have hpush : Integrable (fun x => f x ^ 2)
      (volume.withDensity (fun x => ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1316.d004489 d) x))) := by
    rw [← _root_.GD.N0232.N0719.N0988.d019781 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim),
      ← _root_.GD.N0232.N0719.N0997.d019814 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)]
    apply (integrable_map_equiv (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) _).mpr
    simpa only [f, q, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hint
  have hi := (integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0719.N0996.d019934 (_root_.GD.N0232.N0720.N1316.d004489 d)).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hpush
  have hi' : Integrable (fun x : _root_.GD.N0232.N0719.N0996.d019929 =>
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * (f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) := by
    apply hi.congr
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0719.N0996.d019933 _ x), smul_eq_mul,
      _root_.GD.N0232.N0720.N1316.d004490]
    ring
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (_root_.GD.N0232.N0720.N1316.d004446 (_root_.GD.N0232.N0720.N1316.d004489 d)).ne') _).mp hi'

theorem d019945
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    _root_.GD.N0238.N0753.d004397 (s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm) := by
  intro a ha x
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨0, Real.log a⟩
  have hinput : g • ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) = a • ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) := by
    funext i j
    change 0 + Real.exp (Real.log a) * ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x i j) =
      a * ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x i j)
    rw [Real.exp_log ha, zero_add]
  have h := hs.2.1 g ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)
  change s (g • ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) =
    g • s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) at h
  rw [hinput] at h
  simpa only [Function.comp_apply, _root_.GD.N0232.N0719.N0997.d019810,
    _root_.GD.N0232.N0719.N0946.d009229.d009244, g,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log ha,
    zero_add, smul_eq_mul] using h



theorem d019946
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d, _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)) h ∧
      ∀ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k), _root_.GD.N0232.N0719.N0996.d019931 sizes hdim h =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  let f : _root_.GD.N0232.N0719.N0996.d019929 → ℝ := s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm
  have hfm : Measurable f := hs.1.comp (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm.measurable
  have hhom := _root_.GD.N0232.N0719.N0996.d019945 sizes hdim hs
  have hint := _root_.GD.N0232.N0719.N0996.d019944 sizes hdim hs
  let h := _root_.GD.N0232.N0719.N0999.d019926 f hfm hhom hint
  have heq : ∀ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k), _root_.GD.N0232.N0719.N0996.d019931 sizes hdim h =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
    intro theta
    have hh := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim
      (_root_.GD.N0232.N0719.N0999.d019928 f hfm hhom hint) theta
    change (fun omega => _root_.GD.N0232.N0720.N1341.d004418 h (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s
    simpa only [f, h, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hh
  refine ⟨h, ?_, heq⟩
  have hrisk : ∀ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k),
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0996.d019931 sizes hdim h) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta s :=
    fun theta => _root_.GD.N0232.N0719.N0896.d011094 k sizes theta (heq theta)
  apply _root_.GD.N0232.N0719.N0996.d019942
  rintro ⟨e, he, hweak, theta, hstrict⟩
  have hterm := hs.2.2.2 e he (fun q => (hweak q).trans (hrisk q).le) theta
  have heRisk := _root_.GD.N0232.N0719.N0896.d011094 k sizes theta hterm
  rw [heRisk, hrisk theta] at hstrict
  exact lt_irrefl _ hstrict

end
end GD.N0232.N0719.N0996

#print axioms _root_.GD.N0232.N0719.N0996.d019940
#print axioms _root_.GD.N0232.N0719.N0996.d019946
