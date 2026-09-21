import GD.Module1632

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0491
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0896

def d027933 (k : ℕ) (sizes : Fin k → ℕ)
    (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  Measurable s ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) => g • z)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) s ∧
    (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta s ≠ ⊤) ∧
    _root_.GD.N0232.N0719.N0970.d012309 k sizes s

namespace N0777
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0999 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0107
variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)

theorem d027934
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
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
      hs.2.2.1 (_root_.GD.N0232.N0719.N0996.d019935 q)
  have hpush : Integrable (fun x => f x ^ 2)
      (volume.withDensity (fun x => ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1316.d004489 d) x))) := by
    rw [← _root_.GD.N0232.N0719.N0988.d019781 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim),
      ← _root_.GD.N0232.N0719.N0997.d019814 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)]
    apply (integrable_map_equiv (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) _).mpr
    simpa only [f, q, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hint
  have hi := (integrable_withDensity_iff_integrable_smul'
    (show Measurable (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1316.d004489 d)) by unfold _root_.GD.N0232.N0720.N1316.d004445; fun_prop).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hpush
  have hi' : Integrable (fun x : _root_.GD.N0232.N0719.N0996.d019929 =>
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * (f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) := by
    apply hi.congr
    filter_upwards [] with x
    have hdens : 0 ≤ _root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1316.d004489 d) x := by
      unfold _root_.GD.N0232.N0720.N1316.d004445
      exact mul_nonneg (_root_.GD.N0232.N0720.N1316.d004446 _).le (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal hdens, smul_eq_mul,
      _root_.GD.N0232.N0720.N1316.d004490]
    ring
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (_root_.GD.N0232.N0720.N1316.d004446 (_root_.GD.N0232.N0720.N1316.d004489 d)).ne') _).mp hi'

theorem d027935
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
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



theorem d027936
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d, _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)) h ∧
      ∀ theta : _root_.GD.N0232.N0719.N0996.d019930 (k := k), _root_.GD.N0232.N0719.N0996.d019931 sizes hdim h =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  let f : _root_.GD.N0232.N0719.N0996.d019929 → ℝ := s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm
  have hfm : Measurable f := hs.1.comp (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm.measurable
  have hhom := _root_.GD.N0213.N0491.N0777.d027935 sizes hdim hs
  have hint := _root_.GD.N0213.N0491.N0777.d027934 sizes hdim hs
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

end N0777
namespace N0774
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0213.N0476
open _root_.GD.N0213.N0480
open _root_.GD.N0230.N0556
variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)

theorem d027937 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    _root_.GD.N0232.N0719.N0977.d009783 d (s ∘ (_root_.GD.N0213.N0480.d020443 sizes hdim).symm) := by
  intro b a ha z
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
  have hinput : g • (_root_.GD.N0213.N0480.d020443 sizes hdim).symm z =
      _root_.GD.N0232.N0719.N0900.d009095 k sizes b a ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm z) := by
    funext i j
    change b + Real.exp (Real.log a) * _ = b + a * _
    rw [Real.exp_log ha]
  have h := hs.2.1 g ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm z)
  change s (g • (_root_.GD.N0213.N0480.d020443 sizes hdim).symm z) =
    b + Real.exp (Real.log a) * s ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm z) at h
  rw [hinput, Real.exp_log ha] at h
  have hcoord := _root_.GD.N0213.N0480.d020445 sizes hdim b a ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm z)
  rw [MeasurableEquiv.apply_symm_apply] at hcoord
  have hinv := congrArg (_root_.GD.N0213.N0480.d020443 sizes hdim).symm hcoord
  rw [MeasurableEquiv.symm_apply_apply] at hinv
  simpa only [Function.comp_def, ← hinv] using h

theorem d027938 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    Integrable (_root_.GD.N0213.N0476.d020417 (_root_.GD.N0213.N0480.d020446 (d := d))
      (s ∘ (_root_.GD.N0213.N0480.d020443 sizes hdim).symm)) := by
  have h := _root_.GD.N0213.N0491.N0777.d027934 sizes hdim hs
  have hcomp := (PiLp.volume_preserving_toLp (Fin (d + 2))).integrable_comp_of_integrable h
  apply hcomp.congr
  filter_upwards [] with x
  unfold _root_.GD.N0213.N0476.d020417
  simp only [Function.comp_apply]
  congr 1
  rw [_root_.GD.N0232.N0720.N1341.d004426, EuclideanSpace.real_norm_sq_eq]
  unfold _root_.GD.N0232.N0719.N0977.d009777 _root_.GD.N0213.N0480.d020446
  congr 2
  rw [← Finset.mul_sum]
  ring

theorem d027939 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d, ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 h =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  let f := s ∘ (_root_.GD.N0213.N0480.d020443 sizes hdim).symm
  obtain ⟨h, hh⟩ := _root_.GD.N0213.N0476.d020439
    (_root_.GD.N0213.N0480.d020446 (d := d)) f (hs.1.comp (_root_.GD.N0213.N0480.d020443 sizes hdim).symm.measurable)
    (_root_.GD.N0213.N0491.N0774.d027937 sizes hdim hs)
    (_root_.GD.N0213.N0491.N0774.d027938 sizes hdim hs)
  refine ⟨h, ?_⟩
  intro theta
  have htoLp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (d + 2))).quasiMeasurePreserving.ae_eq_comp hh
  have hraw := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim htoLp theta
  filter_upwards [hraw] with omega homega
  change _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h (_root_.GD.N0213.N0480.d020443 sizes hdim omega) =
    s ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm (_root_.GD.N0213.N0480.d020443 sizes hdim omega)) at homega
  simpa only [_root_.GD.N0213.N0480.d020451, Function.comp_apply, MeasurableEquiv.symm_apply_apply] using homega

theorem d027940 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d,
      _root_.GD.N0230.N0556.d000031 (fun v : Fin k → Ioo (0 : ℝ) 1 =>
        _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0213.N0480.d020446 (_root_.GD.N0213.N0480.d020447 sizes hdim v)) h ∧
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 h =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  obtain ⟨h, hh⟩ := _root_.GD.N0213.N0491.N0774.d027939 sizes hdim hs
  refine ⟨h, ?_, hh⟩
  rintro ⟨g, hweak, v, hstrict⟩
  have hreal (w : Fin k → Ioo (0 : ℝ) 1) :
      _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim w) (_root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 g) ≤
        _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim w) (_root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h) := by
    have hr := _root_.GD.N0213.N0476.d020433 _root_.GD.N0213.N0480.d020446
      (_root_.GD.N0213.N0480.d020447 sizes hdim w) g h
    have hw := hweak w
    linarith
  have hrawWeak (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 g) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta s := by
    rw [← _root_.GD.N0232.N0719.N0896.d011094 k sizes theta (hh theta),
      _root_.GD.N0213.N0480.d020462 sizes hdim _root_.GD.N0213.N0480.d020446 g theta,
      _root_.GD.N0213.N0480.d020462 sizes hdim _root_.GD.N0213.N0480.d020446 h theta]
    simp only [_root_.GD.N0213.N0480.d020461]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hreal _) (_root_.GD.N0213.N0480.d020459 sizes hdim _).le)) _
  have heq := hs.2.2.2 (_root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 g)
    (_root_.GD.N0213.N0480.d020452 sizes hdim _root_.GD.N0213.N0480.d020446 g) hrawWeak (_root_.GD.N0213.N0480.d020457 v)
  have hequal := _root_.GD.N0232.N0719.N0896.d011094 k sizes (_root_.GD.N0213.N0480.d020457 v)
    (heq.trans (hh (_root_.GD.N0213.N0480.d020457 v)).symm)
  rw [_root_.GD.N0213.N0480.d020461, _root_.GD.N0213.N0480.d020461] at hequal
  have hnonneg : 0 ≤ _root_.GD.N0213.N0480.d020458 sizes hdim v *
      _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 g) :=
    mul_nonneg (_root_.GD.N0213.N0480.d020459 sizes hdim v).le
      (integral_nonneg (_root_.GD.N0213.N0476.d020418 _ _))
  have hlt : _root_.GD.N0213.N0480.d020458 sizes hdim v *
      _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 g) <
      _root_.GD.N0213.N0480.d020458 sizes hdim v *
      _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h) := by
    apply mul_lt_mul_of_pos_left _ (_root_.GD.N0213.N0480.d020459 sizes hdim v)
    have hr := _root_.GD.N0213.N0476.d020433 _root_.GD.N0213.N0480.d020446
      (_root_.GD.N0213.N0480.d020447 sizes hdim v) g h
    linarith
  have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).mpr hlt
  rw [hequal] at this
  exact lt_irrefl _ this

end N0774
namespace N0775
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0213.N0476
open _root_.GD.N0213.N0481
open _root_.GD.N0213.N0480
open _root_.GD.N0213.N0477
open _root_.GD.N0213.N0479
open _root_.GD.N0213.N0483
open _root_.GD.N0213.N0478
variable {k d : ℕ} [NeZero k] (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)

include hdim in
theorem d027941 (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ pi : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        s =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] fun omega =>
          _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d) (_root_.GD.N0232.N0719.N0986.d020360 sizes omega) (_root_.GD.N0232.N0719.N0986.d020361 sizes omega)
            (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  obtain ⟨h, hadm, heq⟩ := _root_.GD.N0213.N0491.N0774.d027940 sizes hdim hs
  obtain ⟨pi, hpi⟩ := _root_.GD.N0213.N0478.d027924 sizes hdim hn h hadm
  refine ⟨pi, ?_⟩
  let P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop := fun z =>
    (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i) ∧
      _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h z =
        _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
  have hinvariant : ∀ c a, 0 < a → ∀ z, P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z := by
    intro c a ha z
    have hr : (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) i) ↔
        (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i) := by
      simp_rw [_root_.GD.N0213.N0481.d020440 sizes hdim hn c a z]
      exact forall_congr' (fun i => mul_pos_iff_of_pos_left (sq_pos_of_pos ha))
    constructor
    · rintro ⟨hpos, he⟩
      have hz := hr.mp hpos
      refine ⟨hz, ?_⟩
      have hm := _root_.GD.N0213.N0483.d022032 (_root_.GD.N0213.N0477.d020391 d) c a ha.ne'
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) hz (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
      simp_rw [← _root_.GD.N0213.N0478.d027925 sizes hdim hn c a z,
        ← _root_.GD.N0213.N0481.d020440 sizes hdim hn c a z] at hm
      rw [_root_.GD.N0213.N0476.d020413 _root_.GD.N0213.N0480.d020446 h c a ha z, hm] at he
      nlinarith
    · rintro ⟨hpos, he⟩
      refine ⟨hr.mpr hpos, ?_⟩
      have hm := _root_.GD.N0213.N0483.d022032 (_root_.GD.N0213.N0477.d020391 d) c a ha.ne'
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) hpos (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
      simp_rw [← _root_.GD.N0213.N0478.d027925 sizes hdim hn c a z,
        ← _root_.GD.N0213.N0481.d020440 sizes hdim hn c a z] at hm
      rw [_root_.GD.N0213.N0476.d020413 _root_.GD.N0213.N0480.d020446 h c a ha z, hm, he]
  have hraw : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z := by
    apply _root_.GD.N0213.N0479.d009790 P hinvariant
    filter_upwards [hpi, _root_.GD.N0213.N0481.d020442 sizes hdim hn] with u hu hr
    exact ⟨hr, by simpa only [_root_.GD.N0213.N0476.d020414] using hu⟩
  have hcoordinate : _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h =ᵐ[volume] fun z =>
      _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d) (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
    filter_upwards [hraw] with z hz
    exact hz.2
  intro theta
  have htoLp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (d + 2))).quasiMeasurePreserving.ae_eq_comp hcoordinate
  have hphysical := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim htoLp theta
  apply (heq theta).symm.trans
  filter_upwards [hphysical] with omega homega
  have hcoord : _root_.GD.N0213.N0477.d020379 sizes hdim
      ((MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) = omega :=
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm_apply_apply omega
  change _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h
    ((MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) = _
  simpa only [Function.comp_apply, hcoord] using homega

end N0775
namespace N0776
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0991
open _root_.GD.N0232.N0720.N1341 (d004418)
open _root_.GD.N0213.N0500
open _root_.GD.N0213.N0496
open _root_.GD.N0213.N0501
open _root_.GD.N0156.N0444
variable {k d : ℕ}

theorem d027942
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1) (hn : ∀ i, 0 < sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0213.N0496.d022000 k)
      (a : ∀ j, Option (Fin (ell j)) → ℝ)
      (ν : ℕ → ProbabilityMeasure (_root_.GD.N0213.N0496.d022000 k)),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i l, 0 < (_root_.GD.N0232.N0719.N0983.d009710 l (p j i).2 : ℝ)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) x)
          atTop (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  obtain ⟨h, ha, heq⟩ := _root_.GD.N0213.N0491.N0777.d027936 sizes hdim hs
  obtain ⟨ell, p, a, ν, han, has, hν, hpi, hlim⟩ :=
    _root_.GD.N0213.N0500.d027916 sizes hdim hn h ha
  have heqv : _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[volume] s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm := by
    apply _root_.GD.N0213.N0500.d027915 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [Filter.EventuallyEq, _root_.GD.N0232.N0719.N0996.d019931,
      Function.comp_def, MeasurableEquiv.symm_apply_apply,
      _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0996.d019935] using
      heq (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  refine ⟨ell, p, a, ν, han, has, hν, hpi, ?_⟩
  filter_upwards [hlim, heqv] with x hx he
  simpa only [he, Function.comp_apply] using hx

theorem d027943 [NeZero k]
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 0 < sizes i) (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      (∀ c : ℝ, (∀ i, (_root_.GD.N0213.N0496.d022003 sizes hdim x).1 i ≤ c) →
        s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) ≤ c) ∧
      (∀ c : ℝ, (∀ i, c ≤ (_root_.GD.N0213.N0496.d022003 sizes hdim x).1 i) →
        c ≤ s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) := by
  have hf : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := ⟨hs.1, fun θ => hs.2.2.1 θ⟩
  have he : ∀ c : ℝ, ∀ z, s (fun i j => c + z i j) = c + s z := by
    intro c z
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨c, 0⟩
    have h := hs.2.1 g z
    change s (fun i j => c + Real.exp 0 * z i j) = c + Real.exp 0 * s z at h
    simpa only [Real.exp_zero, one_mul] using h
  have hraw := _root_.GD.N0156.N0444.d020673 sizes hn s hf he hs.2.2.2
    (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  have hvol : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      _root_.GD.N0156.N0444.d020667 sizes s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) := by
    apply _root_.GD.N0213.N0500.d027915 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0996.d019935] using hraw
  filter_upwards [hvol] with x hx
  constructor
  · intro c hc
    apply hx.2.trans
    apply Finset.sup'_le
    intro i _
    exact hc i
  · intro c hc
    apply le_trans _ hx.1
    apply Finset.le_inf'
    intro i _
    exact hc i

theorem d027944 [NeZero k]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hdim : (∑ i, sizes i) = d + 1)
    (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ∃ ν : ℕ → ProbabilityMeasure (_root_.GD.N0213.N0496.d022000 k),
      (∀ beta : ℝ, 0 < beta → beta < 1 / 2 → ∃ B : ℝ, ∀ j,
        Integrable (fun p : _root_.GD.N0213.N0496.d022000 k => Real.exp (beta * p.1 ^ 2))
          (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) ∧
        (∫ p, Real.exp (beta * p.1 ^ 2) ∂(ν j : Measure (_root_.GD.N0213.N0496.d022000 k))) ≤ B) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
        (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim
          (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) x) atTop
        (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  have hd : 1 ≤ d := by
    have hsum : sizes (0 : Fin k) ≤ ∑ i, sizes i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ _)
    have hsize := hn (0 : Fin k)
    omega
  obtain ⟨ell, p, weight, ν, hw, hprob, hν, _hinterior, hlim⟩ :=
    _root_.GD.N0213.N0491.N0776.d027942
      sizes hdim hn0 hs
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (weight j) (_root_.GD.N0213.N0496.d022003 sizes hdim x)) atTop
      (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x))) := by
    simpa only [hν, _root_.GD.N0213.N0501.d027921 sizes hdim _ _ (hw _)] using hlim
  have hbounds := _root_.GD.N0213.N0491.N0776.d027943 sizes hdim hn0 s hs
  refine ⟨ν, ?_, hlim⟩
  intro beta hbeta hhalf
  obtain ⟨B, hB⟩ := _root_.GD.N0213.N0496.d021999 sizes hdim hn hd p weight hw hprob
    (fun x => s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) hlim'
    (hbounds.mono fun _ hx => hx.1) (hbounds.mono fun _ hx => hx.2) hbeta.le hhalf
  refine ⟨B, fun j => ?_⟩
  constructor
  · rw [hν]
    exact _root_.GD.N0213.N0501.d027919 (p j) (weight j) _
  · rw [hν, _root_.GD.N0213.N0501.d027920 (p j) (weight j) (hw j)]
    exact hB j

end N0776
end
end GD.N0213.N0491

#print axioms _root_.GD.N0213.N0491.N0777.d027934
#print axioms _root_.GD.N0213.N0491.N0777.d027936
#print axioms _root_.GD.N0213.N0491.N0774.d027939
#print axioms _root_.GD.N0213.N0491.N0774.d027940
#print axioms _root_.GD.N0213.N0491.N0775.d027941
#print axioms _root_.GD.N0213.N0491.N0776.d027942
#print axioms _root_.GD.N0213.N0491.N0776.d027943
#print axioms _root_.GD.N0213.N0491.N0776.d027944
