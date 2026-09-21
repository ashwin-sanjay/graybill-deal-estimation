import GD.Module1265
import GD.Module1228

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0480

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0996 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0213.N0476
open _root_.GD.N0230.N0556

variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)

def d020443 : _root_.GD.N0232.N0719.N0997.d019804 sizes ≃ᵐ _root_.GD.N0232.N0719.N0977.d009764 d :=
  (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).trans (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm

theorem d020444 :
    MeasurePreserving (_root_.GD.N0213.N0480.d020443 sizes hdim) volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 2))).comp
    (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim)

theorem d020445 (b a : ℝ) (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0213.N0480.d020443 sizes hdim (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a omega) =
      _root_.GD.N0232.N0719.N0977.d009774 d b a (_root_.GD.N0213.N0480.d020443 sizes hdim omega) := by
  apply (_root_.GD.N0213.N0480.d020443 sizes hdim).symm.injective
  rw [MeasurableEquiv.symm_apply_apply]
  funext i j
  have h := congrFun (congrFun ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm_apply_apply omega) i) j
  change _root_.GD.N0213.N0480.d020443 sizes hdim omega (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩) = omega i j at h
  change b + a * omega i j = b + a * _root_.GD.N0213.N0480.d020443 sizes hdim omega (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩)
  rw [h]

def d020446 : _root_.GD.N0232.N0719.N0976.d019733 d := ⟨fun _ => 2, by intro i; norm_num⟩

def d020447 (v : Fin k → Ioo (0 : ℝ) 1) : _root_.GD.N0232.N0719.N0976.d019733 d :=
  ⟨fun j => ((v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)).1)⁻¹,
    fun j => inv_pos.mpr (v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)).2.1⟩

@[fun_prop] theorem d020448 :
    Continuous (_root_.GD.N0213.N0480.d020447 sizes hdim) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_apply (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)).subtype_val).inv₀
    (fun v => (v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)).2.1.ne')

def d020449 : Fin k → Ioo (0 : ℝ) 1 :=
  fun _ => ⟨1 / 2, by norm_num⟩

@[simp] theorem d020450 :
    _root_.GD.N0213.N0480.d020447 sizes hdim _root_.GD.N0213.N0480.d020449 = _root_.GD.N0213.N0480.d020446 := by
  apply Subtype.ext
  funext i
  norm_num [_root_.GD.N0213.N0480.d020447, _root_.GD.N0213.N0480.d020449, _root_.GD.N0213.N0480.d020446]

def d020451 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ :=
  _root_.GD.N0213.N0476.d020410 ref h ∘ _root_.GD.N0213.N0480.d020443 sizes hdim

@[fun_prop] theorem d020452 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Measurable (_root_.GD.N0213.N0480.d020451 sizes hdim ref h) :=
  (_root_.GD.N0213.N0476.d020411 ref h).comp (_root_.GD.N0213.N0480.d020443 sizes hdim).measurable

theorem d020453 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (b a : ℝ) (ha : 0 < a) (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0213.N0480.d020451 sizes hdim ref h (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a omega) =
      b + a * _root_.GD.N0213.N0480.d020451 sizes hdim ref h omega := by
  simp only [_root_.GD.N0213.N0480.d020451, Function.comp_apply]
  rw [_root_.GD.N0213.N0480.d020445]
  exact _root_.GD.N0213.N0476.d020413 ref h b a ha _

theorem d020454 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
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

theorem d020455 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    Integrable (_root_.GD.N0213.N0476.d020417 (_root_.GD.N0213.N0480.d020446 (d := d))
      (s ∘ (_root_.GD.N0213.N0480.d020443 sizes hdim).symm)) := by
  have h := _root_.GD.N0232.N0719.N0996.d019944 sizes hdim hs
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

theorem d020456 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d, ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 h =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  let f := s ∘ (_root_.GD.N0213.N0480.d020443 sizes hdim).symm
  obtain ⟨h, hh⟩ := _root_.GD.N0213.N0476.d020439
    (_root_.GD.N0213.N0480.d020446 (d := d)) f (hs.1.comp (_root_.GD.N0213.N0480.d020443 sizes hdim).symm.measurable)
    (_root_.GD.N0213.N0480.d020454 sizes hdim hs)
    (_root_.GD.N0213.N0480.d020455 sizes hdim hs)
  refine ⟨h, ?_⟩
  intro theta
  have htoLp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (d + 2))).quasiMeasurePreserving.ae_eq_comp hh
  have hraw := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim htoLp theta
  filter_upwards [hraw] with omega homega
  change _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h (_root_.GD.N0213.N0480.d020443 sizes hdim omega) =
    s ((_root_.GD.N0213.N0480.d020443 sizes hdim).symm (_root_.GD.N0213.N0480.d020443 sizes hdim omega)) at homega
  simpa only [_root_.GD.N0213.N0480.d020451, Function.comp_apply, MeasurableEquiv.symm_apply_apply] using homega

def d020457 (v : Fin k → Ioo (0 : ℝ) 1) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0996.d019935 (0, v)

def d020458 (v : Fin k → Ioo (0 : ℝ) 1) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (0, v))

theorem d020459 (v : Fin k → Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0213.N0480.d020458 sizes hdim v := _root_.GD.N0232.N0720.N1316.d004446 _

theorem d020460 (v : Fin k → Ioo (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (Fin (d + 2))) :
    _root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (0, v)) x =
      _root_.GD.N0213.N0480.d020458 sizes hdim v *
        Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0213.N0480.d020447 sizes hdim v).1
          ((MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm x)) := by
  unfold _root_.GD.N0232.N0720.N1316.d004445 _root_.GD.N0213.N0480.d020458
  congr 1
  congr 1
  unfold _root_.GD.N0232.N0719.N0977.d009777
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [_root_.GD.N0232.N0719.N0988.d019779, _root_.GD.N0213.N0480.d020447]
  field_simp [(v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim i)).2.1.ne']
  ring

theorem d020461 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (v : Fin k → Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0213.N0480.d020457 v)
      (_root_.GD.N0213.N0480.d020451 sizes hdim ref h) =
      ENNReal.ofReal (_root_.GD.N0213.N0480.d020458 sizes hdim v *
        _root_.GD.N0213.N0476.d020430 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 ref h)) := by
  let e := MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)
  let F : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := _root_.GD.N0213.N0476.d020410 ref h ∘ e.symm
  have hF : Measurable F := (_root_.GD.N0213.N0476.d020411 ref h).comp e.symm.measurable
  have hweight := _root_.GD.N0213.N0476.d020423 ref (_root_.GD.N0213.N0480.d020447 sizes hdim v) h
  have hcomp : Integrable (fun x : EuclideanSpace ℝ (Fin (d + 2)) =>
      _root_.GD.N0213.N0476.d020417 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 ref h) (e.symm x)) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 2))).integrable_comp_of_integrable hweight
  change (∫⁻ omega, ENNReal.ofReal ((F (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega) - 0) ^ 2)
    ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0997.d019811 (0, v))) = _
  rw [_root_.GD.N0232.N0719.N0997.d019815 sizes hdim (0, v) F hF]
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold _root_.GD.N0232.N0720.N1316.d004445; fun_prop) (((hF.sub measurable_const).pow_const 2).ennreal_ofReal)]
  have hpoint (x : EuclideanSpace ℝ (Fin (d + 2))) :
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (0, v)) x) *
        ENNReal.ofReal ((F x - 0) ^ 2) =
      ENNReal.ofReal (_root_.GD.N0213.N0480.d020458 sizes hdim v *
        _root_.GD.N0213.N0476.d020417 (_root_.GD.N0213.N0480.d020447 sizes hdim v) (_root_.GD.N0213.N0476.d020410 ref h) (e.symm x)) := by
    rw [_root_.GD.N0213.N0480.d020460]
    rw [← ENNReal.ofReal_mul (mul_nonneg (_root_.GD.N0213.N0480.d020459 sizes hdim v).le (Real.exp_pos _).le)]
    congr 1
    dsimp [F, _root_.GD.N0213.N0476.d020417, e]
    ring
  simp only [Pi.mul_apply]
  simp_rw [hpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcomp.const_mul _)
    (ae_of_all _ fun x => mul_nonneg (_root_.GD.N0213.N0480.d020459 sizes hdim v).le
      (_root_.GD.N0213.N0476.d020418 _ _ _)), integral_const_mul]
  congr 1
  congr 1
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 2))).integral_comp
    e.symm.measurableEmbedding _

theorem d020462 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0213.N0480.d020451 sizes hdim ref h) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019796 theta.scale ^ 2) *
        _root_.GD.N0232.N0719.N0859.d010840 k sizes
          (_root_.GD.N0213.N0480.d020457 (_root_.GD.N0232.N0719.N0988.d019799 0 theta.scale theta.scale_pos).2)
          (_root_.GD.N0213.N0480.d020451 sizes hdim ref h) := by
  let q := _root_.GD.N0232.N0719.N0988.d019799 0 theta.scale theta.scale_pos
  let c := _root_.GD.N0232.N0719.N0988.d019796 theta.scale
  have hc : 0 < c := _root_.GD.N0232.N0719.N0988.d019797 theta.scale
  have hscale : (fun i => c * _root_.GD.N0232.N0719.N0997.d019811 (0, q.2) i) = theta.scale := by
    funext i
    exact _root_.GD.N0232.N0719.N0988.d019802 0 theta.scale theta.scale_pos i
  have hmap := _root_.GD.N0232.N0719.d009188 k sizes theta.location c 0 (_root_.GD.N0232.N0719.N0997.d019811 (0, q.2))
  simp only [mul_zero, add_zero, hscale] at hmap
  change (∫⁻ omega, ENNReal.ofReal
    ((_root_.GD.N0213.N0480.d020451 sizes hdim ref h omega - theta.location) ^ 2)
    ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale) = _
  rw [← hmap, lintegral_map
    ((((_root_.GD.N0213.N0480.d020452 sizes hdim ref h).sub measurable_const).pow_const 2).ennreal_ofReal)
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes theta.location c)]
  simp_rw [_root_.GD.N0213.N0480.d020453 sizes hdim ref h theta.location c hc]
  have hsq (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
      (theta.location + c * _root_.GD.N0213.N0480.d020451 sizes hdim ref h omega - theta.location) ^ 2 =
        c ^ 2 * (_root_.GD.N0213.N0480.d020451 sizes hdim ref h omega - 0) ^ 2 := by ring
  simp_rw [hsq, ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul _ (by fun_prop)

theorem d020463 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d,
      _root_.GD.N0230.N0556.d000031 (fun v : Fin k → Ioo (0 : ℝ) 1 =>
        _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0213.N0480.d020446 (_root_.GD.N0213.N0480.d020447 sizes hdim v)) h ∧
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0213.N0480.d020451 sizes hdim _root_.GD.N0213.N0480.d020446 h =ᵐ[
          _root_.GD.N0232.N0719.N0859.d010812 k sizes theta] s := by
  obtain ⟨h, hh⟩ := _root_.GD.N0213.N0480.d020456 sizes hdim hs
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

end
end GD.N0213.N0480

#print axioms _root_.GD.N0213.N0480.d020456
#print axioms _root_.GD.N0213.N0480.d020461
#print axioms _root_.GD.N0213.N0480.d020462
#print axioms _root_.GD.N0213.N0480.d020463
