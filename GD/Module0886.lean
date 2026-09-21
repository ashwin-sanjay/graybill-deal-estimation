import GD.Module0885
import Mathlib.Analysis.Convex.Function










open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1272

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1266

instance d013735 : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013679 2 2) :=
  _root_.GD.N0232.N0720.N1434.d013564 (by omega : 2 ≤ 2) (by omega : 2 ≤ 2)
    (by norm_num) (by norm_num)

def d013736 : Measure _root_.GD.N0232.N0720.N1266.d013712 := (_root_.GD.N0232.N0720.N1441.d013679 2 2).map _root_.GD.N0232.N0720.N1266.d013726

instance d013737 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1272.d013736 :=
  Measure.isProbabilityMeasure_map _root_.GD.N0232.N0720.N1266.d013727.aemeasurable

theorem d013738 :
    MeasurePreserving _root_.GD.N0232.N0720.N1266.d013726 (_root_.GD.N0232.N0720.N1441.d013679 2 2) _root_.GD.N0232.N0720.N1272.d013736 :=
  ⟨_root_.GD.N0232.N0720.N1266.d013727, rfl⟩



def d013739 (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) →L[ℝ] Lp ℝ p (_root_.GD.N0232.N0720.N1441.d013679 2 2) :=
  (Lp.compMeasurePreservingₗᵢ ℝ _root_.GD.N0232.N0720.N1266.d013726 _root_.GD.N0232.N0720.N1272.d013738).toContinuousLinearMap.comp
    (ContinuousMap.toLp p _root_.GD.N0232.N0720.N1272.d013736 ℝ)

theorem d013740 (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) :
    _root_.GD.N0232.N0720.N1272.d013739 p a =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦ a (_root_.GD.N0232.N0720.N1266.d013726 x) := by
  have hcomp := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp p _root_.GD.N0232.N0720.N1272.d013736 ℝ a)
    _root_.GD.N0232.N0720.N1272.d013738
  have hvalue := ae_of_ae_map _root_.GD.N0232.N0720.N1266.d013727.aemeasurable
    (ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1272.d013736 a)
  exact hcomp.trans hvalue

def d013741 (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) : _root_.GD.N0232.N0720.N1441.d013681 2 2 →L[ℝ] _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1441.d013679 2 2) ∞ 2 2 (_root_.GD.N0232.N0720.N1272.d013739 ∞ a)

theorem d013742 (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1272.d013741 a h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦ a (_root_.GD.N0232.N0720.N1266.d013726 x) * h x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (_root_.GD.N0232.N0720.N1272.d013739 ∞ a) h,
    _root_.GD.N0232.N0720.N1272.d013740 ∞ a] with x hx ha
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (_root_.GD.N0232.N0720.N1272.d013739 ∞ a) h) x = _
  simpa only [ContinuousLinearMap.mul_apply', ha] using hx

@[fun_prop] theorem d013743 :
    Continuous (fun p : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) × _root_.GD.N0232.N0720.N1441.d013681 2 2 ↦ _root_.GD.N0232.N0720.N1272.d013741 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1272.d013741
  fun_prop

def d013744 : _root_.GD.N0232.N0720.N1441.d013681 2 2 := _root_.GD.N0232.N0720.N1272.d013739 2 (ContinuousMap.const _root_.GD.N0232.N0720.N1266.d013712 1)

theorem d013745 : _root_.GD.N0232.N0720.N1272.d013744 =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun _ ↦ (1 : ℝ) :=
  _root_.GD.N0232.N0720.N1272.d013740 2 (ContinuousMap.const _root_.GD.N0232.N0720.N1266.d013712 1)

def d013746 (t : _root_.GD.N0232.N0720.N1441.d013676) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun p := Real.sqrt (_root_.GD.N0232.N0720.N1266.d013718 t p)
  continuous_toFun := (_root_.GD.N0232.N0720.N1266.d013721 t).continuous.sqrt

@[fun_prop] theorem d013747 : Continuous _root_.GD.N0232.N0720.N1272.d013746 := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0720.N1266.d013720.sqrt

def d013748 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
  h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1272.d013744

theorem d013749 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1272.d013748 t h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦ h x - _root_.GD.N0232.N0720.N1441.d013680 t := by
  unfold _root_.GD.N0232.N0720.N1272.d013748
  filter_upwards [Lp.coeFn_sub h (_root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1272.d013744),
    Lp.coeFn_smul (_root_.GD.N0232.N0720.N1441.d013680 t) _root_.GD.N0232.N0720.N1272.d013744, _root_.GD.N0232.N0720.N1272.d013745] with x hsub hmul hone
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hone, mul_one] using hsub.trans
    (congrArg (fun a : ℝ ↦ h x - a) hmul)

def d013750 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
  _root_.GD.N0232.N0720.N1272.d013741 (_root_.GD.N0232.N0720.N1272.d013746 t) (_root_.GD.N0232.N0720.N1272.d013748 t h)

theorem d013751 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1272.d013750 t h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] fun x ↦
      Real.sqrt (_root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x)) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) := by
  unfold _root_.GD.N0232.N0720.N1272.d013750
  filter_upwards [_root_.GD.N0232.N0720.N1272.d013742 (_root_.GD.N0232.N0720.N1272.d013746 t) (_root_.GD.N0232.N0720.N1272.d013748 t h),
    _root_.GD.N0232.N0720.N1272.d013749 t h] with x hx he
  simpa only [_root_.GD.N0232.N0720.N1272.d013746, ContinuousMap.coe_mk, he] using hx

def d013752 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : ℝ := ‖_root_.GD.N0232.N0720.N1272.d013750 t h‖ ^ 2

@[fun_prop] theorem d013753 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1441.d013681 2 2 ↦ _root_.GD.N0232.N0720.N1272.d013752 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1272.d013750 _root_.GD.N0232.N0720.N1272.d013748 _root_.GD.N0232.N0720.N1441.d013680
  have htarget : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1441.d013681 2 2 ↦
      p.1.1 - (1 / 2 : ℝ)) := by fun_prop
  exact (_root_.GD.N0232.N0720.N1272.d013743.comp
    ((_root_.GD.N0232.N0720.N1272.d013747.comp continuous_fst).prodMk
      (continuous_snd.sub (htarget.smul continuous_const)))).norm.pow 2

theorem d013754 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : 0 ≤ _root_.GD.N0232.N0720.N1272.d013752 t h :=
  sq_nonneg _

theorem d013755 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1272.d013752 t h = ∫ x, _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2
      ∂_root_.GD.N0232.N0720.N1441.d013679 2 2 := by
  rw [_root_.GD.N0232.N0720.N1272.d013752, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1272.d013751 t h] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (_root_.GD.N0232.N0720.N1266.d013719 t (_root_.GD.N0232.N0720.N1266.d013726 x)).le]

theorem d013756 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2)
      (_root_.GD.N0232.N0720.N1441.d013679 2 2) := by
  apply (Lp.memLp (_root_.GD.N0232.N0720.N1272.d013750 t h)).integrable_sq.congr
  filter_upwards [_root_.GD.N0232.N0720.N1272.d013751 t h] with x hx
  rw [hx, mul_pow, Real.sq_sqrt (_root_.GD.N0232.N0720.N1266.d013719 t (_root_.GD.N0232.N0720.N1266.d013726 x)).le]

theorem d013757 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    Integrable (fun x ↦ (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2) (_root_.GD.N0232.N0720.N1441.d013678 2 2 t) := by
  rw [_root_.GD.N0232.N0720.N1266.d013733,
    integrable_withDensity_iff_integrable_smul' (_root_.GD.N0232.N0720.N1266.d013732 t).ennreal_ofReal (by simp)]
  simpa only [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1266.d013719 t _).le, smul_eq_mul] using
    _root_.GD.N0232.N0720.N1272.d013756 t h

theorem d013758 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1272.d013752 t h = ∫ x, (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t := by
  rw [_root_.GD.N0232.N0720.N1266.d013734, _root_.GD.N0232.N0720.N1272.d013755]


theorem d013759 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) :
    _root_.GD.N0232.N0720.N1441.d013689 2 2 t h = ENNReal.ofReal (_root_.GD.N0232.N0720.N1272.d013752 t h) := by
  rw [_root_.GD.N0232.N0720.N1272.d013758]
  exact (ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0232.N0720.N1272.d013757 t h)
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (h x - _root_.GD.N0232.N0720.N1441.d013680 t)))).symm

theorem d013760 (t : _root_.GD.N0232.N0720.N1441.d013676) : ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1272.d013752 t) := by
  have hnorm : ConvexOn ℝ univ (fun h : _root_.GD.N0232.N0720.N1441.d013681 2 2 ↦ ‖h‖ ^ 2) :=
    convexOn_univ_norm.pow (fun h _ ↦ norm_nonneg h) 2
  let op := _root_.GD.N0232.N0720.N1272.d013741 (_root_.GD.N0232.N0720.N1272.d013746 t)
  let shift : _root_.GD.N0232.N0720.N1441.d013681 2 2 →ᵃ[ℝ] _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
    { toFun := fun h ↦ op (h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1272.d013744)
      linear := op.toLinearMap
      map_vadd' := by
        intro h v
        change op (v + h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1272.d013744) =
          op v + op (h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1272.d013744)
        rw [add_sub_assoc, map_add] }
  simpa only [Set.preimage_univ, Function.comp_def, shift, _root_.GD.N0232.N0720.N1272.d013752, _root_.GD.N0232.N0720.N1272.d013750,
    _root_.GD.N0232.N0720.N1272.d013748, op] using! hnorm.comp_affineMap shift

theorem d013761 (p : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1266.d013718 _root_.GD.N0232.N0720.N1441.d013677 p = 1 := by
  have hp := (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1266.d013716 _root_.GD.N0232.N0720.N1441.d013677 p)
    (-(5 / 2 : ℝ))).ne'
  simp only [_root_.GD.N0232.N0720.N1266.d013718, _root_.GD.N0232.N0720.N1441.d013677, _root_.GD.N0232.N0720.N1271.d013403]
  norm_num
  exact hp

theorem d013762 (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : _root_.GD.N0232.N0720.N1272.d013750 _root_.GD.N0232.N0720.N1441.d013677 h = h := by
  apply Lp.ext
  filter_upwards [_root_.GD.N0232.N0720.N1272.d013751 _root_.GD.N0232.N0720.N1441.d013677 h] with x hx
  simpa only [_root_.GD.N0232.N0720.N1272.d013761, Real.sqrt_one, _root_.GD.N0232.N0720.N1441.d013684,
    sub_zero, one_mul] using hx

theorem d013763 (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) : _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1441.d013677 h = ‖h‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1272.d013752, _root_.GD.N0232.N0720.N1272.d013762]

end
end GD.N0232.N0720.N1272

#print axioms _root_.GD.N0232.N0720.N1272.d013753
#print axioms _root_.GD.N0232.N0720.N1272.d013759
#print axioms _root_.GD.N0232.N0720.N1272.d013760
#print axioms _root_.GD.N0232.N0720.N1272.d013763
