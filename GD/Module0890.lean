import GD.Module0889
import Mathlib.Analysis.Convex.Function










open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1337

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1312
open _root_.GD.N0232.N0720.N1266 (d013712 d013726 d013727)

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn in
theorem d013809 : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013679 m n) :=
  _root_.GD.N0232.N0720.N1434.d013564 hm hn
    (by norm_num) (by norm_num)

def d013810 : Measure _root_.GD.N0232.N0720.N1266.d013712 := (_root_.GD.N0232.N0720.N1441.d013679 m n).map _root_.GD.N0232.N0720.N1266.d013726

include hm hn in
theorem d013811 : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1337.d013810 m n) := by
  letI := _root_.GD.N0232.N0720.N1337.d013809 m n hm hn
  exact Measure.isProbabilityMeasure_map _root_.GD.N0232.N0720.N1266.d013727.aemeasurable

theorem d013812 :
    MeasurePreserving _root_.GD.N0232.N0720.N1266.d013726 (_root_.GD.N0232.N0720.N1441.d013679 m n) (_root_.GD.N0232.N0720.N1337.d013810 m n) :=
  ⟨_root_.GD.N0232.N0720.N1266.d013727, rfl⟩



def d013813 (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) →L[ℝ] Lp ℝ p (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  letI := _root_.GD.N0232.N0720.N1337.d013811 m n hm hn
  exact (Lp.compMeasurePreservingₗᵢ ℝ _root_.GD.N0232.N0720.N1266.d013726 (_root_.GD.N0232.N0720.N1337.d013812 m n)).toContinuousLinearMap.comp
    (ContinuousMap.toLp p (_root_.GD.N0232.N0720.N1337.d013810 m n) ℝ)

theorem d013814 (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) :
    _root_.GD.N0232.N0720.N1337.d013813 m n hm hn p a =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦ a (_root_.GD.N0232.N0720.N1266.d013726 x) := by
  letI := _root_.GD.N0232.N0720.N1337.d013811 m n hm hn
  have hcomp := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp p (_root_.GD.N0232.N0720.N1337.d013810 m n) ℝ a)
    (_root_.GD.N0232.N0720.N1337.d013812 m n)
  have hvalue := ae_of_ae_map _root_.GD.N0232.N0720.N1266.d013727.aemeasurable
    (ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1337.d013810 m n) a)
  exact hcomp.trans hvalue

def d013815 (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) : _root_.GD.N0232.N0720.N1441.d013681 m n →L[ℝ] _root_.GD.N0232.N0720.N1441.d013681 m n :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1441.d013679 m n) ∞ 2 2 (_root_.GD.N0232.N0720.N1337.d013813 m n hm hn ∞ a)

theorem d013816 (a : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ)) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1337.d013815 m n hm hn a h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦ a (_root_.GD.N0232.N0720.N1266.d013726 x) * h x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (_root_.GD.N0232.N0720.N1337.d013813 m n hm hn ∞ a) h,
    _root_.GD.N0232.N0720.N1337.d013814 m n hm hn ∞ a] with x hx ha
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (_root_.GD.N0232.N0720.N1337.d013813 m n hm hn ∞ a) h) x = _
  simpa only [ContinuousLinearMap.mul_apply', ha] using hx

@[fun_prop] theorem d013817 :
    Continuous (fun p : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) × _root_.GD.N0232.N0720.N1441.d013681 m n ↦ _root_.GD.N0232.N0720.N1337.d013815 m n hm hn p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1337.d013815
  fun_prop

def d013818 : _root_.GD.N0232.N0720.N1441.d013681 m n := _root_.GD.N0232.N0720.N1337.d013813 m n hm hn 2 (ContinuousMap.const _root_.GD.N0232.N0720.N1266.d013712 1)

theorem d013819 : _root_.GD.N0232.N0720.N1337.d013818 m n hm hn =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun _ ↦ (1 : ℝ) :=
  _root_.GD.N0232.N0720.N1337.d013814 m n hm hn 2 (ContinuousMap.const _root_.GD.N0232.N0720.N1266.d013712 1)

def d013820 (t : _root_.GD.N0232.N0720.N1441.d013676) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun p := Real.sqrt (_root_.GD.N0232.N0720.N1312.d013797 m n t p)
  continuous_toFun := (_root_.GD.N0232.N0720.N1312.d013800 m n hm hn t).continuous.sqrt

@[fun_prop] theorem d013821 : Continuous (_root_.GD.N0232.N0720.N1337.d013820 m n hm hn) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (_root_.GD.N0232.N0720.N1312.d013799 m n hm hn).sqrt

def d013822 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : _root_.GD.N0232.N0720.N1441.d013681 m n :=
  h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1337.d013818 m n hm hn

theorem d013823 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1337.d013822 m n hm hn t h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦ h x - _root_.GD.N0232.N0720.N1441.d013680 t := by
  unfold _root_.GD.N0232.N0720.N1337.d013822
  filter_upwards [Lp.coeFn_sub h (_root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1337.d013818 m n hm hn),
    Lp.coeFn_smul (_root_.GD.N0232.N0720.N1441.d013680 t) (_root_.GD.N0232.N0720.N1337.d013818 m n hm hn), _root_.GD.N0232.N0720.N1337.d013819 m n hm hn] with x hsub hmul hone
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hone, mul_one] using hsub.trans
    (congrArg (fun a : ℝ ↦ h x - a) hmul)

def d013824 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : _root_.GD.N0232.N0720.N1441.d013681 m n :=
  _root_.GD.N0232.N0720.N1337.d013815 m n hm hn (_root_.GD.N0232.N0720.N1337.d013820 m n hm hn t) (_root_.GD.N0232.N0720.N1337.d013822 m n hm hn t h)

theorem d013825 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1337.d013824 m n hm hn t h =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
      Real.sqrt (_root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x)) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) := by
  unfold _root_.GD.N0232.N0720.N1337.d013824
  filter_upwards [_root_.GD.N0232.N0720.N1337.d013816 m n hm hn (_root_.GD.N0232.N0720.N1337.d013820 m n hm hn t) (_root_.GD.N0232.N0720.N1337.d013822 m n hm hn t h),
    _root_.GD.N0232.N0720.N1337.d013823 m n hm hn t h] with x hx he
  simpa only [_root_.GD.N0232.N0720.N1337.d013820, ContinuousMap.coe_mk, he] using hx

def d013826 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : ℝ := ‖_root_.GD.N0232.N0720.N1337.d013824 m n hm hn t h‖ ^ 2

@[fun_prop] theorem d013827 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1441.d013681 m n ↦ _root_.GD.N0232.N0720.N1337.d013826 m n hm hn p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1337.d013826 _root_.GD.N0232.N0720.N1337.d013824 _root_.GD.N0232.N0720.N1337.d013822 _root_.GD.N0232.N0720.N1441.d013680
  have htarget : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1441.d013681 m n ↦
      p.1.1 - (1 / 2 : ℝ)) := by fun_prop
  exact ((_root_.GD.N0232.N0720.N1337.d013817 m n hm hn).comp
    (((_root_.GD.N0232.N0720.N1337.d013821 m n hm hn).comp continuous_fst).prodMk
      (continuous_snd.sub (htarget.smul continuous_const)))).norm.pow 2

theorem d013828 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : 0 ≤ _root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h :=
  sq_nonneg _

theorem d013829 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h = ∫ x, _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2
      ∂_root_.GD.N0232.N0720.N1441.d013679 m n := by
  rw [_root_.GD.N0232.N0720.N1337.d013826, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1337.d013825 m n hm hn t h] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn t (_root_.GD.N0232.N0720.N1266.d013726 x)).le]

include hm hn in
theorem d013830 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) * (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2)
      (_root_.GD.N0232.N0720.N1441.d013679 m n) := by
  apply (Lp.memLp (_root_.GD.N0232.N0720.N1337.d013824 m n hm hn t h)).integrable_sq.congr
  filter_upwards [_root_.GD.N0232.N0720.N1337.d013825 m n hm hn t h] with x hx
  rw [hx, mul_pow, Real.sq_sqrt (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn t (_root_.GD.N0232.N0720.N1266.d013726 x)).le]

include hm hn in
theorem d013831 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    Integrable (fun x ↦ (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2) (_root_.GD.N0232.N0720.N1441.d013678 m n t) := by
  rw [_root_.GD.N0232.N0720.N1312.d013806 m n hm hn,
    integrable_withDensity_iff_integrable_smul' (_root_.GD.N0232.N0720.N1312.d013805 m n hm hn t).ennreal_ofReal (by simp)]
  simpa only [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn t _).le, smul_eq_mul] using
    _root_.GD.N0232.N0720.N1337.d013830 m n hm hn t h

theorem d013832 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h = ∫ x, (h x - _root_.GD.N0232.N0720.N1441.d013680 t) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t := by
  rw [_root_.GD.N0232.N0720.N1312.d013807 m n hm hn, _root_.GD.N0232.N0720.N1337.d013829 m n hm hn]


theorem d013833 (t : _root_.GD.N0232.N0720.N1441.d013676) (h : _root_.GD.N0232.N0720.N1441.d013681 m n) :
    _root_.GD.N0232.N0720.N1441.d013689 m n t h = ENNReal.ofReal (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h) := by
  rw [_root_.GD.N0232.N0720.N1337.d013832 m n hm hn]
  exact (ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0232.N0720.N1337.d013831 m n hm hn t h)
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (h x - _root_.GD.N0232.N0720.N1441.d013680 t)))).symm

theorem d013834 (t : _root_.GD.N0232.N0720.N1441.d013676) : ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn t) := by
  have hnorm : ConvexOn ℝ univ (fun h : _root_.GD.N0232.N0720.N1441.d013681 m n ↦ ‖h‖ ^ 2) :=
    convexOn_univ_norm.pow (fun h _ ↦ norm_nonneg h) 2
  let op := _root_.GD.N0232.N0720.N1337.d013815 m n hm hn (_root_.GD.N0232.N0720.N1337.d013820 m n hm hn t)
  let shift : _root_.GD.N0232.N0720.N1441.d013681 m n →ᵃ[ℝ] _root_.GD.N0232.N0720.N1441.d013681 m n :=
    { toFun := fun h ↦ op (h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1337.d013818 m n hm hn)
      linear := op.toLinearMap
      map_vadd' := by
        intro h v
        change op (v + h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1337.d013818 m n hm hn) =
          op v + op (h - _root_.GD.N0232.N0720.N1441.d013680 t • _root_.GD.N0232.N0720.N1337.d013818 m n hm hn)
        rw [add_sub_assoc, map_add] }
  simpa only [Set.preimage_univ, Function.comp_def, shift, _root_.GD.N0232.N0720.N1337.d013826, _root_.GD.N0232.N0720.N1337.d013824,
    _root_.GD.N0232.N0720.N1337.d013822, op] using! hnorm.comp_affineMap shift

theorem d013835 (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : _root_.GD.N0232.N0720.N1337.d013824 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 h = h := by
  apply Lp.ext
  filter_upwards [_root_.GD.N0232.N0720.N1337.d013825 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 h] with x hx
  simpa only [_root_.GD.N0232.N0720.N1312.d013808 m n hm hn, Real.sqrt_one, _root_.GD.N0232.N0720.N1441.d013684,
    sub_zero, one_mul] using hx

theorem d013836 (h : _root_.GD.N0232.N0720.N1441.d013681 m n) : _root_.GD.N0232.N0720.N1337.d013826 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 h = ‖h‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1337.d013826, _root_.GD.N0232.N0720.N1337.d013835 m n hm hn]

end
end GD.N0232.N0720.N1337

#print axioms _root_.GD.N0232.N0720.N1337.d013827
#print axioms _root_.GD.N0232.N0720.N1337.d013833
#print axioms _root_.GD.N0232.N0720.N1337.d013834
#print axioms _root_.GD.N0232.N0720.N1337.d013836
