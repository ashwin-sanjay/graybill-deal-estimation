import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import GD.Module0659
import Mathlib.MeasureTheory.Integral.Prod
import GD.Module0663
import GD.Module0811
import GD.Module1224
import GD.Module0708
import Mathlib.Probability.Independence.Integration
import GD.Module0705









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0938
noncomputable section

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]

def d007527 (e B : ℝ) : ℝ := (1 + e * B)⁻¹ ^ 2

def d007528 (e B q : ℝ) : ℝ := e * q ^ 2 / (1 + e * B) ^ 2


theorem d007529 {e B q : ℝ}
    (he : 0 ≤ e) (hq : 0 ≤ q) (hqB : q ≤ B) :
    _root_.GD.N0232.N0719.N0938.d007528 e B q ≤ q / 4 := by
  have hB : 0 ≤ B := hq.trans hqB
  have hd : 0 < (1 + e * B) ^ 2 := sq_pos_of_pos (by positivity)
  rw [_root_.GD.N0232.N0719.N0938.d007528, div_le_iff₀ hd]
  have hden : (1 + e * q) ^ 2 ≤ (1 + e * B) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    gcongr
  have hsq := sq_nonneg (1 - e * q)
  have hmul := mul_le_mul_of_nonneg_left hden hq
  nlinarith


def d007530 (e : ℝ) (q : I → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, q i) + ∑ i, _root_.GD.N0232.N0719.N0938.d007528 e (∑ j, q j) (q i)

theorem d007531 {e : ℝ} (he : 0 ≤ e) (q : I → ℝ) : 0 ≤ _root_.GD.N0232.N0719.N0938.d007530 e q := by
  unfold _root_.GD.N0232.N0719.N0938.d007530 _root_.GD.N0232.N0719.N0938.d007527 _root_.GD.N0232.N0719.N0938.d007528
  positivity

theorem d007532 {e : ℝ} (he : 0 ≤ e)
    (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) :
    _root_.GD.N0232.N0719.N0938.d007530 e q ≤ 1 + (∑ i, q i) / 4 := by
  have hB : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => hq i
  have hret : _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, q i) ≤ 1 := by
    unfold _root_.GD.N0232.N0719.N0938.d007527
    have hden : 1 ≤ 1 + e * ∑ i, q i := le_add_of_nonneg_right (mul_nonneg he hB)
    have hi : 0 ≤ (1 + e * ∑ i, q i)⁻¹ := by positivity
    have hi1 : (1 + e * ∑ i, q i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
    nlinarith
  calc
    _root_.GD.N0232.N0719.N0938.d007530 e q ≤ 1 + ∑ i, q i / 4 := add_le_add hret (Finset.sum_le_sum fun i _ =>
      _root_.GD.N0232.N0719.N0938.d007529 he (hq i)
        (Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)))
    _ = _ := by rw [Finset.sum_div]

theorem d007533 (q : I → ℝ) (e : ℕ → ℝ)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007530 (e n) q) atTop (𝓝 1) := by
  have hd : Tendsto (fun n => 1 + e n * ∑ i, q i) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (he0.mul_const (∑ i, q i))
  have hr : Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007527 (e n) (∑ i, q i)) atTop (𝓝 1) := by
    simpa [_root_.GD.N0232.N0719.N0938.d007527] using (hd.inv₀ one_ne_zero).pow 2
  have hi (i : I) : Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ j, q j) (q i))
      atTop (𝓝 0) := by
    have h := (he0.mul_const (q i ^ 2)).div (hd.pow 2) (by norm_num)
    convert h using 1
    · rfl
    · norm_num
  simpa [_root_.GD.N0232.N0719.N0938.d007530] using hr.add (tendsto_finsetSum Finset.univ fun i _ => hi i)



theorem d007534 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → Ω → ℝ) (hqm : ∀ i, Measurable (q i))
    (hq : ∀ᵐ x ∂μ, ∀ i, 0 ≤ q i x) (hqi : ∀ i, Integrable (q i) μ)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, _root_.GD.N0232.N0719.N0938.d007530 (e n) (fun i => q i x) ∂μ) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => ∫ x, _root_.GD.N0232.N0719.N0938.d007530 (e n) (fun i => q i x) ∂μ)
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 1 + (∑ i, q i x) / 4)
    · intro n
      have hm : Measurable (fun x => ∑ i, q i x) := Finset.measurable_sum _ fun i _ => hqm i
      unfold _root_.GD.N0232.N0719.N0938.d007530 _root_.GD.N0232.N0719.N0938.d007527 _root_.GD.N0232.N0719.N0938.d007528
      fun_prop
    · exact (integrable_const 1).add ((integrable_finsetSum _ fun i _ => hqi i).div_const 4)
    · intro n
      filter_upwards [hq] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0719.N0938.d007531 (he n) _)]
      exact _root_.GD.N0232.N0719.N0938.d007532 (he n) _ hx
    · exact ae_of_all _ fun x => _root_.GD.N0232.N0719.N0938.d007533 (fun i => q i x) e he0
  simpa using hlim

end
end GD.N0232.N0719.N0938

#print axioms _root_.GD.N0232.N0719.N0938.d007529
#print axioms _root_.GD.N0232.N0719.N0938.d007532
#print axioms _root_.GD.N0232.N0719.N0938.d007534








set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GD.N0232.N0719.N0876
noncomputable section
theorem d020682
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x⁻¹) (gammaMeasure a r) := by
  have ha0 : 0 < a := by linarith
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x⁻¹)
    (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hkernel :
      IntegrableOn
        (fun x : ℝ ↦
          (r ^ a / Real.Gamma a) *
            (x ^ (a - 2) * Real.exp (-(r * x))))
        (Set.Ioi 0) := by
    have hbase :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a - 2) (b := r)
        (by linarith) (by norm_num) hr
    have hbase' :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (a - 2) * Real.exp (-(r * x)))
          (Set.Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using hbase
    exact hbase'.const_mul _
  have hkernelActual :
      IntegrableOn
        (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹)
        (Set.Ioi 0) := by
    apply hkernel.congr_fun
    · intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
        rw [← Real.rpow_neg_one x]
        calc
          x ^ (a - 1) * x ^ (-1 : ℝ) =
              x ^ ((a - 1) + (-1 : ℝ)) :=
                (Real.rpow_add hxpos (a - 1) (-1 : ℝ)).symm
          _ = x ^ (a - 2) := by ring_nf
      symm
      calc
        gammaPDFReal a r x * x⁻¹ =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x⁻¹) * Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a - 2) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    · exact measurableSet_Ioi
  have hdensity :
      Integrable (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹) := by
    apply hkernelActual.integrable_of_forall_notMem_eq_zero
    intro x hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]
  apply hdensity.congr'
  · fun_prop
  filter_upwards with x
  have hpdf : 0 ≤ gammaPDFReal a r x :=
    gammaPDFReal_nonneg ha0 hr x
  simp only [smul_eq_mul,
    ENNReal.toReal_ofReal hpdf]


end
end GD.N0232.N0719.N0876

#print axioms _root_.GD.N0232.N0719.N0876.d020682









set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace GD.N0232.N0719.N0880
noncomputable section
open _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0972



theorem d020683 {I : Type*} [Fintype I]
    (v : I → ℝ≥0) (p : I → ℝ) :
    (∫ y, _root_.GD.N0232.N0719.N0885.d009311 p y ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 0 v) =
      ∑ i, p i ^ 2 * (v i : ℝ) := by
  have hc : cov[_root_.GD.N0232.N0719.N0885.d009311 p, _root_.GD.N0232.N0719.N0885.d009311 p; _root_.GD.N0232.N0719.N0980.d009697 0 v] =
      ∑ i, p i ^ 2 * (v i : ℝ) := by
    change cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => ∑ i, p i * y i; _] = _
    rw [covariance_fun_sum_right]
    · simp_rw [covariance_const_mul_right, _root_.GD.N0232.N0719.N0885.d009319]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · exact fun i => (_root_.GD.N0232.N0719.N0885.d009315 0 v i).memLp_two.const_mul (p i)
    · exact (_root_.GD.N0232.N0719.N0885.d009318 0 v p).memLp_two
  rw [covariance_self (_root_.GD.N0232.N0719.N0885.d009318 0 v p).aemeasurable,
    variance_eq_integral (_root_.GD.N0232.N0719.N0885.d009318 0 v p).aemeasurable,
    _root_.GD.N0232.N0719.N0980.d009700] at hc
  simpa using hc

def d020684 {k : ℕ} (v : Fin k → ℝ≥0) (t : Fin k → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i ^ 2 * (v i : ℝ)

theorem d020685 {k : ℕ} (v : Fin k → ℝ≥0) (t : Fin k → ℝ) :
    (∫ y, _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k (y, t)) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 0 v) =
      _root_.GD.N0232.N0719.N0880.d020684 v t := by
  exact _root_.GD.N0232.N0719.N0880.d020683 v (fun i => _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i)



theorem d020686
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (hm : theta.location = 0) :
    _root_.GD.N0232.N0719.N0972.d012340 k sizes theta =
      ∫ t, _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes theta.scale) t
        ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes theta.scale := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 theta.scale) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes theta.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn theta.scale
  let F : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ := fun s => _root_.GD.N0232.N0719.N0900.d009110 s ^ 2
  have hF : Measurable F := _root_.GD.N0232.N0719.N0900.d009121.pow_const 2
  have hraw := _root_.GD.N0232.N0719.N0933.d009310
    k sizes hn 0 theta.scale F hF
  have hfull : Integrable (fun z => F (_root_.GD.N0232.N0719.N0933.d009305 k z))
      ((_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 theta.scale).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes theta.scale)) := by
    simpa [F] using (_root_.GD.N0232.N0719.N0910.d010292 hk sizes hn 0 theta.scale).integrable_sq
  unfold _root_.GD.N0232.N0719.N0972.d012340 _root_.GD.N0232.N0719.N0859.d010812
  rw [hm]
  simp only [sub_zero]
  change (∫ x, F (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) ∂_root_.GD.N0232.N0719.d009176 k sizes 0 theta.scale) = _
  rw [hraw, integral_prod_symm _ hfull]
  apply integral_congr_ae
  filter_upwards with t
  rw [_root_.GD.N0232.N0719.N0933.d009302 k sizes hn]
  exact _root_.GD.N0232.N0719.N0880.d020685 (_root_.GD.N0232.N0719.N0885.d009329 sizes theta.scale) t

end
end GD.N0232.N0719.N0880

#print axioms _root_.GD.N0232.N0719.N0880.d020683
#print axioms _root_.GD.N0232.N0719.N0880.d020686











set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace GD.N0232.N0719.N0941
noncomputable section
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0844 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0974

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)

def d020687 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  (∑ i, (sizes i : ℝ) / theta.scale i ^ 2)⁻¹ / _root_.GD.N0232.N0719.N0972.d012340 k sizes theta

include hk hn



theorem d020688
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) :
    ∀ theta, _root_.GD.N0232.N0719.N0941.d020687 k sizes theta ≤ c := by
  obtain ⟨e, hem, heq, heb⟩ := _root_.GD.N0232.N0719.N0843.d012245
    k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) hk hn c hc f hf hb
  have he : ∀ b : ℝ, ∀ x, e (fun i j => b + x i j) = b + e x := by
    intro b x
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, 0⟩
    have h := heq g x
    have h' : e (_root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x) = b + e x := by
      simpa [g, _root_.GD.N0232.N0719.N0946.d009258,
        _root_.GD.N0232.N0719.N0946.d009229.d009244,
        _root_.GD.N0232.N0719.N0946.d009229.d009239,
        _root_.GD.N0232.N0719.N0946.d009229.shift] using h
    have hfun : _root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x = (fun i j => b + x i j) := by
      funext i j
      change b + 1 * x i j = b + x i j
      ring
    rw [hfun] at h'
    exact h'
  intro theta
  have hpos := _root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn theta
  have hr := _root_.GD.N0232.N0719.N0974.d019823 sizes theta e hem
    (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) (mul_nonneg hc hpos.le) (heb theta)
  have ho := _root_.GD.N0232.N0719.N0974.d019819 sizes (by omega)
    (fun i => by have := hn i; omega) theta e hem he hr.1
  exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using ho.trans hr.2)



theorem d020689
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1))
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) : 1 ≤ c := by
  exact le_of_tendsto hsat (Eventually.of_forall fun n =>
    _root_.GD.N0232.N0719.N0941.d020688 k sizes hk hn f hf c hc hb (theta n))



theorem d020690
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1)) :
    _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn = 1 := by
  obtain ⟨e, _, heD, hvD, _, hv1⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 k sizes hk hn
  let M := _root_.GD.N0232.N0719.N0844.d012247 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) e
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top (by simp) hv1
  have hcap : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
      ENNReal.ofReal (M.toReal * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
    intro theta
    apply (_root_.GD.N0232.N0719.N0844.d012250 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) (by omega)
      (fun i => by have := hn i; omega)
      M.toReal ENNReal.toReal_nonneg theta e).mp
    rw [ENNReal.ofReal_toReal hM]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0844.d012246 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) theta e) theta
  have hge := _root_.GD.N0232.N0719.N0941.d020689 k sizes hk hn theta hsat e heD.1
    M.toReal ENNReal.toReal_nonneg hcap
  have hreal : M.toReal = 1 := le_antisymm
    (by simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hv1) hge
  have hone : M = 1 := by rw [← ENNReal.ofReal_toReal hM, hreal]; norm_num
  exact hvD.symm.trans hone

theorem d020691
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1)) :
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = 0 ∧
      _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = 0 := by
  obtain ⟨_, _, _, hD, hE, _, _⟩ := _root_.GD.N0232.N0719.N0973.d012380 k sizes hk hn
  rw [_root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn theta hsat] at hD hE
  simpa using And.intro hD hE



theorem d020692
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1))
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) :
    _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn f = 0 := by
  let gamma := _root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn
  let r := _root_.GD.N0232.N0719.N0844.d012246 k sizes gamma
  have hfinite : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
    refine ⟨hf, fun theta => ?_⟩
    apply ne_top_of_le_ne_top _ (hb theta)
    rw [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn]
    exact ENNReal.ofReal_ne_top
  have hpoint (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : r theta f ≤ 1 := by
    have h := hb theta
    rw [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn] at h
    simpa only [ENNReal.ofReal_one, r] using
      (_root_.GD.N0232.N0719.N0844.d012250 k sizes gamma
      (by omega) (fun i => by have := hn i; omega)
      1 (by norm_num) theta f).mpr (by simpa [gamma, _root_.GD.N0232.N0719.N0972.d012343] using h)
  have hle : _root_.GD.N0230.N0611.d003516 r f ≤ 1 := iSup_le hpoint
  have hge : 1 ≤ _root_.GD.N0230.N0611.d003516 r f := by
    rw [← _root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn theta hsat]
    exact _root_.GD.N0230.N0611.d003520 r hfinite
  have heq : _root_.GD.N0230.N0611.d003516 r f = 1 := le_antisymm hle hge
  haveI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩
  have h := _root_.GD.N0230.N0686.d003548 r f
    (ne_top_of_le_ne_top (by simp) hle)
  rw [heq] at h
  simpa [_root_.GD.N0232.N0719.N0973.d012375, r, gamma] using h

end
end GD.N0232.N0719.N0941

#print axioms _root_.GD.N0232.N0719.N0941.d020688
#print axioms _root_.GD.N0232.N0719.N0941.d020689
#print axioms _root_.GD.N0232.N0719.N0941.d020690
#print axioms _root_.GD.N0232.N0719.N0941.d020691
#print axioms _root_.GD.N0232.N0719.N0941.d020692









set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace GD.N0232.N0719.N0877
noncomputable section
open _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0876 _root_.GD.N0232.N0719.N0910
open _root_.GD.N0232.N0719.N0924 (d010432)

variable {k : ℕ}

def d020693 (h : Fin k) (a : Fin k → ℝ) (i : Fin k) : ℝ :=
  if i = h then 0 else a h / a i



theorem d020694 {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (gammaMeasure a r) := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  have h2 : MemLp (fun x : ℝ => x) 2 (gammaMeasure a r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (_root_.GD.N0232.N0719.N0924.d010432 ha hr)
  exact h2.integrable (by norm_num)



theorem d020695
    (shape rate : Fin k → ℝ) (hs : ∀ i, 0 < shape i) (hr : ∀ i, 0 < rate i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 1 < shape i) (i : Fin k) :
    Integrable (fun a => _root_.GD.N0232.N0719.N0877.d020693 h a i)
      (Measure.pi fun j => gammaMeasure (shape j) (rate j)) := by
  let μ := fun j => gammaMeasure (shape j) (rate j)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hr j)
  by_cases hi : i = h
  · simp only [_root_.GD.N0232.N0719.N0877.d020693, if_pos hi]
    exact integrable_const 0
  · have hret : Integrable (fun a : Fin k → ℝ => a h) (Measure.pi μ) :=
      (measurePreserving_eval μ h).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0877.d020694 (hs h) (hr h))
    have hinv : Integrable (fun a : Fin k → ℝ => (a i)⁻¹) (Measure.pi μ) :=
      (measurePreserving_eval μ i).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0876.d020682 (hother i hi) (hr i))
    have hind : IndepFun (fun a : Fin k → ℝ => a h) (fun a => (a i)⁻¹) (Measure.pi μ) := by
      have hb : IndepFun (fun a : Fin k → ℝ => a h) (fun a => a i) (Measure.pi μ) :=
        (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun (Ne.symm hi)
      exact hb.comp measurable_id measurable_inv
    have hp := hind.integrable_mul hret hinv
    change Integrable (fun a => a h * (a i)⁻¹) (Measure.pi μ) at hp
    simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hi, div_eq_mul_inv, μ] using hp

theorem d020696
    (shape rate : Fin k → ℝ) (hs : ∀ i, 0 < shape i) (hr : ∀ i, 0 < rate i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 1 < shape i)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a)
      ∂(Measure.pi fun j => gammaMeasure (shape j) (rate j))) atTop (𝓝 1) := by
  let μ := fun j => gammaMeasure (shape j) (rate j)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hr j)
  apply _root_.GD.N0232.N0719.N0938.d007534 (Measure.pi μ) (fun i a => _root_.GD.N0232.N0719.N0877.d020693 h a i)
  · intro i
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs <;> fun_prop
  · have hpos : ∀ᵐ a ∂Measure.pi μ, ∀ i, 0 < a i := _root_.GD.N0232.N0719.N0910.d010287 hs hr
    filter_upwards [hpos] with a ha
    intro i
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha i)).le
  · exact _root_.GD.N0232.N0719.N0877.d020695 shape rate hs hr h hother
  · exact he
  · exact he0


theorem d020697
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a)
      ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
        (((sizes j - 1 : ℕ) : ℝ) / 2))) atTop (𝓝 1) := by
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  apply _root_.GD.N0232.N0719.N0877.d020696 _ _ hs hs h _ e he he0
  intro i hi
  have hnat : 2 < sizes i - 1 := by have := hother i hi; omega
  have hreal : (2 : ℝ) < (sizes i - 1 : ℕ) := by exact_mod_cast hnat
  linarith

end
end GD.N0232.N0719.N0877

#print axioms _root_.GD.N0232.N0719.N0877.d020695
#print axioms _root_.GD.N0232.N0719.N0877.d020696
#print axioms _root_.GD.N0232.N0719.N0877.d020697









set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace GD.N0232.N0719.N0939
noncomputable section
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0880 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0938
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973 _root_.GD.N0232.N0719.N0941
open _root_.GD.N0232.N0719.N0885

variable {k : ℕ}

def d020698 (h : Fin k) (e : ℝ) (i : Fin k) : ℝ := if i = h then e else 1

def d020699 (sizes : Fin k → ℕ) (h : Fin k) (e : ℝ) (i : Fin k) : ℝ :=
  Real.sqrt (sizes i) * Real.sqrt (_root_.GD.N0232.N0719.N0939.d020698 h e i)

def d020700 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (e : ℝ) (he : 0 < e) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := _root_.GD.N0232.N0719.N0939.d020699 sizes h e
  scale_pos i := by
    have hn0 : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
    have hv : 0 < _root_.GD.N0232.N0719.N0939.d020698 h e i := by unfold _root_.GD.N0232.N0719.N0939.d020698; split_ifs <;> positivity
    exact mul_pos (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hv)

def d020701 (h : Fin k) (e : ℝ) (a : Fin k → ℝ) : Fin k → ℝ :=
  fun i => _root_.GD.N0232.N0719.N0939.d020698 h e i * a i

def d020702 (h : Fin k) (e : ℝ) (a : Fin k → ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  _root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), _root_.GD.N0232.N0719.N0939.d020701 h e a)

theorem d020703 (h : Fin k) {e : ℝ} (he : 0 < e) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0939.d020698 h e i := by unfold _root_.GD.N0232.N0719.N0939.d020698; split_ifs <;> positivity

theorem d020704 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) (i : Fin k) :
    _root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 / (sizes i : ℝ) = _root_.GD.N0232.N0719.N0939.d020698 h e i := by
  have hn0 : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
  unfold _root_.GD.N0232.N0719.N0939.d020699
  rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt (_root_.GD.N0232.N0719.N0939.d020703 h he i).le]
  field_simp [hn0.ne']



theorem d020705 (h : Fin k) {e : ℝ} (he : 0 < e)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i =
      ((if i = h then 1 else 0) + e * _root_.GD.N0232.N0719.N0877.d020693 h a i) /
        (1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j) := by
  let s := _root_.GD.N0232.N0719.N0939.d020702 h e a
  have ht (j : Fin k) : 0 < s.meanVariance j := mul_pos (_root_.GD.N0232.N0719.N0939.d020703 h he j) (ha j)
  have hP : 0 < _root_.GD.N0232.N0719.N0900.d009107 s := _root_.GD.N0232.N0719.N0915.d010392 h s ht
  have hsingle (j : Fin k) : _root_.GD.N0232.N0719.N0900.d009106 s j * (e * a h) =
      (if j = h then 1 else 0) + e * _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (ht j)]
    by_cases hj : j = h
    · subst j
      simp only [s, _root_.GD.N0232.N0719.N0939.d020702, _root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0877.d020693,
        if_true, mul_zero, add_zero]
      exact inv_mul_cancel₀ (mul_ne_zero he.ne' (ha h).ne')
    · simp [s, _root_.GD.N0232.N0719.N0939.d020702, _root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0877.d020693, hj, div_eq_mul_inv]
      ring
  have htotal : _root_.GD.N0232.N0719.N0900.d009107 s * (e * a h) = 1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    change (∑ j, _root_.GD.N0232.N0719.N0900.d009106 s j) * (e * a h) = _
    rw [Finset.sum_mul]
    simp_rw [hsingle]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hq (j : Fin k) : 0 ≤ _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha j)).le
  have hden : 0 < 1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    have hsum : 0 ≤ ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := Finset.sum_nonneg fun j _ => hq j
    positivity
  rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg hP.ne']
  apply (div_eq_div_iff hP.ne' hden.ne').mpr
  rw [← htotal, ← hsingle i]
  ring



theorem d020706 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e))
      (_root_.GD.N0232.N0719.N0939.d020701 h e a) = e * _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a) := by
  let R := ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j
  have hq (j : Fin k) : 0 ≤ _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha j)).le
  have hden : 1 + e * R ≠ 0 := ne_of_gt (by
    have hsum : 0 ≤ R := Finset.sum_nonneg fun j _ => hq j
    positivity)
  have hi (i : Fin k) :
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i ^ 2 *
        (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e) i : ℝ) =
      e * ((if i = h then _root_.GD.N0232.N0719.N0938.d007527 e R else 0) +
        _root_.GD.N0232.N0719.N0938.d007528 e R (_root_.GD.N0232.N0719.N0877.d020693 h a i)) := by
    rw [_root_.GD.N0232.N0719.N0939.d020705 h he a ha i]
    change ((_ + e * _root_.GD.N0232.N0719.N0877.d020693 h a i) / (1 + e * R)) ^ 2 *
      (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 / (sizes i : ℝ)) = _
    rw [_root_.GD.N0232.N0719.N0939.d020704 sizes hn h he i]
    by_cases hih : i = h
    · subst i
      simp [_root_.GD.N0232.N0719.N0877.d020693, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0938.d007527, _root_.GD.N0232.N0719.N0938.d007528, div_eq_mul_inv]
      ring
    · simp only [if_neg hih, zero_add, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0938.d007527, _root_.GD.N0232.N0719.N0938.d007528]
      field_simp [hden]
  unfold _root_.GD.N0232.N0719.N0880.d020684
  change (∑ i, _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i ^ 2 * _) = _
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp [_root_.GD.N0232.N0719.N0938.d007530, R]




theorem d020707
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0939.d020701 h e)
      (Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
        (((sizes j - 1 : ℕ) : ℝ) / 2))
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) := by
  let μ := fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
    (((sizes j - 1 : ℕ) : ℝ) / 2)
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hs j)
  have hfun : _root_.GD.N0232.N0719.N0939.d020701 h e = fun a i =>
      _root_.GD.N0232.N0719.N0933.d009287 (sizes i) (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i) (a i) := by
    funext a i
    simp only [_root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0933.d009287, _root_.GD.N0232.N0719.N0939.d020704 sizes hn h he]
  refine ⟨by unfold _root_.GD.N0232.N0719.N0939.d020701; fun_prop, ?_⟩
  rw [hfun, Measure.pi_map_pi]
  · rfl
  · intro i
    exact (_root_.GD.N0232.N0719.N0933.d009294 (sizes i) (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i)).aemeasurable



theorem d020708
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    _root_.GD.N0232.N0719.N0972.d012340 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he) = e *
      ∫ a, _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a)
        ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
          (((sizes j - 1 : ℕ) : ℝ) / 2)) := by
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  have hpos := _root_.GD.N0232.N0719.N0910.d010287 hs hs
  have hmp := _root_.GD.N0232.N0719.N0939.d020707 sizes hn h he
  have hm : Measurable (_root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e))) := by
    unfold _root_.GD.N0232.N0719.N0880.d020684
    apply Finset.measurable_sum
    intro i _
    exact (((_root_.GD.N0232.N0719.N0900.d009119 i).comp ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
      (measurable_const.prodMk measurable_id))).pow_const 2).mul_const _
  rw [_root_.GD.N0232.N0719.N0880.d020686 sizes (Fin.pos h) hn _ rfl]
  change (∫ t, _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) t
    ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) = _
  rw [← hmp.map_eq, integral_map_of_stronglyMeasurable hmp.measurable hm.stronglyMeasurable]
  calc
    _ = ∫ a, e * _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a)
        ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
          (((sizes j - 1 : ℕ) : ℝ) / 2)) := by
      apply integral_congr_ae
      filter_upwards [hpos] with a ha
      exact _root_.GD.N0232.N0719.N0939.d020706 sizes hn h he a ha
    _ = _ := integral_const_mul _ _

theorem d020709
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) / e n)
      atTop (𝓝 1) := by
  have hlim := _root_.GD.N0232.N0719.N0877.d020697 sizes hn h hother e (fun n => (he n).le) he0
  convert hlim using 1
  funext n
  rw [_root_.GD.N0232.N0719.N0939.d020708 sizes hn h (he n)]
  field_simp [(he n).ne']

theorem d020710
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2)⁻¹ =
      e / (1 + ((k : ℝ) - 1) * e) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Fin.pos h)
  have hden : 1 + ((k : ℝ) - 1) * e ≠ 0 := by positivity
  have hprec : (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2) =
      e⁻¹ + ((k : ℝ) - 1) := by
    have hi (i : Fin k) : (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2 =
        1 + if i = h then e⁻¹ - 1 else 0 := by
      change (sizes i : ℝ) / _root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 = _
      rw [← inv_div, _root_.GD.N0232.N0719.N0939.d020704 sizes hn h he i]
      unfold _root_.GD.N0232.N0719.N0939.d020698
      split_ifs <;> simp
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hprec]
  field_simp [he.ne', hden]

theorem d020711
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))
      atTop (𝓝 1) := by
  have hb := _root_.GD.N0232.N0719.N0939.d020709 sizes hn h hother e he he0
  have ho : Tendsto (fun n =>
      (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)).scale i ^ 2)⁻¹ / e n)
      atTop (𝓝 1) := by
    have hx : Tendsto (fun n => (1 + ((k : ℝ) - 1) * e n)⁻¹) atTop (𝓝 1) := by
      have hd : Tendsto (fun n => 1 + ((k : ℝ) - 1) * e n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (he0.const_mul ((k : ℝ) - 1))
      simpa using hd.inv₀ one_ne_zero
    convert hx using 1
    funext n
    rw [_root_.GD.N0232.N0719.N0939.d020710 sizes hn h (he n), div_right_comm, div_self (he n).ne', one_div]
  have hlim := ho.div hb one_ne_zero
  convert hlim using 1
  · funext n
    exact (div_div_div_cancel_right₀ (he n).ne' _ _).symm
  · norm_num



theorem d020712
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn = 1 ∧
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = 0 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsat := _root_.GD.N0232.N0719.N0939.d020711 sizes hn h hother e he he0
  exact ⟨_root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn _ hsat,
    _root_.GD.N0232.N0719.N0941.d020691 k sizes hk hn _ hsat⟩




theorem d020713
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) :
    _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn f = 0 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact _root_.GD.N0232.N0719.N0941.d020692 k sizes hk hn _
    (_root_.GD.N0232.N0719.N0939.d020711 sizes hn h hother e he he0) f hf hb




theorem d020714
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hpositive : 0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes)) :
    ∃ i j : Fin k, i ≠ j ∧ sizes i < 4 ∧ sizes j < 4 := by
  classical
  by_contra hpair
  have hret : ∃ h : Fin k, ∀ i, i ≠ h → 4 ≤ sizes i := by
    by_cases hs : ∃ h, sizes h < 4
    · obtain ⟨h, hh⟩ := hs
      refine ⟨h, fun i hi => ?_⟩
      by_contra hi4
      exact hpair ⟨h, i, Ne.symm hi, hh, by omega⟩
    · refine ⟨⟨0, by omega⟩, fun i _ => ?_⟩
      exact le_of_not_gt (fun hi => hs ⟨i, hi⟩)
  obtain ⟨h, hh⟩ := hret
  rw [(_root_.GD.N0232.N0719.N0939.d020712 sizes hk hn h hh).2.1] at hpositive
  exact (lt_irrefl 0) hpositive

theorem d020715
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hpositive : 0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes)) :
    ∃ i j : Fin k, i ≠ j ∧ (sizes i = 2 ∨ sizes i = 3) ∧
      (sizes j = 2 ∨ sizes j = 3) := by
  obtain ⟨i, j, hij, hi, hj⟩ := _root_.GD.N0232.N0719.N0939.d020714 sizes hk hn hpositive
  exact ⟨i, j, hij, by have := hn i; omega, by have := hn j; omega⟩




def d020716 : Fin 3 → ℕ := ![2, 4, 4]

theorem d020717 : ∀ i, 2 ≤ _root_.GD.N0232.N0719.N0939.d020716 i := by
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0939.d020716]

theorem d020718 :
    _root_.GD.N0232.N0719.N0973.d012377 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 = 1 ∧
    _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717
      (_root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0939.d020716) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717
      (_root_.GD.N0232.N0719.N0962.d012191 3 _root_.GD.N0232.N0719.N0939.d020716) = 0 := by
  apply _root_.GD.N0232.N0719.N0939.d020712 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 0
  intro i hi
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0939.d020716] at *

end
end GD.N0232.N0719.N0939

#print axioms _root_.GD.N0232.N0719.N0939.d020705
#print axioms _root_.GD.N0232.N0719.N0939.d020706

#print axioms _root_.GD.N0232.N0719.N0939.d020708
#print axioms _root_.GD.N0232.N0719.N0939.d020709
#print axioms _root_.GD.N0232.N0719.N0939.d020711
#print axioms _root_.GD.N0232.N0719.N0939.d020712

#print axioms _root_.GD.N0232.N0719.N0939.d020713

#print axioms _root_.GD.N0232.N0719.N0939.d020714
#print axioms _root_.GD.N0232.N0719.N0939.d020715

#print axioms _root_.GD.N0232.N0719.N0939.d020718









set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace GD.N0232.N0719.N1014
noncomputable section
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0973 _root_.GD.N0232.N0719.N0939


theorem d020719
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hn) = 0 := by
  exact _root_.GD.N0232.N0719.N0939.d020713 sizes hk hn h hother
    (_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hn)
    (_root_.GD.N0232.N0719.N0859.d010838 k sizes hk hn)
    (fun theta => (_root_.GD.N0232.N0719.N0859.d010846 k sizes hk hn theta).le)



theorem d020720
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i) :
    ∃ f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable f ∧
      (∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f < _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      (∀ d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ, Measurable d →
        (∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f) →
        ∀ theta, d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] f) ∧
      _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn f = 0 := by
  obtain ⟨hm, hs, ht, _⟩ := _root_.GD.N0232.N0719.N0859.d010850 k sizes hk hn
  exact ⟨_root_.GD.N0232.N0719.N0859.d010837 k sizes hk hn, hm, hs, ht,
    _root_.GD.N0232.N0719.N1014.d020719 sizes hk hn h hother⟩


theorem d020721 :
    ∃ f : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0939.d020716 → ℝ,
      Measurable f ∧
      (∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0939.d020716 theta f < _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0939.d020716 theta (_root_.GD.N0232.N0719.N0859.d010815 3 _root_.GD.N0232.N0719.N0939.d020716)) ∧
      (∀ d : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0939.d020716 → ℝ, Measurable d →
        (∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0939.d020716 theta d ≤ _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0939.d020716 theta f) →
        ∀ theta, d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 3 _root_.GD.N0232.N0719.N0939.d020716 theta] f) ∧
      _root_.GD.N0232.N0719.N0973.d012375 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 f = 0 := by
  apply _root_.GD.N0232.N0719.N1014.d020720 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 0
  intro i hi
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0939.d020716] at *

end
end GD.N0232.N0719.N1014

#print axioms _root_.GD.N0232.N0719.N1014.d020719
#print axioms _root_.GD.N0232.N0719.N1014.d020720
#print axioms _root_.GD.N0232.N0719.N1014.d020721
