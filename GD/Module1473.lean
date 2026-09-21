import GD.Module1472
import GD.Module1466
import GD.Module1328










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0101.N0350
noncomputable section

open _root_.GD.N0101.N0357
open _root_.GD.N0151
open _root_.GD.N0225.N0539
open _root_.GD.N0213.N0495
open _root_.GD.N0213.N0523
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}

def d023172 (a : Fin k → ℝ) (ρ L : ℝ) (t : Fin k → ℝ) : ℝ :=
  ∫ β, _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 ∂_root_.GD.N0101.N0357.d023161 a ρ t

def d023173 (a : Fin k → ℝ) (ρ L : ℝ)
    (i j : Fin k) (t : Fin k → ℝ) : ℝ :=
  _root_.GD.N0101.N0357.d023162 a ρ t * _root_.GD.N0101.N0350.d023172 a ρ L t / (t i + t j)

def d023174 (a : Fin k → ℝ) (ρ L : ℝ) (t : Fin k → ℝ) : ℝ :=
  ∫ β, _root_.GD.N0232.N0719.N0954.d009343 (fun l => _root_.GD.N0213.N0523.d023144 (a l) ρ)
    (fun l => a l * t l) β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2

theorem d023175 (a : Fin k → ℝ) (ρ L : ℝ) :
    Measurable (_root_.GD.N0101.N0350.d023174 a ρ L) := by
  have hp : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0232.N0719.N0954.d009343 (fun l => _root_.GD.N0213.N0523.d023144 (a l) ρ)
        (fun l => a l * z.1 l) z.2) := by
    unfold _root_.GD.N0232.N0719.N0954.d009343
    apply Finset.measurable_prod
    intro i _
    unfold gammaPDFReal
    apply Measurable.ite
    · exact measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
    · fun_prop
    · exact measurable_const
  have he : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0213.N0495.d007175 L (∑ l, z.2 l) ^ 2) := by
    unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
    fun_prop
  exact (hp.mul he).stronglyMeasurable.integral_prod_right'.measurable

theorem d023176 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ l, 0 < a l) (hρ : ρ < 1) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0350.d023172 a ρ L t = _root_.GD.N0101.N0350.d023174 a ρ L t := by
  exact _root_.GD.N0232.N0719.N0954.d009364
    (fun l => zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha l) hρ))
    (fun l => mul_pos (ha l) (ht l)) _

theorem d023177 (a : Fin k → ℝ) (ρ : ℝ) :
    Measurable (_root_.GD.N0101.N0357.d023162 a ρ) := by
  unfold _root_.GD.N0101.N0357.d023162 _root_.GD.N0213.N0523.d023145
  fun_prop

theorem d023178 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ l, 0 < a l) (hρ : ρ < 1) (i j : Fin k) :
    AEStronglyMeasurable (_root_.GD.N0101.N0350.d023173 a ρ L i j) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  have hm : Measurable (fun t : Fin k → ℝ =>
      _root_.GD.N0101.N0357.d023162 a ρ t * _root_.GD.N0101.N0350.d023174 a ρ L t / (t i + t j)) :=
    ((_root_.GD.N0101.N0350.d023177 a ρ).mul (_root_.GD.N0101.N0350.d023175 a ρ L)).div
      ((measurable_pi_apply i).add (measurable_pi_apply j))
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  simp only [_root_.GD.N0101.N0350.d023173, _root_.GD.N0101.N0350.d023176 a ρ L ha hρ ht]

theorem d023179 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ l, 0 < a l) (hρ : ρ < 1) (i j : Fin k)
    {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    0 ≤ _root_.GD.N0101.N0350.d023173 a ρ L i j t := by
  exact div_nonneg
    (mul_nonneg (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le (integral_nonneg fun _ => sq_nonneg _))
    (add_nonneg (ht i).le (ht j).le)

theorem d023180 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ l, 0 < a l) (hρ : ρ < 1) {L : ℝ} (hL : 0 < L)
    {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    Integrable (fun β => _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2)
      (_root_.GD.N0101.N0357.d023161 a ρ t) := by
  exact _root_.GD.N0101.N0402.d023090
    (fun l => a l * (1 - ρ)) (fun l => a l * t l)
    (fun l => mul_pos (ha l) (sub_pos.mpr hρ)) (fun l => mul_pos (ha l) (ht l)) hL

theorem d023181 (α a : Fin k → ℝ)
    (ha : ∀ l, 0 < a l) (i j : Fin k) (hij : i ≠ j) (L : ℝ) :
    0 ≤ᵐ[_root_.GD.N0225.N0539.d008044 α] (fun β => _root_.GD.N0151.d021647 a i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2) := by
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  rw [_root_.GD.N0151.d021648 a ha i j hij hβ]
  exact mul_nonneg (_root_.GD.N0151.d021641 (ha i) (ha j) i j (hβ i) (hβ j)) (sq_nonneg _)



theorem d023182
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ l, 0 < a l) (hρ : ρ < 1)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    (∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0350.d023173 a ρ L i j t)) =
      ∫⁻ β, ENNReal.ofReal (_root_.GD.N0151.d021647 a i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2)
        ∂_root_.GD.N0225.N0539.d008044 (fun l => 1 - ρ * a l) := by
  let F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞ := fun β t =>
    ENNReal.ofReal (_root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j))
  have hF : Measurable (Function.uncurry F) := by
    unfold F _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
    fun_prop
  have hbayes := _root_.GD.N0101.N0357.d023171 a ρ ha hρ F hF
  have hsampling :
      (∫⁻ β, (∫⁻ t, F β t ∂_root_.GD.N0101.N0357.d023160 a β) ∂_root_.GD.N0225.N0539.d008044 (fun l => 1 - ρ * a l)) =
        ∫⁻ β, ENNReal.ofReal (_root_.GD.N0151.d021647 a i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2)
          ∂_root_.GD.N0225.N0539.d008044 (fun l => 1 - ρ * a l) := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 (fun l => 1 - ρ * a l)] with β hβ
    have hi : Integrable (fun t => _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j))
        (_root_.GD.N0101.N0357.d023160 a β) := by
      simpa only [div_eq_mul_inv, _root_.GD.N0101.N0357.d023160, _root_.GD.N0232.N0719.N0954.d009342] using
        (_root_.GD.N0105.d021634 a (fun l => a l * β l)
          ha (fun l => mul_pos (ha l) (hβ l)) i j hij hab).const_mul
            (_root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2)
    have hn : 0 ≤ᵐ[_root_.GD.N0101.N0357.d023160 a β]
        (fun t => _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j)) := by
      filter_upwards [_root_.GD.N0101.N0357.d023165 a (fun l => a l * β l)
        ha (fun l => mul_pos (ha l) (hβ l))] with t ht
      exact div_nonneg (sq_nonneg _) (add_nonneg (ht i).le (ht j).le)
    rw [show (∫⁻ t, F β t ∂_root_.GD.N0101.N0357.d023160 a β) =
        ENNReal.ofReal (∫ t, _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j)
          ∂_root_.GD.N0101.N0357.d023160 a β) from (ofReal_integral_eq_lintegral_ofReal hi hn).symm]
    congr 1
    simp only [div_eq_mul_inv, integral_const_mul, _root_.GD.N0101.N0357.d023160, _root_.GD.N0232.N0719.N0954.d009342, _root_.GD.N0151.d021647]
    ring
  have hposterior :
      (∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        (∫⁻ β, F β t ∂_root_.GD.N0101.N0357.d023161 a ρ t)) =
      ∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0350.d023173 a ρ L i j t) := by
    apply setLIntegral_congr_fun _root_.GD.N0101.N0357.d023159
    intro t ht
    dsimp only
    have hi := (_root_.GD.N0101.N0350.d023180 a ρ ha hρ hL ht).div_const (t i + t j)
    have hn : 0 ≤ᵐ[_root_.GD.N0101.N0357.d023161 a ρ t]
        (fun β => _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j)) :=
      ae_of_all _ fun _ => div_nonneg (sq_nonneg _) (add_nonneg (ht i).le (ht j).le)
    rw [show (∫⁻ β, F β t ∂_root_.GD.N0101.N0357.d023161 a ρ t) =
        ENNReal.ofReal (∫ β, _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 / (t i + t j)
          ∂_root_.GD.N0101.N0357.d023161 a ρ t) from (ofReal_integral_eq_lintegral_ofReal hi hn).symm]
    rw [integral_div, ← ENNReal.ofReal_mul (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le]
    simp only [_root_.GD.N0101.N0350.d023173, _root_.GD.N0101.N0350.d023172, mul_div_assoc]
  exact hposterior.symm.trans (hbayes.symm.trans hsampling)



theorem d023183
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ l, 0 < a l) (hρ : ρ < 1)
    (hα : ∀ l, 0 < 1 - ρ * a l) (hsum : ∑ l, (1 - ρ * a l) = 1)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    Integrable (_root_.GD.N0101.N0350.d023173 a ρ L i j) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  have hn : 0 ≤ᵐ[volume.restrict _root_.GD.N0101.N0357.d023158] _root_.GD.N0101.N0350.d023173 a ρ L i j := by
    filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
    exact _root_.GD.N0101.N0350.d023179 a ρ L ha hρ i j ht
  apply (lintegral_ofReal_ne_top_iff_integrable
    (_root_.GD.N0101.N0350.d023178 a ρ L ha hρ i j) hn).mp
  rw [_root_.GD.N0101.N0350.d023182 a ρ ha hρ i j hij hab hL,
    ← ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0151.d021650 (fun l => 1 - ρ * a l) a hα hsum ha i j hij hab hL)
      (_root_.GD.N0101.N0350.d023181 (fun l => 1 - ρ * a l) a ha i j hij L)]
  exact ENNReal.ofReal_ne_top



theorem d023184
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ l, 0 < a l) (hρ : ρ < 1)
    (hα : ∀ l, 0 < 1 - ρ * a l) (hsum : ∑ l, (1 - ρ * a l) = 1)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    (∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0350.d023173 a ρ L i j t) =
      ∫ β, _root_.GD.N0151.d021647 a i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2
        ∂_root_.GD.N0225.N0539.d008044 (fun l => 1 - ρ * a l) := by
  have hn : 0 ≤ᵐ[volume.restrict _root_.GD.N0101.N0357.d023158] _root_.GD.N0101.N0350.d023173 a ρ L i j := by
    filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
    exact _root_.GD.N0101.N0350.d023179 a ρ L ha hρ i j ht
  have hp := _root_.GD.N0101.N0350.d023181 (fun l => 1 - ρ * a l) a ha i j hij L
  have heq := _root_.GD.N0101.N0350.d023182 a ρ ha hρ i j hij hab hL
  rw [← ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0101.N0350.d023183 a ρ ha hρ hα hsum i j hij hab hL) hn,
    ← ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0151.d021650 (fun l => 1 - ρ * a l) a hα hsum ha i j hij hab hL) hp] at heq
  have hh := congrArg ENNReal.toReal heq
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)] using hh

theorem d023185
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ l, 0 < a l) (hρ : ρ < 1)
    (hα : ∀ l, 0 < 1 - ρ * a l) (hsum : ∑ l, (1 - ρ * a l) = 1)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) :
    Tendsto (fun n : ℕ => ∫ t in _root_.GD.N0101.N0357.d023158,
      _root_.GD.N0101.N0350.d023173 a ρ ((n : ℝ) + 1) i j t) atTop (𝓝 0) := by
  have heq (n : ℕ) := _root_.GD.N0101.N0350.d023184 a ρ ha hρ hα hsum i j hij hab
    (show 0 < (n : ℝ) + 1 by positivity)
  simp_rw [heq]
  exact _root_.GD.N0151.d021651 (fun l => 1 - ρ * a l) a hα hsum ha i j hij hab

end
end GD.N0101.N0350

#print axioms _root_.GD.N0101.N0350.d023182
#print axioms _root_.GD.N0101.N0350.d023183
#print axioms _root_.GD.N0101.N0350.d023184
#print axioms _root_.GD.N0101.N0350.d023185
