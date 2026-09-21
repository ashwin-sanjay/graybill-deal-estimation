import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unnecessarySimpa false
open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0082.N0334

noncomputable section

def d008256 (t u : ℝ) : ℝ := u + t - 2 * u * t

def d008257 (u : ℝ) : ℝ := 3 * u ^ 2 - 2 * u ^ 3

def d008258 (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Ioo (0 : ℝ) 1, ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2

def d008259 (t : ℝ) : ℝ := (1 + _root_.GD.N0082.N0334.d008258 _root_.GD.N0082.N0334.d008257 t) / (1 + _root_.GD.N0082.N0334.d008258 id t)

def d008260 (H : ℝ → ℝ) : Prop :=
  ∀ u ∈ Ioo (0 : ℝ) 1, |H u - u| ≤ u * (1 - u)

theorem d008261 (t u : ℝ) :
    _root_.GD.N0082.N0334.d008256 t u ^ 2 - (u - t) ^ 2 = 4 * u * t * (1 - u) * (1 - t) := by
  unfold _root_.GD.N0082.N0334.d008256
  ring

theorem d008262 (t u : ℝ) :
    _root_.GD.N0082.N0334.d008256 t u - u * (1 - u) = (1 - t) * u ^ 2 + t * (1 - u) ^ 2 := by
  unfold _root_.GD.N0082.N0334.d008256
  ring

theorem d008263 {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0082.N0334.d008256 t u := by
  have h := mul_pos hu.1 (sub_pos.mpr hu.2)
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg u)
  have h₂ := mul_nonneg ht.1 (sq_nonneg (1 - u))
  unfold _root_.GD.N0082.N0334.d008256
  nlinarith

theorem d008264 {H : ℝ → ℝ} (hH : _root_.GD.N0082.N0334.d008260 H)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2 ≤ 4 := by
  have hD := _root_.GD.N0082.N0334.d008263 ht hu
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg u)
  have h₂ := mul_nonneg ht.1 (sq_nonneg (1 - u))
  have h₃ := mul_nonneg ht.1 (sub_nonneg.mpr hu.2.le)
  have h₄ := mul_nonneg hu.1.le (sub_nonneg.mpr ht.2)
  have hB := (abs_le.mp (hH u hu))
  have hlo : -2 ≤ (H u - t) / _root_.GD.N0082.N0334.d008256 t u := by
    apply (le_div_iff₀ hD).mpr
    dsimp [_root_.GD.N0082.N0334.d008256]
    nlinarith
  have hhi : (H u - t) / _root_.GD.N0082.N0334.d008256 t u ≤ 2 := by
    apply (div_le_iff₀ hD).mpr
    dsimp [_root_.GD.N0082.N0334.d008256]
    nlinarith
  nlinarith

theorem d008265 : _root_.GD.N0082.N0334.d008260 _root_.GD.N0082.N0334.d008257 := by
  intro u hu
  have hp : 0 ≤ u * (1 - u) := mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)
  have hlow := mul_nonneg hp hu.1.le
  have hhigh := mul_nonneg hp (sub_nonneg.mpr hu.2.le)
  rw [abs_le]
  dsimp [_root_.GD.N0082.N0334.d008257]
  constructor <;> nlinarith

theorem d008266 : _root_.GD.N0082.N0334.d008260 id := by
  intro u hu
  simp only [id_eq, sub_self, abs_zero]
  exact mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)

theorem d008267 {H : ℝ → ℝ} (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) : ContinuousOn (_root_.GD.N0082.N0334.d008258 H) (Icc (0 : ℝ) 1) := by
  intro t ht
  change Tendsto (fun t => ∫ u in Ioo (0 : ℝ) 1,
    ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2) (𝓝[Icc (0 : ℝ) 1] t)
      (𝓝 (∫ u in Ioo (0 : ℝ) 1, ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ))
  · exact Eventually.of_forall fun t => by
      apply Measurable.aestronglyMeasurable
      dsimp [_root_.GD.N0082.N0334.d008256]
      fun_prop
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0082.N0334.d008264 hH hs hu
  · exact integrable_const 4
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hcont : ContinuousAt (fun s => ((H u - s) / _root_.GD.N0082.N0334.d008256 s u) ^ 2) t := by
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · fun_prop
      · dsimp [_root_.GD.N0082.N0334.d008256]; fun_prop
      · exact (_root_.GD.N0082.N0334.d008263 ht hu).ne'
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem d008268 (H : ℝ → ℝ) (t : ℝ) : 0 ≤ _root_.GD.N0082.N0334.d008258 H t := by
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem d008269 : ContinuousOn _root_.GD.N0082.N0334.d008259 (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · exact continuousOn_const.add (_root_.GD.N0082.N0334.d008267 (by unfold _root_.GD.N0082.N0334.d008257; fun_prop) _root_.GD.N0082.N0334.d008265)
  · exact continuousOn_const.add (_root_.GD.N0082.N0334.d008267 measurable_id _root_.GD.N0082.N0334.d008266)
  · intro t ht
    have := _root_.GD.N0082.N0334.d008268 id t
    linarith

lemma d008270 (H : ℝ → ℝ) :
    _root_.GD.N0082.N0334.d008258 H 0 = ∫ u in Ioo (0 : ℝ) 1, (H u / u) ^ 2 := by
  simp [_root_.GD.N0082.N0334.d008258, _root_.GD.N0082.N0334.d008256]

lemma d008271 :
    (∫ u in Ioo (0 : ℝ) 1, (3 * u - 2 * u ^ 2) ^ 2) = (4 / 5 : ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have heq : (fun u : ℝ => (3 * u - 2 * u ^ 2) ^ 2) =
      fun u => 9 * u ^ 2 - 12 * u ^ 3 + 4 * u ^ 4 := by
    funext u; ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · norm_num [intervalIntegral.integral_const_mul, integral_pow]
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem d008272 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0082.N0334.d008257 0 = (4 / 5 : ℝ) := by
  rw [_root_.GD.N0082.N0334.d008270, ← _root_.GD.N0082.N0334.d008271]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hu0 : u ≠ 0 := ne_of_gt hu.1
  dsimp [_root_.GD.N0082.N0334.d008257]
  field_simp

theorem d008273 : _root_.GD.N0082.N0334.d008258 id 0 = 1 := by
  rw [_root_.GD.N0082.N0334.d008270]
  have heq : (∫ u in Ioo (0 : ℝ) 1, (id u / u) ^ 2) =
      ∫ _u in Ioo (0 : ℝ) 1, (1 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    simp [ne_of_gt hu.1]
  rw [heq]
  simp

theorem d008274 : _root_.GD.N0082.N0334.d008259 0 = (9 / 10 : ℝ) := by
  norm_num [_root_.GD.N0082.N0334.d008259, _root_.GD.N0082.N0334.d008272, _root_.GD.N0082.N0334.d008273]

lemma d008275 (f : ℝ → ℝ) :
    (∫ u in Ioo (0 : ℝ) 1, f (1 - u)) = ∫ u in Ioo (0 : ℝ) 1, f u := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa using intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1

theorem d008276 {H : ℝ → ℝ} (hH : ∀ u, H (1 - u) = 1 - H u) (t : ℝ) :
    _root_.GD.N0082.N0334.d008258 H (1 - t) = _root_.GD.N0082.N0334.d008258 H t := by
  unfold _root_.GD.N0082.N0334.d008258
  rw [← _root_.GD.N0082.N0334.d008275 (fun u => ((H u - (1 - t)) / _root_.GD.N0082.N0334.d008256 (1 - t) u) ^ 2)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [hH]
  have hd : _root_.GD.N0082.N0334.d008256 (1 - t) (1 - u) = _root_.GD.N0082.N0334.d008256 t u := by
    unfold _root_.GD.N0082.N0334.d008256
    ring
  rw [hd]
  ring

theorem d008277 (u : ℝ) : _root_.GD.N0082.N0334.d008257 (1 - u) = 1 - _root_.GD.N0082.N0334.d008257 u := by
  unfold _root_.GD.N0082.N0334.d008257
  ring

theorem d008278 (t : ℝ) : _root_.GD.N0082.N0334.d008259 (1 - t) = _root_.GD.N0082.N0334.d008259 t := by
  unfold _root_.GD.N0082.N0334.d008259
  rw [_root_.GD.N0082.N0334.d008276 _root_.GD.N0082.N0334.d008277,
    _root_.GD.N0082.N0334.d008276 (H := id) (fun u => rfl)]

theorem d008279 : _root_.GD.N0082.N0334.d008259 1 = (9 / 10 : ℝ) := by
  simpa using (_root_.GD.N0082.N0334.d008278 0).trans _root_.GD.N0082.N0334.d008274

theorem d008280 :
    ContinuousOn _root_.GD.N0082.N0334.d008259 (Icc (0 : ℝ) 1) ∧
      _root_.GD.N0082.N0334.d008259 0 = (9 / 10 : ℝ) ∧ _root_.GD.N0082.N0334.d008259 1 = (9 / 10 : ℝ) :=
  ⟨_root_.GD.N0082.N0334.d008269, _root_.GD.N0082.N0334.d008274, _root_.GD.N0082.N0334.d008279⟩

end
end GD.N0082.N0334

#print axioms _root_.GD.N0082.N0334.d008280
