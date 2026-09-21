import GD.Module1342
import GD.Module1348
import Mathlib.MeasureTheory.Function.UniformIntegrable









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace GD.N0106.N0428.N0770.N1745
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0106.N0428.N0770.N1751
open _root_.GD.N0106.N0428.N0770.N1749

abbrev d021821 (k : ℕ) := (Fin k → ℝ) × (Fin k → ℝ)


def d021822 (k : ℕ) : Measure (_root_.GD.N0106.N0428.N0770.N1745.d021821 k) :=
  (_root_.GD.N0106.N0428.N0770.N1751.d021742 k).prod (_root_.GD.N0106.N0428.N0770.N1751.d021742 k)

instance d021823 (k : ℕ) : IsProbabilityMeasure (_root_.GD.N0106.N0428.N0770.N1745.d021822 k) := by
  unfold _root_.GD.N0106.N0428.N0770.N1745.d021822
  infer_instance


def d021824 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 k) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009110
    (_root_.GD.N0232.N0719.N0933.d009305 k (_root_.GD.N0106.N0428.N0770.N1751.d021754 k mu sigma p)) - mu

def d021825 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 k) : ℝ := (_root_.GD.N0106.N0428.N0770.N1745.d021824 k mu sigma p) ^ 2

@[fun_prop] theorem d021826 (k : ℕ) (mu : ℝ) (sigma : Fin k → ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1745.d021824 k mu sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1745.d021824
  exact (_root_.GD.N0232.N0719.N0900.d009121.comp
    ((_root_.GD.N0232.N0719.N0933.d009306 k).comp (_root_.GD.N0106.N0428.N0770.N1751.d021755 k mu sigma))).sub_const mu

@[fun_prop] theorem d021827 (k : ℕ) (mu : ℝ)
    (sigma : Fin k → ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1745.d021825 k mu sigma) :=
  (_root_.GD.N0106.N0428.N0770.N1745.d021826 k mu sigma).pow_const 2



theorem d021828 (k : ℕ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1745.d021825 k theta.location theta.scale p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k) =
      _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta := by
  let F : _root_.GD.N0106.N0428.N0770.N1745.d021821 k → ℝ := fun z =>
    (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) - theta.location) ^ 2
  have hF : Measurable F :=
    ((_root_.GD.N0232.N0719.N0900.d009121.comp
      (_root_.GD.N0232.N0719.N0933.d009306 k)).sub_const theta.location).pow_const 2
  calc
    _ = ∫ z, F z ∂(_root_.GD.N0106.N0428.N0770.N1745.d021822 k).map
        (_root_.GD.N0106.N0428.N0770.N1751.d021754 k theta.location theta.scale) :=
      (integral_map_of_stronglyMeasurable
        (_root_.GD.N0106.N0428.N0770.N1751.d021755 k theta.location theta.scale) hF.stronglyMeasurable).symm
    _ = ∫ z, F z ∂(_root_.GD.N0232.N0719.d009176 k (fun _ => 2) theta.location theta.scale).map
        (_root_.GD.N0232.N0719.N0933.d009304 k (fun _ => 2)) := by
      rw [_root_.GD.N0106.N0428.N0770.N1745.d021822, _root_.GD.N0106.N0428.N0770.N1751.d021757 k theta.location theta.scale theta.scale_pos]
    _ = ∫ omega, F (_root_.GD.N0232.N0719.N0933.d009304 k (fun _ => 2) omega)
        ∂_root_.GD.N0232.N0719.d009176 k (fun _ => 2) theta.location theta.scale :=
      integral_map_of_stronglyMeasurable
        (_root_.GD.N0232.N0719.N0933.d009308 k (fun _ => 2)) hF.stronglyMeasurable
    _ = _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta := by
      simp only [F, _root_.GD.N0232.N0719.N0933.d009307]
      rfl


theorem d021829 (mu : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r] p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3) =
      r / 8 + 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by
  have hsigma : ∀ i : Fin 3, 0 < ![1, 1, r] i := by
    intro i
    fin_cases i <;> simp [hr]
  let theta : _root_.GD.N0232.N0719.N0859.d010809 3 := ⟨mu, ![1, 1, r], hsigma⟩
  exact (_root_.GD.N0106.N0428.N0770.N1745.d021828 3 theta).trans
    (_root_.GD.N0106.N0428.N0770.N1749.d021803 theta hr rfl)

theorem d021830 (mu : ℝ) {r : ℝ} (hr : 0 < r) :
    r / 8 < ∫ p, _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r] p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3 := by
  rw [_root_.GD.N0106.N0428.N0770.N1745.d021829 mu hr]
  have h : 0 < 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by positivity
  linarith


theorem d021831 (mu : ℝ) :
    Tendsto (fun r : ℝ => ∫ p, _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r] p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3)
      atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop (max 1 (8 * (M + 1)))] with r hr
  have h1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
  have hM : 8 * (M + 1) ≤ r := (le_max_right _ _).trans hr
  have h := _root_.GD.N0106.N0428.N0770.N1745.d021830 mu (by linarith : 0 < r)
  linarith

private theorem d021832 {ι : Type*} {k : ℕ}
    {f : ι → _root_.GD.N0106.N0428.N0770.N1745.d021821 k → ℝ} (hUI : UniformIntegrable f 1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 k)) :
    ∃ C : ℝ, ∀ i, (∫ p, f i p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k) ≤ C := by
  obtain ⟨C, hC⟩ := hUI.2.2
  refine ⟨C, fun i => ?_⟩
  have hbound : ‖∫ p, f i p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k‖ₑ ≤ (C : ℝ≥0∞) := by
    apply (enorm_integral_le_lintegral_enorm (f i)).trans
    simpa only [eLpNorm_one_eq_lintegral_enorm] using hC i
  have hreal : ‖∫ p, f i p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k‖ ≤ (C : ℝ) := by
    simpa using ENNReal.toReal_mono (by simp : (C : ℝ≥0∞) ≠ ∞) hbound
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hreal)



theorem d021833 {ι : Type*} (mu : ℝ) (r : ι → ℝ)
    (hr : ∀ C : ℝ, ∃ i, C < r i) :
    ¬ UniformIntegrable (fun i => _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r i]) 1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) := by
  intro hUI
  obtain ⟨C, hC⟩ := _root_.GD.N0106.N0428.N0770.N1745.d021832 hUI
  obtain ⟨i, hi⟩ := hr (max 0 (8 * (C + 1)))
  have hpos : 0 < r i := lt_of_le_of_lt (le_max_left _ _) hi
  have hlarge : 8 * (C + 1) < r i := lt_of_le_of_lt (le_max_right _ _) hi
  have h := _root_.GD.N0106.N0428.N0770.N1745.d021830 mu hpos
  have hb := hC i
  linarith


theorem d021834 (mu : ℝ) :
    ¬ UniformIntegrable
      (fun r : {r : ℝ // 0 < r} => _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r.1])
      1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) := by
  apply _root_.GD.N0106.N0428.N0770.N1745.d021833 mu
  intro C
  refine ⟨⟨|C| + 1, by positivity⟩, ?_⟩
  dsimp
  linarith [le_abs_self C]


theorem d021835 (mu R : ℝ) :
    ¬ UniformIntegrable
      (fun r : {r : ℝ // 0 < r ∧ R ≤ r} => _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r.1])
      1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) := by
  apply _root_.GD.N0106.N0428.N0770.N1745.d021833 mu
  intro C
  have h1 : (1 : ℝ) ≤ max 1 (max R (C + 1)) := le_max_left _ _
  have hR : R ≤ max 1 (max R (C + 1)) := (le_max_left _ _).trans (le_max_right _ _)
  have hC : C + 1 ≤ max 1 (max R (C + 1)) := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨⟨max 1 (max R (C + 1)), ⟨by linarith, hR⟩⟩, by dsimp; linarith⟩


theorem d021836 (mu : ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) :
    ¬ UniformIntegrable (fun n => _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu ![1, 1, r n]) 1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) := by
  apply _root_.GD.N0106.N0428.N0770.N1745.d021833 mu r
  intro C
  exact (hr.eventually (eventually_gt_atTop C)).exists



theorem d021837 {k : ℕ}
    {f : ℕ → _root_.GD.N0106.N0428.N0770.N1745.d021821 k → ℝ} {g : _root_.GD.N0106.N0428.N0770.N1745.d021821 k → ℝ}
    (hUI : UniformIntegrable f 1 (_root_.GD.N0106.N0428.N0770.N1745.d021822 k))
    (hae : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k, Tendsto (fun n => f n p) atTop (𝓝 (g p))) :
    Tendsto (fun n => ∫ p, f n p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k) atTop (𝓝 (∫ p, g p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 k)) := by
  have hg := hUI.memLp_of_ae_tendsto hae
  apply tendsto_integral_of_L1' g hg.aestronglyMeasurable
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUI.memLp n)))
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    hUI.aestronglyMeasurable hg hUI.unifIntegrable hae

end
end GD.N0106.N0428.N0770.N1745

#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021828
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021829
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021830
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021831
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021833
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021834
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021835
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021836
#print axioms _root_.GD.N0106.N0428.N0770.N1745.d021837
