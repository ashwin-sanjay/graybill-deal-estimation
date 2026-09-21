import GD.Module1283
import GD.Module1228

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0473

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0982
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0997
open _root_.GD.N0212.N0462 _root_.GD.N0212.N0464

noncomputable section
variable {k : ℕ}

theorem d023078 {degree : ℕ}
    {F : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ} (m : _root_.GD.N0232.N0719.N0982.d020351 degree F) :
    ContinuousOn F _root_.GD.N0232.N0719.N0982.d020342 := by
  have hc := m.smooth_N.continuousOn.div m.smooth_M.continuousOn
    (fun x hx => (m.positive_M x hx).ne')
  apply hc.congr
  intro x hx
  exact (eq_div_iff (m.positive_M x hx).ne').mpr (m.numerator x hx).symm

def d023079 {degree : ℕ}
    {F G : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ}
    (m : _root_.GD.N0232.N0719.N0982.d020351 degree F) (hFG : EqOn F G _root_.GD.N0232.N0719.N0982.d020342) : _root_.GD.N0232.N0719.N0982.d020351 degree G where
  M := m.M
  N := m.N
  smooth_M := m.smooth_M
  smooth_N := m.smooth_N
  positive_M := m.positive_M
  numerator := by
    intro x hx
    rw [← hFG hx]
    exact m.numerator x hx
  pde := m.pde
  homogeneous := m.homogeneous




theorem d023080 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) (hs : Measurable s)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ s ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 k sizes))
    (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (hrep : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (_root_.GD.N0232.N0719.N0986.d020362 sizes z))
    (F : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ)
    (m : _root_.GD.N0232.N0719.N0982.d020351 ((∑ i, sizes i) + 2) F)
    (hpost : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0982.d020342 → F (_root_.GD.N0232.N0719.N0986.d020362 sizes z) = s z) : False := by
  letI : NeZero k := ⟨by omega⟩
  have hN : 2 ≤ ∑ i, sizes i := (hn 0).trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ 0))
  let d := (∑ i, sizes i) - 1
  have hdim : (∑ i, sizes i) = d + 1 := by dsimp [d]; omega
  have hD : (3 : ℝ) / 2 ≤ (((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2 := by
    have hDnat : 3 ≤ (∑ i, sizes i) + 1 := by omega
    have hDreal : (3 : ℝ) ≤ (((∑ i, sizes i) + 1 : ℕ) : ℝ) := by exact_mod_cast hDnat
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hDreal
  have heq : EqOn F
      (_root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) _root_.GD.N0232.N0719.N0982.d020342 := by
    apply _root_.GD.N0232.N0719.N0986.d020376 sizes hn (_root_.GD.N0212.N0473.d023078 m)
      (_root_.GD.N0212.N0464.d020736 _ _)
    filter_upwards [hpost, hrep] with z hz hrz
    intro hregular
    exact (hz hregular).trans hrz
  have hphysical : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      s z = _root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (_root_.GD.N0232.N0719.N0986.d020362 sizes z) := by
    have hv := (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim)
      (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim)).quasiMeasurePreserving.ae_eq_comp hrep
    have hr := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim hv
      (_root_.GD.N0232.N0719.N0859.d010810 k)
    change ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes
      (_root_.GD.N0232.N0719.N0859.d010810 k),
      s z = _root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (_root_.GD.N0232.N0719.N0986.d020362 sizes z)
    filter_upwards [hr] with z hz
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hz
  have hceiling := _root_.GD.N0212.N0464.d020742 hk sizes hn
    ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2) μ s hs hcap hphysical
  apply _root_.GD.N0212.N0462.d020726 hk ((∑ i, sizes i) + 1) hD μ hceiling
  simpa only [Nat.add_assoc] using (show Nonempty (_root_.GD.N0232.N0719.N0982.d020351 ((∑ i, sizes i) + 2)
    (_root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
      (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)))) from ⟨_root_.GD.N0212.N0473.d023079 m heq⟩)

end
end GD.N0212.N0473

#print axioms _root_.GD.N0212.N0473.d023078
#print axioms _root_.GD.N0212.N0473.d023080
