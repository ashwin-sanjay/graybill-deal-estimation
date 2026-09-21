import GD.Module0637
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0069
noncomputable section



theorem d022755 {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (i j : ι) (hij : i ≠ j) :
    MeasurePreserving (fun z : ι → ℝ => (z i, z j))
      (Measure.pi μ) ((μ i).prod (μ j)) := by
  have hind : IndepFun (fun z : ι → ℝ => z i) (fun z => z j) (Measure.pi μ) :=
    (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  refine ⟨by fun_prop, ?_⟩
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable]
  rw [(measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq]

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933

variable {k : ℕ}

def d022756 (sizes : Fin k → ℕ) (i : Fin k) : ℝ := (sizes i - 1 : ℕ) / 2

theorem d022757 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i : Fin k) :
    0 < _root_.GD.N0069.d022756 sizes i := by
  have h : 0 < sizes i - 1 := by have := hn i; omega
  exact div_pos (Nat.cast_pos.mpr h) (by norm_num)

private theorem d022758 {n : ℕ} (hn : 2 ≤ n) (σ : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009289 n σ) := by
  have ha : 0 < ((n - 1 : ℕ) : ℝ) / 2 := by
    have h : 0 < n - 1 := by omega
    exact div_pos (Nat.cast_pos.mpr h) (by norm_num)
  unfold _root_.GD.N0232.N0719.N0933.d009289
  letI := isProbabilityMeasure_gammaMeasure ha ha
  exact Measure.isProbabilityMeasure_map (_root_.GD.N0232.N0719.N0933.d009294 n σ).aemeasurable


def d022759 (sizes : Fin k → ℕ) (i j : Fin k)
    (z : _root_.GD.N0232.N0719.d009173 k sizes) : (ℝ × ℝ) × (ℝ × ℝ) :=
  let s := _root_.GD.N0232.N0719.N0933.d009304 k sizes z
  ((s.1 i, s.1 j), (s.2 i, s.2 j))

theorem d022760 (sizes : Fin k → ℕ) (i j : Fin k) :
    Measurable (_root_.GD.N0069.d022759 sizes i j) := by
  unfold _root_.GD.N0069.d022759
  fun_prop



theorem d022761
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j) (m : ℝ) (σ : Fin k → ℝ) :
    MeasurePreserving (_root_.GD.N0069.d022759 sizes i j)
      (_root_.GD.N0232.N0719.d009176 k sizes m σ)
      (((_root_.GD.N0232.N0719.N0933.d009288 (sizes i) m (σ i)).prod (_root_.GD.N0232.N0719.N0933.d009288 (sizes j) m (σ j))).prod
        ((_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (σ i)).prod (_root_.GD.N0232.N0719.N0933.d009289 (sizes j) (σ j)))) := by
  letI (r : Fin k) : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009289 (sizes r) (σ r)) :=
    _root_.GD.N0069.d022758 (hn r) (σ r)
  have hm := _root_.GD.N0069.d022755 (fun r => _root_.GD.N0232.N0719.N0933.d009288 (sizes r) m (σ r)) i j hij
  have hv := _root_.GD.N0069.d022755 (fun r => _root_.GD.N0232.N0719.N0933.d009289 (sizes r) (σ r)) i j hij
  have hraw : MeasurePreserving (_root_.GD.N0232.N0719.N0933.d009304 k sizes)
      (_root_.GD.N0232.N0719.d009176 k sizes m σ)
      ((_root_.GD.N0232.N0719.N0933.d009300 k sizes m σ).prod (_root_.GD.N0232.N0719.N0933.d009301 k sizes σ)) :=
    ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes,
      _root_.GD.N0232.N0719.N0933.d009309 k sizes hn m σ⟩
  exact (hm.prod hv).comp hraw

end
end GD.N0069

#print axioms _root_.GD.N0069.d022755
#print axioms _root_.GD.N0069.d022760
#print axioms _root_.GD.N0069.d022761
