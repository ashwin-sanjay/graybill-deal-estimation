import GD.Module1812
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Group.Constructions

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0246

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open _root_.GD.N0005.N0245

noncomputable section

abbrev d030055 (n : ℕ) := Fin n → ℝ
abbrev d030056 (m n : ℕ) := _root_.GD.N0005.N0246.d030055 m × _root_.GD.N0005.N0246.d030055 n
abbrev d030057 (m n : ℕ) := _root_.GD.N0005.N0246.d030056 m n × _root_.GD.N0005.N0246.d030056 m n

def d030058 (n : ℕ) (location : ℝ) : Measure (_root_.GD.N0005.N0246.d030055 n) :=
  Measure.pi fun _ => gaussianReal location 1

instance d030059 (n : ℕ) (location : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0005.N0246.d030058 n location) := by
  unfold _root_.GD.N0005.N0246.d030058
  infer_instance

def d030060 (m n : ℕ) : Measure (_root_.GD.N0005.N0246.d030056 m n) :=
  (_root_.GD.N0005.N0246.d030058 m 0).prod (_root_.GD.N0005.N0246.d030058 n 0)

def d030061 (m n : ℕ) (θ : ℝ) : Measure (_root_.GD.N0005.N0246.d030056 m n) :=
  (_root_.GD.N0005.N0246.d030058 m θ).prod (_root_.GD.N0005.N0246.d030058 n 0)

def d030062 (m n : ℕ) (θ : ℝ) : Measure (_root_.GD.N0005.N0246.d030057 m n) :=
  (_root_.GD.N0005.N0246.d030060 m n).prod (_root_.GD.N0005.N0246.d030061 m n θ)

instance d030063 (m n : ℕ) : IsProbabilityMeasure (_root_.GD.N0005.N0246.d030060 m n) := by
  unfold _root_.GD.N0005.N0246.d030060
  infer_instance

instance d030064 (m n : ℕ) (θ : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0005.N0246.d030061 m n θ) := by
  unfold _root_.GD.N0005.N0246.d030061
  infer_instance

instance d030065 (m n : ℕ) (θ : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0005.N0246.d030062 m n θ) := by
  unfold _root_.GD.N0005.N0246.d030062
  infer_instance

theorem d030066 (m n : ℕ) (θ : ℝ) (A : Set (_root_.GD.N0005.N0246.d030056 m n)) :
    _root_.GD.N0005.N0246.d030062 m n θ {z | z.1 ∈ A} = _root_.GD.N0005.N0246.d030060 m n A :=
  _root_.GD.N0005.N0245.d030054 (_root_.GD.N0005.N0246.d030060 m n) (_root_.GD.N0005.N0246.d030061 m n θ) A

theorem d030067
    (m n : ℕ) (region : _root_.GD.N0005.N0246.d030056 m n → Set (ℝ × ℝ))
    (hgraph : MeasurableSet {z : _root_.GD.N0005.N0246.d030056 m n × (ℝ × ℝ) | z.2 ∈ region z.1})
    (hbounded : ∀ z, Bornology.IsBounded (region z)) :
    Tendsto (fun k : ℕ => _root_.GD.N0005.N0246.d030062 m n k
      {z | (0, (k : ℝ)) ∈ region z.1}) atTop (𝓝 0) := by
  have hm (k : ℕ) : MeasurableSet {z : _root_.GD.N0005.N0246.d030056 m n | (0, (k : ℝ)) ∈ region z} :=
    hgraph.preimage (measurable_id.prodMk measurable_const)
  have ht : Tendsto (fun k : ℕ => ‖((0 : ℝ), (k : ℝ))‖) atTop atTop := by
    have heq : (fun k : ℕ => ‖((0 : ℝ), (k : ℝ))‖) = fun k : ℕ => (k : ℝ) := by
      funext k
      simp
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  have h := _root_.GD.N0005.N0245.d030051 (_root_.GD.N0005.N0246.d030060 m n)
    region (fun k : ℕ => (0, (k : ℝ))) hm hbounded ht
  have heq : (fun k : ℕ => _root_.GD.N0005.N0246.d030062 m n k {z | (0, (k : ℝ)) ∈ region z.1}) =
      (fun k : ℕ => _root_.GD.N0005.N0246.d030060 m n {z | (0, (k : ℝ)) ∈ region z}) := by
    funext k
    exact _root_.GD.N0005.N0246.d030066 m n k {z | (0, (k : ℝ)) ∈ region z}
  rw [heq]
  exact h

theorem d030068
    (m n : ℕ) {p : ℝ≥0∞} (hp : 0 < p) :
    ¬ ∃ region : _root_.GD.N0005.N0246.d030056 m n → Set (ℝ × ℝ),
      MeasurableSet {z : _root_.GD.N0005.N0246.d030056 m n × (ℝ × ℝ) | z.2 ∈ region z.1} ∧
      (∀ z, Bornology.IsBounded (region z)) ∧
      ∀ θ : ℝ, p ≤ _root_.GD.N0005.N0246.d030062 m n θ {z | (0, θ) ∈ region z.1} := by
  rintro ⟨region, hgraph, hbounded, hcoverage⟩
  have h := _root_.GD.N0005.N0246.d030067 m n region hgraph hbounded
  obtain ⟨k, hk⟩ := (h.eventually (eventually_lt_nhds hp)).exists
  exact (not_lt_of_ge (hcoverage (k : ℝ))) hk

theorem d030069
    {p : ℝ} (hp : 0 < p) :
    ¬ ∃ region : _root_.GD.N0005.N0246.d030056 2 2 → Set (ℝ × ℝ),
      MeasurableSet {z : _root_.GD.N0005.N0246.d030056 2 2 × (ℝ × ℝ) | z.2 ∈ region z.1} ∧
      (∀ z, Bornology.IsBounded (region z)) ∧
      ∀ θ : ℝ, _root_.GD.N0005.N0246.d030062 2 2 θ {z | (0, θ) ∈ region z.1} = ENNReal.ofReal p := by
  rintro ⟨region, hgraph, hbounded, hcoverage⟩
  exact _root_.GD.N0005.N0246.d030068 2 2 (ENNReal.ofReal_pos.2 hp)
    ⟨region, hgraph, hbounded, fun θ => (hcoverage θ).ge⟩

end
end GD.N0005.N0246

#print axioms _root_.GD.N0005.N0246.d030067
#print axioms _root_.GD.N0005.N0246.d030068
#print axioms _root_.GD.N0005.N0246.d030069
