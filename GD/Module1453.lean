import GD.Module0810



















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0106.N0428.N0769.N1696
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)


def d023007 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes) :=
  Measure.pi (fun i => Measure.pi (fun _ : Fin (sizes i) =>
    gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i))))


def d023008 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - θ.location) ^ 2) ∂_root_.GD.N0106.N0428.N0769.N1696.d023007 k sizes θ

theorem d023009 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = _root_.GD.N0106.N0428.N0769.N1696.d023007 k sizes θ := by
  simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176,
    _root_.GD.N0106.N0428.N0769.N1696.d023007, _root_.GD.N0232.N0719.N0932.d009211]


theorem d023010 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0106.N0428.N0769.N1696.d023008 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
  rw [_root_.GD.N0106.N0428.N0769.N1696.d023008, ← _root_.GD.N0106.N0428.N0769.N1696.d023009]
  rfl


theorem d023011
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hd : Measurable d) :
    (⨆ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0106.N0428.N0769.N1696.d023008 k sizes θ d) = ⊤ := by
  simpa only [_root_.GD.N0230.N0611.d003516, _root_.GD.N0106.N0428.N0769.N1696.d023010] using
    _root_.GD.N0232.N0719.N0971.d012335 k sizes d hd


theorem d023012
    (S : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ))
    (hS : ∀ d ∈ S, Measurable d) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0106.N0428.N0769.N1696.d023008 k sizes) S = ⊤ := by
  simpa only [_root_.GD.N0230.N0611.d003517, _root_.GD.N0230.N0611.d003516, _root_.GD.N0106.N0428.N0769.N1696.d023010] using
    _root_.GD.N0232.N0719.N0971.d012336 k sizes S hS


theorem d023013 :
    (⨅ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      ⨅ (_ : Measurable d), ⨆ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0106.N0428.N0769.N1696.d023008 k sizes θ d) = ⊤ := by
  simpa only [_root_.GD.N0230.N0611.d003517, _root_.GD.N0230.N0611.d003516, Set.mem_setOf_eq] using
    _root_.GD.N0106.N0428.N0769.N1696.d023012 k sizes {d | Measurable d}
      (fun _ hd => hd)

end
end GD.N0106.N0428.N0769.N1696

#print axioms _root_.GD.N0106.N0428.N0769.N1696.d023009
#print axioms _root_.GD.N0106.N0428.N0769.N1696.d023010
#print axioms _root_.GD.N0106.N0428.N0769.N1696.d023011
#print axioms _root_.GD.N0106.N0428.N0769.N1696.d023012
#print axioms _root_.GD.N0106.N0428.N0769.N1696.d023013
