import GD.Module1226

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set
open scoped Topology

namespace GD.N0232.N0719.N0999

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1326
  (d019886 d019887)
open _root_.GD.N0238.N0753

noncomputable section
abbrev d019923 := _root_.GD.N0232.N0720.N1341.d004414
variable {d : ℕ}



theorem d019924
    (f : _root_.GD.N0232.N0719.N0999.d019923 d → ℝ) (hhom : _root_.GD.N0238.N0753.d004397 f)
    (hint : Integrable (fun x => f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) :
    Integrable (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f u ^ 2) (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  have hproduct : Integrable
      (fun p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ) => f p.1 ^ 2 * _root_.GD.N0232.N0720.N1341.d004427 p.2.1)
      ((_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d)) := by
    rw [_root_.GD.N0232.N0720.N1341.d004423] at hint
    exact hint.congr (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1341.d004432 f hhom))
  have hi := hproduct.integral_prod_left
  simp only [integral_const_mul, _root_.GD.N0232.N0720.N1341.d004431] at hi
  exact (integrable_mul_const_iff
    (isUnit_iff_ne_zero.mpr (_root_.GD.N0232.N0720.N1341.d004429 d).ne') _).mp hi

theorem d019925
    (f : _root_.GD.N0232.N0719.N0999.d019923 d → ℝ) (hf : Measurable f) (hhom : _root_.GD.N0238.N0753.d004397 f)
    (hint : Integrable (fun x => f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) :
    MemLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f u) 2 (_root_.GD.N0232.N0720.N1341.d004416 d) :=
  (memLp_two_iff_integrable_sq
    (hf.comp measurable_subtype_coe).aestronglyMeasurable).2
      (_root_.GD.N0232.N0719.N0999.d019924 f hhom hint)

def d019926 (f : _root_.GD.N0232.N0719.N0999.d019923 d → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f)
    (hint : Integrable (fun x => f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) : _root_.GD.N0232.N0720.N1341.d004417 d :=
  (_root_.GD.N0232.N0719.N0999.d019925 f hf hhom hint).toLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f u)

theorem d019927 (f : _root_.GD.N0232.N0719.N0999.d019923 d → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f)
    (hint : Integrable (fun x => f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) :
    _root_.GD.N0232.N0719.N0999.d019926 f hf hhom hint =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d]
      (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f u) :=
  (_root_.GD.N0232.N0719.N0999.d019925 f hf hhom hint).coeFn_toLp

theorem d019928
    (f : _root_.GD.N0232.N0719.N0999.d019923 d → ℝ) (hf : Measurable f) (hhom : _root_.GD.N0238.N0753.d004397 f)
    (hint : Integrable (fun x => f x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) :
    _root_.GD.N0232.N0720.N1341.d004418 (_root_.GD.N0232.N0719.N0999.d019926 f hf hhom hint) =ᵐ[volume] f := by
  have h := _root_.GD.N0232.N0720.N1326.d019886 (_root_.GD.N0232.N0719.N0999.d019927 f hf hhom hint)
  rwa [_root_.GD.N0232.N0720.N1326.d019887 f hhom] at h

end
end GD.N0232.N0719.N0999

#print axioms _root_.GD.N0232.N0719.N0999.d019925
#print axioms _root_.GD.N0232.N0719.N0999.d019928
