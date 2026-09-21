import GD.Module1552
import GD.Module1264
import GD.Module1450

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0461

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976 _root_.GD.N0232.N0719.N0975
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0211.N0459
open _root_.GD.N0213.N0477

noncomputable section
variable {k d : ℕ}

variable (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)




theorem d024003
    (hn : ∀ i, 2 ≤ sizes i) (q : ℝ) (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s)
    (hshape : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))).1
          (_root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))).2
          (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020362 sizes z).1 (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  have hregular : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
    have hh := (_root_.GD.N0212.N0461.d023998 sizes hdim).quasiMeasurePreserving.ae
      (_root_.GD.N0212.N0461.d024001 sizes hdim hn)
    filter_upwards [hh] with z hz
    change ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes
      ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0211.N0459.d020003 sizes hdim z)) i at hz
    simpa only [MeasurableEquiv.symm_apply_apply] using hz
  apply _root_.GD.N0102.N0425.d022973
    sizes hdim hn0 q μ s _ hregular hshape
  intro c a ha z
  have hh := _root_.GD.N0211.N0459.d020023 sizes hdim hs c a ha
    (_root_.GD.N0211.N0459.d020003 sizes hdim z)
  simp only [Function.comp_apply, _root_.GD.N0211.N0459.d020005,
    MeasurableEquiv.symm_apply_apply] at hh
  change s (fun i j => c + a * z i j) = c + a * s z at hh
  exact hh

def d024004 (v : _root_.GD.N0211.N0459.d020010 k) : _root_.GD.N0213.N0477.d020377 k :=
  ⟨fun i => 1 / (v i : ℝ), fun i => one_div_pos.mpr (v i).property.1⟩

theorem d024005 (v : _root_.GD.N0211.N0459.d020010 k) :
    _root_.GD.N0213.N0477.d020380 sizes hdim (_root_.GD.N0212.N0461.d024004 v) = _root_.GD.N0211.N0459.d020012 sizes hdim v := rfl

variable [NeZero k]




theorem d024006
    (hn : ∀ i, 2 ≤ sizes i) (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ)
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s)
    (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 d,
      |s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))| ≤ 1) :
    ∃ μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k), ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0232.N0719.N0983.d009724 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (_root_.GD.N0232.N0719.N0986.d020362 sizes z).1 (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  obtain ⟨h, hadm, hshape⟩ := _root_.GD.N0211.N0459.d020024 sizes hdim hs hbound
  have hcontinuous : Continuous (fun v : _root_.GD.N0211.N0459.d020010 k =>
      _root_.GD.N0213.N0477.d020380 sizes hdim (_root_.GD.N0212.N0461.d024004 v)) := _root_.GD.N0211.N0459.d020013 sizes hdim
  obtain ⟨μ, hμ⟩ := _root_.GD.N0212.N0460.d020405 sizes hdim
    _root_.GD.N0212.N0461.d024004 hcontinuous _root_.GD.N0211.N0459.d020014 hn0 h hadm (_root_.GD.N0212.N0461.d024002 sizes hdim hn)
  refine ⟨μ, ?_⟩
  have heq : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))).1
          (_root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))).2
          (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
    filter_upwards [hshape, hμ] with u hu hmu
    exact hu.symm.trans hmu
  have hr := _root_.GD.N0212.N0461.d024003 sizes hdim hn (_root_.GD.N0213.N0477.d020391 d) μ s hs heq
  have he : _root_.GD.N0213.N0477.d020391 d = ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2) := by
    unfold _root_.GD.N0213.N0477.d020391
    rw [hdim]
    push_cast
    ring
  simpa only [he] using hr

end
end GD.N0212.N0461

#print axioms _root_.GD.N0212.N0461.d024002
#print axioms _root_.GD.N0212.N0461.d024003
#print axioms _root_.GD.N0212.N0461.d024006
