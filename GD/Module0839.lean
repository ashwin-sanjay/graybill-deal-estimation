import GD.Module0838
import GD.Module0411

set_option warningAsError true














open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0228
namespace N0547
namespace N0784

noncomputable section

open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0779
  _root_.GD.N0228.N0547.N0788


def d012815 (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2

@[fun_prop]
theorem d012816 : Measurable _root_.GD.N0228.N0547.N0784.d012815 := by
  unfold _root_.GD.N0228.N0547.N0784.d012815
  fun_prop


def d012817 (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (p.1, _root_.GD.N0228.N0547.N0784.d012815 p.2)

@[fun_prop]
theorem d012818 : Measurable _root_.GD.N0228.N0547.N0784.d012817 := by
  unfold _root_.GD.N0228.N0547.N0784.d012817
  fun_prop


def d012819 (p : ℝ × (ℝ × ℝ)) : ℝ :=
  p.1 * Real.sqrt (p.2.1 * p.2.2)

@[fun_prop]
theorem d012820 : Measurable _root_.GD.N0228.N0547.N0784.d012819 := by
  unfold _root_.GD.N0228.N0547.N0784.d012819
  fun_prop

theorem d012821 :
    _root_.GD.N0228.N0547.N0788.d006357 ∘ _root_.GD.N0228.N0547.N0784.d012817 =
      _root_.GD.N0228.N0547.N0784.d012819 := by
  rfl


theorem d012822
    {d : ℕ} (hd : 1 < d) :
    ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0784.d012815 =
      _root_.GD.N0228.N0547.N0778.d009365 1 := by
  have hcomplement : 0 < ((d : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d := by exact_mod_cast hd
    positivity
  letI : IsProbabilityMeasure
      (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hcomplement (by norm_num)
  calc
    ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0784.d012815 =
        (((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
          (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0778.d009366).map Prod.fst := by
      rw [Measure.map_map measurable_fst _root_.GD.N0228.N0547.N0778.d009368]
      rfl
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
        (gammaMeasure (((d : ℝ) - 1) / 2) (1 / 2))).map Prod.fst := by
      rw [_root_.GD.N0228.N0547.N0779.d012814 hd]
    _ = _root_.GD.N0228.N0547.N0778.d009365 1 := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]



theorem d012823
    {d : ℕ} (hd : 1 < d) :
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0784.d012817 =
      (_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1) := by
  have hshape : 0 < ((d : ℝ) - 1) / 2 := by
    have hdR : (1 : ℝ) < d := by exact_mod_cast hd
    positivity
  letI : IsProbabilityMeasure
      (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)) :=
    isProbabilityMeasureBeta (by norm_num) hshape
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d) := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    have hdR : 0 < (d : ℝ) := by positivity
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  calc
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0784.d012817 =
        ((_root_.GD.N0228.N0547.N0788.d006356).map id).prod
          (((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
            (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0784.d012815) := by
      exact (Measure.map_prod_map (_root_.GD.N0228.N0547.N0788.d006356)
        ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
          (_root_.GD.N0228.N0547.N0778.d009365 d)) measurable_id
          _root_.GD.N0228.N0547.N0784.d012816).symm
    _ = (_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1) := by
      rw [Measure.map_id, _root_.GD.N0228.N0547.N0784.d012822 hd]




theorem d012824
    {d : ℕ} (hd : 1 < d) :
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0784.d012819 =
      gaussianReal 0 1 := by
  calc
    ((_root_.GD.N0228.N0547.N0788.d006356).prod
      ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
        (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0784.d012819 =
        (((_root_.GD.N0228.N0547.N0788.d006356).prod
          ((betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)).prod
            (_root_.GD.N0228.N0547.N0778.d009365 d))).map _root_.GD.N0228.N0547.N0784.d012817).map
              _root_.GD.N0228.N0547.N0788.d006357 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0788.d006358
        _root_.GD.N0228.N0547.N0784.d012818, _root_.GD.N0228.N0547.N0784.d012821]
    _ = ((_root_.GD.N0228.N0547.N0788.d006356).prod (_root_.GD.N0228.N0547.N0778.d009365 1)).map
          _root_.GD.N0228.N0547.N0788.d006357 := by
      rw [_root_.GD.N0228.N0547.N0784.d012823 hd]
    _ = gaussianReal 0 1 := by
      simpa only [_root_.GD.N0228.N0547.N0778.d009365, _root_.GD.N0121.d006346] using
        _root_.GD.N0228.N0547.N0788.d006371

end

end N0784
end N0547
end N0228
end GD

#print axioms _root_.GD.N0228.N0547.N0784.d012822
#print axioms _root_.GD.N0228.N0547.N0784.d012823
#print axioms _root_.GD.N0228.N0547.N0784.d012824
