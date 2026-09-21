import GD.Module1459
import GD.Module1745

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0471

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0990
open _root_.GD.N0232.N0719.N0991 _root_.GD.N0232.N0719.N0994
open _root_.GD.N0232.N0719.N0993
open _root_.GD.N0232.N0719.N0989 (d011338)
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0213.N0496 (d021972)
open _root_.GD.N0212.N0472 _root_.GD.N0212.N0475

noncomputable section
variable {k d : ℕ} [NeZero k]




theorem d028989
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k),
      _root_.GD.N0232.N0719.N0994.d011375 (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
        _root_.GD.N0232.N0719.N0990.d020512 sizes hdim x ∈ _root_.GD.N0232.N0719.N0989.d011338 →
        _root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) =
          s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) := by
  obtain ⟨ν, hmoment, hraw⟩ :=
    _root_.GD.N0212.N0472.d023048 sizes hdim hn hd hs
  exact _root_.GD.N0212.N0475.d028988 d volume (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim)
    (fun x => s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) ν hmoment hraw




theorem d028990
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k),
      _root_.GD.N0232.N0719.N0994.d011375 (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) ∧
      Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (d + 3)
        (_root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)))) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
        _root_.GD.N0232.N0719.N0990.d020512 sizes hdim x ∈ _root_.GD.N0232.N0719.N0989.d011338 →
        _root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) =
          s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) := by
  obtain ⟨μ, hμ, hpost⟩ := _root_.GD.N0212.N0471.d028989 sizes hdim hn hd hs
  refine ⟨μ, hμ, ?_, hpost⟩
  have hratio : _root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) =
      fun x => _root_.GD.N0232.N0719.N0993.d020541 (d + 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x /
        _root_.GD.N0232.N0719.N0993.d020540 (d + 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x := by
    funext x
    exact _root_.GD.N0212.N0475.d028986 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x
  rw [hratio]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (show Nonempty (_root_.GD.N0232.N0719.N0982.d020351 ((d + 1) + 2)
      (fun x => _root_.GD.N0232.N0719.N0993.d020541 (d + 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x /
        _root_.GD.N0232.N0719.N0993.d020540 (d + 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)) from
      ⟨_root_.GD.N0232.N0719.N0993.d020546 (d + 1) μ hμ⟩)



theorem d028991
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k),
      _root_.GD.N0232.N0719.N0994.d011375 (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) ∧
      Nonempty (_root_.GD.N0232.N0719.N0982.d020351 ((∑ i, sizes i) + 2)
        (_root_.GD.N0212.N0475.d028983 ((∑ i, sizes i) - 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)))) ∧
      (∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
        _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0989.d011338 →
        _root_.GD.N0212.N0475.d028983 ((∑ i, sizes i) - 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))
          (_root_.GD.N0232.N0719.N0986.d020362 sizes z) = s z) := by
  have hN : 2 ≤ ∑ i, sizes i := (hn 0).trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ 0))
  let d := (∑ i, sizes i) - 1
  have hdim : (∑ i, sizes i) = d + 1 := by dsimp [d]; omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdegree : d + 3 = (∑ i, sizes i) + 2 := by omega
  obtain ⟨μ, hμ, hm, hpost⟩ := _root_.GD.N0212.N0471.d028990 sizes hdim hn hd hs
  refine ⟨μ, hμ, ?_, ?_⟩
  · simpa only [hdegree] using hm
  · have hraw := (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim).quasiMeasurePreserving.ae hpost
    simpa only [_root_.GD.N0232.N0719.N0990.d020512, MeasurableEquiv.symm_apply_apply] using hraw

end
end GD.N0212.N0471

#print axioms _root_.GD.N0212.N0471.d028989
#print axioms _root_.GD.N0212.N0471.d028990
#print axioms _root_.GD.N0212.N0471.d028991
