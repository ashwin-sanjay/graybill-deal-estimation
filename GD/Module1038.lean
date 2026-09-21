import GD.Module0020
import GD.Module1030

















open MeasureTheory
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1132

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0618
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1126

set_option linter.unusedSectionVars false

variable (m n : ℕ) [NeZero m] [NeZero n]
variable {I : Type*} [Fintype I] [DecidableEq I]

private noncomputable local instance d016559 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance



theorem d016560
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (i : I) :
    |_root_.GD.N0232.N0720.N1126.d016414 packet i| ≤ _root_.GD.N0232.N0720.N1126.d016418 packet := by
  unfold _root_.GD.N0232.N0720.N1126.d016414 _root_.GD.N0232.N0720.N1126.d016418
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _ ↦ sq_nonneg ((packet j).location)) (Finset.mem_univ i)



theorem d016561
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight weight' : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    |_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
        _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega| ≤
      2 * _root_.GD.N0232.N0720.N1126.d016418 packet *
        _root_.GD.N0230.N0618.d000191 weight weight'
          (_root_.GD.N0232.N0720.N1126.d016413 packet) omega := by
  exact _root_.GD.N0230.N0618.d000197
    weight weight' (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      (_root_.GD.N0232.N0720.N1126.d016418 packet) hweight hweight'
      (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (Real.sqrt_nonneg _)
      (_root_.GD.N0232.N0720.N1132.d016560 packet) omega



theorem d016562
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight weight' : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i) :
    ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n ≤
      4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        ∑ i, |weight i - weight' i| := by
  exact _root_.GD.N0230.N0618.d000201
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight weight'
      (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      (_root_.GD.N0232.N0720.N1126.d016418 packet) hweight hweight'
      (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (_root_.GD.N0232.N0720.N1126.d016422 packet)
      (Real.sqrt_nonneg _)
      (_root_.GD.N0232.N0720.N1132.d016560 packet)


theorem d016563
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight weight' : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i) :
    ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet weight hweight -
        _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight' hweight'‖ ^ 2 ≤
      4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        ∑ i, |weight i - weight' i| := by
  have hraw := _root_.GD.N0232.N0720.N1132.d016562
    m n packet weight weight' hweight hweight'
  calc
    ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet weight hweight -
        _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight' hweight'‖ ^ 2 =
        ∫ omega,
          (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
            _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        Lp.coeFn_sub
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            packet weight hweight)
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            packet weight' hweight'),
        _root_.GD.N0232.N0720.N1126.d016427 (m := m) (n := n)
          packet weight hweight,
        _root_.GD.N0232.N0720.N1126.d016427 (m := m) (n := n)
          packet weight' hweight'] with
          omega hsub homega homega'
      rw [hsub, Pi.sub_apply, homega, homega']
      simp only [RCLike.inner_apply, conj_trivial, pow_two]
    _ ≤ 4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        ∑ i, |weight i - weight' i| := hraw

end

end N1132
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1132.d016563
