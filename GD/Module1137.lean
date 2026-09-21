import GD.Module1070
import GD.Module1135

















open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1121

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1210
open _root_.GD.N0232.N0720.N1482










theorem d018304
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate q := by
  have hweighted : Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact _root_.GD.N0230.N0617.d000185
      (_root_.GD.N0232.N0720.N1080.d014172 m n) candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet)
      (fun omega ↦ q omega) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016420 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016421 candidate.packet)
      (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (candidate.packet i) q (hqFinite (candidate.packet i)))
  have hplain : Integrable
      (fun omega ↦
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply Integrable.mono' hweighted
    · exact ((Lp.aestronglyMeasurable q).aemeasurable.sub
        (_root_.GD.N0232.N0720.N1126.d016423
          candidate.packet candidate.weight).aemeasurable).pow_const 2
          |>.aestronglyMeasurable
    · filter_upwards with omega
      have hsq : 0 ≤
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2 := sq_nonneg _
      have hmass := _root_.GD.N0230.N0617.d000168 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
        (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      simpa only [one_mul, _root_.GD.N0232.N0720.N1126.d016415] using
        (mul_le_mul_of_nonneg_right hmass hsq)
  have hmono :
      (∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      ∫ omega,
        _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_mono hplain hweighted
    intro omega
    have hsq : 0 ≤
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2 := sq_nonneg _
    have hmass := _root_.GD.N0230.N0617.d000168 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega
    simpa only [one_mul, _root_.GD.N0232.N0720.N1126.d016415] using
      (mul_le_mul_of_nonneg_right hmass hsq)
  rw [_root_.GD.N0232.N0720.N1131.d017157]
  simpa only [_root_.GD.N0232.N0720.N1131.d017154] using hmono





def d018305
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017154 m n candidate
      (_root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)) +
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate
      (_root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate))

theorem d018306
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1121.d018305 m n candidate := by
  exact add_nonneg
    (_root_.GD.N0232.N0720.N1131.d017156 m n candidate _)
    (_root_.GD.N0232.N0720.N1131.d017156 m n candidate _)



theorem d018307
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ≤
      _root_.GD.N0232.N0720.N1121.d018305 m n candidate := by
  let r := _root_.GD.N0232.N0720.N1130.d017075 m n candidate
  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
    exact _root_.GD.N0232.N0720.N1126.d016428
      candidate.packet candidate.weight candidate.weight_nonneg
  have htwoFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015228 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158 _root_.GD.N0232.N0720.N1482.d015130 r hrFinite
  have hthreeFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015229 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158
      _root_.GD.N0232.N0720.N1482.d015131 r hrFinite
  have htwo :=
    _root_.GD.N0232.N0720.N1121.d018304
      m n candidate (_root_.GD.N0232.N0720.N1146.d015228 m n r) htwoFinite
  have hthree :=
    _root_.GD.N0232.N0720.N1121.d018304
      m n candidate
        (_root_.GD.N0232.N0720.N1146.d015229 m n r) hthreeFinite
  unfold _root_.GD.N0232.N0720.N1122.d017962
    _root_.GD.N0232.N0720.N1121.d018305
  change
    ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ ^ 2 ≤ _
  rw [norm_sub_rev (_root_.GD.N0232.N0720.N1146.d015228 m n r) r,
    norm_sub_rev (_root_.GD.N0232.N0720.N1146.d015229 m n r) r]
  exact add_le_add htwo hthree





def d018308
    {width : ℕ} (packet : Fin width → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : Fin width → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1130.d017074 where
  width := width
  packet := packet
  weight := weight
  weight_nonneg := hweight


def d018309
    (m n : ℕ) {width : ℕ} (packet : Fin width → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : Fin width → ℝ) (hweight : ∀ i, 0 ≤ weight i) : ℝ :=
  _root_.GD.N0232.N0720.N1121.d018305 m n
    (_root_.GD.N0232.N0720.N1121.d018308 packet weight hweight)







theorem d018310
    {m n : ℕ} {width : ℕ → ℕ}
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (D : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hproduction : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1121.d018309 m n
        (packet j) (weight j) (hweight j) ≤ D j) :
    ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)) ≤ D j := by
  intro j
  have hresidual :
      _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (packet j) (weight j) (hweight j)) ≤
        _root_.GD.N0232.N0720.N1121.d018309 m n
          (packet j) (weight j) (hweight j) := by
    exact _root_.GD.N0232.N0720.N1121.d018307
      m n (_root_.GD.N0232.N0720.N1121.d018308 (packet j) (weight j) (hweight j))
  exact (mul_le_mul_of_nonneg_left hresidual hkappa).trans (hproduction j)





theorem d018311
    {width : ℕ → ℕ}
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 2 2
            _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432
            _root_.GD.N0232.N0720.N1302.d018268
              (packet j) (weight j))
      atTop (nhds 0))
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1121.d018309 2 2
        (packet j) (weight j) (hweight j) ≤ D j) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1210.d018278
    packet weight hweight htight C D htower hC hD hkappa
  exact _root_.GD.N0232.N0720.N1121.d018310
    packet weight hweight D hkappa.le hproduction

end

end N1121
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1121.d018304
#print axioms _root_.GD.N0232.N0720.N1121.d018307
#print axioms _root_.GD.N0232.N0720.N1121.d018310
#print axioms _root_.GD.N0232.N0720.N1121.d018311
