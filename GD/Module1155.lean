import GD.Module1072
import GD.Module1137
import GD.Module1154































open Filter MeasureTheory Topology
open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1120

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0619
open _root_.GD.N0233.N0725
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1119
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1447
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1482





def d018526
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ∫ omega,
    (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega - 1) *
      (q omega - _root_.GD.N0232.N0720.N1126.d016416
        candidate.packet candidate.weight omega) ^ 2
    ∂_root_.GD.N0232.N0720.N1080.d014172 m n


theorem d018527
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1120.d018526 m n candidate q := by
  unfold _root_.GD.N0232.N0720.N1120.d018526
  apply integral_nonneg
  intro omega
  have hmass : 1 ≤
      _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega := by
    simpa only [_root_.GD.N0232.N0720.N1126.d016415] using
      (_root_.GD.N0230.N0617.d000168 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
        (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega)
  exact mul_nonneg (sub_nonneg.mpr hmass) (sq_nonneg _)






theorem d018528
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate q =
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ ^ 2 +
        _root_.GD.N0232.N0720.N1120.d018526 m n candidate q := by
  let weighted : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦
    _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
      (q omega - _root_.GD.N0232.N0720.N1126.d016416
        candidate.packet candidate.weight omega) ^ 2
  let plain : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦
    (q omega - _root_.GD.N0232.N0720.N1126.d016416
      candidate.packet candidate.weight omega) ^ 2
  let active : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦
    (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega - 1) *
      (q omega - _root_.GD.N0232.N0720.N1126.d016416
        candidate.packet candidate.weight omega) ^ 2
  have hweighted : Integrable weighted (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
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
  have hplain : Integrable plain (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply Integrable.mono' hweighted
    · exact ((Lp.aestronglyMeasurable q).aemeasurable.sub
        (_root_.GD.N0232.N0720.N1126.d016423
          candidate.packet candidate.weight).aemeasurable).pow_const 2
          |>.aestronglyMeasurable
    · filter_upwards with omega
      have hsq : 0 ≤ plain omega := sq_nonneg _
      have hmass : 1 ≤
          _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega := by
        simpa only [_root_.GD.N0232.N0720.N1126.d016415] using
          (_root_.GD.N0230.N0617.d000168 candidate.weight
            (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
            (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega)
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      simpa only [weighted, plain, one_mul] using
        (mul_le_mul_of_nonneg_right hmass hsq)
  have hactive : Integrable active (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply (hweighted.sub hplain).congr
    filter_upwards with omega
    change weighted omega - plain omega = active omega
    dsimp only [weighted, plain, active]
    ring
  rw [_root_.GD.N0232.N0720.N1131.d017157]
  change (∫ omega, weighted omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
    (∫ omega, plain omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
      ∫ omega, active omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n
  rw [← integral_add hplain hactive]
  apply integral_congr_ae
  filter_upwards with omega
  dsimp only [weighted, plain, active]
  ring_nf














theorem d018529
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) (decision : ℝ) :
    _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
        _root_.GD.N0230.N0619.d000388 candidate.weight
          (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
          (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega decision =
      (decision - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2 +
        (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega - 1) *
          (decision - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2 +
        (_root_.GD.N0230.N0617.d000165 candidate.weight
            (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
            (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega -
          _root_.GD.N0230.N0617.d000167 candidate.weight
            (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
            (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega) := by
  have hmass : _root_.GD.N0230.N0617.d000163 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega).ne'
  rw [show _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega =
      _root_.GD.N0230.N0617.d000163 candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
        omega by rfl,
    show _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight omega =
      _root_.GD.N0230.N0617.d000166 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet)
        omega by rfl]
  rw [_root_.GD.N0233.N0725.d003188
    candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega decision]
  rw [_root_.GD.N0230.N0619.d000395
    candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega decision hmass]
  ring






def d018530
    (m n : ℕ)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017154 m n scaleTwo
      (_root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base)) +
    _root_.GD.N0232.N0720.N1131.d017154 m n shiftOneScaleThree
      (_root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))

theorem d018531
    (m n : ℕ)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1120.d018530 m n base scaleTwo shiftOneScaleThree := by
  exact add_nonneg
    (_root_.GD.N0232.N0720.N1131.d017156 m n scaleTwo _)
    (_root_.GD.N0232.N0720.N1131.d017156 m n shiftOneScaleThree _)




theorem d018532
    (m n : ℕ)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1130.d017074) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n scaleTwo -
        _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n base)‖ ^ 2 +
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n shiftOneScaleThree -
        _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n base)‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1120.d018530 m n base scaleTwo shiftOneScaleThree := by
  let r := _root_.GD.N0232.N0720.N1130.d017075 m n base
  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
    exact _root_.GD.N0232.N0720.N1126.d016428
      base.packet base.weight base.weight_nonneg
  have hscaleFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015228 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158 _root_.GD.N0232.N0720.N1482.d015130 r hrFinite
  have hshiftFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015229 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158
      _root_.GD.N0232.N0720.N1482.d015131 r hrFinite
  have hscale :=
    _root_.GD.N0232.N0720.N1121.d018304
      m n scaleTwo (_root_.GD.N0232.N0720.N1146.d015228 m n r) hscaleFinite
  have hshift :=
    _root_.GD.N0232.N0720.N1121.d018304
      m n shiftOneScaleThree
        (_root_.GD.N0232.N0720.N1146.d015229 m n r) hshiftFinite
  exact add_le_add hscale hshift





theorem d018533
    (m n : ℕ)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1120.d018530 m n base scaleTwo shiftOneScaleThree =
      (‖_root_.GD.N0232.N0720.N1130.d017075 m n scaleTwo -
          _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n base)‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n shiftOneScaleThree -
          _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n base)‖ ^ 2) +
      (_root_.GD.N0232.N0720.N1120.d018526 m n scaleTwo
          (_root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n base)) +
        _root_.GD.N0232.N0720.N1120.d018526 m n shiftOneScaleThree
          (_root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n base))) := by
  let r := _root_.GD.N0232.N0720.N1130.d017075 m n base
  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
    exact _root_.GD.N0232.N0720.N1126.d016428
      base.packet base.weight base.weight_nonneg
  have hscaleFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015228 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158 _root_.GD.N0232.N0720.N1482.d015130 r hrFinite
  have hshiftFinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015229 m n r) := by
    change _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) r)
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) r hrFinite]
    exact _root_.GD.N0232.N0720.N1482.d015158
      _root_.GD.N0232.N0720.N1482.d015131 r hrFinite
  have hscale :=
    _root_.GD.N0232.N0720.N1120.d018528
      m n scaleTwo (_root_.GD.N0232.N0720.N1146.d015228 m n r) hscaleFinite
  have hshift :=
    _root_.GD.N0232.N0720.N1120.d018528
      m n shiftOneScaleThree
        (_root_.GD.N0232.N0720.N1146.d015229 m n r) hshiftFinite
  unfold _root_.GD.N0232.N0720.N1120.d018530
  rw [hscale, hshift]
  ring






def d018534 : Prop :=
  ∃ base : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268,
    ∃ scaleTwo shiftOneScaleThree :
        ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base scaleTwo)
        atTop (nhds 0) ∧
      Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base
          shiftOneScaleThree)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1120.d018530 2 2 (base.candidate j)
          (scaleTwo j) (shiftOneScaleThree j))
        atTop (nhds 0)



theorem d018535
    (h : _root_.GD.N0232.N0720.N1120.d018534) :
    _root_.GD.N0232.N0720.N1447.d018518 := by
  rcases h with
    ⟨base, scaleTwo, shiftOneScaleThree,
      hscaleReserve, hshiftReserve, htax⟩
  let mismatchEnergy : ℕ → ℝ := fun j ↦
    ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo j) -
        _root_.GD.N0232.N0720.N1146.d015228 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖ ^ 2 +
      ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree j) -
        _root_.GD.N0232.N0720.N1146.d015229 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖ ^ 2
  have hmismatchEnergy : Tendsto mismatchEnergy atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun j ↦ ?_) htax
    simpa only [mismatchEnergy] using
      (_root_.GD.N0232.N0720.N1120.d018532
        2 2 (base.candidate j) (scaleTwo j) (shiftOneScaleThree j))
  have hscaleSq : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo j) -
          _root_.GD.N0232.N0720.N1146.d015228 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖ ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ sq_nonneg _) (fun j ↦ ?_)
      hmismatchEnergy
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hshiftSq : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree j) -
          _root_.GD.N0232.N0720.N1146.d015229 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖ ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ sq_nonneg _) (fun j ↦ ?_)
      hmismatchEnergy
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hscale : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo j) -
          _root_.GD.N0232.N0720.N1146.d015228 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
      atTop (nhds 0) := by
    have hsqrt := hscaleSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  have hshift : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree j) -
          _root_.GD.N0232.N0720.N1146.d015229 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
      atTop (nhds 0) := by
    have hsqrt := hshiftSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact ⟨base, scaleTwo, shiftOneScaleThree,
    hscaleReserve, hshiftReserve, hscale, hshift⟩



theorem d018536
    (h : _root_.GD.N0232.N0720.N1120.d018534) :
    _root_.GD.N0232.N0720.N1448.d018480 := by
  exact _root_.GD.N0232.N0720.N1447.d018519
    (_root_.GD.N0232.N0720.N1120.d018535 h)



theorem d018537
    (h : _root_.GD.N0232.N0720.N1120.d018534) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1448.d018484
    (_root_.GD.N0232.N0720.N1120.d018536 h)

end

end N1120
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1120.d018528
#print axioms _root_.GD.N0232.N0720.N1120.d018529
#print axioms _root_.GD.N0232.N0720.N1120.d018532
#print axioms _root_.GD.N0232.N0720.N1120.d018533
#print axioms _root_.GD.N0232.N0720.N1120.d018535
#print axioms _root_.GD.N0232.N0720.N1120.d018536
#print axioms _root_.GD.N0232.N0720.N1120.d018537
