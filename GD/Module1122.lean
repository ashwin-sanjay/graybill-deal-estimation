import GD.Module1120





























open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1145

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1032
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1144
open _root_.GD.N0232.N0720.N1499

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

private noncomputable local instance d018021 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance






def d018022
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
    |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| ≤
      C * (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ / 16)



def d018023
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : Prop :=
  ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
    _root_.GD.N0232.N0720.N1145.d018022 m n hm hn U omega

variable {m n hm hn}
variable {I : Type*} [Fintype I] [DecidableEq I]



theorem d018024
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) {C : ℝ} (hC : 0 ≤ C)
    (henvelope : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| ≤
        C * (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ / 16))
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    |_root_.GD.N0232.N0720.N1126.d016416 packet weight omega| ≤
      C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight := by
  have hmass := _root_.GD.N0230.N0617.d000168
    weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hmassPos : 0 < _root_.GD.N0230.N0617.d000163 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) omega :=
    lt_of_lt_of_le zero_lt_one hmass
  have hmoment :
      |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega| ≤
        C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight := by
    calc
      |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega| ≤
          ∑ i, |weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
            _root_.GD.N0232.N0720.N1126.d016414 packet i| := by
              unfold _root_.GD.N0230.N0617.d000164
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, weight i *
          (C * (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U
            (packet i).scale₁ (packet i).scale₂ / 16)) := by
              apply Finset.sum_le_sum
              intro i hi
              unfold _root_.GD.N0232.N0720.N1126.d016413 _root_.GD.N0232.N0720.N1126.d016414
              rw [abs_mul, abs_mul, abs_of_nonneg (hweight i)]
              rw [abs_of_nonneg
                (_root_.GD.N0232.N0720.N1499.d015003 m n (packet i) omega)]
              have henv := henvelope (packet i)
              rw [abs_mul, abs_of_nonneg
                (_root_.GD.N0232.N0720.N1499.d015003 m n (packet i) omega)] at henv
              simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left henv (hweight i))
      _ = C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight := by
              unfold _root_.GD.N0232.N0720.N1144.d018001
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
  unfold _root_.GD.N0232.N0720.N1126.d016416 _root_.GD.N0230.N0617.d000166
  rw [abs_div, abs_of_pos hmassPos]
  apply (div_le_iff₀ hmassPos).2
  have hcharge : 0 ≤ C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight :=
    mul_nonneg hC
      (_root_.GD.N0232.N0720.N1144.d018002 U packet weight hweight)
  calc
    |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega| ≤
        C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight := hmoment
    _ ≤ (C * _root_.GD.N0232.N0720.N1144.d018001 U packet weight) *
        _root_.GD.N0230.N0617.d000163 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) omega := by
          nlinarith

variable {Irow : ℕ → Type*}
variable [∀ j, Fintype (Irow j)] [∀ j, DecidableEq (Irow j)]



theorem d018025
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (henvelope : _root_.GD.N0232.N0720.N1145.d018022
      m n hm hn U omega)
    (packet : ∀ j, Irow j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Irow j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hcharge : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1144.d018001 U (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416 (packet j) (weight j) omega)
      atTop (nhds 0) := by
  obtain ⟨C, hC, henvelope⟩ := henvelope
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero (fun j ↦ abs_nonneg _)
    (fun j ↦ _root_.GD.N0232.N0720.N1145.d018024
      U omega hC henvelope (packet j) (weight j) (hweight j))
  simpa only [mul_zero] using (tendsto_const_nhds.mul hcharge :
    Tendsto
      (fun j ↦ C * _root_.GD.N0232.N0720.N1144.d018001 U (packet j) (weight j))
      atTop (nhds (C * 0)))








theorem d018026
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (henvelope : _root_.GD.N0232.N0720.N1145.d018023 m n hm hn U)
    (packet : ∀ j, Irow j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Irow j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) :
    ¬ Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          (packet j) (weight j)) atTop (nhds 0) := by
  intro htight
  have hcharge :=
    _root_.GD.N0232.N0720.N1144.d018009
      U packet weight hweight htight
  have hrawAE : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416
          (packet j) (weight j) omega) atTop (nhds 0) := by
    filter_upwards [henvelope] with omega homega
    exact _root_.GD.N0232.N0720.N1145.d018025
      U omega homega packet weight hweight hcharge
  have hrawMeasure : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416 (packet j) (weight j))
      atTop (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun j ↦
        (_root_.GD.N0232.N0720.N1126.d016423
          (packet j) (weight j)).aestronglyMeasurable)
    simpa only [Pi.zero_apply] using hrawAE
  have hL2 :=
    _root_.GD.N0232.N0720.N1032.d017955
      (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
      (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U)
      (_root_.GD.N0232.N0720.N1144.d017997 m n hm hn U)
      packet weight hweight htight
  have hclassMeasure : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j))
      atTop (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U) :=
    tendstoInMeasure_of_tendsto_Lp hL2
  have hrawToCandidate : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416 (packet j) (weight j))
      atTop (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U) := by
    exact TendstoInMeasure.congr
      (fun j ↦
        (_root_.GD.N0232.N0720.N1126.d016427
          (m := m) (n := n) (packet j) (weight j) (hweight j)))
      Filter.EventuallyEq.rfl hclassMeasure
  have hzero : _root_.GD.N0232.N0720.N1144.d017996 m n hm hn U =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      (fun _ ↦ (0 : ℝ)) :=
    tendstoInMeasure_ae_unique hrawToCandidate hrawMeasure
  have hrep :=
    _root_.GD.N0232.N0720.N1082.d015396
      m n hm hn U (5 / 4)
  apply _root_.GD.N0232.N0720.N1054.d016443
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U) hrep 0
  filter_upwards [hzero] with omega homega
  rw [homega]
  simp

end

end N1145
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1145.d018024
#print axioms _root_.GD.N0232.N0720.N1145.d018026
