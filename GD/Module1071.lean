import GD.Module0164
import GD.Module1070


















open Filter MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1114

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1057
open _root_.GD.N0232.N0720.N1060
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1499


def d017172
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ _root_.GD.N0232.N0720.N1060.d001880 (s.value omega)
    (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
    (_root_.GD.N0232.N0720.N1126.d016416
      candidate.packet candidate.weight omega)


def d017173
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
    (_root_.GD.N0232.N0720.N1126.d016416
      candidate.packet candidate.weight omega - theta.location) ^ 2


def d017174
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ _root_.GD.N0232.N0720.N1060.d001883 (s.value omega)
    (_root_.GD.N0232.N0720.N1126.d016416
      candidate.packet candidate.weight omega)
    (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega) theta.location



theorem d017175
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    Integrable (_root_.GD.N0232.N0720.N1114.d017172 m n s candidate)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h := _root_.GD.N0230.N0617.d000185
    (_root_.GD.N0232.N0720.N1080.d014172 m n) candidate.weight
    (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet)
    (fun omega ↦ s.value omega) candidate.weight_nonneg
    (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet)
    (_root_.GD.N0232.N0720.N1126.d016420 candidate.packet)
    (_root_.GD.N0232.N0720.N1126.d016421 candidate.packet)
    (Lp.memLp s.value).integrable_sq
    (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
      (candidate.packet i) s.value (s.finiteRisk (candidate.packet i)))
  refine h.congr ?_
  filter_upwards with omega
  rfl



theorem d017176
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Integrable (_root_.GD.N0232.N0720.N1114.d017173 m n candidate theta)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hfinite := _root_.GD.N0232.N0720.N1126.d016428 (m := m) (n := n)
    candidate.packet candidate.weight candidate.weight_nonneg theta
  have h := _root_.GD.N0232.N0720.N1126.d016429 theta
    (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) hfinite
  refine h.congr ?_
  filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
    candidate.packet candidate.weight candidate.weight_nonneg] with omega hu
  unfold _root_.GD.N0232.N0720.N1114.d017173 _root_.GD.N0232.N0720.N1130.d017075
  rw [hu]


theorem d017177
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Integrable (_root_.GD.N0232.N0720.N1114.d017174 m n s candidate theta)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hs := _root_.GD.N0232.N0720.N1126.d016429 theta
    s.value (s.finiteRisk theta)
  have hu := _root_.GD.N0232.N0720.N1114.d017176 m n candidate theta
  have hsub := hs.sub hu
  refine hsub.congr ?_
  filter_upwards with omega
  unfold _root_.GD.N0232.N0720.N1114.d017174 _root_.GD.N0232.N0720.N1114.d017173 _root_.GD.N0232.N0720.N1060.d001883
  simp only [Pi.sub_apply]
  ring



theorem d017178
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (∫ omega, _root_.GD.N0232.N0720.N1114.d017174 m n s candidate theta omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal := by
  have hs := _root_.GD.N0232.N0720.N1126.d016429 theta
    s.value (s.finiteRisk theta)
  have hu := _root_.GD.N0232.N0720.N1114.d017176 m n candidate theta
  have hfinite := _root_.GD.N0232.N0720.N1126.d016428 (m := m) (n := n)
    candidate.packet candidate.weight candidate.weight_nonneg theta
  have hgradient :
      (∫ omega, _root_.GD.N0232.N0720.N1114.d017174 m n s candidate theta omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
            (s.value omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
          ∫ omega, _root_.GD.N0232.N0720.N1114.d017173 m n candidate theta omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← integral_sub hs hu]
    apply integral_congr_ae
    filter_upwards with omega
    unfold _root_.GD.N0232.N0720.N1114.d017174 _root_.GD.N0232.N0720.N1114.d017173 _root_.GD.N0232.N0720.N1060.d001883
    ring
  have henvelope :
      (∫ omega, _root_.GD.N0232.N0720.N1114.d017173 m n candidate theta omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
      candidate.packet candidate.weight candidate.weight_nonneg] with omega hcompletion
    unfold _root_.GD.N0232.N0720.N1114.d017173 _root_.GD.N0232.N0720.N1130.d017075
    rw [hcompletion]
  rw [hgradient, henvelope,
    ← _root_.GD.N0232.N0720.N1126.d016430 theta s.value
      (s.finiteRisk theta),
    ← _root_.GD.N0232.N0720.N1126.d016430 theta
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) hfinite]



theorem d017179
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Integrable (_root_.GD.N0232.N0720.N1114.d017172 m n s candidate)
        (_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      Integrable (_root_.GD.N0232.N0720.N1114.d017174 m n s candidate theta)
        (_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      Integrable (_root_.GD.N0232.N0720.N1114.d017173 m n candidate theta)
        (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  ⟨_root_.GD.N0232.N0720.N1114.d017175 m n s candidate,
    _root_.GD.N0232.N0720.N1114.d017177 m n s candidate theta,
    _root_.GD.N0232.N0720.N1114.d017176 m n candidate theta⟩





theorem d017180
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (hviolation :
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal) :
    ∃ t : ℝ, 0 < t ∧
      (∫ omega,
        _root_.GD.N0232.N0720.N1060.d001882 (s.value omega)
          (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
          (_root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega) theta.location t
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) <
      ∫ omega, _root_.GD.N0232.N0720.N1114.d017172 m n s candidate omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hgradientNeg :
      (∫ omega, _root_.GD.N0232.N0720.N1114.d017174 m n s candidate theta omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) < 0 := by
    rw [_root_.GD.N0232.N0720.N1114.d017178]
    linarith
  exact _root_.GD.N0232.N0720.N1057.d001904
    (_root_.GD.N0232.N0720.N1080.d014172 m n) (fun omega ↦ s.value omega)
    (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight)
    (_root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight)
    (_root_.GD.N0232.N0720.N1499.d015001 m n theta) (fun _omega ↦ theta.location)
    (_root_.GD.N0230.N0617.d000177 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016420 candidate.packet))
    (_root_.GD.N0232.N0720.N1126.d016423
      candidate.packet candidate.weight)
    (_root_.GD.N0232.N0720.N1499.d015002 m n theta) measurable_const
    (Filter.Eventually.of_forall fun omega ↦
      _root_.GD.N0230.N0617.d000169 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
        (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega)
    (Filter.Eventually.of_forall fun omega ↦
      _root_.GD.N0232.N0720.N1499.d015003 m n theta omega)
    (_root_.GD.N0232.N0720.N1114.d017175 m n s candidate)
    (_root_.GD.N0232.N0720.N1114.d017177 m n s candidate theta)
    (_root_.GD.N0232.N0720.N1114.d017176 m n candidate theta)
    hgradientNeg

end

end N1114
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1114.d017179
#print axioms _root_.GD.N0232.N0720.N1114.d017180
