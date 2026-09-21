import GD.Module0164
import GD.Module1140
import GD.Module1071











open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1059

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1057
open _root_.GD.N0232.N0720.N1058
open _root_.GD.N0232.N0720.N1060
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1114
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1499



def d018354
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0720.N1130.d017074 where
  width := candidate.width + 1
  packet := Fin.cons theta candidate.packet
  weight := Fin.cons t candidate.weight
  weight_nonneg := Fin.cases ht candidate.weight_nonneg


theorem d018355
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight omega =
      _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega +
        t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega := by
  unfold _root_.GD.N0232.N0720.N1126.d016415 _root_.GD.N0232.N0720.N1126.d016413 _root_.GD.N0230.N0617.d000163
  change
    1 + ∑ x : Fin (candidate.width + 1),
        (Fin.cons t candidate.weight : Fin (candidate.width + 1) → ℝ) x *
          _root_.GD.N0232.N0720.N1499.d015001 m n
            ((Fin.cons theta candidate.packet :
              Fin (candidate.width + 1) → _root_.GD.N0232.N0720.N1080.d014168) x) omega =
      1 + ∑ x : Fin candidate.width,
        candidate.weight x *
          _root_.GD.N0232.N0720.N1499.d015001 m n (candidate.packet x) omega +
            t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring



theorem d018356
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight
        (_root_.GD.N0232.N0720.N1126.d016413
          (m := m) (n := n)
          (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet)
        (_root_.GD.N0232.N0720.N1126.d016414
          (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet) omega =
      _root_.GD.N0230.N0617.d000164 candidate.weight
          (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) candidate.packet)
          (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega +
        t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location := by
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0232.N0720.N1126.d016413 _root_.GD.N0232.N0720.N1126.d016414
  change
    (∑ x : Fin (candidate.width + 1),
      (Fin.cons t candidate.weight : Fin (candidate.width + 1) → ℝ) x *
          _root_.GD.N0232.N0720.N1499.d015001 m n
            ((Fin.cons theta candidate.packet :
              Fin (candidate.width + 1) → _root_.GD.N0232.N0720.N1080.d014168) x) omega *
        ((Fin.cons theta candidate.packet :
          Fin (candidate.width + 1) → _root_.GD.N0232.N0720.N1080.d014168) x).location) =
      (∑ x : Fin candidate.width,
        candidate.weight x *
            _root_.GD.N0232.N0720.N1499.d015001 m n (candidate.packet x) omega *
          (candidate.packet x).location) +
        t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring



theorem d018357
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t)
    (seed : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight omega *
      (seed omega - _root_.GD.N0232.N0720.N1126.d016416
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight omega) ^ 2 =
    _root_.GD.N0232.N0720.N1060.d001882 (seed omega)
      (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
      (_root_.GD.N0232.N0720.N1126.d016416
        candidate.packet candidate.weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega) theta.location t := by
  have hmass : 0 < _root_.GD.N0232.N0720.N1126.d016415
      candidate.packet candidate.weight omega :=
    _root_.GD.N0230.N0617.d000169 candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
      candidate.weight_nonneg (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega
  have hlikelihood : 0 ≤ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega :=
    _root_.GD.N0232.N0720.N1499.d015003 m n theta omega
  have hnewMass : 0 <
      _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega +
        t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega := by positivity
  have hcompletion :
      _root_.GD.N0232.N0720.N1126.d016416
          (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet
          (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight omega =
        _root_.GD.N0232.N0720.N1060.d001881
          (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
          (_root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega) theta.location t := by
    change
      _root_.GD.N0230.N0617.d000164
            (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight
            (_root_.GD.N0232.N0720.N1126.d016413
              (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet)
            (_root_.GD.N0232.N0720.N1126.d016414
              (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415
            (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).packet
            (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht).weight omega =
        (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
              (_root_.GD.N0230.N0617.d000164 candidate.weight
                  (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
                  (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega /
                _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega) +
            t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location) /
          (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega +
            t * _root_.GD.N0232.N0720.N1499.d015001 m n theta omega)
    rw [_root_.GD.N0232.N0720.N1059.d018356,
      _root_.GD.N0232.N0720.N1059.d018355]
    field_simp [hmass.ne', hnewMass.ne'] <;> ring
  rw [_root_.GD.N0232.N0720.N1059.d018355, hcompletion]
  unfold _root_.GD.N0232.N0720.N1060.d001882 _root_.GD.N0232.N0720.N1060.d001881
  field_simp [hnewMass.ne'] <;> ring


theorem d018358
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1131.d017154 m n
        (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht) q =
      ∫ omega, _root_.GD.N0232.N0720.N1060.d001882 (q omega)
        (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
        (_root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega) theta.location t
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  unfold _root_.GD.N0232.N0720.N1131.d017154
  apply integral_congr_ae
  filter_upwards with omega
  exact _root_.GD.N0232.N0720.N1059.d018357
    m n candidate theta t ht (fun omega ↦ q omega) omega








theorem d018359
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∃ (theta : _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ) (ht : 0 ≤ t),
      0 < t ∧
        _root_.GD.N0232.N0720.N1131.d017154 m n
            (_root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht) s.value <
          _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  obtain ⟨theta, hviolation⟩ :=
    _root_.GD.N0232.N0720.N1058.d018349 m n s candidate
  obtain ⟨t, ht, hdescent⟩ :=
    _root_.GD.N0232.N0720.N1114.d017180
      m n s candidate theta hviolation
  refine ⟨theta, t, ht.le, ht, ?_⟩
  rw [_root_.GD.N0232.N0720.N1059.d018358
    m n candidate theta t ht.le s.value]
  simpa [_root_.GD.N0232.N0720.N1114.d017172, _root_.GD.N0232.N0720.N1060.d001880,
    _root_.GD.N0232.N0720.N1131.d017154] using hdescent

end

end N1059
end N0720
end N0232
end GD
