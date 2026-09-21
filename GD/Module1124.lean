import GD.Module1123
import GD.Module1114
import GD.Module1028






















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1077

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1033
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0107
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1502
open _root_.GD.N0232.N0720.N1482

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d018049 : ℝ :=
  ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
    ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2


theorem d018050 :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  intro theta
  apply ne_top_of_le_ne_top _ ((_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).1 theta)
  rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
  exact ENNReal.ofReal_ne_top



theorem d018051
    (g : _root_.GD.N0232.N0720.N1482.d015118)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp =
      _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite := by
  rfl



theorem d018052 :
    ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1077.d018049 m n hm hn := by
  simpa only [_root_.GD.N0232.N0720.N1077.d018049] using
    _root_.GD.N0232.N0720.N1081.d014618 m n hm hn
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn)


theorem d018053 :
    0 ≤ _root_.GD.N0232.N0720.N1077.d018049 m n hm hn := by
  exact le_trans (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1077.d018052 m n hm hn)


theorem d018054 :
    _root_.GD.N0232.N0720.N1077.d018049 m n hm hn = 0 ↔
      _root_.GD.N0232.N0720.N1029.d015364 m n hm hn = _root_.GD.N0232.N0720.N1080.d014191 m n hm hn := by
  constructor
  · intro hzero
    have hsq :
        ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤ 0 := by
      simpa only [hzero] using
        _root_.GD.N0232.N0720.N1077.d018052 m n hm hn
    have hnorm :
        ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ = 0 := by
      nlinarith [norm_nonneg
        (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro heq
    unfold _root_.GD.N0232.N0720.N1077.d018049
    rw [heq]
    exact sub_self _




theorem d018055
    (hmem : _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn) :
    _root_.GD.N0232.N0720.N1029.d015364 m n hm hn = _root_.GD.N0232.N0720.N1080.d014191 m n hm hn := by
  have hbdd : BddBelow
      (Set.range fun w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn ↦
        ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖) := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, rfl⟩
    exact norm_nonneg _
  have hselectorLe :
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ := by
    have hiInfLe :
        (⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖) ≤
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) -
            _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ :=
      ciInf_le hbdd
        ⟨_root_.GD.N0232.N0720.N1080.d014191 m n hm hn, hmem⟩
    rw [← (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).2] at hiInfLe
    simpa only [zero_sub, norm_neg] using hiInfLe
  have htax := _root_.GD.N0232.N0720.N1081.d014618 m n hm hn
    (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn)
  have hsqNorm :
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
    nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn),
      norm_nonneg (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)]
  have hsq :
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤ 0 := by
    linarith
  have hnorm :
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ = 0 := by
    nlinarith [norm_nonneg
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn - _root_.GD.N0232.N0720.N1080.d014191 m n hm hn)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)



theorem d018056 :
    _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ∧
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn := by
  constructor
  · intro hmem
    obtain ⟨hp, hfixed⟩ :=
      (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).1 hmem
    constructor
    · rw [← _root_.GD.N0232.N0720.N1077.d018051 m n hm hn
          _root_.GD.N0232.N0720.N1482.d015130 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) hp
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)]
      exact hfixed _root_.GD.N0232.N0720.N1482.d015130
    · rw [← _root_.GD.N0232.N0720.N1077.d018051 m n hm hn
          _root_.GD.N0232.N0720.N1482.d015131 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) hp
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)]
      exact hfixed _root_.GD.N0232.N0720.N1482.d015131
  · rintro ⟨htwo, hthree⟩
    have hall := _root_.GD.N0232.N0720.N1482.d015167
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) htwo hthree
    refine (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).2
      ⟨(_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).1, ?_⟩
    intro g
    rw [_root_.GD.N0232.N0720.N1077.d018051 m n hm hn g
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).1
      (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)]
    exact hall g



theorem d018057 :
    _root_.GD.N0232.N0720.N1077.d018049 m n hm hn = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ∧
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1077.d018054]
  constructor
  · intro heq
    apply (_root_.GD.N0232.N0720.N1077.d018056
      m n hm hn).1
    rw [← heq]
    exact (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).1
  · intro hfixed
    exact _root_.GD.N0232.N0720.N1077.d018055 m n hm hn
      ((_root_.GD.N0232.N0720.N1077.d018056
        m n hm hn).2 hfixed)



theorem d018058 :
    (_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn ∧
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
          _root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  constructor
  · rintro ⟨htwo, hthree⟩
    exact _root_.GD.N0232.N0720.N1033.d017927 m n
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) htwo hthree
  · intro hchar
    have hall : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
        _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
          (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) =
            _root_.GD.N0232.N0720.N1080.d014191 m n hm hn := by
      intro g
      apply (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1
      intro eta
      let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
      have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
      have heq :
          _root_.GD.N0232.N0720.N1080.d014182 m n eta
              (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
                (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)) =
            _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
        calc
          _root_.GD.N0232.N0720.N1080.d014182 m n eta
              (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
                (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)) =
              _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
                (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
                  (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)) := by rw [heta]
          _ = ENNReal.ofReal (g.d009239 ^ 2) *
                _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) :=
            _root_.GD.N0232.N0720.N1159.d014643 m n g theta
              (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
              (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)
          _ = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
                (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := (hchar g theta).symm
          _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by rw [heta]
      exact heq.le
    exact ⟨hall _root_.GD.N0232.N0720.N1482.d015130, hall _root_.GD.N0232.N0720.N1482.d015131⟩




theorem d018059 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ↔
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
  rw [← _root_.GD.N0232.N0720.N1077.d018058]
  rw [← _root_.GD.N0232.N0720.N1077.d018057]
  constructor
  · intro hzero
    unfold _root_.GD.N0232.N0720.N1077.d018049 at hzero
    linarith
  · intro hle
    have hnonneg := _root_.GD.N0232.N0720.N1077.d018053 m n hm hn
    unfold _root_.GD.N0232.N0720.N1077.d018049 at hnonneg ⊢
    linarith



theorem d018060 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ↔
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 =
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1077.d018059]
  constructor
  · intro hle
    have hnonneg := _root_.GD.N0232.N0720.N1077.d018053 m n hm hn
    unfold _root_.GD.N0232.N0720.N1077.d018049 at hnonneg
    linarith
  · exact fun h ↦ h.le



theorem d018061 :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ↔
      ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 <
        ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 := by
  simpa only [not_le] using not_congr
    (_root_.GD.N0232.N0720.N1077.d018059 m n hm hn)



theorem d018062 :
    _root_.GD.N0232.N0720.N1077.d018049 m n hm hn = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1077.d018057,
    _root_.GD.N0232.N0720.N1077.d018058]
  constructor
  · intro hchar
    apply (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn)).1
    obtain ⟨htwo, hthree⟩ :=
      (_root_.GD.N0232.N0720.N1077.d018058
        m n hm hn).2 hchar
    exact _root_.GD.N0232.N0720.N1482.d015167
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1077.d018050 m n hm hn) htwo hthree
  · exact _root_.GD.N0232.N0720.N1159.d014653
      m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)



theorem d018063 :
    0 < _root_.GD.N0232.N0720.N1077.d018049 m n hm hn ↔
      ¬ _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  constructor
  · intro hpos hrep
    have hzero :=
      (_root_.GD.N0232.N0720.N1077.d018062
        m n hm hn).2 hrep
    linarith
  · intro hnrep
    have hnonneg := _root_.GD.N0232.N0720.N1077.d018053 m n hm hn
    by_contra hnotpos
    have hle : _root_.GD.N0232.N0720.N1077.d018049 m n hm hn ≤ 0 := le_of_not_gt hnotpos
    have hzero : _root_.GD.N0232.N0720.N1077.d018049 m n hm hn = 0 :=
      le_antisymm hle hnonneg
    exact hnrep
      ((_root_.GD.N0232.N0720.N1077.d018062
        m n hm hn).1 hzero)





theorem d018064
    (unrestrictedUpper fixedLower : ℝ)
    (hunrestricted : ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤ unrestrictedUpper)
    (hfixed : fixedLower ≤ ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2)
    (hseparate : unrestrictedUpper < fixedLower) :
    ¬ _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  apply (_root_.GD.N0232.N0720.N1077.d018063
    m n hm hn).1
  unfold _root_.GD.N0232.N0720.N1077.d018049
  linarith



theorem d018065 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n]
  simp only [zero_sub, norm_neg]
  rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
  exact _root_.GD.N0232.N0720.N1077.d018059 m n hm hn



theorem d018066
    (hle : ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hzero : _root_.GD.N0232.N0720.N1077.d018049 m n hm hn = 0 := by
    have hnonneg := _root_.GD.N0232.N0720.N1077.d018053 m n hm hn
    unfold _root_.GD.N0232.N0720.N1077.d018049 at hnonneg ⊢
    linarith
  have heq :=
    (_root_.GD.N0232.N0720.N1077.d018054 m n hm hn).1 hzero
  exact _root_.GD.N0232.N0720.N1148.d018048
    hm hn heq.symm



include hm hn



theorem d018067 :
    _root_.GD.N0232.N0720.N1502.d016364 m n 1 1 =
      1 / (((m + n : ℕ) : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hmn0 : ((m + n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show m + n ≠ 0 by omega)
  unfold _root_.GD.N0232.N0720.N1502.d016364 _root_.GD.N0107.d009046
    _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  norm_num
  field_simp [hm0, hn0, hmn0]
  ring










theorem d018068
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hloc : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu 1 1 one_pos one_pos) p =
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p) :
    1 / (((m + n : ℕ) : ℝ)) ≤ ‖p‖ ^ 2 := by
  let d : _root_.GD.N0232.N0720.N1025.d014303 m n :=
    toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) p
  let cap : ℝ :=
    (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
      (_root_.GD.N0232.N0720.N1078.d016372 0 1 1 one_pos one_pos)).toReal
  have hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := by
    apply (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn d).2
    change p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn
    exact hp
  have hdback :
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d = p := by
    change (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
      (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) p) = p
    rfl
  have hcap : 0 < cap := by
    dsimp only [cap]
    exact ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn _)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn _)
  have hprofile : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 mu 1 1 one_pos one_pos) d =
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal / cap := by
    intro mu
    simp only [_root_.GD.N0232.N0720.N1066.d014327, hd, dite_true, _root_.GD.N0232.N0720.N1066.d014324,
      _root_.GD.N0232.N0720.N1025.d014305, ENNReal.toReal_div]
    rw [hdback]
    rw [hloc mu,
      _root_.GD.N0232.N0720.N1078.d016378
        m n hm hn mu 1 1 one_pos one_pos]
  have hiSupLe :
      (⨆ mu : ℝ,
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 mu 1 1 one_pos one_pos) d) ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal / cap := by
    apply ciSup_le
    intro mu
    exact (hprofile mu).le
  have hminimax :=
    _root_.GD.N0232.N0720.N1078.d016379
      m n hm hn 1 1 one_pos one_pos d hd
  rw [_root_.GD.N0232.N0720.N1078.d016377
    m n hm hn 1 1 one_pos one_pos] at hminimax
  change _root_.GD.N0232.N0720.N1502.d016364 m n 1 1 / cap ≤ _ at hminimax
  have horacle :
      _root_.GD.N0232.N0720.N1502.d016364 m n 1 1 ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal := by
    exact (div_le_div_iff_of_pos_right hcap).1 (hminimax.trans hiSupLe)
  rw [_root_.GD.N0232.N0720.N1077.d018067 m n hm hn] at horacle
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at horacle
  simpa only [zero_sub, norm_neg,
    ENNReal.toReal_ofReal (sq_nonneg ‖p‖)] using horacle



theorem d018069
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    1 / (((m + n : ℕ) : ℝ)) ≤ ‖p‖ ^ 2 := by
  apply _root_.GD.N0232.N0720.N1077.d018068
    m n hm hn p hp
  intro mu
  have h := hchar (_root_.GD.N0232.N0720.N1482.d015128 mu) _root_.GD.N0232.N0720.N1080.d014169
  simpa [_root_.GD.N0232.N0720.N1482.d015128,
    _root_.GD.N0232.N0719.N0946.d009229.d009239,
    _root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1078.d016372, _root_.GD.N0232.N0720.N1080.d014169] using h


theorem d018070 :
    1 / (((m + n : ℕ) : ℝ)) ≤
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1077.d018069
    m n hm hn (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn)
    (_root_.GD.N0232.N0720.N1029.d015370 m n hm hn)

omit hm hn in


theorem d018071 :
    (1 / 4 : ℝ) ≤
      ‖_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)‖ ^ 2 := by
  simpa using _root_.GD.N0232.N0720.N1077.d018070
    2 2 (by omega) (by omega)



theorem d018072
    (hsmall : ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 <
      1 / (((m + n : ℕ) : ℝ))) :
    ¬ (∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu 1 1 one_pos one_pos)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) =
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)) := by
  intro hloc
  have hfloor :=
    _root_.GD.N0232.N0720.N1077.d018068
      m n hm hn (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).1 hloc
  linarith




theorem d018073
    (hsmall : ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 <
      1 / (((m + n : ℕ) : ℝ))) :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  intro hchar
  apply _root_.GD.N0232.N0720.N1077.d018072
    m n hm hn hsmall
  intro mu
  have h := hchar (_root_.GD.N0232.N0720.N1482.d015128 mu) _root_.GD.N0232.N0720.N1080.d014169
  simpa [_root_.GD.N0232.N0720.N1482.d015128,
    _root_.GD.N0232.N0719.N0946.d009229.d009239,
    _root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1078.d016372, _root_.GD.N0232.N0720.N1080.d014169] using h


theorem d018074
    (hsmall : ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 <
      1 / (((m + n : ℕ) : ℝ))) :
    ¬ _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) := by
  exact (_root_.GD.N0232.N0720.N1077.d018063
    m n hm hn).1 <| by
      unfold _root_.GD.N0232.N0720.N1077.d018049
      have hfloor := _root_.GD.N0232.N0720.N1077.d018070
        m n hm hn
      linarith

end

end N1077
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1077.d018052
#print axioms _root_.GD.N0232.N0720.N1077.d018057
#print axioms _root_.GD.N0232.N0720.N1077.d018059
#print axioms _root_.GD.N0232.N0720.N1077.d018061
#print axioms _root_.GD.N0232.N0720.N1077.d018062
#print axioms _root_.GD.N0232.N0720.N1077.d018063
#print axioms _root_.GD.N0232.N0720.N1077.d018064
#print axioms _root_.GD.N0232.N0720.N1077.d018065
#print axioms _root_.GD.N0232.N0720.N1077.d018066
#print axioms _root_.GD.N0232.N0720.N1077.d018068
#print axioms _root_.GD.N0232.N0720.N1077.d018070
#print axioms _root_.GD.N0232.N0720.N1077.d018071
#print axioms _root_.GD.N0232.N0720.N1077.d018072
#print axioms _root_.GD.N0232.N0720.N1077.d018074
