import GD.Module1040
import GD.Module1077
import GD.Module1110
import Mathlib.Tactic































open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1095

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0606
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1450

variable {m n : ℕ}







def d017841
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
      (packet N) (weight N) candidate -
    _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
      (packet N) (weight N)



def d017842
    (weight : (N : ℕ) → Fin N → ℝ) (N : ℕ) : ℝ :=
  1 + ∑ i, weight N i



def d017843
    (weight : (N : ℕ) → Fin N → ℝ) (N : ℕ) : ℝ :=
  1 / _root_.GD.N0232.N0720.N1095.d017842 weight N

theorem d017844
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i) (N : ℕ) :
    0 < _root_.GD.N0232.N0720.N1095.d017842 weight N := by
  have hsum : 0 ≤ ∑ i, weight N i :=
    Finset.sum_nonneg fun i _ ↦ hweight N i
  unfold _root_.GD.N0232.N0720.N1095.d017842
  linarith

theorem d017845
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i) (N : ℕ) :
    0 < _root_.GD.N0232.N0720.N1095.d017843 weight N := by
  unfold _root_.GD.N0232.N0720.N1095.d017843
  exact one_div_pos.mpr
    (_root_.GD.N0232.N0720.N1095.d017844 weight hweight N)



def d017846
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1095.d017843 weight N *
    _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N




theorem d017847
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i) (N : ℕ) :
    _root_.GD.N0232.N0720.N1095.d017846
        candidate packet weight N /
      _root_.GD.N0232.N0720.N1095.d017843 weight N =
        _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by
  unfold _root_.GD.N0232.N0720.N1095.d017846
  exact mul_div_cancel_left₀ _ <|
    ne_of_gt (_root_.GD.N0232.N0720.N1095.d017845 weight hweight N)












theorem d017848
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i)
    (hdefect : _root_.GD.N0230.N0606.d000961
      (_root_.GD.N0232.N0720.N1095.d017841 candidate packet weight)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) candidate := by
  intro e he
  by_contra hne
  have heFinite : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1111.d016607
      m n hcandidate he
  let d : ℝ := ‖e - candidate‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let epsilon : ℝ := (d / 4) ^ 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨N, hsmall⟩ := hdefect epsilon hepsilon
  have hsmallN := hsmall N le_rfl
  have hdefectUpper :
      _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N < epsilon :=
    lt_of_le_of_lt (le_abs_self _) hsmallN
  let completion : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1126.d016426 (packet N) (weight N) (hweight N)
  have hcandidateSq : ‖candidate - completion‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by
    have hbound := _root_.GD.N0232.N0720.N1125.d017259
      (m := m) (n := n) (packet N) (weight N) (hweight N)
      candidate (fun i ↦ hcandidate (packet N i))
    rw [_root_.GD.N0232.N0720.N1125.d017257
      (m := m) (n := n) (packet N) (weight N) (hweight N)] at hbound
    simpa only [completion, _root_.GD.N0232.N0720.N1095.d017841] using hbound
  have href : ‖e‖ ^ 2 ≤ ‖candidate‖ ^ 2 := by
    have hrefReal :=
      (ENNReal.toReal_le_toReal
        (heFinite _root_.GD.N0232.N0720.N1080.d014169)
        (hcandidate _root_.GD.N0232.N0720.N1080.d014169)).2 (he _root_.GD.N0232.N0720.N1080.d014169)
    have hriskToNorm (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q).toReal = ‖q‖ ^ 2 := by
      rw [_root_.GD.N0232.N0720.N1080.d014190]
      simp only [zero_sub, norm_neg,
        ENNReal.toReal_ofReal (sq_nonneg ‖q‖)]
    rw [hriskToNorm e, hriskToNorm candidate] at hrefReal
    exact hrefReal
  have hpacket : ∀ i : Fin N,
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet N i) e).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet N i) candidate).toReal := by
    intro i
    exact
      (ENNReal.toReal_le_toReal
        (heFinite (packet N i))
        (hcandidate (packet N i))).2 (he (packet N i))
  have hobjective :
      _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
          (packet N) (weight N) e ≤
        _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
          (packet N) (weight N) candidate := by
    unfold _root_.GD.N0232.N0720.N1125.d017249
    exact add_le_add href <|
      Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hpacket i) (hweight N i)
  have heSq : ‖e - completion‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by
    have hbound := _root_.GD.N0232.N0720.N1125.d017259
      (m := m) (n := n) (packet N) (weight N) (hweight N)
      e (fun i ↦ heFinite (packet N i))
    rw [_root_.GD.N0232.N0720.N1125.d017257
      (m := m) (n := n) (packet N) (weight N) (hweight N)] at hbound
    calc
      ‖e - completion‖ ^ 2 ≤
          _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
              (packet N) (weight N) e -
            _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
              (packet N) (weight N) := by
        simpa only [completion] using hbound
      _ ≤ _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
              (packet N) (weight N) candidate -
            _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
              (packet N) (weight N) :=
        sub_le_sub_right hobjective _
      _ = _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := rfl
  have hcandidateNorm : ‖candidate - completion‖ < d / 4 := by
    have hsquare := lt_of_le_of_lt hcandidateSq hdefectUpper
    change ‖candidate - completion‖ ^ 2 < (d / 4) ^ 2 at hsquare
    have hd4 : 0 < d / 4 := by positivity
    nlinarith [norm_nonneg (candidate - completion)]
  have heNorm : ‖e - completion‖ < d / 4 := by
    have hsquare := lt_of_le_of_lt heSq hdefectUpper
    change ‖e - completion‖ ^ 2 < (d / 4) ^ 2 at hsquare
    have hd4 : 0 < d / 4 := by positivity
    nlinarith [norm_nonneg (e - completion)]
  have htriangle : d ≤
      ‖e - completion‖ + ‖candidate - completion‖ := by
    dsimp only [d]
    calc
      ‖e - candidate‖ =
          ‖(e - completion) + (completion - candidate)‖ := by
        congr 1
        module
      _ ≤ ‖e - completion‖ + ‖completion - candidate‖ :=
        norm_add_le (e - completion) (completion - candidate)
      _ = ‖e - completion‖ + ‖candidate - completion‖ := by
        rw [norm_sub_rev completion candidate]
  linarith




theorem d017849
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i)
    (hscaled : _root_.GD.N0230.N0606.d000961 (fun N ↦
      _root_.GD.N0232.N0720.N1095.d017846
          candidate packet weight N /
        _root_.GD.N0232.N0720.N1095.d017843 weight N)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) candidate := by
  apply _root_.GD.N0232.N0720.N1095.d017848
    candidate hcandidate packet weight hweight
  intro epsilon hepsilon
  obtain ⟨N, hsmall⟩ := hscaled epsilon hepsilon
  refine ⟨N, ?_⟩
  intro k hk
  simpa only [_root_.GD.N0232.N0720.N1095.d017847
    candidate packet weight hweight k] using hsmall k hk



def d017850 (N : ℕ) : Fin N → _root_.GD.N0232.N0720.N1080.d014168 :=
  fun i ↦ _root_.GD.N0232.N0720.N1133.d016566 i


def d017851 (N : ℕ) : Fin N → ℝ :=
  fun _ ↦ 1


def d017852
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
      (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N) candidate -
    _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
      (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N)



def d017853 (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1095.d017843 _root_.GD.N0232.N0720.N1095.d017851 N


theorem d017854 (N : ℕ) :
    _root_.GD.N0232.N0720.N1095.d017853 N = 1 / (N + 1 : ℝ) := by
  simp [_root_.GD.N0232.N0720.N1095.d017853, _root_.GD.N0232.N0720.N1095.d017843,
    _root_.GD.N0232.N0720.N1095.d017842, _root_.GD.N0232.N0720.N1095.d017851, add_comm]

theorem d017855 (N : ℕ) :
    0 < _root_.GD.N0232.N0720.N1095.d017853 N := by
  exact _root_.GD.N0232.N0720.N1095.d017845
    _root_.GD.N0232.N0720.N1095.d017851 (by intro k i; simp [_root_.GD.N0232.N0720.N1095.d017851]) N



def d017856
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1095.d017853 N * _root_.GD.N0232.N0720.N1095.d017852 candidate N



theorem d017857
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (N : ℕ) :
    _root_.GD.N0232.N0720.N1095.d017856 candidate N /
        _root_.GD.N0232.N0720.N1095.d017853 N =
      _root_.GD.N0232.N0720.N1095.d017852 candidate N := by
  unfold _root_.GD.N0232.N0720.N1095.d017856
  exact mul_div_cancel_left₀ _ (ne_of_gt (_root_.GD.N0232.N0720.N1095.d017855 N))



theorem d017858
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate) (N : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1095.d017852 candidate N := by
  rw [_root_.GD.N0232.N0720.N1095.d017852,
    _root_.GD.N0232.N0720.N1125.d017255
      (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N)
      (by intro i; simp [_root_.GD.N0232.N0720.N1095.d017851]) candidate
      (fun i ↦ hcandidate (_root_.GD.N0232.N0720.N1095.d017850 N i))]
  have hI : 0 ≤ ∫ omega,
      _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N) omega *
        (candidate omega -
          _root_.GD.N0232.N0720.N1126.d016416
            (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N) omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
    integral_nonneg fun omega ↦
      mul_nonneg
        (zero_le_one.trans
          (_root_.GD.N0230.N0617.d000168 (_root_.GD.N0232.N0720.N1095.d017851 N)
            (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1095.d017850 N))
            (by intro i; simp [_root_.GD.N0232.N0720.N1095.d017851])
            (_root_.GD.N0232.N0720.N1126.d016419 (_root_.GD.N0232.N0720.N1095.d017850 N)) omega))
        (sq_nonneg _)
  simpa only [add_sub_cancel_right] using hI




theorem d017859
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hdefect : _root_.GD.N0230.N0606.d000961 (_root_.GD.N0232.N0720.N1095.d017852 candidate)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) candidate := by
  apply _root_.GD.N0232.N0720.N1095.d017848
    candidate hcandidate _root_.GD.N0232.N0720.N1095.d017850 _root_.GD.N0232.N0720.N1095.d017851
  · intro N i
    simp [_root_.GD.N0232.N0720.N1095.d017851]
  · change _root_.GD.N0230.N0606.d000961 (_root_.GD.N0232.N0720.N1095.d017852 candidate)
    exact hdefect






theorem d017860
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hscaled : _root_.GD.N0230.N0606.d000961 (fun N ↦
      _root_.GD.N0232.N0720.N1095.d017856 candidate N /
        _root_.GD.N0232.N0720.N1095.d017853 N)) :
    _root_.GD.N0232.N0720.N1036.d014669 m n candidate := by
  have hdefect : _root_.GD.N0230.N0606.d000961 (_root_.GD.N0232.N0720.N1095.d017852 candidate) := by
    simpa only [_root_.GD.N0232.N0720.N1095.d017857] using hscaled
  have hstrong := _root_.GD.N0232.N0720.N1095.d017859
    candidate hcandidate hdefect
  intro e he theta
  rw [hstrong e he]


theorem d017861
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hdefect : _root_.GD.N0230.N0606.d000961 (_root_.GD.N0232.N0720.N1095.d017852 candidate)) :
    _root_.GD.N0232.N0720.N1036.d014669 m n candidate := by
  apply _root_.GD.N0232.N0720.N1095.d017860
    candidate hcandidate
  simpa only [_root_.GD.N0232.N0720.N1095.d017857] using hdefect





theorem d017862
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdefect : _root_.GD.N0230.N0606.d000961
      (_root_.GD.N0232.N0720.N1095.d017852
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn))) :
    _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0 := by
  apply _root_.GD.N0232.N0720.N1450.d017837 m n hm hn
  exact _root_.GD.N0232.N0720.N1095.d017861
    (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)
    (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).finiteRisk hdefect



theorem d017863
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdefect : _root_.GD.N0230.N0606.d000961
      (_root_.GD.N0232.N0720.N1095.d017852
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn))) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1450.d017838
    m n hm hn
      (_root_.GD.N0232.N0720.N1095.d017861
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)
        (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).finiteRisk hdefect)


theorem d017864
    (hdefect : _root_.GD.N0230.N0606.d000961
      (_root_.GD.N0232.N0720.N1095.d017852
        (_root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega)))) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 :=
  _root_.GD.N0232.N0720.N1095.d017863
    (m := 2) (n := 2) (by omega) (by omega) hdefect


theorem d017865
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfail : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ¬ _root_.GD.N0230.N0606.d000961
      (_root_.GD.N0232.N0720.N1095.d017852
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)) := by
  intro hdefect
  exact hfail <|
    _root_.GD.N0232.N0720.N1095.d017863
      hm hn hdefect

end

end N1095
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1095.d017857
#print axioms _root_.GD.N0232.N0720.N1095.d017845
#print axioms _root_.GD.N0232.N0720.N1095.d017847
#print axioms _root_.GD.N0232.N0720.N1095.d017858
#print axioms _root_.GD.N0232.N0720.N1095.d017848
#print axioms _root_.GD.N0232.N0720.N1095.d017849
#print axioms _root_.GD.N0232.N0720.N1095.d017859
#print axioms _root_.GD.N0232.N0720.N1095.d017860
#print axioms _root_.GD.N0232.N0720.N1095.d017864
#print axioms _root_.GD.N0232.N0720.N1095.d017865
