import GD.Module1111
import Mathlib.Tactic
























open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1094

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0606
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1095
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1450

variable {m n : ℕ}







theorem d017866
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i)
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e candidate)
    (N : ℕ) :
    (‖e - candidate‖ / 2) ^ 2 ≤
      _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by
  have heFinite : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1111.d016607
      m n hcandidate he
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
  have htriangle : ‖e - candidate‖ ≤
      ‖e - completion‖ + ‖candidate - completion‖ := by
    calc
      ‖e - candidate‖ =
          ‖(e - completion) + (completion - candidate)‖ := by
        congr 1
        module
      _ ≤ ‖e - completion‖ + ‖completion - candidate‖ :=
        norm_add_le (e - completion) (completion - candidate)
      _ = ‖e - completion‖ + ‖candidate - completion‖ := by
        rw [norm_sub_rev completion candidate]
  have htriangleSq : ‖e - candidate‖ ^ 2 ≤
      (‖e - completion‖ + ‖candidate - completion‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (e - candidate))
      (add_nonneg (norm_nonneg (e - completion))
        (norm_nonneg (candidate - completion)))).2 htriangle
  calc
    (‖e - candidate‖ / 2) ^ 2 = ‖e - candidate‖ ^ 2 / 4 := by ring
    _ ≤ (‖e - completion‖ + ‖candidate - completion‖) ^ 2 / 4 :=
      (div_le_div_iff_of_pos_right (by norm_num)).2 htriangleSq
    _ ≤ (2 * (‖e - completion‖ ^ 2 +
          ‖candidate - completion‖ ^ 2)) / 4 :=
      (div_le_div_iff_of_pos_right (by norm_num)).2
        (add_sq_le (a := ‖e - completion‖)
          (b := ‖candidate - completion‖))
    _ ≤ (2 * (_root_.GD.N0232.N0720.N1095.d017841
          candidate packet weight N +
        _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N)) / 4 := by
      apply (div_le_div_iff_of_pos_right (by norm_num)).2
      exact mul_le_mul_of_nonneg_left
        (add_le_add heSq hcandidateSq) (by norm_num)
    _ = _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by ring



theorem d017867
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (packet : (N : ℕ) → Fin N → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : (N : ℕ) → Fin N → ℝ)
    (hweight : ∀ N i, 0 ≤ weight N i)
    (hnot : ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) candidate) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ N, epsilon ≤
        _root_.GD.N0232.N0720.N1095.d017841 candidate packet weight N := by
  simp only [_root_.GD.N0230.N0608.d000674] at hnot
  push Not at hnot
  obtain ⟨e, he, hne⟩ := hnot
  let epsilon : ℝ := (‖e - candidate‖ / 2) ^ 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    have hdist : 0 < ‖e - candidate‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    positivity
  refine ⟨epsilon, hepsilon, ?_⟩
  intro N
  exact
    _root_.GD.N0232.N0720.N1094.d017866
      candidate hcandidate packet weight hweight e he N






def d017868 (N : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1126.d016426
    (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N)
    (by intro i; simp [_root_.GD.N0232.N0720.N1095.d017851])



theorem d017869
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate) (N : ℕ) :
    ‖candidate - _root_.GD.N0232.N0720.N1094.d017868 N‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1095.d017852 candidate N := by
  have hbound := _root_.GD.N0232.N0720.N1125.d017259
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N)
    (by intro i; simp [_root_.GD.N0232.N0720.N1095.d017851]) candidate
    (fun i ↦ hcandidate (_root_.GD.N0232.N0720.N1095.d017850 N i))
  rw [_root_.GD.N0232.N0720.N1125.d017257
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1095.d017850 N) (_root_.GD.N0232.N0720.N1095.d017851 N)
    (by intro i; simp [_root_.GD.N0232.N0720.N1095.d017851])] at hbound
  simpa only [_root_.GD.N0232.N0720.N1094.d017868, _root_.GD.N0232.N0720.N1095.d017852] using hbound







theorem d017870
    (candidate limit : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hlimit : Tendsto (_root_.GD.N0232.N0720.N1094.d017868 (m := m) (n := n))
      atTop (nhds limit))
    (hne : candidate ≠ limit) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        epsilon ≤ _root_.GD.N0232.N0720.N1095.d017852 candidate k := by
  let d : ℝ := ‖candidate - limit‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnorm : Tendsto
      (fun k ↦ ‖candidate - _root_.GD.N0232.N0720.N1094.d017868
        (m := m) (n := n) k‖) atTop (nhds d) := by
    simpa only [d] using (tendsto_const_nhds.sub hlimit).norm
  have heventually : ∀ᶠ k in atTop,
      d / 2 < ‖candidate - _root_.GD.N0232.N0720.N1094.d017868
        (m := m) (n := n) k‖ :=
    (tendsto_order.1 hnorm).1 (d / 2) (by linarith)
  rw [eventually_atTop] at heventually
  obtain ⟨N, hN⟩ := heventually
  refine ⟨(d / 2) ^ 2, by positivity, N, ?_⟩
  intro k hk
  have hlower := hN k hk
  have hdefect := _root_.GD.N0232.N0720.N1094.d017869
    candidate hcandidate k
  nlinarith [norm_nonneg
    (candidate - _root_.GD.N0232.N0720.N1094.d017868 (m := m) (n := n) k)]



theorem d017871
    (candidate limit : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hlimit : Tendsto (_root_.GD.N0232.N0720.N1094.d017868 (m := m) (n := n))
      atTop (nhds limit))
    (hne : candidate ≠ limit) :
    ¬ _root_.GD.N0230.N0606.d000961 (_root_.GD.N0232.N0720.N1095.d017852 candidate) := by
  obtain ⟨epsilon, hepsilon, N, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1094.d017870
      candidate limit hcandidate hlimit hne
  intro hzero
  obtain ⟨K, hK⟩ := hzero epsilon hepsilon
  let k := max N K
  have hlow := hfloor k (le_max_left N K)
  have hsmall := hK k (le_max_right N K)
  have hnonneg := _root_.GD.N0232.N0720.N1095.d017858 candidate hcandidate k
  rw [abs_of_nonneg hnonneg] at hsmall
  linarith







theorem d017872
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfail : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ N, epsilon ≤ _root_.GD.N0232.N0720.N1095.d017852
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) N := by
  have hnot : ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) := by
    intro hstrong
    have hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) := by
      intro e he theta
      rw [hstrong e he]
    exact hfail <|
      _root_.GD.N0232.N0720.N1450.d017838
        m n hm hn hterminal
  simpa only [_root_.GD.N0232.N0720.N1095.d017852,
    _root_.GD.N0232.N0720.N1095.d017841] using
    _root_.GD.N0232.N0720.N1094.d017867
      (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).finiteRisk
      _root_.GD.N0232.N0720.N1095.d017850 _root_.GD.N0232.N0720.N1095.d017851
      (by intro N i; simp [_root_.GD.N0232.N0720.N1095.d017851]) hnot

end

end N1094
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1094.d017866
#print axioms _root_.GD.N0232.N0720.N1094.d017867
#print axioms _root_.GD.N0232.N0720.N1094.d017869
#print axioms _root_.GD.N0232.N0720.N1094.d017870
#print axioms _root_.GD.N0232.N0720.N1094.d017871
#print axioms _root_.GD.N0232.N0720.N1094.d017872
