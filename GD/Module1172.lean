import GD.Module1158



























open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1449

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1031
open _root_.GD.N0232.N0720.N1030
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1056
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1108
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1195
open _root_.GD.N0232.N0720.N1196
open _root_.GD.N0232.N0720.N1197
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}

set_option linter.unusedSectionVars false




def d018831 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0140.d006651 omega.1 + _root_.GD.N0140.d006651 omega.2

theorem d018832 : Measurable (_root_.GD.N0232.N0720.N1449.d018831 (m := m) (n := n)) := by
  unfold _root_.GD.N0232.N0720.N1449.d018831
  exact (_root_.GD.N0140.d006652.comp measurable_fst).add
    (_root_.GD.N0140.d006652.comp measurable_snd)



theorem d018833 (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 0 2 (0 + 2 * x) = 2⁻¹ * Real.exp (3 / 2 * x ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1124.d016497 0 2 _ (by norm_num)]
  congr 1
  congr 1
  ring

theorem d018834 (N : ℕ) (x : _root_.GD.N0137.d008894 N) :
    _root_.GD.N0232.N0719.N0932.d009213 N 0 2 (_root_.GD.N0107.d009018 N 0 2 x) =
      (2 : ℝ)⁻¹ ^ N * Real.exp (3 / 2 * _root_.GD.N0140.d006651 x) := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190 _root_.GD.N0140.d006651
  calc ∏ i : Fin N, _root_.GD.N0232.N0719.N0932.d009204 0 2 (_root_.GD.N0107.d009018 N 0 2 x i)
      = ∏ i : Fin N, (2⁻¹ * Real.exp (3 / 2 * x i ^ 2)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact _root_.GD.N0232.N0720.N1449.d018833 (x i)
    _ = (∏ _i : Fin N, (2 : ℝ)⁻¹) * ∏ i : Fin N, Real.exp (3 / 2 * x i ^ 2) :=
        Finset.prod_mul_distrib
    _ = (2 : ℝ)⁻¹ ^ N * Real.exp (∑ i : Fin N, 3 / 2 * x i ^ 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_sum]
    _ = (2 : ℝ)⁻¹ ^ N * Real.exp (3 / 2 * ∑ i : Fin N, x i ^ 2) := by
        rw [Finset.mul_sum]

theorem d018835 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1482.d015130 • omega =
      _root_.GD.N0107.d009024 m n 0 2 2 omega := by
  rw [_root_.GD.N0232.N0720.N1214.d014259 m n, _root_.GD.N0232.N0720.N1148.d018027,
    _root_.GD.N0232.N0720.N1148.d018029]


theorem d018836 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018141 m n omega = (2 : ℝ)⁻¹ ^ (m + n) * Real.exp (3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega) := by
  unfold _root_.GD.N0232.N0720.N1056.d018141 _root_.GD.N0232.N0720.N1499.d015001
  rw [_root_.GD.N0232.N0720.N1449.d018835]
  simp only [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1215.d014275,
    _root_.GD.N0232.N0720.N1148.d018029,
    _root_.GD.N0232.N0720.N1148.d018027, _root_.GD.N0232.N0720.N1080.d014169, mul_zero, add_zero,
    mul_one]
  show _root_.GD.N0232.N0719.N0932.d009213 m 0 2 (_root_.GD.N0107.d009018 m 0 2 omega.1) *
      _root_.GD.N0232.N0719.N0932.d009213 n 0 2 (_root_.GD.N0107.d009018 n 0 2 omega.2) = _
  rw [_root_.GD.N0232.N0720.N1449.d018834, _root_.GD.N0232.N0720.N1449.d018834]
  unfold _root_.GD.N0232.N0720.N1449.d018831
  rw [pow_add, mul_add, Real.exp_add]
  ring


theorem d018837 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018141 m n omega = 1 ↔
      _root_.GD.N0232.N0720.N1449.d018831 omega = 2 * ((m : ℝ) + n) * Real.log 2 / 3 := by
  rw [_root_.GD.N0232.N0720.N1449.d018836]
  have hpow : ((2 : ℝ)⁻¹) ^ (m + n) * 2 ^ (m + n) = 1 := by
    rw [← mul_pow]
    simp
  constructor
  · intro h
    have h2 : Real.exp (3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega) = 2 ^ (m + n) := by
      calc Real.exp (3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega)
          = (2⁻¹ ^ (m + n) * 2 ^ (m + n)) * Real.exp (3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega) := by
            rw [hpow, one_mul]
        _ = 2 ^ (m + n) * (2⁻¹ ^ (m + n) * Real.exp (3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega)) := by ring
        _ = 2 ^ (m + n) := by rw [h, mul_one]
    have h3 : 3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega = Real.log ((2 : ℝ) ^ (m + n)) := by
      rw [← h2, Real.log_exp]
    rw [Real.log_pow] at h3
    push_cast at h3
    linear_combination (2 / 3 : ℝ) * h3
  · intro h
    have h3 : 3 / 2 * _root_.GD.N0232.N0720.N1449.d018831 omega = ((m + n : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      linear_combination (3 / 2 : ℝ) * h
    rw [h3, ← Real.log_pow, Real.exp_log (by positivity)]
    exact hpow



theorem d018838 :
    _root_.GD.N0107.d009024 m n 0 1 1 = id := by
  funext omega
  apply Prod.ext
  · funext i
    simp [_root_.GD.N0107.d009024, _root_.GD.N0107.d009018]
  · funext i
    simp [_root_.GD.N0107.d009024, _root_.GD.N0107.d009018]

theorem d018839 :
    _root_.GD.N0232.N0720.N1080.d014172 m n =
      (_root_.GD.N0137.d008895 m).prod (_root_.GD.N0137.d008895 n) := by
  show _root_.GD.N0107.d009030 m n 0 1 1 = _
  unfold _root_.GD.N0107.d009030
  rw [_root_.GD.N0232.N0720.N1449.d018838, Measure.map_id]
  rfl



theorem d018840 (d : ℕ) (c : ℝ) :
    _root_.GD.N0121.d006346 d {c} = 0 := by
  unfold _root_.GD.N0121.d006346 ProbabilityTheory.gammaMeasure
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

theorem d018841 (d : ℕ) (hd : 0 < d) (c : ℝ) :
    _root_.GD.N0137.d008895 d {x | _root_.GD.N0140.d006651 x = c} = 0 := by
  have hmap := _root_.GD.N0140.d006656 d hd
  have hpre : {x : _root_.GD.N0137.d008894 d | _root_.GD.N0140.d006651 x = c} =
      _root_.GD.N0140.d006651 ⁻¹' {c} := by
    ext x
    simp
  rw [hpre, ← Measure.map_apply _root_.GD.N0140.d006652 (measurableSet_singleton c)]
  unfold _root_.GD.N0137.d008895
  rw [hmap]
  exact _root_.GD.N0232.N0720.N1449.d018840 d c

theorem d018842 (hm : 0 < m) (r : ℝ) :
    _root_.GD.N0232.N0720.N1080.d014172 m n {omega | _root_.GD.N0232.N0720.N1449.d018831 omega = r} = 0 := by
  rw [_root_.GD.N0232.N0720.N1449.d018839]
  have hs : MeasurableSet {omega : _root_.GD.N0232.N0720.N1080.d014170 m n | _root_.GD.N0232.N0720.N1449.d018831 omega = r} :=
    measurableSet_eq_fun _root_.GD.N0232.N0720.N1449.d018832 measurable_const
  rw [Measure.prod_apply_symm hs]
  have hsec : ∀ y : _root_.GD.N0137.d008894 n,
      _root_.GD.N0137.d008895 m
        ((fun x : _root_.GD.N0137.d008894 m ↦ (x, y)) ⁻¹'
          {omega : _root_.GD.N0232.N0720.N1080.d014170 m n | _root_.GD.N0232.N0720.N1449.d018831 omega = r}) = 0 := by
    intro y
    have hset : (fun x : _root_.GD.N0137.d008894 m ↦ (x, y)) ⁻¹'
        {omega : _root_.GD.N0232.N0720.N1080.d014170 m n | _root_.GD.N0232.N0720.N1449.d018831 omega = r} =
        {x | _root_.GD.N0140.d006651 x = r - _root_.GD.N0140.d006651 y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, _root_.GD.N0232.N0720.N1449.d018831]
      constructor <;> intro h <;> linarith
    rw [hset]
    exact _root_.GD.N0232.N0720.N1449.d018841 m hm _
  simp only [hsec, lintegral_zero]


theorem d018843 (hm : 0 < m) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1 := by
  rw [ae_iff]
  have hset : {omega : _root_.GD.N0232.N0720.N1080.d014170 m n | ¬ _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1} =
      {omega | _root_.GD.N0232.N0720.N1449.d018831 omega = 2 * ((m : ℝ) + n) * Real.log 2 / 3} := by
    ext omega
    simp only [Set.mem_setOf_eq, not_not]
    exact _root_.GD.N0232.N0720.N1449.d018837 omega
  rw [hset]
  exact _root_.GD.N0232.N0720.N1449.d018842 hm _



theorem d018844 (hm : 0 < m)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (htax : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0)) :
    ∃ jseq : ℕ → ℕ, Tendsto jseq atTop atTop ∧
      ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
        Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate (jseq k)).packet
          (candidate (jseq k)).weight omega) atTop atTop := by
  obtain ⟨jseq, hj, hesc⟩ := _root_.GD.N0232.N0720.N1196.d018197 candidate htax
  refine ⟨jseq, hj, ?_⟩
  filter_upwards [hesc, _root_.GD.N0232.N0720.N1449.d018843 (n := n) hm] with omega h1 h2
  exact h1 h2

theorem d018845 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1482.d015130 packet weight omega = 0 := by
  unfold _root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1030.d018092
  rw [_root_.GD.N0232.N0720.N1148.d018027]
  simp







theorem d018846 (hm : 0 < m) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hbudget : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1117.d018540 s (candidate j)
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 (candidate j))
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 (candidate j)))
      atTop (𝓝 0))
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G₁ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₁ : Integrable G₁ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₁ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet
        (candidate j).weight omega| ≤ G₁ omega)
    (G₃ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₃ : Integrable G₃ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₃ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015131
        (candidate j).packet (candidate j).weight omega| ≤ G₃ omega)
    (G₄ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₄ : Integrable G₄ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₄ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1482.d015131
        (candidate j).packet (candidate j).weight omega| ≤ G₄ omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 =
        0 := by
  have htax : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0) :=
    squeeze_zero (fun j ↦ add_nonneg (_root_.GD.N0232.N0720.N1195.d018569 _ _)
      (_root_.GD.N0232.N0720.N1195.d018569 _ _))
      (fun j ↦ _root_.GD.N0232.N0720.N1195.d018570 s (candidate j)) hbudget
  obtain ⟨jseq, hj, hesc⟩ := _root_.GD.N0232.N0720.N1449.d018844 hm candidate htax
  have hR' : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate (jseq k)).packet
      (candidate (jseq k)).weight) atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)) :=
    hR.comp hj
  have hcompl' : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016416 (candidate (jseq k)).packet
        (candidate (jseq k)).weight omega) atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)) := by
    filter_upwards [hcompl] with omega h
    exact h.comp hj
  have hdom₂ : ∀ k, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1482.d015130 (candidate (jseq k)).packet
        (candidate (jseq k)).weight omega| ≤ (fun _ ↦ (0 : ℝ)) omega := by
    intro k
    filter_upwards with omega
    rw [_root_.GD.N0232.N0720.N1449.d018845]
    simp
  exact _root_.GD.N0232.N0720.N1030.d018129 s (fun k ↦ candidate (jseq k)) hR' hesc hcompl'
    G₁ hG₁ (fun k ↦ hdom₁ (jseq k)) (fun _ ↦ (0 : ℝ)) (integrable_zero _ _ _) hdom₂
    G₃ hG₃ (fun k ↦ hdom₃ (jseq k)) G₄ hG₄ (fun k ↦ hdom₄ (jseq k))

end

end N1449
end N0720
end N0232
end GD
