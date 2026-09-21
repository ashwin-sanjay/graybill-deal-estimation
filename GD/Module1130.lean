import GD.Module1129


























open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1196

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
open _root_.GD.N0232.N0720.N1108
open _root_.GD.N0232.N0720.N1197
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false



theorem d018189 (K c : ℝ) (hK : 1 ≤ K) (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1056.d018147 K c ≤ K * _root_.GD.N0232.N0720.N1056.d018147 2 c := by
  unfold _root_.GD.N0232.N0720.N1056.d018147
  nlinarith [sq_nonneg c, hc, hK]


theorem d018190 (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega / K ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega := by
  have hc₀ := _root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega
  have hc₁ := _root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega
  have hDK₀ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₀
  have hDK₁ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₁
  have hD2₀ := _root_.GD.N0232.N0720.N1056.d018148 (by norm_num : (1 : ℝ) ≤ 2) hc₀
  have hD2₁ := _root_.GD.N0232.N0720.N1056.d018148 (by norm_num : (1 : ℝ) ≤ 2) hc₁
  have hm₀ := _root_.GD.N0232.N0720.N1196.d018189 K (_root_.GD.N0232.N0720.N1056.d018141 m n omega) hK hc₀
  have hm₁ := _root_.GD.N0232.N0720.N1196.d018189 K (_root_.GD.N0232.N0720.N1056.d018142 m n omega) hK hc₁
  unfold _root_.GD.N0232.N0720.N1056.d018150
  set α := 4 * (_root_.GD.N0232.N0720.N1056.d018141 m n omega - 1) ^ 2
  set β := 3 * (_root_.GD.N0232.N0720.N1056.d018142 m n omega - 1)
  have hα : 0 ≤ α := by positivity
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg _
  by_cases hαβ : α + β ^ 2 = 0
  · have hα0 : α = 0 := by linarith
    rw [hα0]
    simp
  · have hαβpos : 0 < α + β ^ 2 := lt_of_le_of_ne (by linarith) (Ne.symm hαβ)
    rw [div_div]
    apply div_le_div_of_nonneg_left hα (mul_pos hαβpos (by linarith))
    have : _root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018141 m n omega) + _root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018142 m n omega) ≤
        K * (_root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018141 m n omega) + _root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018142 m n omega)) := by
      linarith
    calc (α + β ^ 2) * (_root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018141 m n omega) +
          _root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018142 m n omega))
        ≤ (α + β ^ 2) * (K * (_root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018141 m n omega) +
            _root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018142 m n omega))) :=
          mul_le_mul_of_nonneg_left this hαβpos.le
      _ = (α + β ^ 2) * (_root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018141 m n omega) +
            _root_.GD.N0232.N0720.N1056.d018147 2 (_root_.GD.N0232.N0720.N1056.d018142 m n omega)) * K := by ring




theorem d018191 : (_root_.GD.N0232.N0720.N1080.d014172 m n Set.univ).toReal = 1 := by
  have h := _root_.GD.N0232.N0720.N1484.d015104 m n _root_.GD.N0232.N0720.N1080.d014169
  simp only [_root_.GD.N0232.N0720.N1031.d017131, integral_const, smul_eq_mul, mul_one]
    at h
  exact h

theorem d018192 (s : Set (_root_.GD.N0232.N0720.N1080.d014170 m n)) : _root_.GD.N0232.N0720.N1080.d014172 m n s ≠ ∞ := by
  have huniv : _root_.GD.N0232.N0720.N1080.d014172 m n Set.univ ≠ ∞ := by
    intro h
    have := _root_.GD.N0232.N0720.N1196.d018191 (m := m) (n := n)
    rw [h, ENNReal.toReal_top] at this
    exact zero_ne_one this
  exact ne_top_of_le_ne_top huniv (measure_mono (Set.subset_univ s))




def d018193 (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (k j : ℕ) :
    Set (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  _root_.GD.N0232.N0720.N1197.d018180 (candidate j).packet (candidate j).weight ((k : ℝ) + 1) ∩
    {omega | 1 / ((k : ℝ) + 1) ^ 2 ≤ _root_.GD.N0232.N0720.N1056.d018150 m n ((k : ℝ) + 1) omega}

theorem d018194 (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (htax : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1080.d014172 m n (_root_.GD.N0232.N0720.N1196.d018193 (m := m) (n := n) candidate k j)) atTop (𝓝 0) := by
  have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hη : (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 := by positivity
  have hreal := _root_.GD.N0232.N0720.N1197.d018187 (m := m) (n := n) candidate
    ((k : ℝ) + 1) hK (1 / ((k : ℝ) + 1) ^ 2) hη htax
  have h1 := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at h1
  refine h1.congr fun j ↦ ?_
  exact ofReal_measureReal (_root_.GD.N0232.N0720.N1196.d018192 _)

theorem d018195 (k : ℕ) : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k :=
  ENNReal.pow_pos (ENNReal.inv_pos.mpr (by simp)) k

theorem d018196 : (∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ≠ ∞ := by
  rw [ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.mpr ?_
  refine (tsub_pos_iff_lt.mpr ?_).ne'
  exact ENNReal.inv_lt_one.mpr (by norm_num)




theorem d018197 (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (htax : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0)) :
    ∃ jseq : ℕ → ℕ, Tendsto jseq atTop atTop ∧
      ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1 →
        Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate (jseq k)).packet
          (candidate (jseq k)).weight omega) atTop atTop := by
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ j, N ≤ j →
      _root_.GD.N0232.N0720.N1080.d014172 m n (_root_.GD.N0232.N0720.N1196.d018193 (m := m) (n := n) candidate k j) < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    exact eventually_atTop.mp
      ((tendsto_order.1 (_root_.GD.N0232.N0720.N1196.d018194 candidate htax k)).2 _ (_root_.GD.N0232.N0720.N1196.d018195 k))
  choose N hN using hN
  let jseq : ℕ → ℕ := fun k ↦ max k (N k)
  have hjk : ∀ k, k ≤ jseq k := fun k ↦ le_max_left _ _
  have hjN : ∀ k, N k ≤ jseq k := fun k ↦ le_max_right _ _
  refine ⟨jseq, tendsto_atTop_mono hjk tendsto_id, ?_⟩

  have hsum : (∑' k : ℕ, _root_.GD.N0232.N0720.N1080.d014172 m n (_root_.GD.N0232.N0720.N1196.d018193 (m := m) (n := n) candidate k (jseq k))) ≠ ∞ := by
    refine ne_top_of_le_ne_top _root_.GD.N0232.N0720.N1196.d018196 ?_
    exact ENNReal.tsum_le_tsum fun k ↦ (hN k (jseq k) (hjN k)).le
  have hae := ae_eventually_notMem hsum
  filter_upwards [hae] with omega hω hne

  have hφ2 : 0 < _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega :=
    (_root_.GD.N0232.N0720.N1197.d018182 2 (by norm_num) omega).mpr hne
  have hlevel : ∀ᶠ k : ℕ in atTop,
      1 / ((k : ℝ) + 1) ^ 2 ≤ _root_.GD.N0232.N0720.N1056.d018150 m n ((k : ℝ) + 1) omega := by
    refine eventually_atTop.mpr ⟨⌈1 / _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega⌉₊, fun k hk ↦ ?_⟩
    have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hceil : 1 / _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega ≤ (k : ℝ) + 1 := by
      have h1 := Nat.le_ceil (1 / _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega)
      have h2 : ((⌈1 / _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hprod : 1 ≤ _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega * ((k : ℝ) + 1) := by
      rw [div_le_iff₀ hφ2] at hceil
      linarith
    have hstep : 1 / ((k : ℝ) + 1) ^ 2 ≤ _root_.GD.N0232.N0720.N1056.d018150 m n 2 omega / ((k : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) hkpos]
      nlinarith [hprod, hkpos]
    exact le_trans hstep (_root_.GD.N0232.N0720.N1196.d018190 ((k : ℝ) + 1) hK omega)

  have hbig : ∀ᶠ k : ℕ in atTop, (k : ℝ) + 1 <
      _root_.GD.N0232.N0720.N1126.d016415 (candidate (jseq k)).packet (candidate (jseq k)).weight omega := by
    filter_upwards [hω, hlevel] with k hk hl
    by_contra hcon
    push Not at hcon
    exact hk ⟨hcon, hl⟩
  refine tendsto_atTop_mono' atTop (hbig.mono fun k hk ↦ hk.le) ?_
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop





theorem d018198 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hesc : _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 1 →
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
      atTop (𝓝 (P omega))) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1108.d018082 g P omega)) := by
  by_cases hc :
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) = 1
  · have h0 : ∀ j, _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega = 0 := by
      intro j
      unfold _root_.GD.N0232.N0720.N1108.d018079
      rw [hc]
      simp
    have hl : _root_.GD.N0232.N0720.N1108.d018082 g P omega = 0 := by
      unfold _root_.GD.N0232.N0720.N1108.d018082 _root_.GD.N0232.N0720.N1108.d018077
      rw [hc]
      simp
    simp only [h0, hl]
    exact tendsto_const_nhds
  · exact _root_.GD.N0232.N0720.N1108.d018083 g candidate P omega (hesc hc) hcompl

theorem d018199 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 1 →
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
          atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (P omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight) atTop
      (𝓝 (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ (_root_.GD.N0232.N0720.N1031.d017147 (m := m) (n := n) g hg (candidate j).packet
      (candidate j).weight (candidate j).weight_nonneg).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      ‖_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega‖ ≤ G omega := by
    intro j
    filter_upwards [hdom j] with omega h
    simpa [Real.norm_eq_abs] using h
  have hlim : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1108.d018082 g P omega)) := by
    filter_upwards [hesc, hcompl] with omega h1 h2
    exact _root_.GD.N0232.N0720.N1196.d018198 g candidate P omega h1 h2
  exact tendsto_integral_of_dominated_convergence G hmeas hG hbound hlim

theorem d018200 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 1 →
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
          atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  have hE := _root_.GD.N0232.N0720.N1196.d018199 g hg candidate
    (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) hesc hcompl G hG hdom
  rw [_root_.GD.N0232.N0720.N1108.d018088 s g hg] at hE
  have hform : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight -
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight := by
    intro j
    have := _root_.GD.N0232.N0720.N1031.d017148 s g hg (candidate j).packet (candidate j).weight
      (candidate j).weight_nonneg
    linarith
  have hlim : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight) atTop
      (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + _root_.GD.N0232.N0720.N1159.d014647 m n s g)) := by
    simp only [hform]
    have hlim := (hR.const_mul (g.d009239 ^ 2)).sub (hE.const_mul (g.d009239 ^ 2))
    have ha : g.d009239 ^ 2 ≠ 0 := (pow_pos g.d009240 2).ne'
    convert hlim using 2
    field_simp
    ring
  have hle : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    intro j
    let image : _root_.GD.N0232.N0720.N1130.d017074 :=
      { width := (candidate j).width
        packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)
        weight := (candidate j).weight
        weight_nonneg := (candidate j).weight_nonneg }
    exact _root_.GD.N0232.N0720.N1113.d017125 m n s image
  have hbound := le_of_tendsto' hlim hle
  have hnn := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  linarith







theorem d018201 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (htax : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0))
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet
        (candidate j).weight omega| ≤ G omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 := by
  obtain ⟨jseq, hjseq, hesc⟩ := _root_.GD.N0232.N0720.N1196.d018197 candidate htax
  have hR' : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate (jseq k)).packet
      (candidate (jseq k)).weight) atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)) :=
    hR.comp hjseq
  have hcompl' : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016416 (candidate (jseq k)).packet
        (candidate (jseq k)).weight omega) atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)) := by
    filter_upwards [hcompl] with omega h
    exact h.comp hjseq
  have hesc' : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1482.d015130 • omega) ≠ 1 →
        Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate (jseq k)).packet
          (candidate (jseq k)).weight omega) atTop atTop := hesc
  exact _root_.GD.N0232.N0720.N1196.d018200 s
    _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1148.d018027
    (fun k ↦ candidate (jseq k)) hR' hesc' hcompl' G hG (fun k ↦ hdom (jseq k))

end

end N1196
end N0720
end N0232
end GD
