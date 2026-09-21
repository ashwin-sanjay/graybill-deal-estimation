import GD.Module1127




















open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1197

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




def d018180 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (K : ℝ) : Set (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  {omega | _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≤ K}

theorem d018181 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (K : ℝ) :
    MeasurableSet (_root_.GD.N0232.N0720.N1197.d018180 (m := m) (n := n) packet weight K) :=
  measurableSet_le (_root_.GD.N0232.N0720.N1030.d018107 packet weight) measurable_const



theorem d018182 (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1056.d018150 m n K omega ↔ _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1 := by
  constructor
  · intro hpos heq
    unfold _root_.GD.N0232.N0720.N1056.d018150 at hpos
    rw [heq] at hpos
    simp at hpos
  · intro hne
    unfold _root_.GD.N0232.N0720.N1056.d018150
    have hc₀ := _root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega
    have hc₁ := _root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega
    have hD₀ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₀
    have hD₁ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₁
    have hα : 0 < 4 * (_root_.GD.N0232.N0720.N1056.d018141 m n omega - 1) ^ 2 := by
      have : _root_.GD.N0232.N0720.N1056.d018141 m n omega - 1 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    apply div_pos hα
    apply mul_pos
    · have : 0 ≤ (3 * (_root_.GD.N0232.N0720.N1056.d018142 m n omega - 1)) ^ 2 := sq_nonneg _
      linarith
    · linarith



theorem d018183 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    (_root_.GD.N0232.N0720.N1197.d018180 packet weight K).indicator (_root_.GD.N0232.N0720.N1056.d018150 m n K) omega ≤
      _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015130 packet weight omega +
        _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015131 packet weight
          omega := by
  classical
  by_cases h : omega ∈ _root_.GD.N0232.N0720.N1197.d018180 packet weight K
  · rw [Set.indicator_of_mem h]
    exact _root_.GD.N0232.N0720.N1056.d018152 packet weight hweight K hK omega h
  · rw [Set.indicator_apply, if_neg h]
    exact add_nonneg (_root_.GD.N0232.N0720.N1056.d018132 _ _ _ hweight _) (_root_.GD.N0232.N0720.N1056.d018132 _ _ _ hweight _)

theorem d018184 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (K : ℝ)
    (hK : 1 ≤ K) :
    Integrable ((_root_.GD.N0232.N0720.N1197.d018180 packet weight K).indicator (_root_.GD.N0232.N0720.N1056.d018150 m n K))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  (_root_.GD.N0232.N0720.N1056.d018156 K hK).indicator (_root_.GD.N0232.N0720.N1197.d018181 packet weight K)



theorem d018185 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (hK : 1 ≤ K) :
    (∫ omega, (_root_.GD.N0232.N0720.N1197.d018180 packet weight K).indicator (_root_.GD.N0232.N0720.N1056.d018150 m n K) omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 packet
          weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          packet weight := by
  unfold _root_.GD.N0232.N0720.N1056.d018131
  have h0 := _root_.GD.N0232.N0720.N1056.d018137 (m := m) (n := n)
    _root_.GD.N0232.N0720.N1482.d015130 packet weight hweight
  have h1 := _root_.GD.N0232.N0720.N1056.d018137 (m := m) (n := n)
    _root_.GD.N0232.N0720.N1482.d015131 packet weight hweight
  rw [← integral_add h0 h1]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun omega ↦
      Set.indicator_nonneg (fun omega _ ↦ _root_.GD.N0232.N0720.N1056.d018151 K hK omega) omega
  · exact h0.add h1
  · exact Filter.Eventually.of_forall fun omega ↦
      _root_.GD.N0232.N0720.N1197.d018183 packet weight hweight K hK omega




theorem d018186 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (hK : 1 ≤ K) (η : ℝ) (hη : 0 < η) :
    η * (_root_.GD.N0232.N0720.N1080.d014172 m n).real
        (_root_.GD.N0232.N0720.N1197.d018180 packet weight K ∩ {omega | η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega}) ≤
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 packet
          weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          packet weight := by
  classical
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := _root_.GD.N0232.N0720.N1080.d014172 m n)
    (f := (_root_.GD.N0232.N0720.N1197.d018180 packet weight K).indicator (_root_.GD.N0232.N0720.N1056.d018150 m n K))
    (Filter.Eventually.of_forall fun omega ↦
      Set.indicator_nonneg (fun omega _ ↦ _root_.GD.N0232.N0720.N1056.d018151 K hK omega) omega)
    (_root_.GD.N0232.N0720.N1197.d018184 packet weight K hK) η
  have hset : {omega | η ≤ (_root_.GD.N0232.N0720.N1197.d018180 packet weight K).indicator (_root_.GD.N0232.N0720.N1056.d018150 m n K) omega} =
      _root_.GD.N0232.N0720.N1197.d018180 packet weight K ∩ {omega | η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega} := by
    ext omega
    constructor
    · intro hω
      simp only [Set.mem_setOf_eq, Set.indicator_apply] at hω
      by_cases h : omega ∈ _root_.GD.N0232.N0720.N1197.d018180 packet weight K
      · rw [if_pos h] at hω
        exact ⟨h, hω⟩
      · rw [if_neg h] at hω
        exact absurd hω (not_le.mpr hη)
    · rintro ⟨h, hφ⟩
      simp only [Set.mem_setOf_eq, Set.indicator_apply]
      rw [if_pos h]
      exact hφ
  rw [hset] at hm
  exact le_trans hm (_root_.GD.N0232.N0720.N1197.d018185 packet weight hweight K hK)




theorem d018187
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (K : ℝ) (hK : 1 ≤ K) (η : ℝ)
    (hη : 0 < η)
    (h : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0)) :
    Tendsto (fun j ↦ (_root_.GD.N0232.N0720.N1080.d014172 m n).real
      (_root_.GD.N0232.N0720.N1197.d018180 (candidate j).packet (candidate j).weight K ∩
        {omega | η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega})) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun j ↦
      (_root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) / η) atTop (𝓝 0) := by
    have := h.div_const η
    rwa [zero_div] at this
  refine squeeze_zero (fun j ↦ measureReal_nonneg) (fun j ↦ ?_) hdiv
  rw [le_div_iff₀ hη]
  have hm := _root_.GD.N0232.N0720.N1197.d018186 (m := m) (n := n) (candidate j).packet
    (candidate j).weight (candidate j).weight_nonneg K hK η hη
  calc (_root_.GD.N0232.N0720.N1080.d014172 m n).real
        (_root_.GD.N0232.N0720.N1197.d018180 (candidate j).packet (candidate j).weight K ∩
          {omega | η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega}) * η
      = η * (_root_.GD.N0232.N0720.N1080.d014172 m n).real
        (_root_.GD.N0232.N0720.N1197.d018180 (candidate j).packet (candidate j).weight K ∩
          {omega | η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega}) := mul_comm _ _
    _ ≤ _ := hm



theorem d018188 (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hne : _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega :=
  ⟨_root_.GD.N0232.N0720.N1056.d018150 m n K omega, (_root_.GD.N0232.N0720.N1197.d018182 K hK omega).mpr hne, le_refl _⟩

end

end N1197
end N0720
end N0232
end GD
