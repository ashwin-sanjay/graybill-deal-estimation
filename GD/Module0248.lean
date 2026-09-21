import GD.Module0232














open Set

namespace GD.N0232.N0719.N0861

noncomputable section



theorem d003551
    {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {gain energy : X → ℝ}
    (hgain_cont : ContinuousOn gain K)
    (henergy_cont : ContinuousOn energy K)
    (hgain_pos : ∀ x ∈ K, 0 < gain x)
    (henergy_pos : ∀ x ∈ K, 0 < energy x) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, η * energy x ≤ gain x := by
  obtain ⟨xmin, hxmin, hxmin_min⟩ :=
    hK.exists_isMinOn hKne hgain_cont
  obtain ⟨xmax, hxmax, hxmax_max⟩ :=
    hK.exists_isMaxOn hKne henergy_cont
  let η := gain xmin / energy xmax
  have hη : 0 < η := div_pos (hgain_pos xmin hxmin)
    (henergy_pos xmax hxmax)
  refine ⟨η, hη, ?_⟩
  intro x hx
  have hgain_min : gain xmin ≤ gain x := hxmin_min hx
  have henergy_max : energy x ≤ energy xmax := hxmax_max hx
  have henergy_max_pos : 0 < energy xmax := henergy_pos xmax hxmax
  calc
    η * energy x ≤ η * energy xmax :=
      mul_le_mul_of_nonneg_left henergy_max hη.le
    _ = gain xmin := by
      simp only [η]
      field_simp
    _ ≤ gain x := hgain_min


theorem d003552
    {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {gain energy : X → ℝ}
    (hgain_cont : ContinuousOn gain K)
    (henergy_cont : ContinuousOn energy K)
    (hgain_pos : ∀ x ∈ K, 0 < gain x)
    (henergy_pos : ∀ x ∈ K, 0 < energy x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K, -2 * ε * gain x + ε ^ 2 * energy x < 0 := by
  obtain ⟨η, hη, hcap⟩ :=
    _root_.GD.N0232.N0719.N0861.d003551 hK hKne hgain_cont henergy_cont
      hgain_pos henergy_pos
  refine ⟨η, hη, ?_⟩
  intro x hx
  have hg := hgain_pos x hx
  have he := henergy_pos x hx
  have hc := hcap x hx
  have hηe : η * energy x ≤ gain x := hc
  nlinarith




theorem d003553
    {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {gain energy : X → ℝ}
    (hgain_cont : ContinuousOn gain K)
    (henergy_cont : ContinuousOn energy K)
    (hgain_pos : ∀ x ∈ K, 0 < gain x)
    (henergy_pos : ∀ x ∈ K, 0 < energy x) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ε, 0 < ε → ε < 2 * η →
        ∀ x ∈ K, -2 * ε * gain x + ε ^ 2 * energy x < 0 := by
  obtain ⟨η, hη, hcap⟩ :=
    _root_.GD.N0232.N0719.N0861.d003551 hK hKne hgain_cont henergy_cont
      hgain_pos henergy_pos
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη x hx
  have hg := hgain_pos x hx
  have he := henergy_pos x hx
  have hc := hcap x hx
  have hεe : ε * energy x < 2 * gain x := by
    calc
      ε * energy x < (2 * η) * energy x :=
        mul_lt_mul_of_pos_right hεη he
      _ ≤ 2 * gain x := by nlinarith
  nlinarith

end

end GD.N0232.N0719.N0861
