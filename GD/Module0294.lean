import GD.Module0293
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
























open Set

namespace GD
namespace N0238
namespace N0751

noncomputable section

variable {X I : Type*}


def d004301
    (u : Finset I) (action : I → X → ℝ) (x : X) : ℝ :=
  ∑ i ∈ u, action i x


theorem d004302
    (base : Set X)
    (u : Finset I) (action : I → X → ℝ)
    (haction_nonneg : ∀ i x, x ∈ base → 0 ≤ action i x)
    {x : X} (hx : x ∈ base) :
    0 ≤ _root_.GD.N0238.N0751.d004301 u action x := by
  unfold _root_.GD.N0238.N0751.d004301
  exact Finset.sum_nonneg fun i _ ↦ haction_nonneg i x hx





theorem d004303
    (base : Set X)
    (u : Finset I) (action : I → X → ℝ)
    (haction_nonneg : ∀ i x, x ∈ base → 0 ≤ action i x)
    {x : X} (hx : x ∈ base) :
    _root_.GD.N0238.N0751.d004301 u action x = 0 ↔
      ∀ i ∈ u, action i x = 0 := by
  constructor
  · intro hzero
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ haction_nonneg i x hx)).mp hzero
  · intro hall
    unfold _root_.GD.N0238.N0751.d004301
    exact Finset.sum_eq_zero fun i hi ↦ hall i hi

section Continuity

variable [TopologicalSpace X]


theorem d004304
    (u : Finset I) (action : I → X → ℝ)
    (haction_cont : ∀ i, Continuous (action i)) :
    Continuous (_root_.GD.N0238.N0751.d004301 u action) := by
  unfold _root_.GD.N0238.N0751.d004301
  exact continuous_finsetSum _ fun i _ ↦ haction_cont i








theorem d004305
    (base : Set X)
    (hbase : IsCompact base)
    (action : I → X → ℝ)
    (haction_cont : ∀ i, Continuous (action i))
    (haction_nonneg : ∀ i x, x ∈ base → 0 ≤ action i x)
    (hno :
      ¬ ∃ x, x ∈ base ∧ ∀ i, action i x = 0) :
    ∃ u : Finset I, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x ∈ base, δ ≤ _root_.GD.N0238.N0751.d004301 u action x := by
  classical
  by_cases hnonempty : base.Nonempty
  · obtain ⟨u, hu⟩ :=
      _root_.GD.N0238.d004300
        base hbase action haction_cont hno
    have hsum_cont :
        ContinuousOn (_root_.GD.N0238.N0751.d004301 u action) base :=
      (_root_.GD.N0238.N0751.d004304 u action haction_cont).continuousOn
    obtain ⟨x₀, hx₀, hmin⟩ :=
      hbase.exists_isMinOn hnonempty hsum_cont
    have hx₀_ne : _root_.GD.N0238.N0751.d004301 u action x₀ ≠ 0 := by
      intro hzero
      apply hu
      exact
        ⟨x₀, hx₀,
          (_root_.GD.N0238.N0751.d004303
            base u action haction_nonneg hx₀).mp hzero⟩
    have hx₀_pos : 0 < _root_.GD.N0238.N0751.d004301 u action x₀ :=
      lt_of_le_of_ne
        (_root_.GD.N0238.N0751.d004302
          base u action haction_nonneg hx₀)
        (Ne.symm hx₀_ne)
    refine
      ⟨u, _root_.GD.N0238.N0751.d004301 u action x₀, hx₀_pos, ?_⟩
    intro x hx
    exact isMinOn_iff.mp hmin x hx
  · have hempty : base = ∅ :=
      not_nonempty_iff_eq_empty.mp hnonempty
    refine ⟨∅, 1, by norm_num, ?_⟩
    intro x hx
    simp [hempty] at hx





theorem d004306
    (base : Set X)
    (hbase : IsCompact base)
    (action : I → X → ℝ)
    (haction_cont : ∀ i, Continuous (action i))
    (haction_nonneg : ∀ i x, x ∈ base → 0 ≤ action i x) :
    (¬ ∃ x, x ∈ base ∧ ∀ i, action i x = 0) ↔
      ∃ u : Finset I, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x ∈ base, δ ≤ _root_.GD.N0238.N0751.d004301 u action x := by
  constructor
  · exact
      _root_.GD.N0238.N0751.d004305
        base hbase action haction_cont haction_nonneg
  · rintro ⟨u, δ, hδ, hmargin⟩
    rintro ⟨x, hx, hzero⟩
    have hsum_zero : _root_.GD.N0238.N0751.d004301 u action x = 0 := by
      unfold _root_.GD.N0238.N0751.d004301
      exact Finset.sum_eq_zero fun i _ ↦ hzero i
    have hlower := hmargin x hx
    rw [hsum_zero] at hlower
    linarith







theorem d004307
    (base : Set X)
    (hbase : IsCompact base)
    (action : I → X → ℝ)
    (haction_cont : ∀ i, Continuous (action i))
    (haction_nonneg : ∀ i x, x ∈ base → 0 ≤ action i x) :
    (∃ x, x ∈ base ∧ ∀ i, action i x = 0) ∨
      ∃ u : Finset I, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x ∈ base, δ ≤ _root_.GD.N0238.N0751.d004301 u action x := by
  classical
  by_cases hzero :
      ∃ x, x ∈ base ∧ ∀ i, action i x = 0
  · exact Or.inl hzero
  · exact Or.inr <|
      _root_.GD.N0238.N0751.d004305
        base hbase action haction_cont haction_nonneg hzero

omit [TopologicalSpace X] in

theorem d004308
    (base : Set X)
    (action : I → X → ℝ) :
    (∃ x, x ∈ base ∧ ∀ i, action i x = 0) →
      ¬ ∃ u : Finset I, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x ∈ base, δ ≤ _root_.GD.N0238.N0751.d004301 u action x := by
  rintro ⟨x, hx, hzero⟩
  rintro ⟨u, δ, hδ, hmargin⟩
  have hsum_zero : _root_.GD.N0238.N0751.d004301 u action x = 0 := by
    unfold _root_.GD.N0238.N0751.d004301
    exact Finset.sum_eq_zero fun i _ ↦ hzero i
  have hlower := hmargin x hx
  rw [hsum_zero] at hlower
  linarith

end Continuity

end

end N0751
end N0238
end GD
