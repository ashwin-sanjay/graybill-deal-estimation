import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact




















open Set

namespace GD
namespace N0238
namespace N0748

noncomputable section

variable {X V : Type*} [TopologicalSpace X]




theorem d004289
    (base : Set X) (hbase : IsCompact base)
    (residual : X → V) (kernel : Set V)
    (energy : X → ℝ)
    (henergy_cont : Continuous energy)
    (henergy_nonneg : ∀ x ∈ base, 0 ≤ energy x)
    (hzero_kernel :
      ∀ x ∈ base, energy x = 0 ↔ residual x ∈ kernel) :
    (¬ ∃ x, x ∈ base ∧ residual x ∈ kernel) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ base, δ ≤ energy x := by
  constructor
  · intro hno
    by_cases hnonempty : base.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ :=
        hbase.exists_isMinOn hnonempty henergy_cont.continuousOn
      have hx₀_ne : energy x₀ ≠ 0 := by
        intro hzero
        apply hno
        exact ⟨x₀, hx₀, (hzero_kernel x₀ hx₀).1 hzero⟩
      have hx₀_pos : 0 < energy x₀ :=
        lt_of_le_of_ne (henergy_nonneg x₀ hx₀) (Ne.symm hx₀_ne)
      refine ⟨energy x₀, hx₀_pos, ?_⟩
      intro x hx
      exact isMinOn_iff.mp hmin x hx
    · have hempty : base = ∅ :=
        not_nonempty_iff_eq_empty.mp hnonempty
      refine ⟨1, by norm_num, ?_⟩
      intro x hx
      simp [hempty] at hx
  · rintro ⟨δ, hδ, hmargin⟩
    rintro ⟨x, hx, hxkernel⟩
    have hzero : energy x = 0 :=
      (hzero_kernel x hx).2 hxkernel
    have hlower := hmargin x hx
    rw [hzero] at hlower
    linarith




theorem d004290
    (base : Set X) (hbase : IsCompact base)
    (residual : X → V) (kernel : Set V)
    (energy : X → ℝ)
    (henergy_cont : Continuous energy)
    (henergy_nonneg : ∀ x ∈ base, 0 ≤ energy x)
    (hzero_kernel :
      ∀ x ∈ base, energy x = 0 ↔ residual x ∈ kernel) :
    (∃ x, x ∈ base ∧ residual x ∈ kernel) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ base, δ ≤ energy x := by
  by_cases hkernel : ∃ x, x ∈ base ∧ residual x ∈ kernel
  · exact Or.inl hkernel
  · exact Or.inr <|
      (_root_.GD.N0238.N0748.d004289
        base hbase residual kernel energy henergy_cont
        henergy_nonneg hzero_kernel).1 hkernel

omit [TopologicalSpace X] in

theorem d004291
    (base : Set X)
    (residual : X → V) (kernel : Set V)
    (energy : X → ℝ)
    (hzero_kernel :
      ∀ x ∈ base, energy x = 0 ↔ residual x ∈ kernel) :
    (∃ x, x ∈ base ∧ residual x ∈ kernel) →
      ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ base, δ ≤ energy x := by
  rintro ⟨x, hx, hxkernel⟩
  rintro ⟨δ, hδ, hmargin⟩
  have hzero : energy x = 0 :=
    (hzero_kernel x hx).2 hxkernel
  have hlower := hmargin x hx
  rw [hzero] at hlower
  linarith

end

end N0748
end N0238
end GD
