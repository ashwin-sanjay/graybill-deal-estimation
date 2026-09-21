import GD.Module0293
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

















open Filter Set
open scoped Topology

namespace GD.N0238.N0755

noncomputable section

variable {X I : Type*}



def d004732 (u : Finset I)
    (obs : I → X → ℝ) (target : I → ℝ) (x : X) : ℝ :=
  ∑ i ∈ u, (obs i x - target i) ^ 2


theorem d004733
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ) (x : X) :
    0 ≤ _root_.GD.N0238.N0755.d004732 u obs target x := by
  unfold _root_.GD.N0238.N0755.d004732
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (obs i x - target i)



theorem d004734
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ) (x : X) :
    _root_.GD.N0238.N0755.d004732 u obs target x = 0 ↔
      ∀ i ∈ u, obs i x = target i := by
  constructor
  · intro hzero i hi
    have hterm : (obs i x - target i) ^ 2 = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j hj ↦ sq_nonneg (obs j x - target j))).mp
          hzero i hi
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)
  · intro hagree
    apply Finset.sum_eq_zero
    intro i hi
    rw [hagree i hi, sub_self, zero_pow (by norm_num)]

section Continuity

variable [TopologicalSpace X]


theorem d004735
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i)) :
    Continuous (_root_.GD.N0238.N0755.d004732 u obs target) := by
  unfold _root_.GD.N0238.N0755.d004732
  exact continuous_finsetSum _ fun i _ ↦
    ((hobs i).sub continuous_const).pow 2










theorem d004736
    (boundary : Set X)
    (hboundary : IsCompact boundary)
    (obs : I → X → ℝ)
    (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (havoid : ∀ x ∈ boundary, ∃ i, obs i x ≠ target i) :
    ∃ u : Finset I, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x ∈ boundary, δ ≤ _root_.GD.N0238.N0755.d004732 u obs target x := by
  classical
  by_cases hnonempty : boundary.Nonempty
  · have hno :
        ¬ ∃ x, x ∈ boundary ∧ ∀ i, obs i x = target i := by
      rintro ⟨x, hx, hall⟩
      obtain ⟨i, hi⟩ := havoid x hx
      exact hi (hall i)
    obtain ⟨u, hu⟩ :=
      _root_.GD.N0238.d004299
        boundary hboundary obs target hobs hno
    have hcost_cont :
        ContinuousOn (_root_.GD.N0238.N0755.d004732 u obs target) boundary :=
      (_root_.GD.N0238.N0755.d004735 u obs target hobs).continuousOn
    obtain ⟨x₀, hx₀, hmin⟩ :=
      hboundary.exists_isMinOn hnonempty hcost_cont
    have hx₀_ne : _root_.GD.N0238.N0755.d004732 u obs target x₀ ≠ 0 := by
      intro hzero
      apply hu
      exact ⟨x₀, hx₀,
        (_root_.GD.N0238.N0755.d004734 u obs target x₀).mp hzero⟩
    have hx₀_pos : 0 < _root_.GD.N0238.N0755.d004732 u obs target x₀ :=
      lt_of_le_of_ne
        (_root_.GD.N0238.N0755.d004733 u obs target x₀)
        (Ne.symm hx₀_ne)
    refine ⟨u, _root_.GD.N0238.N0755.d004732 u obs target x₀, hx₀_pos, ?_⟩
    intro x hx
    exact isMinOn_iff.mp hmin x hx
  · have hempty : boundary = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    refine ⟨∅, 1, by norm_num, ?_⟩
    intro x hx
    simp [hempty] at hx






theorem d004737
    (boundary : Set X)
    (hboundary : IsCompact boundary)
    (obs : I → X → ℝ)
    (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i)) :
    (∀ x ∈ boundary, ∃ i, obs i x ≠ target i) ↔
      ∃ u : Finset I, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x ∈ boundary, δ ≤ _root_.GD.N0238.N0755.d004732 u obs target x := by
  constructor
  · exact _root_.GD.N0238.N0755.d004736
      boundary hboundary obs target hobs
  · rintro ⟨u, δ, hδ, hmargin⟩ x hx
    by_contra hnone
    have hall : ∀ i, obs i x = target i := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    have hzero : _root_.GD.N0238.N0755.d004732 u obs target x = 0 :=
      (_root_.GD.N0238.N0755.d004734 u obs target x).mpr
        (fun i _ ↦ hall i)
    have := hmargin x hx
    rw [hzero] at this
    linarith





theorem d004738
    (boundary : Set X)
    (hboundary : IsCompact boundary)
    (obs : ℕ → X → ℝ)
    (target : ℕ → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (havoid : ∀ x ∈ boundary, ∃ i, obs i x ≠ target i) :
    ∃ N : ℕ, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x ∈ boundary,
        δ ≤ _root_.GD.N0238.N0755.d004732 (Finset.range N) obs target x := by
  obtain ⟨u, δ, hδ, hmargin⟩ :=
    _root_.GD.N0238.N0755.d004736
      boundary hboundary obs target hobs havoid
  obtain ⟨N, hN⟩ := u.exists_nat_subset_range
  refine ⟨N, δ, hδ, ?_⟩
  intro x hx
  exact (hmargin x hx).trans <| by
    unfold _root_.GD.N0238.N0755.d004732
    exact Finset.sum_le_sum_of_subset_of_nonneg hN
      (fun i _ _ ↦ sq_nonneg (obs i x - target i))








theorem d004739
    (ambient boundary : Set X)
    (hambient : IsCompact ambient)
    (hboundary : IsCompact boundary)
    (obs : I → X → ℝ)
    (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (havoid : ∀ x ∈ boundary, ∃ i, obs i x ≠ target i) :
    ∃ u : Finset I, ∃ ε : ℝ,
      0 < ε ∧
      IsCompact
        (ambient ∩ {x | _root_.GD.N0238.N0755.d004732 u obs target x ≤ ε}) ∧
      (ambient ∩ {x | _root_.GD.N0238.N0755.d004732 u obs target x ≤ ε}) ∩
          boundary = ∅ := by
  obtain ⟨u, δ, hδ, hmargin⟩ :=
    _root_.GD.N0238.N0755.d004736
      boundary hboundary obs target hobs havoid
  refine ⟨u, δ / 2, half_pos hδ, ?_, ?_⟩
  · exact hambient.inter_right <|
      isClosed_le
        (_root_.GD.N0238.N0755.d004735 u obs target hobs)
        continuous_const
  · rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hupper : _root_.GD.N0238.N0755.d004732 u obs target x ≤ δ / 2 := hx.1.2
    have hlower : δ ≤ _root_.GD.N0238.N0755.d004732 u obs target x :=
      hmargin x hx.2
    linarith








theorem d004740
    {A : Type*} {l : Filter A} [NeBot l]
    (boundary : Set X)
    (u : Finset I)
    (obs : I → X → ℝ)
    (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    {x : A → X} {y : X}
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin :
      ∀ z ∈ boundary, δ ≤ _root_.GD.N0238.N0755.d004732 u obs target z)
    (hxy : Tendsto x l (𝓝 y))
    (hcost :
      Tendsto (fun a ↦ _root_.GD.N0238.N0755.d004732 u obs target (x a))
        l (𝓝 0)) :
    y ∉ boundary := by
  intro hy
  have hcost_y :
      Tendsto (fun a ↦ _root_.GD.N0238.N0755.d004732 u obs target (x a))
        l (𝓝 (_root_.GD.N0238.N0755.d004732 u obs target y)) :=
    (_root_.GD.N0238.N0755.d004735 u obs target hobs).continuousAt.tendsto.comp hxy
  have hzero : _root_.GD.N0238.N0755.d004732 u obs target y = 0 :=
    tendsto_nhds_unique hcost_y hcost
  have := hmargin y hy
  rw [hzero] at this
  linarith

end Continuity

section NonlinearVersusLinear


theorem d004741
    (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) :
    1 ≤ (x - 0) ^ 2 := by
  simp only [mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num






theorem d004742 :
    ¬ ∃ a : ℝ,
      ∀ x ∈ ({-1, 1} : Set ℝ), 0 < a * (x - 0) := by
  rintro ⟨a, ha⟩
  have hneg := ha (-1) (by simp)
  have hpos := ha 1 (by simp)
  norm_num at hneg hpos
  linarith

end NonlinearVersusLinear

end

end GD.N0238.N0755
