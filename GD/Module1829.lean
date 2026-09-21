import GD.Module0149

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0675

namespace GD.N0046.N0304

noncomputable section

section Abstract

variable {D Θ : Type*} [AddCommGroup D] [Module ℝ D]

def d030189 (C : Set D) (risk : Θ → D → ℝ) (budget : Θ → ℝ) : Set D :=
  {x | x ∈ C ∧ ∀ θ, risk θ x ≤ budget θ}

def d030190 (C : Set D) (risk : Θ → D → ℝ) (budget : Θ → ℝ) : Set D :=
  {x | x ∈ C ∧ ∀ θ, risk θ x < budget θ}

omit [AddCommGroup D] [Module ℝ D] in
theorem d030191 (C : Set D) (risk : Θ → D → ℝ)
    (budget : Θ → ℝ) : _root_.GD.N0046.N0304.d030190 C risk budget ⊆ _root_.GD.N0046.N0304.d030189 C risk budget := by
  intro x hx
  exact ⟨hx.1, fun θ => (hx.2 θ).le⟩

theorem d030192 (C : Set D) (risk : Θ → D → ℝ)
    (budget : Θ → ℝ) (hC : Convex ℝ C)
    (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C)
    {x y : D} (hx : x ∈ _root_.GD.N0046.N0304.d030189 C risk budget)
    (hy : y ∈ _root_.GD.N0046.N0304.d030189 C risk budget) (hne : x ≠ y) :
    _root_.GD.N0230.N0718.d001528 x y ∈ _root_.GD.N0046.N0304.d030190 C risk budget := by
  constructor
  · unfold _root_.GD.N0230.N0718.d001528
    exact hC hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  · intro θ
    have hc := hcurvature θ hx.1 hy.1 hne
    have hxb := hx.2 θ
    have hyb := hy.2 θ
    linarith

theorem d030193 (C : Set D)
    (risk : Θ → D → ℝ) (budget : Θ → ℝ) (hC : Convex ℝ C)
    (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C)
    (hbranch : ¬ (_root_.GD.N0046.N0304.d030189 C risk budget).Subsingleton) :
    (_root_.GD.N0046.N0304.d030190 C risk budget).Nonempty := by
  classical
  have hpair : ∃ x ∈ _root_.GD.N0046.N0304.d030189 C risk budget, ∃ y ∈ _root_.GD.N0046.N0304.d030189 C risk budget, x ≠ y := by
    simpa only [Set.Subsingleton, not_forall, exists_prop] using hbranch
  obtain ⟨x, hx, y, hy, hne⟩ := hpair
  exact ⟨_root_.GD.N0230.N0718.d001528 x y, _root_.GD.N0046.N0304.d030192 C risk budget hC hcurvature hx hy hne⟩

theorem d030194 (C : Set D)
    (risk : Θ → D → ℝ) (budget : Θ → ℝ) (hC : Convex ℝ C)
    (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C)
    (hempty : _root_.GD.N0046.N0304.d030190 C risk budget = ∅) :
    (_root_.GD.N0046.N0304.d030189 C risk budget).Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hm := _root_.GD.N0046.N0304.d030192 C risk budget hC hcurvature hx hy hne
  simp [hempty] at hm

theorem d030195 (C : Set D)
    (risk : Θ → D → ℝ) (budget : Θ → ℝ) (hC : Convex ℝ C)
    (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C) :
    _root_.GD.N0046.N0304.d030190 C risk budget = ∅ ↔
      _root_.GD.N0046.N0304.d030189 C risk budget = ∅ ∨
        ∃ x : D, _root_.GD.N0046.N0304.d030189 C risk budget = {x} ∧
          ∃ θ : Θ, risk θ x = budget θ := by
  classical
  constructor
  · intro hempty
    by_cases hw : (_root_.GD.N0046.N0304.d030189 C risk budget).Nonempty
    · obtain ⟨x, hx⟩ := hw
      right
      refine ⟨x, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · intro y hy
          exact (_root_.GD.N0046.N0304.d030194 C risk budget hC hcurvature
            hempty hy hx : y = x)
        · intro y hy
          exact (Set.mem_singleton_iff.mp hy) ▸ hx
      · have hn : ¬ ∀ θ, risk θ x < budget θ := by
          intro hs
          have hm : x ∈ _root_.GD.N0046.N0304.d030190 C risk budget := ⟨hx.1, hs⟩
          simp [hempty] at hm
        obtain ⟨θ, hθ⟩ := not_forall.mp hn
        exact ⟨θ, le_antisymm (hx.2 θ) (le_of_not_gt hθ)⟩
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hw)
  · rintro (hempty | ⟨x, hsingleton, θ, hactive⟩)
    · exact Set.eq_empty_iff_forall_notMem.mpr fun y hy => by
        have hw := _root_.GD.N0046.N0304.d030191 C risk budget hy
        simp [hempty] at hw
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hxy : y = x := by
        have hw := _root_.GD.N0046.N0304.d030191 C risk budget hy
        simpa [hsingleton] using hw
      have hs := hy.2 θ
      rw [hxy, hactive] at hs
      exact (lt_irrefl _) hs

theorem d030196
    (C : Set D) (risk : Θ → D → ℝ) (budget : Θ → ℝ) (hC : Convex ℝ C)
    (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C) :
    (_root_.GD.N0046.N0304.d030190 C risk budget).Nonempty ↔
      (_root_.GD.N0046.N0304.d030189 C risk budget).Nonempty ∧
        ¬ ∃ x : D, _root_.GD.N0046.N0304.d030189 C risk budget = {x} ∧
          ∃ θ : Θ, risk θ x = budget θ := by
  have h := _root_.GD.N0046.N0304.d030195 C risk budget hC hcurvature
  simpa only [← Set.not_nonempty_iff_eq_empty, not_or, not_not] using not_congr h

omit [AddCommGroup D] [Module ℝ D] in
theorem d030197 (C : Set D) (risk : Θ → D → ℝ) (budget : Θ → ℝ)
    {x y : D} (hx : x ∈ _root_.GD.N0046.N0304.d030190 C risk budget) (hyC : y ∈ C)
    (hdominates : ∀ θ, risk θ y ≤ risk θ x) :
    y ∈ _root_.GD.N0046.N0304.d030190 C risk budget :=
  ⟨hyC, fun θ => lt_of_le_of_lt (hdominates θ) (hx.2 θ)⟩

theorem d030198 (C : Set D)
    (risk : Θ → D → ℝ) (budget : Θ → ℝ) (terminal : D → Prop)
    (hC : Convex ℝ C) (hcurvature : ∀ θ, _root_.GD.N0230.N0675.d001658 (risk θ) C)
    (hbranch : ¬ (_root_.GD.N0046.N0304.d030189 C risk budget).Subsingleton)
    (hselection : ∀ x ∈ _root_.GD.N0046.N0304.d030190 C risk budget,
      ∃ y ∈ C, terminal y ∧ ∀ θ, risk θ y ≤ risk θ x) :
    ∃ y ∈ _root_.GD.N0046.N0304.d030190 C risk budget, terminal y := by
  obtain ⟨x, hx⟩ := _root_.GD.N0046.N0304.d030193 C risk budget hC hcurvature hbranch
  obtain ⟨y, hyC, ht, hdom⟩ := hselection x hx
  exact ⟨y, _root_.GD.N0046.N0304.d030197 C risk budget hx hyC hdom, ht⟩

end Abstract

section Quadratic

open _root_.GD.N0230.N0602

variable {Ω Θ : Type*} [MeasurableSpace Ω]

theorem d030199
    {μ₀ : Measure Ω} (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (C : Set (_root_.GD.N0230.N0602.d000116 μ₀)) (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : ∀ θ, μ₀ ≪ μ θ)
    (hfinite : ∀ x ∈ C, ∀ θ, _root_.GD.N0230.N0602.d000117 (μ θ) (target θ) x ≠ ⊤) :
    ∀ θ, _root_.GD.N0230.N0675.d001658 (_root_.GD.N0230.N0675.d001652 (μ θ) (target θ)) C := by
  intro θ x y hx hy hne
  have hid := _root_.GD.N0230.N0675.d001655 (hμ θ) (target θ) x y
    (hfinite x hx θ) (hfinite y hy θ)
  have htax := _root_.GD.N0230.N0675.d001656 (hμ θ) (hμ₀ θ) (target θ)
    (hfinite x hx θ) (hfinite y hy θ) hne
  linarith

theorem d030200
    {μ₀ : Measure Ω} (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (C : Set (_root_.GD.N0230.N0602.d000116 μ₀)) (budget : Θ → ℝ)
    (hC : Convex ℝ C) (hμ : ∀ θ, μ θ ≪ μ₀)
    (hμ₀ : ∀ θ, μ₀ ≪ μ θ)
    (hfinite : ∀ x ∈ C, ∀ θ, _root_.GD.N0230.N0602.d000117 (μ θ) (target θ) x ≠ ⊤) :
    _root_.GD.N0046.N0304.d030190 C (fun θ => _root_.GD.N0230.N0675.d001652 (μ θ) (target θ)) budget = ∅ ↔
      _root_.GD.N0046.N0304.d030189 C (fun θ => _root_.GD.N0230.N0675.d001652 (μ θ) (target θ)) budget = ∅ ∨
        ∃ x : _root_.GD.N0230.N0602.d000116 μ₀,
          _root_.GD.N0046.N0304.d030189 C (fun θ => _root_.GD.N0230.N0675.d001652 (μ θ) (target θ)) budget = {x} ∧
          ∃ θ, _root_.GD.N0230.N0675.d001652 (μ θ) (target θ) x = budget θ :=
  _root_.GD.N0046.N0304.d030195 C _ budget hC
    (_root_.GD.N0046.N0304.d030199 μ target C hμ hμ₀ hfinite)

end Quadratic

end

end GD.N0046.N0304

#print axioms _root_.GD.N0046.N0304.d030192
#print axioms _root_.GD.N0046.N0304.d030195
#print axioms _root_.GD.N0046.N0304.d030198
#print axioms _root_.GD.N0046.N0304.d030200
