import GD.Module0296















open Set
open scoped BigOperators

namespace GD.N0238



def d004327
    {I : Type*} (stage : ℕ → Finset I) : Prop :=
  ∀ u : Finset I, ∃ N, u ⊆ stage N


theorem d004328 :
    _root_.GD.N0238.d004327 (fun N ↦ Finset.range N) := by
  intro u
  exact Finset.exists_nat_subset_range u



theorem d004329
    {X I : Type*} {u v : Finset I} (huv : u ⊆ v)
    (obs : I → X → ℝ) (target : I → ℝ) (x : X) :
    _root_.GD.N0238.d004321 u obs target x ≤
      _root_.GD.N0238.d004321 v obs target x := by
  classical
  unfold _root_.GD.N0238.d004321
  exact Finset.sum_le_sum_of_subset_of_nonneg huv
    (fun i _hi _hiu ↦ sq_nonneg (obs i x - target i))



theorem d004330
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, obs i x = target i) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤
        _root_.GD.N0238.d004321 (stage N) obs target x := by
  obtain ⟨u, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004324
      base hbase obs target hobs hno
  obtain ⟨N, hsubset⟩ := hstage u
  refine ⟨N, ε, hε, ?_⟩
  intro x hx
  exact (hmargin x hx).trans
    (_root_.GD.N0238.d004329 hsubset obs target x)



theorem d004331
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hfinite : ∀ N, ∃ x, x ∈ base ∧
      ∀ i ∈ stage N, obs i x = target i) :
    ∃ x, x ∈ base ∧ ∀ i, obs i x = target i := by
  classical
  by_contra hno
  obtain ⟨N, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004330
      base hbase obs target hobs stage hstage hno
  obtain ⟨x, hx, hmatch⟩ := hfinite N
  have hzero : _root_.GD.N0238.d004321 (stage N) obs target x = 0 := by
    unfold _root_.GD.N0238.d004321
    apply Finset.sum_eq_zero
    intro i hi
    rw [hmatch i hi]
    simp
  have hle : ε ≤ 0 := by
    simpa only [hzero] using hmargin x hx
  exact (not_lt_of_ge hle) hε


theorem d004332
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage) :
    (∃ x, x ∈ base ∧ ∀ i, obs i x = target i) ↔
      ∀ N, ∃ x, x ∈ base ∧
        ∀ i ∈ stage N, obs i x = target i := by
  constructor
  · rintro ⟨x, hx, hmatch⟩ N
    exact ⟨x, hx, fun i _hi ↦ hmatch i⟩
  · exact _root_.GD.N0238.d004331
      base hbase obs target hobs stage hstage



theorem d004333
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (base : Set X) (hbase : IsCompact base)
    (targets : Set Y) (htargets : IsCompact targets)
    (obs : I → X → ℝ) (targetObs : I → Y → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (htargetObs : ∀ i, Continuous (targetObs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hno : ¬ ∃ x, x ∈ base ∧ ∃ y, y ∈ targets ∧
      ∀ i, obs i x = targetObs i y) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ∀ y ∈ targets, ε ≤
        ∑ i ∈ stage N, (obs i x - targetObs i y) ^ 2 := by
  obtain ⟨u, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004326
      base hbase targets htargets obs targetObs
      hobs htargetObs hno
  obtain ⟨N, hsubset⟩ := hstage u
  refine ⟨N, ε, hε, ?_⟩
  intro x hx y hy
  exact (hmargin x hx y hy).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _hi _hiu ↦ sq_nonneg (obs i x - targetObs i y)))



theorem d004334
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage) :
    (∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤ _root_.GD.N0238.d004321 (stage N) obs target x) ∨
      (∃ x, x ∈ base ∧ ∀ i, obs i x = target i) := by
  classical
  by_cases hmatch : ∃ x, x ∈ base ∧ ∀ i, obs i x = target i
  · exact Or.inr hmatch
  · exact Or.inl (_root_.GD.N0238.d004330
      base hbase obs target hobs stage hstage hmatch)




theorem d004335
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (base : Set X) (hbase : IsCompact base)
    (targets : Set Y) (htargets : IsCompact targets)
    (obs : I → X → ℝ) (targetObs : I → Y → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (htargetObs : ∀ i, Continuous (targetObs i))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage) :
    (∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ∀ y ∈ targets, ε ≤
        ∑ i ∈ stage N, (obs i x - targetObs i y) ^ 2) ∨
      (∃ x, x ∈ base ∧ ∃ y, y ∈ targets ∧
        ∀ i, obs i x = targetObs i y) := by
  classical
  by_cases hmatch : ∃ x, x ∈ base ∧ ∃ y, y ∈ targets ∧
      ∀ i, obs i x = targetObs i y
  · exact Or.inr hmatch
  · exact Or.inl (_root_.GD.N0238.d004333
      base hbase targets htargets obs targetObs
      hobs htargetObs stage hstage hmatch)

end GD.N0238
