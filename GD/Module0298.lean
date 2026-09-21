import GD.Module0297














open Set

namespace GD.N0238



def d004336
    {X : Type*} [TopologicalSpace X] (x : ℕ → X) : Prop :=
  ∀ K : Set X, IsCompact K →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → x n ∉ K



theorem d004337
    {X I : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hno : ¬ ∃ x, x ∈ K ∧ ∀ i, obs i x = target i) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ ∃ x, x ∈ K ∧ ∀ i ∈ stage n, obs i x = target i := by
  classical
  obtain ⟨N, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004330
      K hK obs target hobs stage hstage hno
  refine ⟨N, ?_⟩
  intro n hNn
  rintro ⟨x, hxK, hmatch⟩
  have hsubset : stage N ⊆ stage n := hmono hNn
  have hzero : _root_.GD.N0238.d004321 (stage N) obs target x = 0 := by
    unfold _root_.GD.N0238.d004321
    apply Finset.sum_eq_zero
    intro i hi
    rw [hmatch i (hsubset hi)]
    simp
  have hle : ε ≤ 0 := by
    simpa only [hzero] using hmargin x hxK
  exact (not_lt_of_ge hle) hε



theorem d004338
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hno : ¬ ∃ x, ∀ i, obs i x = target i)
    (x : ℕ → X)
    (hmatch : ∀ n, ∀ i ∈ stage n, obs i (x n) = target i) :
    _root_.GD.N0238.d004336 x := by
  intro K hK
  have hnoK : ¬ ∃ y, y ∈ K ∧ ∀ i, obs i y = target i := by
    rintro ⟨y, _hyK, hy⟩
    exact hno ⟨y, hy⟩
  obtain ⟨N, hN⟩ :=
    _root_.GD.N0238.d004337
      K hK obs target hobs stage hstage hmono hnoK
  refine ⟨N, ?_⟩
  intro n hNn hxnK
  exact hN n hNn ⟨x n, hxnK, hmatch n⟩




theorem d004339
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hfinite : ∀ n, ∃ x, ∀ i ∈ stage n, obs i x = target i)
    (hno : ¬ ∃ x, ∀ i, obs i x = target i) :
    ∃ x : ℕ → X,
      (∀ n, ∀ i ∈ stage n, obs i (x n) = target i) ∧
      _root_.GD.N0238.d004336 x := by
  classical
  choose x hx using hfinite
  refine ⟨x, hx, ?_⟩
  exact _root_.GD.N0238.d004338
    obs target hobs stage hstage hmono hno x hx

end GD.N0238

#print axioms _root_.GD.N0238.d004337
#print axioms _root_.GD.N0238.d004338
#print axioms _root_.GD.N0238.d004339
