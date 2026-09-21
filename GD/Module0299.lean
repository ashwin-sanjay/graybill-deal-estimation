import GD.Module0298














namespace GD.N0238



def d004340
    {X I : Type*} (stage : ℕ → Finset I)
    (obs : I → X → ℝ) (target : I → ℝ) (x : ℕ → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    _root_.GD.N0238.d004321 (stage n) obs target (x n) < ε



theorem d004341
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hno : ¬ ∃ x, ∀ i, obs i x = target i)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage obs target x) :
    _root_.GD.N0238.d004336 x := by
  intro K hK
  have hnoK : ¬ ∃ y, y ∈ K ∧ ∀ i, obs i y = target i := by
    rintro ⟨y, _hyK, hy⟩
    exact hno ⟨y, hy⟩
  obtain ⟨M, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004330
      K hK obs target hobs stage hstage hnoK
  obtain ⟨N, hN⟩ := hvanish ε hε
  refine ⟨max M N, ?_⟩
  intro n hn hxnK
  have hMn : M ≤ n := le_trans (le_max_left M N) hn
  have hNn : N ≤ n := le_trans (le_max_right M N) hn
  have hlower : ε ≤ _root_.GD.N0238.d004321 (stage M) obs target (x n) :=
    hmargin (x n) hxnK
  have hstageLower :
      _root_.GD.N0238.d004321 (stage M) obs target (x n) ≤
        _root_.GD.N0238.d004321 (stage n) obs target (x n) :=
    _root_.GD.N0238.d004329 (hmono hMn) obs target (x n)
  have hupper :
      _root_.GD.N0238.d004321 (stage n) obs target (x n) < ε :=
    hN n hNn
  exact (not_lt_of_ge (hlower.trans hstageLower)) hupper

end GD.N0238

#print axioms _root_.GD.N0238.d004341
