import GD.Module0299










namespace GD.N0238


def d004342
    {X : Type*} [TopologicalSpace X] (action : X → ℝ) : Prop :=
  ∀ R : ℝ, IsCompact {x | action x ≤ R}


def d004343
    {X : Type*} (action : X → ℝ) (x : ℕ → X) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R < action (x n)



def d004344
    {X : Type*} (action : X → ℝ) (x : ℕ → X) : Prop :=
  ∃ R : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → action (x n) ≤ R



theorem d004345
    {X : Type*} (action : X → ℝ) (x : ℕ → X)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ¬ _root_.GD.N0238.d004343 action x := by
  intro hdiv
  obtain ⟨R, N₀, hR⟩ := hbounded
  obtain ⟨N₁, hN₁⟩ := hdiv R
  let n := max N₀ N₁
  have hupper : action (x n) ≤ R := hR n (le_max_left _ _)
  have hlower : R < action (x n) := hN₁ n (le_max_right _ _)
  exact (not_lt_of_ge hupper) hlower



theorem d004346
    {X : Type*} [TopologicalSpace X]
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (x : ℕ → X) (hescape : _root_.GD.N0238.d004336 x) :
    _root_.GD.N0238.d004343 action x := by
  intro R
  obtain ⟨N, hN⟩ := hescape {y | action y ≤ R} (hcompact R)
  refine ⟨N, ?_⟩
  intro n hNn
  have hout : x n ∉ {y | action y ≤ R} := hN n hNn
  exact lt_of_not_ge hout





theorem d004347
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (R : ℝ) :
    (∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x, action x ≤ R →
        ε ≤ _root_.GD.N0238.d004321 (stage N) obs target x) ∨
      (∃ x, action x ≤ R ∧ ∀ i, obs i x = target i) := by
  simpa only [Set.mem_setOf_eq] using
    (_root_.GD.N0238.d004334
      {x | action x ≤ R} (hcompact R)
      obs target hobs stage hstage)





theorem d004348
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hno : ¬ ∃ x, ∀ i, obs i x = target i) :
    ∀ R : ℝ, ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x, action x ≤ R →
        ε ≤ _root_.GD.N0238.d004321 (stage N) obs target x := by
  intro R
  rcases _root_.GD.N0238.d004347
      obs target hobs stage hstage action hcompact R with hmargin | hmatch
  · exact hmargin
  · obtain ⟨x, _hxR, hx⟩ := hmatch
    exact False.elim (hno ⟨x, hx⟩)





theorem d004349
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hno : ¬ ∃ x, ∀ i, obs i x = target i)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage obs target x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action) :
    _root_.GD.N0238.d004343 action x := by
  exact _root_.GD.N0238.d004346 action hcompact x
    (_root_.GD.N0238.d004341
      obs target hobs stage hstage hmono hno x hvanish)





theorem d004350
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage obs target x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action) :
    (∃ y, ∀ i, obs i y = target i) ∨ _root_.GD.N0238.d004343 action x := by
  by_cases hmatch : ∃ y, ∀ i, obs i y = target i
  · exact Or.inl hmatch
  · exact Or.inr
      (_root_.GD.N0238.d004349
        obs target hobs stage hstage hmono hmatch x hvanish action hcompact)






theorem d004351
    {X I : Type*} [TopologicalSpace X]
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (stage : ℕ → Finset I)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage obs target x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y, ∀ i, obs i y = target i := by
  rcases _root_.GD.N0238.d004350
      obs target hobs stage hstage hmono x hvanish action hcompact with
    hmatch | hdiv
  · exact hmatch
  · exact False.elim ((_root_.GD.N0238.d004345
      action x hbounded) hdiv)

end GD.N0238

#print axioms _root_.GD.N0238.d004346
#print axioms _root_.GD.N0238.d004347
#print axioms _root_.GD.N0238.d004348
#print axioms _root_.GD.N0238.d004349
#print axioms _root_.GD.N0238.d004350
#print axioms _root_.GD.N0238.d004351
