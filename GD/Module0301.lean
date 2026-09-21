import GD.Module0300
































namespace GD
namespace N0230
namespace N0579

open _root_.GD.N0238

variable {G X I : Type*}


def d004352 [PseudoMetricSpace X]
    (act : G → X → X) (g : G) (x : X) : ℝ :=
  dist (act g x) x


theorem d004353 [PseudoMetricSpace X]
    (act : G → X → X) (hact : ∀ g, Continuous (act g)) (g : G) :
    Continuous (_root_.GD.N0230.N0579.d004352 act g) := by
  exact (hact g).dist continuous_id


theorem d004354 [MetricSpace X]
    (act : G → X → X) (x : X) :
    (∀ g, _root_.GD.N0230.N0579.d004352 act g x = 0) ↔
      ∀ g, act g x = x := by
  constructor
  · intro h g
    exact dist_eq_zero.mp (by simpa [_root_.GD.N0230.N0579.d004352] using h g)
  · intro h g
    simp [_root_.GD.N0230.N0579.d004352, h g]





theorem d004355
    [MetricSpace X]
    (base : Set X) (hbase : IsCompact base)
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ g, act g x = x) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤
        _root_.GD.N0238.d004321 (stage N)
          (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0) x := by
  apply _root_.GD.N0238.d004330
    base hbase (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0)
    (_root_.GD.N0230.N0579.d004353 act hact) stage hstage
  rintro ⟨x, hx, hres⟩
  exact hno ⟨x, hx,
    (_root_.GD.N0230.N0579.d004354 act x).mp (by simpa using hres)⟩






theorem d004356
    [MetricSpace X]
    (base : Set X) (hbase : IsCompact base)
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hfinite : ∀ N, ∃ x, x ∈ base ∧ ∀ g ∈ stage N, act g x = x) :
    ∃ x, x ∈ base ∧ ∀ g, act g x = x := by
  obtain ⟨x, hx, hres⟩ :=
    _root_.GD.N0238.d004331
      base hbase (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0)
      (_root_.GD.N0230.N0579.d004353 act hact) stage hstage (by
        intro N
        obtain ⟨x, hx, hfixed⟩ := hfinite N
        exact ⟨x, hx, fun g hg ↦ by
          simp [_root_.GD.N0230.N0579.d004352, hfixed g hg]⟩)
  exact ⟨x, hx,
    (_root_.GD.N0230.N0579.d004354 act x).mp (by simpa using hres)⟩








theorem d004357
    [MetricSpace X]
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y : X, ∀ g, act g y = y := by
  obtain ⟨y, hy⟩ :=
    _root_.GD.N0238.d004351
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0)
      (_root_.GD.N0230.N0579.d004353 act hact)
      stage hstage hmono x hvanish action hcompact hbounded
  exact ⟨y, (_root_.GD.N0230.N0579.d004354 act y).mp (by simpa using hy)⟩





theorem d004358
    [MetricSpace X]
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action) :
    (∃ y : X, ∀ g, act g y = y) ∨ _root_.GD.N0238.d004343 action x := by
  rcases _root_.GD.N0238.d004350
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0)
      (_root_.GD.N0230.N0579.d004353 act hact)
      stage hstage hmono x hvanish action hcompact with hfixed | hescape
  · left
    obtain ⟨y, hy⟩ := hfixed
    exact ⟨y, (_root_.GD.N0230.N0579.d004354 act y).mp (by simpa using hy)⟩
  · exact Or.inr hescape





theorem d004359
    [MetricSpace X]
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (hno : ¬ ∃ y : X, ∀ g, act g y = y)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action) :
    _root_.GD.N0238.d004343 action x := by
  rcases _root_.GD.N0230.N0579.d004358 act hact stage hstage hmono
      x hvanish action hcompact with hfixed | hescape
  · exact False.elim (hno hfixed)
  · exact hescape





theorem d004360
    [TopologicalSpace G] [TopologicalSpace X] [T2Space X]
    (label : I → G) (hlabel : DenseRange label)
    (act : G → X → X) (x : X)
    (hcontinuous : Continuous (fun g ↦ act g x))
    (hfixed : ∀ i, act (label i) x = x) :
    ∀ g, act g x = x := by
  have heq : (fun g ↦ act g x) = (fun _ : G ↦ x) :=
    hlabel.equalizer hcontinuous continuous_const (by
      funext i
      exact hfixed i)
  intro g
  exact congrFun heq g






theorem d004361
    [TopologicalSpace G] [MetricSpace X]
    (base : Set X) (hbase : IsCompact base)
    (label : I → G) (hlabel : DenseRange label)
    (act : G → X → X)
    (hstate : ∀ g, Continuous (act g))
    (hparameter : ∀ y, Continuous (fun g ↦ act g y))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ g, act g x = x) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤
        _root_.GD.N0238.d004321 (stage N)
          (fun i ↦ _root_.GD.N0230.N0579.d004352 act (label i)) (fun _ ↦ 0) x := by
  apply _root_.GD.N0230.N0579.d004355
    base hbase (fun i ↦ act (label i)) (fun i ↦ hstate (label i))
    stage hstage
  rintro ⟨x, hx, hfixed⟩
  exact hno ⟨x, hx, _root_.GD.N0230.N0579.d004360 label hlabel act x
    (hparameter x) hfixed⟩









theorem d004362
    [TopologicalSpace G] [MetricSpace X]
    (label : I → G) (hlabel : DenseRange label)
    (act : G → X → X)
    (hstate : ∀ g, Continuous (act g))
    (hparameter : ∀ y, Continuous (fun g ↦ act g y))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (x : ℕ → X)
    (hvanish : _root_.GD.N0238.d004340 stage
      (fun i ↦ _root_.GD.N0230.N0579.d004352 act (label i)) (fun _ ↦ 0) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y : X, ∀ g, act g y = y := by
  obtain ⟨y, hy⟩ :=
    _root_.GD.N0230.N0579.d004357
      (fun i ↦ act (label i)) (fun i ↦ hstate (label i))
      stage hstage hmono x hvanish action hcompact hbounded
  exact ⟨y, _root_.GD.N0230.N0579.d004360 label hlabel act y
    (hparameter y) hy⟩

end N0579
end N0230
end GD

#print axioms _root_.GD.N0230.N0579.d004357
#print axioms _root_.GD.N0230.N0579.d004355
#print axioms _root_.GD.N0230.N0579.d004356
#print axioms _root_.GD.N0230.N0579.d004358
#print axioms _root_.GD.N0230.N0579.d004359
#print axioms _root_.GD.N0230.N0579.d004360
#print axioms _root_.GD.N0230.N0579.d004361
#print axioms _root_.GD.N0230.N0579.d004362
