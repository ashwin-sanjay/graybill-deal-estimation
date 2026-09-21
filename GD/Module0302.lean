import GD.Module0005
import GD.Module0301



















open scoped BigOperators

namespace GD
namespace N0230
namespace N0559

open _root_.GD.N0238
open _root_.GD.N0230.N0557
open _root_.GD.N0230.N0579

variable {G X Theta I : Type*}


def d004363
    (stage : ℕ → Finset G) (energy : G → X → ℝ)
    (x : ℕ → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (∑ g ∈ stage n, energy g (x n)) < ε



theorem d004364
    [MetricSpace X]
    (base : Set X) (hbase : IsCompact base)
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (energy : G → X → ℝ)
    (henergy : ∀ g x, x ∈ base →
      dist (act g x) x ^ 2 ≤ energy g x)
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ g, act g x = x) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤ ∑ g ∈ stage N, energy g x := by
  classical
  obtain ⟨N, ε, hε, hmargin⟩ :=
    _root_.GD.N0230.N0579.d004355
      base hbase act hact stage hstage hno
  refine ⟨N, ε, hε, ?_⟩
  intro x hx
  refine (hmargin x hx).trans ?_
  unfold _root_.GD.N0238.d004321 _root_.GD.N0230.N0579.d004352
  simp only [sub_zero]
  exact Finset.sum_le_sum fun g hg ↦ henergy g x hx



theorem d004365
    [MetricSpace X]
    (act : G → X → X)
    (stage : ℕ → Finset G) (energy : G → X → ℝ)
    (x : ℕ → X)
    (henergy : ∀ n, ∀ g ∈ stage n,
      dist (act g (x n)) (x n) ^ 2 ≤ energy g (x n))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy x) :
    _root_.GD.N0238.d004340 stage
      (_root_.GD.N0230.N0579.d004352 act) (fun _ ↦ 0) x := by
  intro ε hε
  obtain ⟨N, hN⟩ := hvanish ε hε
  refine ⟨N, ?_⟩
  intro n hn
  refine lt_of_le_of_lt ?_ (hN n hn)
  classical
  unfold _root_.GD.N0238.d004321 _root_.GD.N0230.N0579.d004352
  simp only [sub_zero]
  exact Finset.sum_le_sum fun g hg ↦ henergy n g hg



theorem d004366
    [MetricSpace X]
    (act : G → X → X) (hact : ∀ g, Continuous (act g))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : G → X → ℝ) (x : ℕ → X)
    (henergy : ∀ n, ∀ g ∈ stage n,
      dist (act g (x n)) (x n) ^ 2 ≤ energy g (x n))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y : X, ∀ g, act g y = y := by
  exact _root_.GD.N0230.N0579.d004357
    act hact stage hstage hmono x
    (_root_.GD.N0230.N0559.d004365
      act stage energy x henergy hvanish)
    action hcompact hbounded

section OrbitCirculation

variable [Group G] [MulAction G Theta]
variable [NormedAddCommGroup X] [MulAction G X]



theorem d004367
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (p : X)
    (hmin : ∀ g : G, risk theta p ≤ risk theta (g • p))
    (htax : ∀ g : G,
      ‖g • p - p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (g : G) :
    dist (g • p) p ^ 2 ≤ _root_.GD.N0230.N0557.d000042 risk theta p g := by
  rw [_root_.GD.N0230.N0557.d000043
    risk weight hRisk theta p g]
  have hinverse : 0 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ :=
    _root_.GD.N0230.N0557.d000044 risk theta p hmin g⁻¹
  have hweighted : 0 ≤ weight g * _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ :=
    mul_nonneg (hweight g).le hinverse
  have hbound :
      ‖g • p - p‖ ^ 2 ≤
        _root_.GD.N0230.N0557.d000041 risk theta p g +
          weight g * _root_.GD.N0230.N0557.d000041 risk theta p g⁻¹ :=
    (htax g).trans (le_add_of_nonneg_right hweighted)
  simpa [dist_eq_norm] using
    hbound






theorem d004368
    (base : Set X) (hbase : IsCompact base)
    (hact : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta)
    (hmin : ∀ p ∈ base, ∀ g : G,
      risk theta p ≤ risk theta (g • p))
    (htax : ∀ p ∈ base, ∀ g : G,
      ‖g • p - p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (hno : ¬ ∃ p, p ∈ base ∧ ∀ g : G, g • p = p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ base, ε ≤
        ∑ g ∈ stage N, _root_.GD.N0230.N0557.d000042 risk theta p g := by
  apply _root_.GD.N0230.N0559.d004364
    base hbase (fun g p ↦ g • p) hact stage hstage
    (fun g p ↦ _root_.GD.N0230.N0557.d000042 risk theta p g)
  · intro g p hp
    exact _root_.GD.N0230.N0559.d004367
      risk weight hRisk hweight theta p (hmin p hp) (htax p hp) g
  · exact hno






theorem d004369
    (hact : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (stage : ℕ → Finset G) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (x : ℕ → X)
    (hmin : ∀ n, ∀ g : G,
      risk theta (x n) ≤ risk theta (g • x n))
    (htax : ∀ n, ∀ g : G,
      ‖g • x n - x n‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta (x n) g)
    (hvanish : _root_.GD.N0230.N0559.d004363 stage
      (fun g p ↦ _root_.GD.N0230.N0557.d000042 risk theta p g) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y : X, ∀ g : G, g • y = y := by
  apply _root_.GD.N0230.N0559.d004366
    (fun g p ↦ g • p) hact stage hstage hmono
    (fun g p ↦ _root_.GD.N0230.N0557.d000042 risk theta p g) x
  · intro n g hg
    exact _root_.GD.N0230.N0559.d004367
      risk weight hRisk hweight theta (x n) (hmin n) (htax n) g
  · exact hvanish
  · exact hcompact
  · exact hbounded

end OrbitCirculation

section DenseOrbitCirculation

variable [TopologicalSpace G] [Group G] [MulAction G Theta]
variable [NormedAddCommGroup X] [MulAction G X]






theorem d004370
    (base : Set X) (hbase : IsCompact base)
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (hparameter : ∀ x : X, Continuous (fun g : G ↦ g • x))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta)
    (hmin : ∀ p ∈ base, ∀ g : G,
      risk theta p ≤ risk theta (g • p))
    (htax : ∀ p ∈ base, ∀ g : G,
      ‖g • p - p‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta p g)
    (hno : ¬ ∃ p, p ∈ base ∧ ∀ g : G, g • p = p) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ base, ε ≤
        ∑ i ∈ stage N, _root_.GD.N0230.N0557.d000042 risk theta p (label i) := by
  apply _root_.GD.N0230.N0559.d004364
    base hbase (fun i p ↦ label i • p)
    (fun i ↦ hstate (label i)) stage hstage
    (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i))
  · intro i p hp
    exact _root_.GD.N0230.N0559.d004367
      risk weight hRisk hweight theta p (hmin p hp) (htax p hp) (label i)
  · rintro ⟨p, hp, hfixed⟩
    apply hno
    refine ⟨p, hp, ?_⟩
    exact _root_.GD.N0230.N0579.d004360 label hlabel
      (fun g p ↦ g • p) p (hparameter p) hfixed






theorem d004371
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (hparameter : ∀ x : X, Continuous (fun g : G ↦ g • x))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (x : ℕ → X)
    (hmin : ∀ n, ∀ g : G,
      risk theta (x n) ≤ risk theta (g • x n))
    (htax : ∀ n, ∀ g : G,
      ‖g • x n - x n‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta (x n) g)
    (hvanish : _root_.GD.N0230.N0559.d004363 stage
      (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i)) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action x) :
    ∃ y : X, ∀ g : G, g • y = y := by
  apply _root_.GD.N0230.N0579.d004362
    label hlabel (fun g p ↦ g • p) hstate hparameter
    stage hstage hmono x
  · exact _root_.GD.N0230.N0559.d004365
      (fun i p ↦ label i • p) stage
      (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i)) x
      (fun n i hi ↦ _root_.GD.N0230.N0559.d004367
        risk weight hRisk hweight theta (x n) (hmin n) (htax n) (label i))
      hvanish
  · exact hcompact
  · exact hbounded






theorem d004372
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (hparameter : ∀ x : X, Continuous (fun g : G ↦ g • x))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (x : ℕ → X)
    (hmin : ∀ n, ∀ g : G,
      risk theta (x n) ≤ risk theta (g • x n))
    (htax : ∀ n, ∀ g : G,
      ‖g • x n - x n‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta (x n) g)
    (hvanish : _root_.GD.N0230.N0559.d004363 stage
      (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i)) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action) :
    (∃ y : X, ∀ g : G, g • y = y) ∨ _root_.GD.N0238.d004343 action x := by
  have hresidual : _root_.GD.N0238.d004340 stage
      (fun i ↦ _root_.GD.N0230.N0579.d004352 (fun g (p : X) ↦ g • p) (label i))
      (fun _ ↦ 0) x := by
    exact _root_.GD.N0230.N0559.d004365
      (fun i p ↦ label i • p) stage
      (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i)) x
      (fun n i hi ↦ _root_.GD.N0230.N0559.d004367
        risk weight hRisk hweight theta (x n) (hmin n) (htax n) (label i))
      hvanish
  rcases _root_.GD.N0230.N0579.d004358
      (fun i p ↦ label i • p) (fun i ↦ hstate (label i))
      stage hstage hmono x hresidual action hcompact with hfixed | hescape
  · left
    obtain ⟨y, hy⟩ := hfixed
    exact ⟨y, _root_.GD.N0230.N0579.d004360 label hlabel
      (fun g p ↦ g • p) y (hparameter y) hy⟩
  · exact Or.inr hescape



theorem d004373
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous (fun x : X ↦ g • x))
    (hparameter : ∀ x : X, Continuous (fun g : G ↦ g • x))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (risk : Theta → X → ℝ) (weight : G → ℝ)
    (hRisk : _root_.GD.N0230.N0557.d000040 risk weight)
    (hweight : ∀ g, 0 < weight g)
    (theta : Theta) (x : ℕ → X)
    (hmin : ∀ n, ∀ g : G,
      risk theta (x n) ≤ risk theta (g • x n))
    (htax : ∀ n, ∀ g : G,
      ‖g • x n - x n‖ ^ 2 ≤ _root_.GD.N0230.N0557.d000041 risk theta (x n) g)
    (hvanish : _root_.GD.N0230.N0559.d004363 stage
      (fun i p ↦ _root_.GD.N0230.N0557.d000042 risk theta p (label i)) x)
    (action : X → ℝ) (hcompact : _root_.GD.N0238.d004342 action)
    (hno : ¬ ∃ y : X, ∀ g : G, g • y = y) :
    _root_.GD.N0238.d004343 action x := by
  rcases _root_.GD.N0230.N0559.d004372
      label hlabel hstate hparameter stage hstage hmono
      risk weight hRisk hweight theta x hmin htax hvanish
      action hcompact with hfixed | hescape
  · exact False.elim (hno hfixed)
  · exact hescape

end DenseOrbitCirculation

end N0559
end N0230
end GD

#print axioms _root_.GD.N0230.N0559.d004364
#print axioms _root_.GD.N0230.N0559.d004366
#print axioms _root_.GD.N0230.N0559.d004367
#print axioms _root_.GD.N0230.N0559.d004368
#print axioms _root_.GD.N0230.N0559.d004369
#print axioms _root_.GD.N0230.N0559.d004370
#print axioms _root_.GD.N0230.N0559.d004371
#print axioms _root_.GD.N0230.N0559.d004372
#print axioms _root_.GD.N0230.N0559.d004373
