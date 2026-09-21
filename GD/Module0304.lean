import GD.Module0073
import GD.Module0303


















namespace GD
namespace N0230
namespace N0677

open _root_.GD.N0238
open _root_.GD.N0230.N0559
open _root_.GD.N0230.N0571
open _root_.GD.N0230.N0579
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0676

variable {G I Theta Rule : Type*}
variable [TopologicalSpace G] [Group G]
variable [MulAction G Theta] [MulAction G Rule]
variable [MetricSpace Rule]


abbrev d004383
    (risk : Theta → Rule → ENNReal) (cap : Theta → ENNReal) :=
  {d : Rule // d ∈ _root_.GD.N0230.N0676.d000920 risk cap}



def d004384
    (risk : Theta → Rule → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (g : G) (d : _root_.GD.N0230.N0677.d004383 risk cap) :
    _root_.GD.N0230.N0677.d004383 risk cap :=
  ⟨g • (d : Rule),
    (_root_.GD.N0230.N0676.d000921
      risk cap weight hRisk hCap (d : Rule) g).2 d.property⟩

omit [TopologicalSpace G] [MetricSpace Rule] in
@[simp]
theorem d004385
    (risk : Theta → Rule → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (g : G) (d : _root_.GD.N0230.N0677.d004383 risk cap) :
    (_root_.GD.N0230.N0677.d004384 risk cap weight hRisk hCap g d : Rule) =
      g • (d : Rule) :=
  rfl












theorem d004386
    (risk : Theta → Rule → ENNReal) (cap : Theta → ENNReal)
    (weight : G → ENNReal)
    (hRisk : _root_.GD.N0230.N0676.d000914 risk weight)
    (hCap : _root_.GD.N0230.N0676.d000915 cap weight)
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous
      (_root_.GD.N0230.N0677.d004384 risk cap weight hRisk hCap g))
    (hparameter : ∀ d : _root_.GD.N0230.N0677.d004383 risk cap, Continuous
      (fun g : G ↦
        _root_.GD.N0230.N0677.d004384 risk cap weight hRisk hCap g d))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : I → _root_.GD.N0230.N0677.d004383 risk cap → ℝ)
    (point : ℕ → _root_.GD.N0230.N0677.d004383 risk cap)
    (henergy : ∀ n, ∀ i ∈ stage n,
      dist
          (_root_.GD.N0230.N0677.d004384 risk cap weight hRisk hCap
            (label i) (point n))
          (point n) ^ 2 ≤
        energy i (point n))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy point)
    (control : _root_.GD.N0230.N0677.d004383 risk cap → ℝ)
    (hcompact : _root_.GD.N0238.d004342 control)
    (hbounded : _root_.GD.N0238.d004344 control point) :
    ∃ d : Rule,
      _root_.GD.N0230.N0571.d000684 risk cap d ∧
      _root_.GD.N0230.N0608.d000674 risk d ∧
      ∀ g : G, g • d = d := by
  let act : G → _root_.GD.N0230.N0677.d004383 risk cap →
      _root_.GD.N0230.N0677.d004383 risk cap :=
    _root_.GD.N0230.N0677.d004384 risk cap weight hRisk hCap
  have hresidual : _root_.GD.N0238.d004340 stage
      (fun i ↦ _root_.GD.N0230.N0579.d004352 act (label i)) (fun _ ↦ 0) point := by
    exact _root_.GD.N0230.N0559.d004365
      (fun i d ↦ act (label i) d) stage energy point henergy hvanish
  obtain ⟨d, hfixed⟩ :=
    _root_.GD.N0230.N0579.d004362
      label hlabel act hstate hparameter stage hstage hmono point
        hresidual control hcompact hbounded
  have hfixedRule : ∀ g : G, g • (d : Rule) = (d : Rule) := by
    intro g
    have h := congrArg Subtype.val (hfixed g)
    simpa [act] using h
  exact ⟨(d : Rule), d.property.1, d.property.2, hfixedRule⟩

end N0677
end N0230
end GD

#print axioms _root_.GD.N0230.N0677.d004386
