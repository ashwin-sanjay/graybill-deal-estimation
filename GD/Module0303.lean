import GD.Module0302
import GD.Module0058
import GD.Module0083





























namespace GD
namespace N0230
namespace N0699

open _root_.GD.N0238
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0559
open _root_.GD.N0230.N0579
open _root_.GD.N0230.N0625
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0697
open _root_.GD.N0230.N0700

variable {G I Theta Rule : Type*}
variable [TopologicalSpace G] [Group G]
variable [MulAction G Theta] [MulAction G Rule]
variable [MetricSpace Rule]


abbrev d004374
    (risk : Theta → Rule → ℝ) (safe : Rule → Prop) (bar : Rule) :=
  {d : Rule // d ∈ _root_.GD.N0230.N0697.d001077 risk safe bar}




def d004375
    (risk : Theta → Rule → ℝ) (safe : Rule → Prop) (bar : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (hbar : ∀ g : G, g • bar = bar)
    (g : G) (d : _root_.GD.N0230.N0699.d004374 risk safe bar) :
    _root_.GD.N0230.N0699.d004374 risk safe bar :=
  ⟨g • (d : Rule), by
    have htransported :
        g • (d : Rule) ∈
          _root_.GD.N0230.N0697.d001077 risk safe (g • bar) :=
      (_root_.GD.N0230.N0700.d001110
        risk safe hRisk hSafe g bar (d : Rule)).2 d.property
    simpa only [hbar g] using htransported⟩

omit [TopologicalSpace G] [MetricSpace Rule] in
@[simp]
theorem d004376
    (risk : Theta → Rule → ℝ) (safe : Rule → Prop) (bar : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (hbar : ∀ g : G, g • bar = bar)
    (g : G) (d : _root_.GD.N0230.N0699.d004374 risk safe bar) :
    (_root_.GD.N0230.N0699.d004375 risk safe bar hRisk hSafe hbar g d : Rule) =
      g • (d : Rule) :=
  rfl















theorem d004377
    (risk : Theta → Rule → ℝ) (safe : Rule → Prop) (bar : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (hbar : ∀ g : G, g • bar = bar)
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous
      (_root_.GD.N0230.N0699.d004375 risk safe bar hRisk hSafe hbar g))
    (hparameter : ∀ d : _root_.GD.N0230.N0699.d004374 risk safe bar, Continuous
      (fun g : G ↦
        _root_.GD.N0230.N0699.d004375 risk safe bar hRisk hSafe hbar g d))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : I → _root_.GD.N0230.N0699.d004374 risk safe bar → ℝ)
    (point : ℕ → _root_.GD.N0230.N0699.d004374 risk safe bar)
    (henergy : ∀ n, ∀ i ∈ stage n,
      dist
          (_root_.GD.N0230.N0699.d004375 risk safe bar hRisk hSafe hbar
            (label i) (point n))
          (point n) ^ 2 ≤
        energy i (point n))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy point)
    (action : _root_.GD.N0230.N0699.d004374 risk safe bar → ℝ)
    (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action point) :
    ∃ d : Rule,
      safe d ∧
      _root_.GD.N0230.N0630.d000786 risk d ∧
      _root_.GD.N0230.N0556.d000028 risk d bar ∧
      ∀ g : G, g • d = d := by
  let act : G → _root_.GD.N0230.N0699.d004374 risk safe bar →
      _root_.GD.N0230.N0699.d004374 risk safe bar :=
    _root_.GD.N0230.N0699.d004375 risk safe bar hRisk hSafe hbar
  have hresidual : _root_.GD.N0238.d004340 stage
      (fun i ↦ _root_.GD.N0230.N0579.d004352 act (label i)) (fun _ ↦ 0) point := by
    exact _root_.GD.N0230.N0559.d004365
      (fun i d ↦ act (label i) d) stage energy point henergy hvanish
  obtain ⟨d, hfixed⟩ :=
    _root_.GD.N0230.N0579.d004362
      label hlabel act hstate hparameter stage hstage hmono point
        hresidual action hcompact hbounded
  have hfixedRule : ∀ g : G, g • (d : Rule) = (d : Rule) := by
    intro g
    have h := congrArg Subtype.val (hfixed g)
    simpa [act] using h
  exact
    ⟨(d : Rule), d.property.1, d.property.2.1, d.property.2.2,
      hfixedRule⟩



omit [TopologicalSpace G] [MetricSpace Rule] in



theorem d004378
    (risk : Theta → Rule → ENNReal)
    (hRisk :
      _root_.GD.N0230.N0610.d000707
        (G := G) risk)
    {d : Rule}
    (hd : _root_.GD.N0230.N0608.d000674 risk d)
    (g : G) :
    _root_.GD.N0230.N0608.d000674 risk (g • d) := by
  intro e he
  have hback :
      _root_.GD.N0230.N0608.d000672
        risk (g⁻¹ • e) d := by
    have htransported :=
      _root_.GD.N0230.N0610.d000710
        risk hRisk he g⁻¹
    simpa using htransported
  have heq : g⁻¹ • e = d := hd (g⁻¹ • e) hback
  calc
    e = g • (g⁻¹ • e) := by simp
    _ = g • d := by rw [heq]


abbrev d004379
    (risk : Theta → Rule → ENNReal) (bar : Rule) :=
  {d : Rule //
    _root_.GD.N0230.N0608.d000673 risk bar d ∧
      _root_.GD.N0230.N0608.d000674 risk d}




def d004380
    (risk : Theta → Rule → ENNReal) (bar : Rule)
    (hRisk :
      _root_.GD.N0230.N0610.d000707
        (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (g : G) (d : _root_.GD.N0230.N0699.d004379 risk bar) :
    _root_.GD.N0230.N0699.d004379 risk bar :=
  ⟨g • (d : Rule),
    ⟨_root_.GD.N0230.N0610.d000712
        risk hRisk bar hbar d.property.1 g,
      _root_.GD.N0230.N0699.d004378 risk hRisk d.property.2 g⟩⟩

omit [TopologicalSpace G] [MetricSpace Rule] in
@[simp]
theorem d004381
    (risk : Theta → Rule → ENNReal) (bar : Rule)
    (hRisk :
      _root_.GD.N0230.N0610.d000707
        (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (g : G) (d : _root_.GD.N0230.N0699.d004379 risk bar) :
    (_root_.GD.N0230.N0699.d004380 risk bar hRisk hbar g d : Rule) =
      g • (d : Rule) :=
  rfl













theorem d004382
    (risk : Theta → Rule → ENNReal) (bar : Rule)
    (hRisk :
      _root_.GD.N0230.N0610.d000707
        (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (label : I → G) (hlabel : DenseRange label)
    (hstate : ∀ g : G, Continuous
      (_root_.GD.N0230.N0699.d004380 risk bar hRisk hbar g))
    (hparameter : ∀ d : _root_.GD.N0230.N0699.d004379 risk bar, Continuous
      (fun g : G ↦
        _root_.GD.N0230.N0699.d004380 risk bar hRisk hbar g d))
    (stage : ℕ → Finset I) (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : I → _root_.GD.N0230.N0699.d004379 risk bar → ℝ)
    (point : ℕ → _root_.GD.N0230.N0699.d004379 risk bar)
    (henergy : ∀ n, ∀ i ∈ stage n,
      dist
          (_root_.GD.N0230.N0699.d004380 risk bar hRisk hbar
            (label i) (point n))
          (point n) ^ 2 ≤
        energy i (point n))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy point)
    (action : _root_.GD.N0230.N0699.d004379 risk bar → ℝ)
    (hcompact : _root_.GD.N0238.d004342 action)
    (hbounded : _root_.GD.N0238.d004344 action point) :
    ∃ d : Rule,
      _root_.GD.N0230.N0608.d000673 risk bar d ∧
      _root_.GD.N0230.N0608.d000674 risk d ∧
      ∀ g : G, g • d = d := by
  let act : G → _root_.GD.N0230.N0699.d004379 risk bar →
      _root_.GD.N0230.N0699.d004379 risk bar :=
    _root_.GD.N0230.N0699.d004380 risk bar hRisk hbar
  have hresidual : _root_.GD.N0238.d004340 stage
      (fun i ↦ _root_.GD.N0230.N0579.d004352 act (label i)) (fun _ ↦ 0) point := by
    exact _root_.GD.N0230.N0559.d004365
      (fun i d ↦ act (label i) d) stage energy point henergy hvanish
  obtain ⟨d, hfixed⟩ :=
    _root_.GD.N0230.N0579.d004362
      label hlabel act hstate hparameter stage hstage hmono point
        hresidual action hcompact hbounded
  have hfixedRule : ∀ g : G, g • (d : Rule) = (d : Rule) := by
    intro g
    have h := congrArg Subtype.val (hfixed g)
    simpa [act] using h
  exact ⟨(d : Rule), d.property.1, d.property.2, hfixedRule⟩

end N0699
end N0230
end GD

#print axioms _root_.GD.N0230.N0699.d004377
#print axioms _root_.GD.N0230.N0699.d004382
