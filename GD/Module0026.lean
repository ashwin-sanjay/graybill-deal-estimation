import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic























open MeasureTheory Set Filter

namespace GD
namespace N0230
namespace N0644

variable {G X Y : Type*}
  [MeasurableSpace X] [MeasurableSpace Y]




def d000295 (source : G → X → X) (good : Set X) : Prop :=
  ∀ g x, source g x ∈ good ↔ x ∈ good


def d000296
    (source : G → X → X) (target : G → Y → Y)
    (good : Set X) (value : X → Y) : Prop :=
  ∀ g x, x ∈ good → value (source g x) = target g (value x)


def d000297
    (source : G → X → X) (target : G → Y → Y)
    (value : X → Y) : Prop :=
  ∀ g x, value (source g x) = target g (value x)


noncomputable def d000298
    (good : Set X) (value fallback : X → Y) : X → Y := by
  classical
  exact good.piecewise value fallback

@[simp]
theorem d000299
    (good : Set X) (value fallback : X → Y)
    {x : X} (hx : x ∈ good) :
    _root_.GD.N0230.N0644.d000298 good value fallback x = value x := by
  simp [_root_.GD.N0230.N0644.d000298, hx]

@[simp]
theorem d000300
    (good : Set X) (value fallback : X → Y)
    {x : X} (hx : x ∉ good) :
    _root_.GD.N0230.N0644.d000298 good value fallback x = fallback x := by
  simp [_root_.GD.N0230.N0644.d000298, hx]


theorem d000301
    {good : Set X} {value fallback : X → Y}
    (hgood : MeasurableSet good)
    (hvalue : Measurable value) (hfallback : Measurable fallback) :
    Measurable (_root_.GD.N0230.N0644.d000298 good value fallback) := by
  classical
  simpa [_root_.GD.N0230.N0644.d000298] using
    hvalue.piecewise hgood hfallback



theorem d000302
    (mu : Measure X) {good : Set X} (value fallback : X → Y)
    (hconull : ∀ᵐ x ∂mu, x ∈ good) :
    _root_.GD.N0230.N0644.d000298 good value fallback =ᵐ[mu] value := by
  filter_upwards [hconull] with x hx
  exact _root_.GD.N0230.N0644.d000299 good value fallback hx



theorem d000303
    (mu : Measure X) {good : Set X} (value fallback original : X → Y)
    (hconull : ∀ᵐ x ∂mu, x ∈ good)
    (hvalue : value =ᵐ[mu] original) :
    _root_.GD.N0230.N0644.d000298 good value fallback =ᵐ[mu] original :=
  (_root_.GD.N0230.N0644.d000302 mu value fallback hconull).trans hvalue




theorem d000304
    (source : G → X → X) (target : G → Y → Y)
    {good : Set X} (value fallback : X → Y)
    (hinvariant : _root_.GD.N0230.N0644.d000295 source good)
    (hvalue : _root_.GD.N0230.N0644.d000296 source target good value)
    (hfallback : _root_.GD.N0230.N0644.d000297 source target fallback) :
    _root_.GD.N0230.N0644.d000297 source target
      (_root_.GD.N0230.N0644.d000298 good value fallback) := by
  intro g x
  by_cases hx : x ∈ good
  · have hgx : source g x ∈ good := (hinvariant g x).2 hx
    simp [_root_.GD.N0230.N0644.d000298, hx, hgx, hvalue g x hx]
  · have hgx : source g x ∉ good := by
      intro hsource
      exact hx ((hinvariant g x).1 hsource)
    simp [_root_.GD.N0230.N0644.d000298, hx, hgx, hfallback g x]





theorem d000305
    (mu : Measure X)
    (source : G → X → X) (target : G → Y → Y)
    (good : Set X) (value fallback : X → Y)
    (hgood : MeasurableSet good)
    (hconull : ∀ᵐ x ∂mu, x ∈ good)
    (hvalue_meas : Measurable value)
    (hfallback_meas : Measurable fallback)
    (hinvariant : _root_.GD.N0230.N0644.d000295 source good)
    (hvalue_equivariant :
      _root_.GD.N0230.N0644.d000296 source target good value)
    (hfallback_equivariant : _root_.GD.N0230.N0644.d000297 source target fallback) :
    ∃ repaired : X → Y,
      Measurable repaired ∧
      repaired =ᵐ[mu] value ∧
      _root_.GD.N0230.N0644.d000297 source target repaired := by
  refine ⟨_root_.GD.N0230.N0644.d000298 good value fallback, ?_, ?_, ?_⟩
  · exact _root_.GD.N0230.N0644.d000301 hgood hvalue_meas hfallback_meas
  · exact _root_.GD.N0230.N0644.d000302 mu value fallback hconull
  · exact _root_.GD.N0230.N0644.d000304 source target value fallback
      hinvariant hvalue_equivariant hfallback_equivariant



theorem d000306
    (mu : Measure X)
    (source : G → X → X) (target : G → Y → Y)
    (good : Set X) (value fallback original : X → Y)
    (hgood : MeasurableSet good)
    (hconull : ∀ᵐ x ∂mu, x ∈ good)
    (hvalue_meas : Measurable value)
    (hfallback_meas : Measurable fallback)
    (hinvariant : _root_.GD.N0230.N0644.d000295 source good)
    (hvalue_equivariant :
      _root_.GD.N0230.N0644.d000296 source target good value)
    (hfallback_equivariant : _root_.GD.N0230.N0644.d000297 source target fallback)
    (hvalue_original : value =ᵐ[mu] original) :
    ∃ repaired : X → Y,
      Measurable repaired ∧
      repaired =ᵐ[mu] original ∧
      _root_.GD.N0230.N0644.d000297 source target repaired := by
  refine ⟨_root_.GD.N0230.N0644.d000298 good value fallback, ?_, ?_, ?_⟩
  · exact _root_.GD.N0230.N0644.d000301 hgood hvalue_meas hfallback_meas
  · exact _root_.GD.N0230.N0644.d000303
      mu value fallback original hconull hvalue_original
  · exact _root_.GD.N0230.N0644.d000304 source target value fallback
      hinvariant hvalue_equivariant hfallback_equivariant

end N0644
end N0230
end GD

#print axioms _root_.GD.N0230.N0644.d000304
#print axioms _root_.GD.N0230.N0644.d000305
#print axioms _root_.GD.N0230.N0644.d000306
