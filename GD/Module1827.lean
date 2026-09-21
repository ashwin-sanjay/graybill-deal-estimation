import GD.Module1826
import GD.Module1824
import GD.Module1813
import GD.Module1822
import GD.Module1818
import GD.Module1817
import GD.Module1810
import GD.Module1806

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0244

open MeasureTheory
open _root_.GD.N0236.N0745
open _root_.GD.N0005.N0248

theorem d030184
    {S Θ : Type*} [MeasurableSpace S]
    (μ : Θ → Measure S) (δ : Θ → ℝ) [∀ θ, IsProbabilityMeasure (μ θ)] :
    _root_.GD.N0236.N0745.d030178 μ δ ↔ _root_.GD.N0236.N0745.d030179 μ δ :=
  _root_.GD.N0236.N0745.d030183 μ δ

theorem d030185 :
    ¬ ∀ a b x y : ℝ, 0 < a → 0 < b →
      ∃! u : ℝ, ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 2 2 a b x y v ≤ _root_.GD.N0005.N0248.d030071 2 2 a b x y u := by
  intro h
  obtain ⟨a, b, x, y, u, v, ha, hb, hne, hu, hv⟩ := _root_.GD.N0005.N0248.d030106
  obtain ⟨z, _, hz⟩ := h a b x y ha hb
  exact hne ((hz u hu).trans (hz v hv).symm)

theorem d030186
    {Ω Θ I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (law : Θ → Measure Ω) (sample : I → Θ) (v : J → Ω → ℝ)
    (hv : ∀ i j, Integrable (v j) (law (sample i)))
    (target : Θ → ℝ)
    (hdet : Matrix.det
      ((_root_.GD.N0005.N0243.d029999 (law ∘ sample) v).transpose *
        _root_.GD.N0005.N0243.d029999 (law ∘ sample) v) ≠ 0)
    (hpos : 0 < _root_.GD.N0233.N0721.d004998
      (_root_.GD.N0005.N0243.d029999 (law ∘ sample) v) (target ∘ sample)) :
    ¬ ∃ x : J → ℝ, ∀ θ,
      ∫ ω, _root_.GD.N0005.N0243.d030000 v x ω ∂law θ = target θ := by
  rintro ⟨x, hx⟩
  exact _root_.GD.N0005.N0243.d030004
    (law ∘ sample) v hv hdet (target ∘ sample) hpos
    ⟨x, fun i => hx (sample i)⟩

end GD.N0005.N0244

#print axioms _root_.GD.N0005.N0244.d030184
#print axioms _root_.GD.N0236.N0745.d030151
#print axioms _root_.GD.N0236.N0745.d030156
#print axioms _root_.GD.N0236.N0745.d030177
#print axioms _root_.GD.N0236.N0745.d030160
#print axioms _root_.GD.N0236.N0745.d030162
#print axioms _root_.GD.N0236.N0745.d030163

#print axioms _root_.GD.N0005.N0245.d030051
#print axioms _root_.GD.N0005.N0245.d030053
#print axioms _root_.GD.N0005.N0246.d030067
#print axioms _root_.GD.N0005.N0246.d030068
#print axioms _root_.GD.N0005.N0246.d030069

#print axioms _root_.GD.N0005.N0248.d030079
#print axioms _root_.GD.N0005.N0248.d030080
#print axioms _root_.GD.N0005.N0248.d030081
#print axioms _root_.GD.N0005.N0248.d030082
#print axioms _root_.GD.N0005.N0248.d030085
#print axioms _root_.GD.N0005.N0248.d030093
#print axioms _root_.GD.N0005.N0248.d030126
#print axioms _root_.GD.N0005.N0248.d030135
#print axioms _root_.GD.N0005.N0247.d030142
#print axioms _root_.GD.N0005.N0247.d030144
#print axioms _root_.GD.N0005.N0247.d030141
#print axioms _root_.GD.N0005.N0247.d030137
#print axioms _root_.GD.N0005.N0247.d030138
#print axioms _root_.GD.N0005.N0247.d030139
#print axioms _root_.GD.N0005.N0247.d030140
#print axioms _root_.GD.N0005.N0248.d030095
#print axioms _root_.GD.N0005.N0248.d030096
#print axioms _root_.GD.N0005.N0248.d030097
#print axioms _root_.GD.N0005.N0248.d030104
#print axioms _root_.GD.N0005.N0248.d030105
#print axioms _root_.GD.N0005.N0248.d030106
#print axioms _root_.GD.N0005.N0248.d030112
#print axioms _root_.GD.N0005.N0248.d030117
#print axioms _root_.GD.N0005.N0248.d030108
#print axioms _root_.GD.N0005.N0248.d030109
#print axioms _root_.GD.N0005.N0248.d030110
#print axioms _root_.GD.N0005.N0244.d030185
#print axioms _root_.GD.N0005.N0244.d030186

#print axioms _root_.GD.N0005.N0252.d030015
#print axioms _root_.GD.N0005.N0252.d030024
#print axioms _root_.GD.N0005.N0252.d030026
#print axioms _root_.GD.N0005.N0252.d030027
#print axioms _root_.GD.N0005.N0250.d030035
#print axioms _root_.GD.N0005.N0250.d030036
#print axioms _root_.GD.N0005.N0251.d030037
#print axioms _root_.GD.N0005.N0251.d030038
#print axioms _root_.GD.N0005.N0251.d030039
#print axioms _root_.GD.N0005.N0249.d030040

#print axioms _root_.GD.N0005.N0243.d030001
#print axioms _root_.GD.N0005.N0243.d030002
#print axioms _root_.GD.N0005.N0243.d030003
#print axioms _root_.GD.N0005.N0243.d030004
#print axioms _root_.GD.N0233.N0721.d005001
#print axioms _root_.GD.N0233.N0722.d004989
