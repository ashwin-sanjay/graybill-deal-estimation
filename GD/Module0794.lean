import GD.Module0793






























open Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0957

noncomputable section

open _root_.GD.N0232.N0719.N0958


def d012044 {k : ℕ}
    (active : Finset (Fin k)) (x : Fin k → ℝ) : ℝ :=
  ∑ i ∈ active, x i


def d012045 {k : ℕ}
    (active : Finset (Fin k)) (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  x i / _root_.GD.N0232.N0719.N0957.d012044 active x


theorem d012046
    {k : ℕ} (active : Finset (Fin k)) (x : Fin k → ℝ)
    (hmass : _root_.GD.N0232.N0719.N0957.d012044 active x ≠ 0) :
    ∑ i ∈ active, _root_.GD.N0232.N0719.N0957.d012045 active x i = 1 := by
  unfold _root_.GD.N0232.N0719.N0957.d012045 _root_.GD.N0232.N0719.N0957.d012044
  rw [← Finset.sum_div]
  exact div_self hmass



theorem d012047
    {k : ℕ} (outer inner : Finset (Fin k)) (x : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0957.d012044 inner (_root_.GD.N0232.N0719.N0957.d012045 outer x) =
      _root_.GD.N0232.N0719.N0957.d012044 inner x / _root_.GD.N0232.N0719.N0957.d012044 outer x := by
  simp only [_root_.GD.N0232.N0719.N0957.d012044, _root_.GD.N0232.N0719.N0957.d012045]
  rw [← Finset.sum_div]







theorem d012048
    {k : ℕ} (middle final : Finset (Fin k)) (x : Fin k → ℝ)
    (hmiddle : _root_.GD.N0232.N0719.N0957.d012044 middle x ≠ 0)
    (hfinal : _root_.GD.N0232.N0719.N0957.d012044 final x ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 final (_root_.GD.N0232.N0719.N0957.d012045 middle x) = _root_.GD.N0232.N0719.N0957.d012045 final x := by
  funext i
  change
    _root_.GD.N0232.N0719.N0957.d012045 middle x i /
        _root_.GD.N0232.N0719.N0957.d012044 final (_root_.GD.N0232.N0719.N0957.d012045 middle x) =
      x i / _root_.GD.N0232.N0719.N0957.d012044 final x
  rw [_root_.GD.N0232.N0719.N0957.d012047]
  change
    (x i / _root_.GD.N0232.N0719.N0957.d012044 middle x) /
        (_root_.GD.N0232.N0719.N0957.d012044 final x / _root_.GD.N0232.N0719.N0957.d012044 middle x) =
      x i / _root_.GD.N0232.N0719.N0957.d012044 final x
  field_simp [hmiddle, hfinal]


theorem d012049
    {k : ℕ} (active : Finset (Fin k)) (x : Fin k → ℝ)
    (hmass : _root_.GD.N0232.N0719.N0957.d012044 active x ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 active (_root_.GD.N0232.N0719.N0957.d012045 active x) = _root_.GD.N0232.N0719.N0957.d012045 active x := by
  exact _root_.GD.N0232.N0719.N0957.d012048 active active x hmass hmass



theorem d012050
    {k : ℕ} {active : Finset (Fin k)} (hactive : active.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0958.d012032 active theta := by
  unfold _root_.GD.N0232.N0719.N0958.d012032
  exact Finset.sum_pos'
    (fun i _ ↦ (theta.scale_pos i).le)
    (by
      obtain ⟨i, hi⟩ := hactive
      exact ⟨i, hi, theta.scale_pos i⟩)


theorem d012051
    {k : ℕ} (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0958.d012033 active theta = _root_.GD.N0232.N0719.N0957.d012045 active theta.scale := by
  funext i
  rfl


theorem d012052
    {k : ℕ} {outer inner : Finset (Fin k)}
    (houter : outer.Nonempty) (hinner : inner.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0957.d012045 inner (_root_.GD.N0232.N0719.N0958.d012033 outer theta) =
      _root_.GD.N0232.N0719.N0958.d012033 inner theta := by
  change _root_.GD.N0232.N0719.N0957.d012045 inner (_root_.GD.N0232.N0719.N0957.d012045 outer theta.scale) =
    _root_.GD.N0232.N0719.N0957.d012045 inner theta.scale
  exact _root_.GD.N0232.N0719.N0957.d012048 outer inner theta.scale
    (_root_.GD.N0232.N0719.N0957.d012050 houter theta).ne'
    (_root_.GD.N0232.N0719.N0957.d012050 hinner theta).ne'


theorem d012053
    {k : ℕ} {first middle final : Finset (Fin k)}
    (hfirst : first.Nonempty) (hmiddle : middle.Nonempty)
    (hfinal : final.Nonempty)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0957.d012045 final
        (_root_.GD.N0232.N0719.N0957.d012045 middle (_root_.GD.N0232.N0719.N0958.d012033 first theta)) =
      _root_.GD.N0232.N0719.N0958.d012033 final theta := by
  rw [_root_.GD.N0232.N0719.N0957.d012052 hfirst hmiddle theta]
  exact _root_.GD.N0232.N0719.N0957.d012052 hmiddle hfinal theta



theorem d012054
    {k : ℕ} (active : Finset (Fin k)) (w : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0958.d012035 active w =
      _root_.GD.N0232.N0719.N0957.d012045 active (fun i ↦ (Real.sqrt (w i))⁻¹) := by
  funext i
  rfl


theorem d012055
    {k : ℕ} (outer inner : Finset (Fin k)) (w : Fin k → ℝ) :
    ∑ i ∈ inner, _root_.GD.N0232.N0719.N0958.d012035 outer w i =
      _root_.GD.N0232.N0719.N0958.d012034 inner w /
        _root_.GD.N0232.N0719.N0958.d012034 outer w := by
  unfold _root_.GD.N0232.N0719.N0958.d012035 _root_.GD.N0232.N0719.N0958.d012034
  rw [← Finset.sum_div]






theorem d012056
    {k : ℕ} (outer inner : Finset (Fin k)) (w : Fin k → ℝ)
    (houter : _root_.GD.N0232.N0719.N0958.d012034 outer w ≠ 0)
    (hinner : _root_.GD.N0232.N0719.N0958.d012034 inner w ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 inner (_root_.GD.N0232.N0719.N0958.d012035 outer w) =
      _root_.GD.N0232.N0719.N0958.d012035 inner w := by
  change _root_.GD.N0232.N0719.N0957.d012045 inner
      (_root_.GD.N0232.N0719.N0957.d012045 outer (fun i ↦ (Real.sqrt (w i))⁻¹)) =
    _root_.GD.N0232.N0719.N0957.d012045 inner (fun i ↦ (Real.sqrt (w i))⁻¹)
  exact _root_.GD.N0232.N0719.N0957.d012048 outer inner
    (fun i ↦ (Real.sqrt (w i))⁻¹) houter hinner


theorem d012057
    {k : ℕ} (outer inner : Finset (Fin k)) (w : Fin k → ℝ)
    (houter : _root_.GD.N0232.N0719.N0958.d012034 outer w ≠ 0)
    (hinner : _root_.GD.N0232.N0719.N0958.d012034 inner w ≠ 0)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0958.d012035 inner w i =
      _root_.GD.N0232.N0719.N0958.d012035 outer w i /
        (∑ j ∈ inner, _root_.GD.N0232.N0719.N0958.d012035 outer w j) := by
  have htransition := congrFun
    (_root_.GD.N0232.N0719.N0957.d012056 outer inner w houter hinner) i
  exact htransition.symm



theorem d012058
    {k : ℕ} {outer inner : Finset (Fin k)}
    (houter : outer.Nonempty) (hinner : inner.Nonempty)
    (w : Fin k → ℝ)
    (hwOuter : ∀ i ∈ outer, 0 < w i)
    (hwInner : ∀ i ∈ inner, 0 < w i) :
    _root_.GD.N0232.N0719.N0957.d012045 inner (_root_.GD.N0232.N0719.N0958.d012035 outer w) =
      _root_.GD.N0232.N0719.N0958.d012035 inner w := by
  exact _root_.GD.N0232.N0719.N0957.d012056 outer inner w
    (_root_.GD.N0232.N0719.N0958.d012036 houter hwOuter).ne'
    (_root_.GD.N0232.N0719.N0958.d012036 hinner hwInner).ne'






theorem d012059
    {k : ℕ} (first middle final : Finset (Fin k))
    (w : Fin k → ℝ)
    (hfirst : _root_.GD.N0232.N0719.N0958.d012034 first w ≠ 0)
    (hmiddle : _root_.GD.N0232.N0719.N0958.d012034 middle w ≠ 0)
    (hfinal : _root_.GD.N0232.N0719.N0958.d012034 final w ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 final
        (_root_.GD.N0232.N0719.N0957.d012045 middle (_root_.GD.N0232.N0719.N0958.d012035 first w)) =
      _root_.GD.N0232.N0719.N0958.d012035 final w := by
  rw [_root_.GD.N0232.N0719.N0957.d012056 first middle w
      hfirst hmiddle]
  exact _root_.GD.N0232.N0719.N0957.d012056 middle final w
    hmiddle hfinal



theorem d012060
    {k : ℕ} (first middle final : Finset (Fin k))
    (w : Fin k → ℝ)
    (hfirst : _root_.GD.N0232.N0719.N0958.d012034 first w ≠ 0)
    (hmiddle : _root_.GD.N0232.N0719.N0958.d012034 middle w ≠ 0)
    (hfinal : _root_.GD.N0232.N0719.N0958.d012034 final w ≠ 0) :
    _root_.GD.N0232.N0719.N0957.d012045 final
        (_root_.GD.N0232.N0719.N0957.d012045 middle (_root_.GD.N0232.N0719.N0958.d012035 first w)) =
      _root_.GD.N0232.N0719.N0957.d012045 final (_root_.GD.N0232.N0719.N0958.d012035 first w) := by
  rw [_root_.GD.N0232.N0719.N0957.d012059 first middle final w
      hfirst hmiddle hfinal]
  symm
  exact _root_.GD.N0232.N0719.N0957.d012056 first final w
    hfirst hfinal



theorem d012061
    {k : ℕ} {first middle final : Finset (Fin k)}
    (hfirst : first.Nonempty) (hmiddle : middle.Nonempty)
    (hfinal : final.Nonempty) (w : Fin k → ℝ)
    (hwFirst : ∀ i ∈ first, 0 < w i)
    (hwMiddle : ∀ i ∈ middle, 0 < w i)
    (hwFinal : ∀ i ∈ final, 0 < w i) :
    _root_.GD.N0232.N0719.N0957.d012045 final
        (_root_.GD.N0232.N0719.N0957.d012045 middle (_root_.GD.N0232.N0719.N0958.d012035 first w)) =
      _root_.GD.N0232.N0719.N0958.d012035 final w := by
  exact _root_.GD.N0232.N0719.N0957.d012059 first middle final w
    (_root_.GD.N0232.N0719.N0958.d012036 hfirst hwFirst).ne'
    (_root_.GD.N0232.N0719.N0958.d012036 hmiddle hwMiddle).ne'
    (_root_.GD.N0232.N0719.N0958.d012036 hfinal hwFinal).ne'

end

end N0957
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0957.d012048
#print axioms _root_.GD.N0232.N0719.N0957.d012056
#print axioms _root_.GD.N0232.N0719.N0957.d012059
