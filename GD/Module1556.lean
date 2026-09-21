import GD.Module0664

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0100.N0346

open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0720.N1290

noncomputable section


theorem d024017 (p : _root_.GD.N0232.N0719.N0983.d009709 2) :
    (_root_.GD.N0232.N0719.N0983.d009710 1 p : ℝ) = 1 - (_root_.GD.N0232.N0719.N0983.d009710 0 p : ℝ) := by
  have h := _root_.GD.N0232.N0719.N0983.d009712 p
  rw [Fin.sum_univ_two] at h
  linarith

def d024018 (t : _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0719.N0983.d009709 2 :=
  ⟨![t, ⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩],
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩

@[simp] theorem d024019 (t : _root_.GD.N0232.N0720.N1290.d004131) :
    _root_.GD.N0232.N0719.N0983.d009710 0 (_root_.GD.N0100.N0346.d024018 t) = t := rfl

@[simp] theorem d024020 (t : _root_.GD.N0232.N0720.N1290.d004131) :
    (_root_.GD.N0232.N0719.N0983.d009710 1 (_root_.GD.N0100.N0346.d024018 t) : ℝ) = 1 - (t : ℝ) := rfl

@[simp] theorem d024021 (p : _root_.GD.N0232.N0719.N0983.d009709 2) :
    _root_.GD.N0100.N0346.d024018 (_root_.GD.N0232.N0719.N0983.d009710 0 p) = p := by
  apply Subtype.ext
  funext i
  fin_cases i
  · rfl
  · apply Subtype.ext
    exact (_root_.GD.N0100.N0346.d024017 p).symm

def d024022 : _root_.GD.N0232.N0720.N1290.d004131 ≃ _root_.GD.N0232.N0719.N0983.d009709 2 where
  toFun := _root_.GD.N0100.N0346.d024018
  invFun := _root_.GD.N0232.N0719.N0983.d009710 0
  left_inv := _root_.GD.N0100.N0346.d024019
  right_inv := _root_.GD.N0100.N0346.d024021


def d024023 (x y r s : ℝ) (t : _root_.GD.N0232.N0720.N1290.d004131) : ℝ :=
  (t : ℝ) * r + (1 - (t : ℝ)) * s +
    (t : ℝ) * (1 - (t : ℝ)) * (x - y) ^ 2 / 2

theorem d024024 (y : Fin 2 → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 2) :
    _root_.GD.N0232.N0719.N0983.d009713 y p = (_root_.GD.N0232.N0719.N0983.d009710 0 p : ℝ) * y 0 +
      (1 - (_root_.GD.N0232.N0719.N0983.d009710 0 p : ℝ)) * y 1 := by
  simp only [_root_.GD.N0232.N0719.N0983.d009713, Fin.sum_univ_two, _root_.GD.N0100.N0346.d024017]


theorem d024025 (y r : Fin 2 → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 2) :
    _root_.GD.N0232.N0719.N0983.d009714 y r p = _root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1) (_root_.GD.N0232.N0719.N0983.d009710 0 p) := by
  simp only [_root_.GD.N0232.N0719.N0983.d009714, Fin.sum_univ_two, _root_.GD.N0100.N0346.d024024, _root_.GD.N0100.N0346.d024017,
    _root_.GD.N0100.N0346.d024023]
  ring

theorem d024026 (x y r s : ℝ) :
    Continuous (_root_.GD.N0100.N0346.d024023 x y r s) := by
  unfold _root_.GD.N0100.N0346.d024023
  fun_prop

theorem d024027 (x y r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < _root_.GD.N0100.N0346.d024023 x y r s t := by
  have h := _root_.GD.N0232.N0719.N0983.d009718 ![x, y] ![r, s]
    (by intro i; fin_cases i <;> simpa using ‹_›) (_root_.GD.N0100.N0346.d024018 t)
  simpa only [_root_.GD.N0100.N0346.d024025, _root_.GD.N0100.N0346.d024019,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

def d024028 (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) : Measure _root_.GD.N0232.N0720.N1290.d004131 :=
  Measure.map (_root_.GD.N0232.N0719.N0983.d009710 0) mu

instance d024029 (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (_root_.GD.N0100.N0346.d024028 mu) :=
  Measure.isProbabilityMeasure_map (_root_.GD.N0232.N0719.N0983.d009711 0).measurable.aemeasurable


theorem d024030 (q : ℝ) (y r : Fin 2 → ℝ)
    (hr : ∀ i, 0 < r i) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) :
    _root_.GD.N0232.N0719.N0983.d009723 q y r mu =
      _root_.GD.N0232.N0720.N1290.d004139 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (_root_.GD.N0100.N0346.d024028 mu) := by
  have hc : Continuous (fun t => _root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1) t ^ (-q)) :=
    (_root_.GD.N0100.N0346.d024026 _ _ _ _).rpow_const
      (fun t => Or.inl (_root_.GD.N0100.N0346.d024027 _ _ _ _ (hr 0) (hr 1) t).ne')
  rw [_root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0100.N0346.d024028,
    integral_map (_root_.GD.N0232.N0719.N0983.d009711 0).measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [_root_.GD.N0232.N0719.N0983.d009723, _root_.GD.N0232.N0719.N0983.d009720, _root_.GD.N0100.N0346.d024025]


theorem d024031 (q : ℝ) (y r : Fin 2 → ℝ)
    (hr : ∀ i, 0 < r i) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) :
    _root_.GD.N0232.N0719.N0983.d009725 q y r mu 0 =
      _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (_root_.GD.N0100.N0346.d024028 mu) := by
  have hc : Continuous (fun t : _root_.GD.N0232.N0720.N1290.d004131 => (t : ℝ) *
      _root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1) t ^ (-q)) :=
    continuous_subtype_val.mul ((_root_.GD.N0100.N0346.d024026 _ _ _ _).rpow_const
      (fun t => Or.inl (_root_.GD.N0100.N0346.d024027 _ _ _ _ (hr 0) (hr 1) t).ne'))
  unfold _root_.GD.N0232.N0719.N0983.d009725 _root_.GD.N0232.N0720.N1290.d004140
  rw [_root_.GD.N0100.N0346.d024030 q y r hr]
  congr 1
  rw [_root_.GD.N0100.N0346.d024028,
    integral_map (_root_.GD.N0232.N0719.N0983.d009711 0).measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [_root_.GD.N0232.N0719.N0983.d009720, _root_.GD.N0100.N0346.d024025]

theorem d024032 (q : ℝ) (y r : Fin 2 → ℝ)
    (hr : ∀ i, 0 < r i) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) [IsProbabilityMeasure mu]
    (i : Fin 2) : 0 ≤ _root_.GD.N0232.N0719.N0983.d009725 q y r mu i := by
  apply div_nonneg
  · exact integral_nonneg fun p =>
      mul_nonneg (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1 (_root_.GD.N0232.N0719.N0983.d009722 q y r hr p).le
  · exact (_root_.GD.N0232.N0719.N0983.d009728 q y r hr mu).le



theorem d024033 (q : ℝ) (y r : Fin 2 → ℝ)
    (hr : ∀ i, 0 < r i) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) [IsProbabilityMeasure mu] :
    let w := _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (_root_.GD.N0100.N0346.d024028 mu)
    w ∈ Icc (0 : ℝ) 1 ∧ _root_.GD.N0232.N0719.N0983.d009724 q y r mu = w * y 0 + (1 - w) * y 1 := by
  dsimp only
  rw [← _root_.GD.N0100.N0346.d024031 q y r hr mu]
  have hsum := _root_.GD.N0232.N0719.N0983.d009729 q y r hr mu
  rw [Fin.sum_univ_two] at hsum
  have hzero := _root_.GD.N0100.N0346.d024032 q y r hr mu 0
  have hone := _root_.GD.N0100.N0346.d024032 q y r hr mu 1
  constructor
  · exact ⟨hzero, by linarith⟩
  · rw [_root_.GD.N0232.N0719.N0983.d009730 q y r hr mu, Fin.sum_univ_two]
    congr 1
    congr 1
    linarith



theorem d024034 (mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 2)) :
    ∃ nu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131, ∀ (q : ℝ) (y r : Fin 2 → ℝ),
      (∀ i, 0 < r i) →
      let w := _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (nu : Measure _root_.GD.N0232.N0720.N1290.d004131)
      w ∈ Icc (0 : ℝ) 1 ∧
        _root_.GD.N0232.N0719.N0983.d009724 q y r (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) = w * y 0 + (1 - w) * y 1 := by
  refine ⟨⟨_root_.GD.N0100.N0346.d024028 (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)), inferInstance⟩, ?_⟩
  intro q y r hr
  exact _root_.GD.N0100.N0346.d024033 q y r hr (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2))



theorem d024035 (q : ℝ) (y r : Fin 2 → ℝ)
    (hr : ∀ i, 0 < r i) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 2)) [IsProbabilityMeasure mu]
    (hneq : y 0 ≠ y 1) (w : ℝ) :
    _root_.GD.N0232.N0719.N0983.d009724 q y r mu = y 1 + (y 0 - y 1) * w ↔
      _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (_root_.GD.N0100.N0346.d024028 mu) = w := by
  have hmix := (_root_.GD.N0100.N0346.d024033 q y r hr mu).2
  constructor
  · intro heq
    have hprod :
        (_root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0100.N0346.d024023 (y 0) (y 1) (r 0) (r 1)) (_root_.GD.N0100.N0346.d024028 mu) - w) *
          (y 0 - y 1) = 0 := by
      nlinarith [hmix, heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hneq))
  · intro heq
    rw [hmix, heq]
    ring

end
end GD.N0100.N0346

#print axioms _root_.GD.N0100.N0346.d024025
#print axioms _root_.GD.N0100.N0346.d024031
#print axioms _root_.GD.N0100.N0346.d024033
#print axioms _root_.GD.N0100.N0346.d024034
#print axioms _root_.GD.N0100.N0346.d024035
