import GD.Module0646

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0954

noncomputable section


def d009492 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) : _root_.GD.N0232.N0719.N0953.d003306 n
  | Sum.inl i => _root_.GD.N0232.N0719.N0953.d003307 x i
  | Sum.inr _ => ω

@[simp]
theorem d009493 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003308 (_root_.GD.N0232.N0719.N0954.d009492 x ω) = ω := by
  rfl

@[simp]
theorem d009494 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) (i : Fin n) :
    _root_.GD.N0232.N0719.N0953.d003307 (_root_.GD.N0232.N0719.N0954.d009492 x ω) i = _root_.GD.N0232.N0719.N0953.d003307 x i := by
  rfl

@[simp]
theorem d009495 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003309 (_root_.GD.N0232.N0719.N0954.d009492 x ω) = _root_.GD.N0232.N0719.N0953.d003309 x := by
  simp [_root_.GD.N0232.N0719.N0953.d003309, _root_.GD.N0232.N0719.N0954.d009492]

@[simp]
theorem d009496 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ)
    (i : _root_.GD.N0232.N0719.N0953.d003305 n) :
    _root_.GD.N0232.N0719.N0953.d003334 (_root_.GD.N0232.N0719.N0954.d009492 x ω) i =
      _root_.GD.N0232.N0719.N0953.d003334 x i := by
  cases i with
  | inl i => rfl
  | inr i =>
      fin_cases i
      exact _root_.GD.N0232.N0719.N0954.d009495 x ω

@[simp]
theorem d009497 {n : ℕ}
    (rate x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003337 rate (_root_.GD.N0232.N0719.N0954.d009492 x ω) =
      _root_.GD.N0232.N0719.N0953.d003337 rate x := by
  unfold _root_.GD.N0232.N0719.N0953.d003337
  simp

@[simp]
theorem d009498 {n : ℕ}
    (shape x : _root_.GD.N0232.N0719.N0953.d003306 n) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0954.d009482 shape (_root_.GD.N0232.N0719.N0954.d009492 x ω) =
      _root_.GD.N0232.N0719.N0954.d009482 shape x := by
  unfold _root_.GD.N0232.N0719.N0954.d009482
  apply Finset.prod_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0719.N0954.d009496]


theorem d009499
    {n : ℕ} {shape rate x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    (∫ ω : ℝ in Set.Ioi 0,
        ω ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
          Real.exp (-(ω * _root_.GD.N0232.N0719.N0953.d003337 rate x))) =
      (1 / _root_.GD.N0232.N0719.N0953.d003337 rate x) ^ (_root_.GD.N0232.N0719.N0954.d009479 shape) *
        Real.Gamma (_root_.GD.N0232.N0719.N0954.d009479 shape) := by
  have htotal :
      0 < _root_.GD.N0232.N0719.N0954.d009479 shape := by
    unfold _root_.GD.N0232.N0719.N0954.d009479
    exact Finset.sum_pos
      (fun i _ => hshape i)
      Finset.univ_nonempty
  have hprojectiveRate :
      0 < _root_.GD.N0232.N0719.N0953.d003337 rate x :=
    _root_.GD.N0232.N0719.N0953.d003338 hrate hx
  simpa [mul_comm] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi
      htotal hprojectiveRate)



def d009500 {n : ℕ}
    (shape rate x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009481 shape rate *
    Real.Gamma (_root_.GD.N0232.N0719.N0954.d009479 shape) *
    (_root_.GD.N0232.N0719.N0953.d003337 rate x) ^ (-_root_.GD.N0232.N0719.N0954.d009479 shape) *
    _root_.GD.N0232.N0719.N0954.d009482 shape x









theorem d009501
    {n : ℕ} {shape rate x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n)
    {ω : ℝ} (hω : 0 ≤ ω) :
    _root_.GD.N0232.N0719.N0954.d009483
        shape rate (_root_.GD.N0232.N0719.N0954.d009492 x ω) =
      _root_.GD.N0232.N0719.N0954.d009500 shape rate x *
        gammaPDFReal
          (_root_.GD.N0232.N0719.N0954.d009479 shape)
          (_root_.GD.N0232.N0719.N0953.d003337 rate x) ω := by
  have hA : 0 < _root_.GD.N0232.N0719.N0954.d009479 shape := by
    unfold _root_.GD.N0232.N0719.N0954.d009479
    exact Finset.sum_pos
      (fun i _ => hshape i)
      Finset.univ_nonempty
  have hR : 0 < _root_.GD.N0232.N0719.N0953.d003337 rate x :=
    _root_.GD.N0232.N0719.N0953.d003338 hrate hx
  unfold _root_.GD.N0232.N0719.N0954.d009483
    _root_.GD.N0232.N0719.N0954.d009500
  simp only [_root_.GD.N0232.N0719.N0954.d009493, _root_.GD.N0232.N0719.N0954.d009497,
    _root_.GD.N0232.N0719.N0954.d009498, gammaPDFReal, if_pos hω]
  rw [Real.rpow_neg hR.le]
  field_simp [
    (Real.Gamma_pos_of_pos hA).ne',
    (Real.rpow_pos_of_pos hR (_root_.GD.N0232.N0719.N0954.d009479 shape)).ne']


theorem d009502
    {n : ℕ} {shape rate x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    (∫ ω : ℝ in Set.Ioi 0,
        _root_.GD.N0232.N0719.N0954.d009483
          shape rate (_root_.GD.N0232.N0719.N0954.d009492 x ω)) =
      _root_.GD.N0232.N0719.N0954.d009500 shape rate x := by
  have hratePos :
      0 < _root_.GD.N0232.N0719.N0953.d003337 rate x :=
    _root_.GD.N0232.N0719.N0953.d003338 hrate hx
  simp only [_root_.GD.N0232.N0719.N0954.d009483, _root_.GD.N0232.N0719.N0954.d009493,
    _root_.GD.N0232.N0719.N0954.d009497, _root_.GD.N0232.N0719.N0954.d009498]
  rw [show
      (fun ω : ℝ =>
        _root_.GD.N0232.N0719.N0954.d009481 shape rate *
            ω ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
            Real.exp
              (-(ω *
                _root_.GD.N0232.N0719.N0953.d003337 rate x)) *
          _root_.GD.N0232.N0719.N0954.d009482 shape x) =
        fun ω =>
          (_root_.GD.N0232.N0719.N0954.d009481 shape rate *
              _root_.GD.N0232.N0719.N0954.d009482 shape x) *
            (ω ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
              Real.exp
                (-(ω *
                  _root_.GD.N0232.N0719.N0953.d003337 rate x))) by
      funext ω
      ring]
  rw [integral_const_mul]
  rw [_root_.GD.N0232.N0719.N0954.d009499 hshape hrate hx]
  unfold _root_.GD.N0232.N0719.N0954.d009500
  rw [one_div, Real.inv_rpow hratePos.le,
    ← Real.rpow_neg hratePos.le]
  ring

end

end GD.N0232.N0719.N0954
