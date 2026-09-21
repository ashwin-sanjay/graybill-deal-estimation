import GD.Module0230
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
































open scoped BigOperators Matrix
open MeasureTheory

namespace GD.N0232.N0719.N0953

noncomputable section


abbrev d003305 (n : ℕ) := Fin n ⊕ Fin 1


abbrev d003306 (n : ℕ) := _root_.GD.N0232.N0719.N0953.d003305 n → ℝ


def d003307 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) (i : Fin n) : ℝ :=
  x (Sum.inl i)


def d003308 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  x (Sum.inr 0)


def d003309 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  1 - ∑ i, _root_.GD.N0232.N0719.N0953.d003307 x i


def d003310 (n : ℕ) : Set (_root_.GD.N0232.N0719.N0953.d003306 n) :=
  {t | ∀ i, 0 < t i}


def d003311 (n : ℕ) : Set (_root_.GD.N0232.N0719.N0953.d003306 n) :=
  {x | 0 < _root_.GD.N0232.N0719.N0953.d003308 x ∧ (∀ i, 0 < _root_.GD.N0232.N0719.N0953.d003307 x i) ∧ 0 < _root_.GD.N0232.N0719.N0953.d003309 x}


def d003312 {n : ℕ} (t : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  (∑ i, (t (Sum.inl i))⁻¹) + (t (Sum.inr 0))⁻¹


def d003313 {n : ℕ} (t : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  (_root_.GD.N0232.N0719.N0953.d003312 t)⁻¹


def d003314 {n : ℕ} (t : _root_.GD.N0232.N0719.N0953.d003306 n) : _root_.GD.N0232.N0719.N0953.d003306 n
  | Sum.inl i => _root_.GD.N0232.N0719.N0953.d003313 t / t (Sum.inl i)
  | Sum.inr _ => _root_.GD.N0232.N0719.N0953.d003313 t


def d003315 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) : _root_.GD.N0232.N0719.N0953.d003306 n
  | Sum.inl i => _root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003307 x i
  | Sum.inr _ => _root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003309 x

theorem d003316 {n : ℕ} {t : _root_.GD.N0232.N0719.N0953.d003306 n}
    (ht : t ∈ _root_.GD.N0232.N0719.N0953.d003310 n) :
    0 < _root_.GD.N0232.N0719.N0953.d003312 t := by
  unfold _root_.GD.N0232.N0719.N0953.d003312
  apply add_pos_of_nonneg_of_pos
  · exact Finset.sum_nonneg fun i _ => (inv_pos.mpr (ht (Sum.inl i))).le
  · exact inv_pos.mpr (ht (Sum.inr 0))

theorem d003317 {n : ℕ} {t : _root_.GD.N0232.N0719.N0953.d003306 n}
    (ht : t ∈ _root_.GD.N0232.N0719.N0953.d003310 n) :
    0 < _root_.GD.N0232.N0719.N0953.d003313 t :=
  inv_pos.mpr (_root_.GD.N0232.N0719.N0953.d003316 ht)

@[simp]
theorem d003318 {n : ℕ} (t : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003308 (_root_.GD.N0232.N0719.N0953.d003314 t) = _root_.GD.N0232.N0719.N0953.d003313 t := by
  rfl

@[simp]
theorem d003319 {n : ℕ} (t : _root_.GD.N0232.N0719.N0953.d003306 n) (i : Fin n) :
    _root_.GD.N0232.N0719.N0953.d003307 (_root_.GD.N0232.N0719.N0953.d003314 t) i =
      _root_.GD.N0232.N0719.N0953.d003313 t / t (Sum.inl i) := by
  rfl

theorem d003320 {n : ℕ} {t : _root_.GD.N0232.N0719.N0953.d003306 n}
    (ht : t ∈ _root_.GD.N0232.N0719.N0953.d003310 n) :
    _root_.GD.N0232.N0719.N0953.d003309 (_root_.GD.N0232.N0719.N0953.d003314 t) =
      _root_.GD.N0232.N0719.N0953.d003313 t / t (Sum.inr 0) := by
  have hm : _root_.GD.N0232.N0719.N0953.d003312 t ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0719.N0953.d003316 ht)
  have hunit :
      _root_.GD.N0232.N0719.N0953.d003313 t * _root_.GD.N0232.N0719.N0953.d003312 t = 1 := by
    exact inv_mul_cancel₀ hm
  have hsum :
      ∑ i, _root_.GD.N0232.N0719.N0953.d003307 (_root_.GD.N0232.N0719.N0953.d003314 t) i =
        _root_.GD.N0232.N0719.N0953.d003313 t * ∑ i, (t (Sum.inl i))⁻¹ := by
    simp only [_root_.GD.N0232.N0719.N0953.d003319, div_eq_mul_inv, Finset.mul_sum]
  rw [_root_.GD.N0232.N0719.N0953.d003309, hsum]
  calc
    1 - _root_.GD.N0232.N0719.N0953.d003313 t * ∑ i, (t (Sum.inl i))⁻¹ =
        _root_.GD.N0232.N0719.N0953.d003313 t * _root_.GD.N0232.N0719.N0953.d003312 t -
          _root_.GD.N0232.N0719.N0953.d003313 t * ∑ i, (t (Sum.inl i))⁻¹ := by
            rw [hunit]
    _ = _root_.GD.N0232.N0719.N0953.d003313 t * (t (Sum.inr 0))⁻¹ := by
      unfold _root_.GD.N0232.N0719.N0953.d003312
      ring
    _ = _root_.GD.N0232.N0719.N0953.d003313 t / t (Sum.inr 0) := by
      rw [div_eq_mul_inv]

theorem d003321 {n : ℕ} {t : _root_.GD.N0232.N0719.N0953.d003306 n}
    (ht : t ∈ _root_.GD.N0232.N0719.N0953.d003310 n) :
    _root_.GD.N0232.N0719.N0953.d003314 t ∈ _root_.GD.N0232.N0719.N0953.d003311 n := by
  refine ⟨_root_.GD.N0232.N0719.N0953.d003317 ht, ?_, ?_⟩
  · intro i
    exact div_pos (_root_.GD.N0232.N0719.N0953.d003317 ht) (ht (Sum.inl i))
  · rw [_root_.GD.N0232.N0719.N0953.d003320 ht]
    exact div_pos (_root_.GD.N0232.N0719.N0953.d003317 ht) (ht (Sum.inr 0))

theorem d003322 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0953.d003315 x ∈ _root_.GD.N0232.N0719.N0953.d003310 n := by
  intro i
  cases i with
  | inl i => exact div_pos hx.1 (hx.2.1 i)
  | inr i =>
      fin_cases i
      exact div_pos hx.1 hx.2.2

theorem d003323 {n : ℕ} {t : _root_.GD.N0232.N0719.N0953.d003306 n}
    (ht : t ∈ _root_.GD.N0232.N0719.N0953.d003310 n) :
    _root_.GD.N0232.N0719.N0953.d003315 (_root_.GD.N0232.N0719.N0953.d003314 t) = t := by
  funext i
  cases i with
  | inl i =>
      change _root_.GD.N0232.N0719.N0953.d003313 t /
          (_root_.GD.N0232.N0719.N0953.d003313 t / t (Sum.inl i)) = t (Sum.inl i)
      field_simp [ne_of_gt (_root_.GD.N0232.N0719.N0953.d003317 ht),
        ne_of_gt (ht (Sum.inl i))]
  | inr i =>
      fin_cases i
      change _root_.GD.N0232.N0719.N0953.d003313 t /
          _root_.GD.N0232.N0719.N0953.d003309 (_root_.GD.N0232.N0719.N0953.d003314 t) = t (Sum.inr 0)
      rw [_root_.GD.N0232.N0719.N0953.d003320 ht]
      field_simp [ne_of_gt (_root_.GD.N0232.N0719.N0953.d003317 ht),
        ne_of_gt (ht (Sum.inr 0))]

theorem d003324 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0953.d003312 (_root_.GD.N0232.N0719.N0953.d003315 x) = (_root_.GD.N0232.N0719.N0953.d003308 x)⁻¹ := by
  have hω : _root_.GD.N0232.N0719.N0953.d003308 x ≠ 0 := ne_of_gt hx.1
  have hp : ∀ i, _root_.GD.N0232.N0719.N0953.d003307 x i ≠ 0 :=
    fun i => ne_of_gt (hx.2.1 i)
  have hplast : _root_.GD.N0232.N0719.N0953.d003309 x ≠ 0 := ne_of_gt hx.2.2
  unfold _root_.GD.N0232.N0719.N0953.d003312 _root_.GD.N0232.N0719.N0953.d003315
  simp_rw [inv_div, ← Finset.sum_div]
  rw [← add_div]
  have hweights :
      (∑ i, _root_.GD.N0232.N0719.N0953.d003307 x i) + _root_.GD.N0232.N0719.N0953.d003309 x = 1 := by
    unfold _root_.GD.N0232.N0719.N0953.d003309
    ring
  rw [hweights, one_div]

theorem d003325 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0953.d003313 (_root_.GD.N0232.N0719.N0953.d003315 x) = _root_.GD.N0232.N0719.N0953.d003308 x := by
  rw [_root_.GD.N0232.N0719.N0953.d003313, _root_.GD.N0232.N0719.N0953.d003324 hx, inv_inv]

theorem d003326 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0953.d003315 x) = x := by
  funext i
  cases i with
  | inl i =>
      change _root_.GD.N0232.N0719.N0953.d003313 (_root_.GD.N0232.N0719.N0953.d003315 x) /
          (_root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003307 x i) =
        _root_.GD.N0232.N0719.N0953.d003307 x i
      rw [_root_.GD.N0232.N0719.N0953.d003325 hx]
      field_simp [ne_of_gt hx.1, ne_of_gt (hx.2.1 i)]
  | inr i =>
      fin_cases i
      exact _root_.GD.N0232.N0719.N0953.d003325 hx



theorem d003327 (n : ℕ) :
    _root_.GD.N0232.N0719.N0953.d003314 '' _root_.GD.N0232.N0719.N0953.d003310 n = _root_.GD.N0232.N0719.N0953.d003311 n := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact _root_.GD.N0232.N0719.N0953.d003321 ht
  · intro hx
    exact ⟨_root_.GD.N0232.N0719.N0953.d003315 x, _root_.GD.N0232.N0719.N0953.d003322 hx, _root_.GD.N0232.N0719.N0953.d003326 hx⟩

theorem d003328 (n : ℕ) :
    Set.InjOn _root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0953.d003310 n) := by
  intro t ht u hu htu
  rw [← _root_.GD.N0232.N0719.N0953.d003323 ht, ← _root_.GD.N0232.N0719.N0953.d003323 hu, htu]

theorem d003329 (n : ℕ) :
    Set.BijOn _root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0953.d003310 n) (_root_.GD.N0232.N0719.N0953.d003311 n) := by
  refine ⟨fun _ ht => _root_.GD.N0232.N0719.N0953.d003321 ht, _root_.GD.N0232.N0719.N0953.d003328 n, ?_⟩
  intro x hx
  exact ⟨_root_.GD.N0232.N0719.N0953.d003315 x, _root_.GD.N0232.N0719.N0953.d003322 hx, _root_.GD.N0232.N0719.N0953.d003326 hx⟩

theorem d003330 (n : ℕ) :
    _root_.GD.N0232.N0719.N0953.d003315 '' _root_.GD.N0232.N0719.N0953.d003311 n = _root_.GD.N0232.N0719.N0953.d003310 n := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact _root_.GD.N0232.N0719.N0953.d003322 hx
  · intro ht
    exact ⟨_root_.GD.N0232.N0719.N0953.d003314 t, _root_.GD.N0232.N0719.N0953.d003321 ht, _root_.GD.N0232.N0719.N0953.d003323 ht⟩

theorem d003331 (n : ℕ) :
    Set.InjOn _root_.GD.N0232.N0719.N0953.d003315 (_root_.GD.N0232.N0719.N0953.d003311 n) := by
  intro x hx y hy hxy
  rw [← _root_.GD.N0232.N0719.N0953.d003326 hx, ← _root_.GD.N0232.N0719.N0953.d003326 hy, hxy]

theorem d003332 (n : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0719.N0953.d003310 n) := by
  have hcoord :
      ∀ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        Measurable (fun t : _root_.GD.N0232.N0719.N0953.d003306 n => t i) := by
    intro i
    fun_prop
  rw [show _root_.GD.N0232.N0719.N0953.d003310 n =
      ⋂ i : _root_.GD.N0232.N0719.N0953.d003305 n, {t : _root_.GD.N0232.N0719.N0953.d003306 n | 0 < t i} by
    ext t
    simp [_root_.GD.N0232.N0719.N0953.d003310]]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (hcoord i)

theorem d003333 (n : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0719.N0953.d003311 n) := by
  have hzero :
      Measurable (fun _ : _root_.GD.N0232.N0719.N0953.d003306 n => (0 : ℝ)) :=
    measurable_const
  have hradial :
      Measurable (_root_.GD.N0232.N0719.N0953.d003308 : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ) := by
    unfold _root_.GD.N0232.N0719.N0953.d003308
    fun_prop
  have hfree :
      ∀ i : Fin n,
        Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 n => _root_.GD.N0232.N0719.N0953.d003307 x i) := by
    intro i
    unfold _root_.GD.N0232.N0719.N0953.d003307
    fun_prop
  have hlast :
      Measurable (_root_.GD.N0232.N0719.N0953.d003309 : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ) := by
    unfold _root_.GD.N0232.N0719.N0953.d003309
    fun_prop
  rw [show _root_.GD.N0232.N0719.N0953.d003311 n =
      ({x : _root_.GD.N0232.N0719.N0953.d003306 n | 0 < _root_.GD.N0232.N0719.N0953.d003308 x} ∩
        (⋂ i : Fin n, {x | 0 < _root_.GD.N0232.N0719.N0953.d003307 x i})) ∩
        {x | 0 < _root_.GD.N0232.N0719.N0953.d003309 x} by
    ext x
    simp [_root_.GD.N0232.N0719.N0953.d003311, and_assoc]]
  exact
    ((measurableSet_lt hzero hradial).inter
      (MeasurableSet.iInter fun i =>
        measurableSet_lt hzero (hfree i))).inter
      (measurableSet_lt hzero hlast)




def d003334 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003305 n → ℝ
  | Sum.inl i => _root_.GD.N0232.N0719.N0953.d003307 x i
  | Sum.inr _ => _root_.GD.N0232.N0719.N0953.d003309 x

theorem d003335 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    ∑ i, _root_.GD.N0232.N0719.N0953.d003334 x i = 1 := by
  rw [Fintype.sum_sum_type]
  simp [_root_.GD.N0232.N0719.N0953.d003334, _root_.GD.N0232.N0719.N0953.d003309]

theorem d003336 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) (i : _root_.GD.N0232.N0719.N0953.d003305 n) :
    0 < _root_.GD.N0232.N0719.N0953.d003334 x i := by
  cases i with
  | inl i => exact hx.2.1 i
  | inr i =>
      fin_cases i
      exact hx.2.2



def d003337 {n : ℕ}
    (rate : _root_.GD.N0232.N0719.N0953.d003306 n) (x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  (∑ i, rate (Sum.inl i) / _root_.GD.N0232.N0719.N0953.d003307 x i) +
    rate (Sum.inr 0) / _root_.GD.N0232.N0719.N0953.d003309 x

theorem d003338 {n : ℕ}
    {rate x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hrate : ∀ i, 0 < rate i)
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    0 < _root_.GD.N0232.N0719.N0953.d003337 rate x := by
  unfold _root_.GD.N0232.N0719.N0953.d003337
  apply add_pos_of_nonneg_of_pos
  · exact Finset.sum_nonneg fun i _ =>
      (div_pos (hrate (Sum.inl i)) (hx.2.1 i)).le
  · exact div_pos (hrate (Sum.inr 0)) hx.2.2





theorem d003339 {n : ℕ}
    (rate x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    (∑ i, rate (Sum.inl i) * _root_.GD.N0232.N0719.N0953.d003315 x (Sum.inl i)) +
        rate (Sum.inr 0) * _root_.GD.N0232.N0719.N0953.d003315 x (Sum.inr 0) =
      _root_.GD.N0232.N0719.N0953.d003308 x * _root_.GD.N0232.N0719.N0953.d003337 rate x := by
  unfold _root_.GD.N0232.N0719.N0953.d003315 _root_.GD.N0232.N0719.N0953.d003337
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring






def d003340 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    Matrix (_root_.GD.N0232.N0719.N0953.d003305 n) (_root_.GD.N0232.N0719.N0953.d003305 n) ℝ
  | Sum.inl i, Sum.inl j =>
      if i = j then -_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2 else 0
  | Sum.inl i, Sum.inr _ => 1 / _root_.GD.N0232.N0719.N0953.d003307 x i
  | Sum.inr _, Sum.inl _ => _root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2
  | Sum.inr _, Sum.inr _ => 1 / _root_.GD.N0232.N0719.N0953.d003309 x




noncomputable def d003341 {n : ℕ} (i : _root_.GD.N0232.N0719.N0953.d003305 n) :
    _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

@[simp]
theorem d003342 {n : ℕ}
    (i : _root_.GD.N0232.N0719.N0953.d003305 n) (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003341 i x = x i := by
  simp [_root_.GD.N0232.N0719.N0953.d003341]



noncomputable def d003343 {n : ℕ} :
    _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
  ∑ i : Fin n, _root_.GD.N0232.N0719.N0953.d003341 (Sum.inl i)

@[simp]
theorem d003344 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003343 x = ∑ i, x (Sum.inl i) := by
  simp [_root_.GD.N0232.N0719.N0953.d003343]



noncomputable def d003345 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003306 n →ₗ[ℝ] _root_.GD.N0232.N0719.N0953.d003306 n where
  toFun h
    | Sum.inl i =>
        (-_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2) * h (Sum.inl i) +
          (1 / _root_.GD.N0232.N0719.N0953.d003307 x i) * h (Sum.inr 0)
    | Sum.inr _ =>
        (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) *
            (∑ i, h (Sum.inl i)) +
          (1 / _root_.GD.N0232.N0719.N0953.d003309 x) * h (Sum.inr 0)
  map_add' h g := by
    funext i
    cases i with
    | inl i =>
        simp only [Pi.add_apply]
        ring
    | inr i =>
        fin_cases i
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        ring
  map_smul' c h := by
    funext i
    cases i with
    | inl i =>
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
    | inr i =>
        fin_cases i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← Finset.mul_sum]
        ring



noncomputable def d003346 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] _root_.GD.N0232.N0719.N0953.d003306 n :=
  LinearMap.toContinuousLinearMap (_root_.GD.N0232.N0719.N0953.d003345 x)

@[simp]
theorem d003347 {n : ℕ}
    (x h : _root_.GD.N0232.N0719.N0953.d003306 n) (i : Fin n) :
    _root_.GD.N0232.N0719.N0953.d003346 x h (Sum.inl i) =
      (-_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2) * h (Sum.inl i) +
        (1 / _root_.GD.N0232.N0719.N0953.d003307 x i) * h (Sum.inr 0) := by
  rfl

@[simp]
theorem d003348 {n : ℕ}
    (x h : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003346 x h (Sum.inr 0) =
      (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) *
          (∑ i, h (Sum.inl i)) +
        (1 / _root_.GD.N0232.N0719.N0953.d003309 x) * h (Sum.inr 0) := by
  rfl



theorem d003349 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    HasFDerivAt _root_.GD.N0232.N0719.N0953.d003315 (_root_.GD.N0232.N0719.N0953.d003346 x) x := by
  let dRadial : _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
    _root_.GD.N0232.N0719.N0953.d003341 (Sum.inr 0)
  let dFree : Fin n → _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
    fun i => _root_.GD.N0232.N0719.N0953.d003341 (Sum.inl i)
  have hRadial :
      HasFDerivAt (_root_.GD.N0232.N0719.N0953.d003308 : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ) dRadial x := by
    change
      HasFDerivAt
        (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => y (Sum.inr 0))
        (_root_.GD.N0232.N0719.N0953.d003341 (Sum.inr 0)) x
    exact (_root_.GD.N0232.N0719.N0953.d003341 (Sum.inr 0)).hasFDerivAt
  have hFree :
      ∀ i, HasFDerivAt
        (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => _root_.GD.N0232.N0719.N0953.d003307 y i) (dFree i) x := by
    intro i
    change
      HasFDerivAt
        (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => y (Sum.inl i))
        (_root_.GD.N0232.N0719.N0953.d003341 (Sum.inl i)) x
    exact (_root_.GD.N0232.N0719.N0953.d003341 (Sum.inl i)).hasFDerivAt
  have hFreeSum :
      HasFDerivAt
        (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => ∑ i, _root_.GD.N0232.N0719.N0953.d003307 y i)
        _root_.GD.N0232.N0719.N0953.d003343 x := by
    convert (_root_.GD.N0232.N0719.N0953.d003343 (n := n)).hasFDerivAt using 1 <;>
      try rfl
    funext y
    simp [_root_.GD.N0232.N0719.N0953.d003343, _root_.GD.N0232.N0719.N0953.d003307]
  have hLast := hFreeSum.const_sub (1 : ℝ)
  let dInvFree : Fin n → _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
    fun i =>
      (ContinuousLinearMap.toSpanSingleton ℝ
          (-((_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)⁻¹)).comp
        (dFree i)
  let dInvLast : _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ
        (-((_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2)⁻¹)).comp
      (-_root_.GD.N0232.N0719.N0953.d003343)
  have hInvFree :
      ∀ i, HasFDerivAt
        (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => (_root_.GD.N0232.N0719.N0953.d003307 y i)⁻¹)
        (dInvFree i) x := by
    intro i
    exact
      (hasFDerivAt_inv (ne_of_gt (hx.2.1 i))).comp x (hFree i)
  have hLast_ne :
      1 - ∑ i, _root_.GD.N0232.N0719.N0953.d003307 x i ≠ 0 := by
    simpa only [_root_.GD.N0232.N0719.N0953.d003309] using ne_of_gt hx.2.2
  have hInvLast :=
    (hasFDerivAt_inv hLast_ne).comp x hLast
  let dComp :
      _root_.GD.N0232.N0719.N0953.d003305 n → _root_.GD.N0232.N0719.N0953.d003306 n →L[ℝ] ℝ
    | Sum.inl i =>
        _root_.GD.N0232.N0719.N0953.d003308 x • dInvFree i + (_root_.GD.N0232.N0719.N0953.d003307 x i)⁻¹ • dRadial
    | Sum.inr _ =>
        _root_.GD.N0232.N0719.N0953.d003308 x • dInvLast + (_root_.GD.N0232.N0719.N0953.d003309 x)⁻¹ • dRadial
  have hComponent :
      ∀ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        HasFDerivAt (fun y : _root_.GD.N0232.N0719.N0953.d003306 n => _root_.GD.N0232.N0719.N0953.d003315 y i)
          (dComp i) x := by
    intro i
    cases i with
    | inl i =>
        convert hRadial.mul (hInvFree i) using 1 <;>
          try rfl <;>
          simp [_root_.GD.N0232.N0719.N0953.d003315, div_eq_mul_inv, dComp]
    | inr i =>
        fin_cases i
        convert hRadial.mul hInvLast using 1 <;>
          try rfl <;>
          simp [_root_.GD.N0232.N0719.N0953.d003315, div_eq_mul_inv, dComp]
  have hD :
      HasFDerivAt _root_.GD.N0232.N0719.N0953.d003315 (ContinuousLinearMap.pi dComp) x :=
    hasFDerivAt_pi.2 hComponent
  have hDeq :
      ContinuousLinearMap.pi dComp = _root_.GD.N0232.N0719.N0953.d003346 x := by
    apply ContinuousLinearMap.ext
    intro h
    funext i
    cases i with
    | inl i =>
        simp only [ContinuousLinearMap.pi_apply, dComp, dInvFree,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, dRadial, dFree,
          _root_.GD.N0232.N0719.N0953.d003342, _root_.GD.N0232.N0719.N0953.d003347, smul_eq_mul]
        field_simp [ne_of_gt (hx.2.1 i)]
    | inr i =>
        fin_cases i
        change
          (ContinuousLinearMap.pi dComp) h (Sum.inr 0) =
            _root_.GD.N0232.N0719.N0953.d003346 x h (Sum.inr 0)
        simp only [ContinuousLinearMap.pi_apply, dComp, dInvLast,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, dRadial,
          _root_.GD.N0232.N0719.N0953.d003342, _root_.GD.N0232.N0719.N0953.d003344,
          _root_.GD.N0232.N0719.N0953.d003348, zero_apply, zero_sub, neg_apply,
          smul_eq_mul]
        field_simp [ne_of_gt hx.2.2]
  exact hD.congr_fderiv hDeq

theorem d003350 {n : ℕ}
    {x : _root_.GD.N0232.N0719.N0953.d003306 n} (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    DifferentiableWithinAt ℝ _root_.GD.N0232.N0719.N0953.d003315 (_root_.GD.N0232.N0719.N0953.d003311 n) x :=
  (_root_.GD.N0232.N0719.N0953.d003349 hx).differentiableAt.differentiableWithinAt



theorem d003351 {n : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003345 x =
      Matrix.toLin' (_root_.GD.N0232.N0719.N0953.d003340 x) := by
  apply LinearMap.ext
  intro h
  funext i
  cases i with
  | inl i =>
      simp [_root_.GD.N0232.N0719.N0953.d003345, _root_.GD.N0232.N0719.N0953.d003340,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, RingHom.id_apply]
  | inr i =>
      fin_cases i
      simp [_root_.GD.N0232.N0719.N0953.d003345, _root_.GD.N0232.N0719.N0953.d003340,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, Finset.mul_sum, RingHom.id_apply]



theorem d003352 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    (_root_.GD.N0232.N0719.N0953.d003346 x).det = Matrix.det (_root_.GD.N0232.N0719.N0953.d003340 x) := by
  unfold _root_.GD.N0232.N0719.N0953.d003346
  rw [LinearMap.det_toContinuousLinearMap,
    _root_.GD.N0232.N0719.N0953.d003351, LinearMap.det_toLin']



def d003353 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    _root_.GD.N0232.N0719.N0953.d003305 n → ℝ
  | Sum.inl i => -_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2
  | Sum.inr _ => _root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2


def d003354 {n : ℕ} (x : _root_.GD.N0232.N0719.N0953.d003306 n) :
    Matrix (_root_.GD.N0232.N0719.N0953.d003305 n) (_root_.GD.N0232.N0719.N0953.d003305 n) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin n) (Fin n) ℝ)
    (fun i _ => -_root_.GD.N0232.N0719.N0953.d003307 x i / _root_.GD.N0232.N0719.N0953.d003308 x)
    (fun _ _ => 1)
    (fun _ _ => _root_.GD.N0232.N0719.N0953.d003309 x / _root_.GD.N0232.N0719.N0953.d003308 x)

theorem d003355 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0953.d003340 x =
      Matrix.diagonal (_root_.GD.N0232.N0719.N0953.d003353 x) * _root_.GD.N0232.N0719.N0953.d003354 x := by
  ext i j
  rw [Matrix.diagonal_mul]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases hij : i = j
          · subst j
            simp [_root_.GD.N0232.N0719.N0953.d003340, _root_.GD.N0232.N0719.N0953.d003353, _root_.GD.N0232.N0719.N0953.d003354]
          · simp [_root_.GD.N0232.N0719.N0953.d003340, _root_.GD.N0232.N0719.N0953.d003353, _root_.GD.N0232.N0719.N0953.d003354, hij]
      | inr j =>
          fin_cases j
          simp [_root_.GD.N0232.N0719.N0953.d003340, _root_.GD.N0232.N0719.N0953.d003353, _root_.GD.N0232.N0719.N0953.d003354,
            ne_of_gt hx.1, ne_of_gt (hx.2.1 i)]
          field_simp [ne_of_gt hx.1, ne_of_gt (hx.2.1 i)]
  | inr i =>
      fin_cases i
      cases j with
      | inl j =>
          simp [_root_.GD.N0232.N0719.N0953.d003340, _root_.GD.N0232.N0719.N0953.d003353, _root_.GD.N0232.N0719.N0953.d003354]
      | inr j =>
          fin_cases j
          simp [_root_.GD.N0232.N0719.N0953.d003340, _root_.GD.N0232.N0719.N0953.d003353, _root_.GD.N0232.N0719.N0953.d003354]
          field_simp [ne_of_gt hx.1, ne_of_gt hx.2.2]

theorem d003356 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    Matrix.det (_root_.GD.N0232.N0719.N0953.d003354 x) = 1 / _root_.GD.N0232.N0719.N0953.d003308 x := by
  unfold _root_.GD.N0232.N0719.N0953.d003354
  rw [Matrix.det_fromBlocks_one₁₁]
  simp [Matrix.mul_apply, _root_.GD.N0232.N0719.N0953.d003309, ← Finset.sum_div]
  field_simp [ne_of_gt hx.1]
  ring


theorem d003357 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    Matrix.det (_root_.GD.N0232.N0719.N0953.d003340 x) =
      (∏ i, (-_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
        (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0953.d003355 hx, Matrix.det_mul,
    Matrix.det_diagonal, _root_.GD.N0232.N0719.N0953.d003356 hx]
  simp [_root_.GD.N0232.N0719.N0953.d003353]
  field_simp [ne_of_gt hx.1, ne_of_gt hx.2.2]



theorem d003358 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    |Matrix.det (_root_.GD.N0232.N0719.N0953.d003340 x)| =
      (∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
        (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0953.d003357 hx, abs_div, abs_pow]
  rw [Finset.abs_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [abs_div, abs_neg, abs_of_pos hx.1, abs_pow,
      abs_of_pos (hx.2.1 i)]
  · rw [abs_of_pos hx.2.2]

theorem d003359 {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    |(_root_.GD.N0232.N0719.N0953.d003346 x).det| =
      (∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
        (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0953.d003352, _root_.GD.N0232.N0719.N0953.d003358 hx]












theorem d003360
    {n : ℕ} (G : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ) :
    (∫ t in _root_.GD.N0232.N0719.N0953.d003310 n, G t) =
      ∫ x in _root_.GD.N0232.N0719.N0953.d003311 n,
        |(_root_.GD.N0232.N0719.N0953.d003346 x).det| • G (_root_.GD.N0232.N0719.N0953.d003315 x) := by
  have hTarget : MeasurableSet (_root_.GD.N0232.N0719.N0953.d003311 n) :=
    _root_.GD.N0232.N0719.N0953.d003333 n
  have hFDeriv :
      ∀ x ∈ _root_.GD.N0232.N0719.N0953.d003311 n,
        HasFDerivWithinAt _root_.GD.N0232.N0719.N0953.d003315 (_root_.GD.N0232.N0719.N0953.d003346 x) (_root_.GD.N0232.N0719.N0953.d003311 n) x :=
    fun x hx => (_root_.GD.N0232.N0719.N0953.d003349 hx).hasFDerivWithinAt
  rw [← _root_.GD.N0232.N0719.N0953.d003330 n]
  exact
    integral_image_eq_integral_abs_det_fderiv_smul
      MeasureTheory.volume hTarget hFDeriv (_root_.GD.N0232.N0719.N0953.d003331 n) G









theorem d003361
    {n : ℕ} (G : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ) :
    (∫ t in _root_.GD.N0232.N0719.N0953.d003310 n, G t) =
      ∫ x in _root_.GD.N0232.N0719.N0953.d003311 n,
        ((∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
            (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) *
          G (_root_.GD.N0232.N0719.N0953.d003315 x) := by
  rw [_root_.GD.N0232.N0719.N0953.d003360]
  apply setIntegral_congr_fun (_root_.GD.N0232.N0719.N0953.d003333 n)
  intro x hx
  change
    |(_root_.GD.N0232.N0719.N0953.d003346 x).det| • G (_root_.GD.N0232.N0719.N0953.d003315 x) =
      ((∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
          (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) *
        G (_root_.GD.N0232.N0719.N0953.d003315 x)
  rw [_root_.GD.N0232.N0719.N0953.d003359 hx, smul_eq_mul]

end

end GD.N0232.N0719.N0953
