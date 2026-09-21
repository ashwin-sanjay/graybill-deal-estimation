import GD.Module0650
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntegrableOn
















open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0853

noncomputable section



def d009566 {k : ℕ} (hk : 0 < k)
    (p : Fin k → ℝ) : _root_.GD.N0232.N0719.N0857.d009377 k :=
  fun j =>
    p (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j))



def d009567 {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (i : Fin k) : ℝ :=
  match (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
  | Sum.inl j => q j
  | Sum.inr _ => 1 - ∑ j, q j

@[simp]
theorem d009568
    {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (j : Fin (k - 1)) :
    _root_.GD.N0232.N0719.N0853.d009567 hk q
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j)) =
      q j := by
  simp [_root_.GD.N0232.N0719.N0853.d009567]

@[simp]
theorem d009569
    {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0853.d009567 hk q
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inr 0)) =
      1 - ∑ j, q j := by
  simp [_root_.GD.N0232.N0719.N0853.d009567]

theorem d009570
    {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) :
    ∑ i, _root_.GD.N0232.N0719.N0853.d009567 hk q i = 1 := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  rw [show
      (∑ i : Fin k, _root_.GD.N0232.N0719.N0853.d009567 hk q i) =
        ∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          _root_.GD.N0232.N0719.N0853.d009567 hk q (e j) by
    symm
    exact Fintype.sum_equiv e _ _ fun _ => rfl]
  rw [Fintype.sum_sum_type]
  simp only [_root_.GD.N0232.N0719.N0853.d009567, e, Equiv.symm_apply_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (∑ j, q j) + (1 - ∑ j, q j) = 1
  ring

theorem d009571
    {k : ℕ} (hk : 0 < k)
    {p : Fin k → ℝ}
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0853.d009567 hk (_root_.GD.N0232.N0719.N0853.d009566 hk p) = p := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  have hsum' :
      (∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          p (e j)) = 1 := by
    rw [← hsum]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [Fintype.sum_sum_type, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero] at hsum'
  funext i
  rw [← e.apply_symm_apply i]
  cases hi : e.symm i with
  | inl j =>
      simp [_root_.GD.N0232.N0719.N0853.d009567, _root_.GD.N0232.N0719.N0853.d009566, e, hi]
  | inr j =>
      fin_cases j
      have homit :
          1 - ∑ j : Fin (k - 1), p (e (Sum.inl j)) =
            p (e (Sum.inr 0)) := by
        linarith
      simpa [_root_.GD.N0232.N0719.N0853.d009567, _root_.GD.N0232.N0719.N0853.d009566, e] using homit



def d009572 {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0857.d009377 k :=
  _root_.GD.N0232.N0719.N0853.d009566 hk anchor +
    _root_.GD.N0232.N0719.N0857.d009386 k • u

theorem d009573
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k) :
    _root_.GD.N0232.N0719.N0853.d009566 hk (_root_.GD.N0232.N0719.N0857.d009388 hk anchor u) =
      _root_.GD.N0232.N0719.N0853.d009572 hk anchor u := by
  funext j
  have huj : u j ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨hu.1 j, hu.2 j⟩
  simp [_root_.GD.N0232.N0719.N0853.d009566, _root_.GD.N0232.N0719.N0853.d009572, _root_.GD.N0232.N0719.N0857.d009388,
    _root_.GD.N0232.N0719.N0857.d009381 huj, Pi.smul_apply, smul_eq_mul]

theorem d009574
    {k : ℕ} (hk : 0 < k)
    {anchor : Fin k → ℝ}
    (hanchor : ∑ i, anchor i = 1)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k) :
    _root_.GD.N0232.N0719.N0853.d009567 hk (_root_.GD.N0232.N0719.N0853.d009572 hk anchor u) =
      _root_.GD.N0232.N0719.N0857.d009388 hk anchor u := by
  rw [← _root_.GD.N0232.N0719.N0853.d009573 hk anchor hu]
  exact
    _root_.GD.N0232.N0719.N0853.d009571 hk
      (_root_.GD.N0232.N0719.N0857.d009391 hk hanchor u)


def d009575 (k : ℕ) :
    _root_.GD.N0232.N0719.N0857.d009377 k →L[ℝ] _root_.GD.N0232.N0719.N0857.d009377 k :=
  LinearMap.toContinuousLinearMap
    (_root_.GD.N0232.N0719.N0857.d009386 k •
      (LinearMap.id : _root_.GD.N0232.N0719.N0857.d009377 k →ₗ[ℝ] _root_.GD.N0232.N0719.N0857.d009377 k))

theorem d009576
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    HasFDerivAt
      (_root_.GD.N0232.N0719.N0853.d009572 hk anchor)
      (_root_.GD.N0232.N0719.N0853.d009575 k) u := by
  have hF :
      (_root_.GD.N0232.N0719.N0857.d009386 k •
          ContinuousLinearMap.id ℝ
            (_root_.GD.N0232.N0719.N0857.d009377 k)) =
        _root_.GD.N0232.N0719.N0853.d009575 k := by
    ext x i
    rfl
  have h :=
    (((hasFDerivAt_id u).const_smul (𝕜 := ℝ)
      (_root_.GD.N0232.N0719.N0857.d009386 k)).const_add
      (_root_.GD.N0232.N0719.N0853.d009566 hk anchor))
  rw [hF] at h
  simpa [_root_.GD.N0232.N0719.N0853.d009572, Pi.smul_apply, smul_eq_mul, add_comm] using h

theorem d009577 (k : ℕ) :
    (_root_.GD.N0232.N0719.N0853.d009575 k).det = _root_.GD.N0232.N0719.N0857.d009401 k := by
  unfold _root_.GD.N0232.N0719.N0853.d009575 _root_.GD.N0232.N0719.N0857.d009401
  rw [LinearMap.det_toContinuousLinearMap,
    LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fin_fun]

theorem d009578
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) :
    Function.Injective (_root_.GD.N0232.N0719.N0853.d009572 hk anchor) := by
  intro u v huv
  funext j
  have hj := congrFun huv j
  have hmul :
      _root_.GD.N0232.N0719.N0857.d009386 k * u j =
        _root_.GD.N0232.N0719.N0857.d009386 k * v j := by
    simpa [_root_.GD.N0232.N0719.N0853.d009572, Pi.smul_apply, smul_eq_mul]
      using hj
  exact mul_left_cancel₀ (_root_.GD.N0232.N0719.N0857.d009387 hk).ne' hmul





theorem d009579
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ)
    (g : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ) :
    (∫ q in _root_.GD.N0232.N0719.N0853.d009572 hk anchor '' _root_.GD.N0232.N0719.N0857.d009383 k, g q) =
      _root_.GD.N0232.N0719.N0857.d009401 k *
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k, g (_root_.GD.N0232.N0719.N0853.d009572 hk anchor u) := by
  have hcov :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume)
      (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
      (fun u _ =>
        (_root_.GD.N0232.N0719.N0853.d009576 hk anchor u).hasFDerivWithinAt)
      (_root_.GD.N0232.N0719.N0853.d009578 hk anchor).injOn g
  calc
    (∫ q in _root_.GD.N0232.N0719.N0853.d009572 hk anchor '' _root_.GD.N0232.N0719.N0857.d009383 k, g q) =
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          |(_root_.GD.N0232.N0719.N0853.d009575 k).det| •
            g (_root_.GD.N0232.N0719.N0853.d009572 hk anchor u) := hcov
    _ =
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0857.d009401 k *
            g (_root_.GD.N0232.N0719.N0853.d009572 hk anchor u) := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
      intro u _
      rw [_root_.GD.N0232.N0719.N0853.d009577,
        abs_of_pos (_root_.GD.N0232.N0719.N0857.d009402 hk)]
      rfl
    _ =
        _root_.GD.N0232.N0719.N0857.d009401 k *
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            g (_root_.GD.N0232.N0719.N0853.d009572 hk anchor u) := by
      rw [integral_const_mul]

theorem d009580
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) :
    MeasurableSet
      (_root_.GD.N0232.N0719.N0853.d009572 hk anchor '' _root_.GD.N0232.N0719.N0857.d009383 k) := by
  exact measurable_image_of_fderivWithin
    (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
    (fun u _ =>
      (_root_.GD.N0232.N0719.N0853.d009576 hk anchor u).hasFDerivWithinAt)
    (_root_.GD.N0232.N0719.N0853.d009578 hk anchor).injOn


def d009581 {k : ℕ} (hk : 0 < k) :
    Set (_root_.GD.N0232.N0719.N0857.d009377 k) :=
  {q | _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0853.d009567 hk q)}

@[fun_prop]
theorem d009582
    {k : ℕ} (hk : 0 < k) (i : Fin k) :
    Continuous
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k => _root_.GD.N0232.N0719.N0853.d009567 hk q i) := by
  unfold _root_.GD.N0232.N0719.N0853.d009567
  split <;> fun_prop

theorem d009583
    {k : ℕ} (hk : 0 < k) :
    IsClosed (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  rw [show _root_.GD.N0232.N0719.N0853.d009581 hk =
      ⋂ i : Fin k,
        {q : _root_.GD.N0232.N0719.N0857.d009377 k |
          _root_.GD.N0232.N0719.N0951.d003578 k ≤ _root_.GD.N0232.N0719.N0853.d009567 hk q i} ∩
        {q : _root_.GD.N0232.N0719.N0857.d009377 k |
          _root_.GD.N0232.N0719.N0853.d009567 hk q i ≤ _root_.GD.N0232.N0719.N0951.d003579 k} by
    ext q
    simp [_root_.GD.N0232.N0719.N0853.d009581, _root_.GD.N0232.N0719.N0951.d003580]]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const
      (_root_.GD.N0232.N0719.N0853.d009582 hk i)).inter
      (isClosed_le
        (_root_.GD.N0232.N0719.N0853.d009582 hk i) continuous_const)

theorem d009584
    {k : ℕ} (hk : 0 < k)
    (hk3 : 3 ≤ k) :
    _root_.GD.N0232.N0719.N0853.d009581 hk ⊆
      Set.Icc (0 : _root_.GD.N0232.N0719.N0857.d009377 k) 1 := by
  intro q hq
  constructor
  · intro j
    have hj :=
      (hq
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j))).1
    rw [_root_.GD.N0232.N0719.N0853.d009568] at hj
    exact (_root_.GD.N0232.N0719.N0951.d003588 hk).le.trans hj
  · intro j
    have hj :=
      (hq
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j))).2
    rw [_root_.GD.N0232.N0719.N0853.d009568] at hj
    have hupp :
        _root_.GD.N0232.N0719.N0951.d003579 k ≤ 1 := by
      unfold _root_.GD.N0232.N0719.N0951.d003579
      have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
      field_simp [hkR.ne']
      nlinarith [show (3 : ℝ) ≤ k by exact_mod_cast hk3]
    exact hj.trans hupp




theorem d009585
    {k : ℕ} (hk : 0 < k)
    (hk3 : 3 ≤ k) :
    volume (_root_.GD.N0232.N0719.N0853.d009581 hk) ≤ 1 := by
  calc
    volume (_root_.GD.N0232.N0719.N0853.d009581 hk) ≤
        volume (Set.Icc
          (0 : _root_.GD.N0232.N0719.N0857.d009377 k) 1) :=
      measure_mono (_root_.GD.N0232.N0719.N0853.d009584 hk hk3)
    _ = 1 := by
      rw [Real.volume_Icc_pi]
      simp

theorem d009586
    {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k ⊆
      _root_.GD.N0232.N0719.N0853.d009581 hk := by
  rintro q ⟨u, hu, rfl⟩
  change _root_.GD.N0232.N0719.N0951.d003580
    (_root_.GD.N0232.N0719.N0853.d009567 hk
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u))
  rw [_root_.GD.N0232.N0719.N0853.d009574 hk
    (_root_.GD.N0232.N0719.N0854.d003829 hk) hu]
  exact _root_.GD.N0232.N0719.N0857.d009397 hk u

theorem d009587
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k ⊆
      _root_.GD.N0232.N0719.N0853.d009581 hk := by
  rintro q ⟨u, hu, rfl⟩
  change _root_.GD.N0232.N0719.N0951.d003580
    (_root_.GD.N0232.N0719.N0853.d009567 hk
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u))
  rw [_root_.GD.N0232.N0719.N0853.d009574 hk
    (_root_.GD.N0232.N0719.N0854.d003830 hk triangle) hu]
  exact _root_.GD.N0232.N0719.N0857.d009398 hk triangle u





theorem d009588
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u v : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u (triangle 0) *
        _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) v (triangle 1) <
      _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u (triangle 1) *
        _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) v (triangle 0) := by
  let p := _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u
  let q := _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) v
  have hp0u : p (triangle 0) ≤ 101 / (100 * (k : ℝ)) :=
    _root_.GD.N0232.N0719.N0856.d009548 hk u _
  have hp1l : 99 / (100 * (k : ℝ)) ≤ p (triangle 1) :=
    _root_.GD.N0232.N0719.N0856.d009547 hk u _
  have hq0l : 119 / (100 * (k : ℝ)) ≤ q (triangle 0) :=
    _root_.GD.N0232.N0719.N0856.d009549 hk triangle v
  have hq1u : q (triangle 1) ≤ 81 / (100 * (k : ℝ)) :=
    _root_.GD.N0232.N0719.N0856.d009550 hk triangle v
  have hp0n : 0 ≤ p (triangle 0) :=
    (_root_.GD.N0232.N0719.N0951.d003590 hk
      (_root_.GD.N0232.N0719.N0857.d009397 hk u) _).le
  have hq1n : 0 ≤ q (triangle 1) :=
    (_root_.GD.N0232.N0719.N0951.d003590 hk
      (_root_.GD.N0232.N0719.N0857.d009398 hk triangle v) _).le
  have hleft :
      p (triangle 0) * q (triangle 1) ≤
        (101 / (100 * (k : ℝ))) *
          (81 / (100 * (k : ℝ))) :=
    mul_le_mul hp0u hq1u hq1n (by positivity)
  have hright :
      (99 / (100 * (k : ℝ))) *
          (119 / (100 * (k : ℝ))) ≤
        p (triangle 1) * q (triangle 0) :=
    mul_le_mul hp1l hq0l (by positivity)
      (_root_.GD.N0232.N0719.N0951.d003590 hk
        (_root_.GD.N0232.N0719.N0857.d009397 hk u) _).le
  have hmiddle :
      (101 / (100 * (k : ℝ))) *
          (81 / (100 * (k : ℝ))) <
        (99 / (100 * (k : ℝ))) *
          (119 / (100 * (k : ℝ))) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    field_simp [hkR.ne']
    norm_num
  exact hleft.trans_lt (hmiddle.trans_le hright)

theorem d009589
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {u v : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k)
    (hv : v ∈ _root_.GD.N0232.N0719.N0857.d009383 k) :
    _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u ≠
      _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) v := by
  intro heq
  have hfull :
      _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u =
        _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) v := by
    rw [← _root_.GD.N0232.N0719.N0853.d009574 hk
        (_root_.GD.N0232.N0719.N0854.d003829 hk) hu,
      ← _root_.GD.N0232.N0719.N0853.d009574 hk
        (_root_.GD.N0232.N0719.N0854.d003830 hk triangle) hv,
      heq]
  have hcross :=
    _root_.GD.N0232.N0719.N0853.d009588 hk triangle u v
  rw [hfull] at hcross
  nlinarith

theorem d009590
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Disjoint
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k)
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k) := by
  rw [Set.disjoint_left]
  intro q hqu hqs
  obtain ⟨u, hu, hqu_eq⟩ := hqu
  obtain ⟨v, hv, hqs_eq⟩ := hqs
  exact
    (_root_.GD.N0232.N0719.N0853.d009589 hk triangle hu hv)
      (hqu_eq.trans hqs_eq.symm)



def d009591
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0856.d009528 triangle (_root_.GD.N0232.N0719.N0853.d009567 hk q) w





def d009592
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  Classical.choose
    (_root_.GD.N0232.N0719.N0856.d009555 hk triangle)

theorem d009593
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    0 < _root_.GD.N0232.N0719.N0853.d009592 hk triangle :=
  (Classical.choose_spec
    (_root_.GD.N0232.N0719.N0856.d009555 hk triangle)).1

theorem d009594
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    _root_.GD.N0232.N0719.N0853.d009592 hk triangle ≤
      _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w :=
  (Classical.choose_spec
    (_root_.GD.N0232.N0719.N0856.d009555 hk triangle)).2
    u hu w hw

theorem d009595
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k)
    (w : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0853.d009591 hk triangle
        (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) w =
      _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w := by
  unfold _root_.GD.N0232.N0719.N0853.d009591 _root_.GD.N0232.N0719.N0856.d009529
  rw [_root_.GD.N0232.N0719.N0853.d009574 hk
    (_root_.GD.N0232.N0719.N0854.d003829 hk) hu]

theorem d009596
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} (hu : u ∈ _root_.GD.N0232.N0719.N0857.d009383 k)
    (w : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0853.d009591 hk triangle
        (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) w =
      _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
  unfold _root_.GD.N0232.N0719.N0853.d009591 _root_.GD.N0232.N0719.N0856.d009530
  rw [_root_.GD.N0232.N0719.N0853.d009574 hk
    (_root_.GD.N0232.N0719.N0854.d003830 hk triangle) hu]







theorem d009597
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    (_root_.GD.N0232.N0719.N0857.d009401 k *
          (_root_.GD.N0232.N0719.N0853.d009592 hk triangle / 2 *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal) ≤
        ∫ q in
          _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w)
      ∨
    (_root_.GD.N0232.N0719.N0857.d009401 k *
          (_root_.GD.N0232.N0719.N0853.d009592 hk triangle / 2 *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal) ≤
        ∫ q in
          _root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w) := by
  have huInt :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009541
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have hsInt :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009542
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have href :
      _root_.GD.N0232.N0719.N0853.d009592 hk triangle *
          (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
    calc
      _root_.GD.N0232.N0719.N0853.d009592 hk triangle *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal =
          ∫ _u : _root_.GD.N0232.N0719.N0857.d009377 k in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0853.d009592 hk triangle := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
        ring
      _ ≤
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
        exact setIntegral_mono_on
          (integrableOn_const
            (_root_.GD.N0232.N0719.N0857.d009404 (k := k)))
          (huInt.add hsInt)
          (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
          (fun u hu =>
            _root_.GD.N0232.N0719.N0853.d009594 hk triangle hu hw)
  have hsplit :
      (_root_.GD.N0232.N0719.N0853.d009592 hk triangle / 2) *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w
      ∨
      (_root_.GD.N0232.N0719.N0853.d009592 hk triangle / 2) *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
    change
      _root_.GD.N0232.N0719.N0853.d009592 hk triangle *
          (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          (_root_.GD.N0232.N0719.N0856.d009529 hk triangle u w +
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
      at href
    rw [integral_add huInt hsInt] at href
    by_contra hnot
    push Not at hnot
    nlinarith
  rcases hsplit with hu | hs
  · left
    rw [_root_.GD.N0232.N0719.N0853.d009579 hk (_root_.GD.N0232.N0719.N0854.d003821 k)]
    have heq :
        (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0853.d009591 hk triangle
              (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) w) =
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
      intro u hu'
      exact _root_.GD.N0232.N0719.N0853.d009595
        hk triangle hu' w
    rw [heq]
    exact mul_le_mul_of_nonneg_left hu
      (_root_.GD.N0232.N0719.N0857.d009402 hk).le
  · right
    rw [_root_.GD.N0232.N0719.N0853.d009579 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle)]
    have heq :
        (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0853.d009591 hk triangle
              (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) w) =
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
      intro u hu'
      exact _root_.GD.N0232.N0719.N0853.d009596
        hk triangle hu' w
    rw [heq]
    exact mul_le_mul_of_nonneg_left hs
      (_root_.GD.N0232.N0719.N0857.d009402 hk).le

theorem d009598
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun q => _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w)
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k) := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume)
    (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
    (fun u _ =>
      (_root_.GD.N0232.N0719.N0853.d009576 hk
        (_root_.GD.N0232.N0719.N0854.d003821 k) u).hasFDerivWithinAt)
    (_root_.GD.N0232.N0719.N0853.d009578 hk (_root_.GD.N0232.N0719.N0854.d003821 k)).injOn]
  have hbase :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009541
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have hscaled :=
    hbase.const_mul (_root_.GD.N0232.N0719.N0857.d009401 k)
  apply MeasureTheory.IntegrableOn.congr_fun hscaled
  · intro u hu
    change
      _root_.GD.N0232.N0719.N0857.d009401 k *
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w =
        |(_root_.GD.N0232.N0719.N0853.d009575 k).det| *
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle
            (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) w
    rw [_root_.GD.N0232.N0719.N0853.d009577,
      abs_of_pos (_root_.GD.N0232.N0719.N0857.d009402 hk),
      _root_.GD.N0232.N0719.N0853.d009595 hk triangle hu w]
  · exact (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet

theorem d009599
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun q => _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w)
      (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k) := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume)
    (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
    (fun u _ =>
      (_root_.GD.N0232.N0719.N0853.d009576 hk
        (_root_.GD.N0232.N0719.N0854.d003822 triangle) u).hasFDerivWithinAt)
    (_root_.GD.N0232.N0719.N0853.d009578 hk
      (_root_.GD.N0232.N0719.N0854.d003822 triangle)).injOn]
  have hbase :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009542
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have hscaled :=
    hbase.const_mul (_root_.GD.N0232.N0719.N0857.d009401 k)
  apply MeasureTheory.IntegrableOn.congr_fun hscaled
  · intro u hu
    change
      _root_.GD.N0232.N0719.N0857.d009401 k *
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w =
        |(_root_.GD.N0232.N0719.N0853.d009575 k).det| *
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle
            (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) w
    rw [_root_.GD.N0232.N0719.N0853.d009577,
      abs_of_pos (_root_.GD.N0232.N0719.N0857.d009402 hk),
      _root_.GD.N0232.N0719.N0853.d009596 hk triangle hu w]
  · exact (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet





theorem d009600
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    _root_.GD.N0232.N0719.N0857.d009401 k *
          (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal) ≤
      ∫ q in
        (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k) ∪
          (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k),
        _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w := by
  have huInt :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009541
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have hsInt :
      IntegrableOn
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    ((_root_.GD.N0232.N0719.N0856.d009542
      hk triangle).comp
      (continuous_id.prodMk continuous_const)).continuousOn
      |>.integrableOn_compact (_root_.GD.N0232.N0719.N0857.d009384 k)
  have href :
      _root_.GD.N0232.N0719.N0853.d009592 hk triangle *
          (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
        (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w) +
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
    calc
      _root_.GD.N0232.N0719.N0853.d009592 hk triangle *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal =
          ∫ _u : _root_.GD.N0232.N0719.N0857.d009377 k in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0853.d009592 hk triangle := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
        ring
      _ ≤
          ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
            _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
        exact setIntegral_mono_on
          (integrableOn_const
            (_root_.GD.N0232.N0719.N0857.d009404 (k := k)))
          (huInt.add hsInt)
          (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
          (fun u hu =>
            _root_.GD.N0232.N0719.N0853.d009594 hk triangle hu hw)
      _ =
          (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
              _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w) +
            ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
              _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
        change
          (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
              (_root_.GD.N0232.N0719.N0856.d009529 hk triangle u w +
                _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)) = _
        rw [integral_add huInt hsInt]
  rw [setIntegral_union
    (_root_.GD.N0232.N0719.N0853.d009590 hk triangle)
    (_root_.GD.N0232.N0719.N0853.d009580 hk
      (_root_.GD.N0232.N0719.N0854.d003822 triangle))
    (_root_.GD.N0232.N0719.N0853.d009598
      hk triangle w)
    (_root_.GD.N0232.N0719.N0853.d009599
      hk triangle w)]
  rw [_root_.GD.N0232.N0719.N0853.d009579 hk (_root_.GD.N0232.N0719.N0854.d003821 k),
    _root_.GD.N0232.N0719.N0853.d009579 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle)]
  have huEq :
      (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle
            (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) w) =
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w := by
    apply setIntegral_congr_fun
      (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
    intro u hu'
    exact _root_.GD.N0232.N0719.N0853.d009595
      hk triangle hu' w
  have hsEq :
      (∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0853.d009591 hk triangle
            (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) w) =
        ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w := by
    apply setIntegral_congr_fun
      (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
    intro u hu'
    exact _root_.GD.N0232.N0719.N0853.d009596
      hk triangle hu' w
  rw [huEq, hsEq]
  nlinarith [_root_.GD.N0232.N0719.N0857.d009402 hk]

end

end GD.N0232.N0719.N0853
