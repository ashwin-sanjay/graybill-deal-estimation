import GD.Module0252














namespace GD.N0232.N0719.N0886

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open _root_.GD.N0232.N0719.N1016

private def d003634 (v t : ℝ) : ℝ :=
  Real.exp (v * t ^ 2 / 2)

private def d003635 (v t : ℝ) : ℝ :=
  v * t * _root_.GD.N0232.N0719.N0886.d003634 v t

private def d003636 (v t : ℝ) : ℝ :=
  (v + v ^ 2 * t ^ 2) * _root_.GD.N0232.N0719.N0886.d003634 v t

private def d003637 (v t : ℝ) : ℝ :=
  (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * _root_.GD.N0232.N0719.N0886.d003634 v t

private def d003638 (v t : ℝ) : ℝ :=
  (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) *
    _root_.GD.N0232.N0719.N0886.d003634 v t

private theorem d003639 (v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0886.d003634 v) = _root_.GD.N0232.N0719.N0886.d003635 v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0886.d003634 _root_.GD.N0232.N0719.N0886.d003635
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const',
    zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one,
    zero_add]
  simp only [_root_.GD.N0232.N0719.N0886.d003634]
  ring

private theorem d003640 (v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0886.d003635 v) = _root_.GD.N0232.N0719.N0886.d003636 v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0886.d003635 _root_.GD.N0232.N0719.N0886.d003636 _root_.GD.N0232.N0719.N0886.d003634
  rw [deriv_fun_mul (by fun_prop) (by fun_prop),
    _root_.deriv_exp (by fun_prop)]
  rw [deriv_const_mul_id]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const',
    zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one,
    zero_add]
  ring

private theorem d003641 (v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0886.d003636 v) = _root_.GD.N0232.N0719.N0886.d003637 v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0886.d003636 _root_.GD.N0232.N0719.N0886.d003637 _root_.GD.N0232.N0719.N0886.d003634
  rw [deriv_fun_mul (by fun_prop) (by fun_prop),
    _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const',
    deriv_const_mul_field]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_fun_add,
    deriv_const', zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one, zero_add]
  ring

private theorem d003642 (v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0886.d003637 v) = _root_.GD.N0232.N0719.N0886.d003638 v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0886.d003637 _root_.GD.N0232.N0719.N0886.d003638 _root_.GD.N0232.N0719.N0886.d003634
  rw [deriv_fun_mul (by fun_prop) (by fun_prop),
    _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_const_mul_id, deriv_const_mul_field]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
    Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_fun_add,
    deriv_const', zero_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one, zero_add]
  ring


@[simp]
theorem d003643 (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have hvar :=
    variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simpa using hvar


@[simp]
theorem d003644 (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v = 0 := by
  calc
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) =
        iteratedDeriv 3
          (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
      symm
      simpa only [Pi.pow_apply, id_eq] using
        (iteratedDeriv_mgf_zero
          (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 v)
          (by simp) 3)
    _ = iteratedDeriv 3 (_root_.GD.N0232.N0719.N0886.d003634 v) 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rfl
    _ = 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_zero]
      rw [_root_.GD.N0232.N0719.N0886.d003639, _root_.GD.N0232.N0719.N0886.d003640, _root_.GD.N0232.N0719.N0886.d003641]
      simp [_root_.GD.N0232.N0719.N0886.d003637, _root_.GD.N0232.N0719.N0886.d003634]


@[simp]
theorem d003645 (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4
          (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
      symm
      simpa only [Pi.pow_apply, id_eq] using
        (iteratedDeriv_mgf_zero
          (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 v)
          (by simp) 4)
    _ = iteratedDeriv 4 (_root_.GD.N0232.N0719.N0886.d003634 v) 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rfl
    _ = 3 * (v : ℝ) ^ 2 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
      rw [_root_.GD.N0232.N0719.N0886.d003639, _root_.GD.N0232.N0719.N0886.d003640, _root_.GD.N0232.N0719.N0886.d003641,
        _root_.GD.N0232.N0719.N0886.d003642]
      simp [_root_.GD.N0232.N0719.N0886.d003638, _root_.GD.N0232.N0719.N0886.d003634]


@[simp]
theorem d003646 (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h :=
    variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem d003647
    (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 v) := by
  have hnorm :
      Integrable (fun x : ℝ ↦ ‖x‖ ^ n) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) n).integrable_norm_pow'
  exact
    (integrable_norm_iff (by fun_prop :
      AEStronglyMeasurable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 v))).mp
      (by simpa [Real.norm_eq_abs, abs_pow] using hnorm)







theorem d003648
    (v : ℝ≥0) (a b c d : ℝ) :
    (∫ x : ℝ,
        x * (a * x ^ 3 + b * x ^ 2 + c * x + d)
          ∂gaussianReal 0 v) =
      (v : ℝ) *
        ∫ x : ℝ,
          (3 * a * x ^ 2 + 2 * b * x + c)
            ∂gaussianReal 0 v := by
  have h0 : Integrable (fun _x : ℝ ↦ d) (gaussianReal 0 v) := by
    fun_prop
  have hc0 : Integrable (fun _x : ℝ ↦ c) (gaussianReal 0 v) := by
    fun_prop
  have h1 := _root_.GD.N0232.N0719.N0886.d003647 v 1
  have h2 := _root_.GD.N0232.N0719.N0886.d003647 v 2
  have h3 := _root_.GD.N0232.N0719.N0886.d003647 v 3
  have h4 := _root_.GD.N0232.N0719.N0886.d003647 v 4
  have ha4 : Integrable (fun x : ℝ ↦ a * x ^ 4) (gaussianReal 0 v) :=
    h4.const_mul a
  have hb3 : Integrable (fun x : ℝ ↦ b * x ^ 3) (gaussianReal 0 v) :=
    h3.const_mul b
  have hc2 : Integrable (fun x : ℝ ↦ c * x ^ 2) (gaussianReal 0 v) :=
    h2.const_mul c
  have hd1 : Integrable (fun x : ℝ ↦ d * x) (gaussianReal 0 v) :=
    by simpa [pow_one] using h1.const_mul d
  have h3a2 :
      Integrable (fun x : ℝ ↦ 3 * a * x ^ 2) (gaussianReal 0 v) :=
    h2.const_mul (3 * a)
  have h2b1 :
      Integrable (fun x : ℝ ↦ 2 * b * x) (gaussianReal 0 v) :=
    by simpa [pow_one] using h1.const_mul (2 * b)
  calc
    (∫ x : ℝ,
        x * (a * x ^ 3 + b * x ^ 2 + c * x + d)
          ∂gaussianReal 0 v) =
        ∫ x : ℝ,
          (a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x)
            ∂gaussianReal 0 v := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ =
        a * (3 * (v : ℝ) ^ 2) +
          b * 0 + c * (v : ℝ) + d * 0 := by
      change
        (∫ x : ℝ,
          (((((fun x : ℝ ↦ a * x ^ 4) +
                (fun x : ℝ ↦ b * x ^ 3)) +
              (fun x : ℝ ↦ c * x ^ 2)) +
            (fun x : ℝ ↦ d * x)) x)
            ∂gaussianReal 0 v) =
          a * (3 * (v : ℝ) ^ 2) +
            b * 0 + c * (v : ℝ) + d * 0
      rw [integral_add' ((ha4.add hb3).add hc2) hd1,
        integral_add' (ha4.add hb3) hc2,
        integral_add' ha4 hb3]
      rw [integral_const_mul a, integral_const_mul b,
        integral_const_mul c, integral_const_mul d]
      simp only [_root_.GD.N0232.N0719.N0886.d003645,
        _root_.GD.N0232.N0719.N0886.d003644, _root_.GD.N0232.N0719.N0886.d003646,
        integral_id_gaussianReal]
    _ =
        (v : ℝ) *
          ((3 * a) * (v : ℝ) + (2 * b) * 0 + c) := by
      ring
    _ =
        (v : ℝ) *
          ∫ x : ℝ,
            (3 * a * x ^ 2 + 2 * b * x + c)
              ∂gaussianReal 0 v := by
      congr 1
      have hab :
          (∫ x : ℝ, 3 * a * x ^ 2 + 2 * b * x
              ∂gaussianReal 0 v) =
            (∫ x : ℝ, 3 * a * x ^ 2 ∂gaussianReal 0 v) +
              ∫ x : ℝ, 2 * b * x ∂gaussianReal 0 v :=
        integral_add h3a2 h2b1
      have habc :
          (∫ x : ℝ, (3 * a * x ^ 2 + 2 * b * x) + c
              ∂gaussianReal 0 v) =
            (∫ x : ℝ, 3 * a * x ^ 2 + 2 * b * x
              ∂gaussianReal 0 v) +
              ∫ _x : ℝ, c ∂gaussianReal 0 v :=
        integral_add (h3a2.add h2b1) hc0
      rw [habc, hab, integral_const_mul (3 * a),
        integral_const_mul (2 * b)]
      simp


def d003649 (v₁ v₂ v₃ : ℝ≥0) : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 v₁).prod ((gaussianReal 0 v₂).prod (gaussianReal 0 v₃))


def d003650 (z : ℝ × (ℝ × ℝ)) : ℝ := z.1
def d003651 (z : ℝ × (ℝ × ℝ)) : ℝ := z.2.1
def d003652 (z : ℝ × (ℝ × ℝ)) : ℝ := z.2.2


def d003653 (p₁ p₂ p₃ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  p₁ * _root_.GD.N0232.N0719.N0886.d003650 z + p₂ * _root_.GD.N0232.N0719.N0886.d003651 z + p₃ * _root_.GD.N0232.N0719.N0886.d003652 z


def d003654 (p₁ p₂ p₃ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ (_root_.GD.N0232.N0719.N0886.d003650 z) (_root_.GD.N0232.N0719.N0886.d003651 z) (_root_.GD.N0232.N0719.N0886.d003652 z)


def d003655 (e : ℕ × ℕ × ℕ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N0886.d003650 z ^ e.1 * (_root_.GD.N0232.N0719.N0886.d003651 z ^ e.2.1 * _root_.GD.N0232.N0719.N0886.d003652 z ^ e.2.2)

theorem d003656
    (v₁ v₂ v₃ : ℝ≥0) (e : ℕ × ℕ × ℕ) :
    Integrable (_root_.GD.N0232.N0719.N0886.d003655 e) (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  have h₁ :
      Integrable (fun x : ℝ ↦ x ^ e.1) (gaussianReal 0 v₁) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.1
  have h₂ :
      Integrable (fun x : ℝ ↦ x ^ e.2.1) (gaussianReal 0 v₂) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.2.1
  have h₃ :
      Integrable (fun x : ℝ ↦ x ^ e.2.2) (gaussianReal 0 v₃) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.2.2
  change
    Integrable
      (fun z : ℝ × (ℝ × ℝ) ↦
        z.1 ^ e.1 * (z.2.1 ^ e.2.1 * z.2.2 ^ e.2.2))
      ((gaussianReal 0 v₁).prod
        ((gaussianReal 0 v₂).prod (gaussianReal 0 v₃)))
  exact h₁.mul_prod (h₂.mul_prod h₃)


theorem d003657
    (v₁ v₂ v₃ : ℝ≥0) (e : ℕ × ℕ × ℕ) :
    ∫ z, _root_.GD.N0232.N0719.N0886.d003655 e z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ =
      (∫ x : ℝ, x ^ e.1 ∂gaussianReal 0 v₁) *
        ((∫ x : ℝ, x ^ e.2.1 ∂gaussianReal 0 v₂) *
          ∫ x : ℝ, x ^ e.2.2 ∂gaussianReal 0 v₃) := by
  unfold _root_.GD.N0232.N0719.N0886.d003655 _root_.GD.N0232.N0719.N0886.d003649 _root_.GD.N0232.N0719.N0886.d003650 _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652
  rw [integral_prod_mul
      (fun x : ℝ ↦ x ^ e.1)
      (fun yz : ℝ × ℝ ↦ yz.1 ^ e.2.1 * yz.2 ^ e.2.2),
    integral_prod_mul
      (fun x : ℝ ↦ x ^ e.2.1)
      (fun x : ℝ ↦ x ^ e.2.2)]


def d003658 : Fin 15 → ℕ × ℕ × ℕ :=
  ![(4, 0, 0), (3, 1, 0), (3, 0, 1), (2, 2, 0), (2, 1, 1),
    (2, 0, 2), (1, 3, 0), (1, 2, 1), (1, 1, 2), (1, 0, 3),
    (0, 4, 0), (0, 3, 1), (0, 2, 2), (0, 1, 3), (0, 0, 4)]


def d003659
    (c : Fin 15 → ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  ∑ i, c i * _root_.GD.N0232.N0719.N0886.d003655 (_root_.GD.N0232.N0719.N0886.d003658 i) z

theorem d003660
    (v₁ v₂ v₃ : ℝ≥0) (c : Fin 15 → ℝ) :
    Integrable (_root_.GD.N0232.N0719.N0886.d003659 c) (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  unfold _root_.GD.N0232.N0719.N0886.d003659
  exact integrable_finset_sum _ fun i _ ↦
    (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ (_root_.GD.N0232.N0719.N0886.d003658 i)).const_mul (c i)


theorem d003661
    (v₁ v₂ v₃ : ℝ≥0) (c : Fin 15 → ℝ) :
    ∫ z, _root_.GD.N0232.N0719.N0886.d003659 c z ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ =
      ∑ i, c i *
        ((∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).1 ∂gaussianReal 0 v₁) *
          ((∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).2.1 ∂gaussianReal 0 v₂) *
            ∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).2.2
              ∂gaussianReal 0 v₃)) := by
  unfold _root_.GD.N0232.N0719.N0886.d003659
  rw [integral_finset_sum _ fun i _ ↦
    (_root_.GD.N0232.N0719.N0886.d003656 v₁ v₂ v₃ (_root_.GD.N0232.N0719.N0886.d003658 i)).const_mul (c i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, _root_.GD.N0232.N0719.N0886.d003657]


def d003662
    (p₁ p₂ p₃ : ℝ) : Fin 15 → ℝ :=
  ![
    -p₁ ^ 2 * (2 * p₁ + p₂ + p₃) /
      (3 * (p₁ + p₂) * (p₁ + p₃)),
    p₁ * (3 * p₁ ^ 2 - 2 * p₁ * p₂ + 3 * p₁ * p₃ -
      p₂ ^ 2 - p₂ * p₃) /
      (3 * (p₁ + p₂) * (p₁ + p₃)),
    p₁ * (3 * p₁ ^ 2 + 3 * p₁ * p₂ - 2 * p₁ * p₃ -
      p₂ * p₃ - p₃ ^ 2) /
      (3 * (p₁ + p₂) * (p₁ + p₃)),
    2 * p₁ * p₂ / (p₁ + p₂),
    -p₁ * (2 * p₁ ^ 2 + p₁ * p₂ + p₁ * p₃ - p₂ ^ 2 +
      2 * p₂ * p₃ - p₃ ^ 2) /
      ((p₁ + p₂) * (p₁ + p₃)),
    2 * p₁ * p₃ / (p₁ + p₃),
    -p₂ * (p₁ ^ 2 + 2 * p₁ * p₂ + p₁ * p₃ -
      3 * p₂ ^ 2 - 3 * p₂ * p₃) /
      (3 * (p₁ + p₂) * (p₂ + p₃)),
    p₂ * (p₁ ^ 2 - p₁ * p₂ - 2 * p₁ * p₃ -
      2 * p₂ ^ 2 - p₂ * p₃ + p₃ ^ 2) /
      ((p₁ + p₂) * (p₂ + p₃)),
    p₃ * (p₁ ^ 2 - 2 * p₁ * p₂ - p₁ * p₃ +
      p₂ ^ 2 - p₂ * p₃ - 2 * p₃ ^ 2) /
      ((p₁ + p₃) * (p₂ + p₃)),
    -p₃ * (p₁ ^ 2 + p₁ * p₂ + 2 * p₁ * p₃ -
      3 * p₂ * p₃ - 3 * p₃ ^ 2) /
      (3 * (p₁ + p₃) * (p₂ + p₃)),
    -p₂ ^ 2 * (p₁ + 2 * p₂ + p₃) /
      (3 * (p₁ + p₂) * (p₂ + p₃)),
    p₂ * (3 * p₁ * p₂ - p₁ * p₃ + 3 * p₂ ^ 2 -
      2 * p₂ * p₃ - p₃ ^ 2) /
      (3 * (p₁ + p₂) * (p₂ + p₃)),
    2 * p₂ * p₃ / (p₂ + p₃),
    -p₃ * (p₁ * p₂ - 3 * p₁ * p₃ + p₂ ^ 2 +
      2 * p₂ * p₃ - 3 * p₃ ^ 2) /
      (3 * (p₁ + p₃) * (p₂ + p₃)),
    -p₃ ^ 2 * (p₁ + p₂ + 2 * p₃) /
      (3 * (p₁ + p₃) * (p₂ + p₃))
  ]

set_option maxHeartbeats 1000000 in
theorem d003663
    {p₁ p₂ p₃ : ℝ}
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    (fun z ↦ _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z) =
      _root_.GD.N0232.N0719.N0886.d003659 (_root_.GD.N0232.N0719.N0886.d003662 p₁ p₂ p₃) := by
  funext z
  rcases z with ⟨z₁', z₂', z₃'⟩
  norm_num [_root_.GD.N0232.N0719.N0886.d003653, _root_.GD.N0232.N0719.N0886.d003654, _root_.GD.N0232.N0719.N0886.d003659, _root_.GD.N0232.N0719.N0886.d003658,
    _root_.GD.N0232.N0719.N0886.d003662, _root_.GD.N0232.N0719.N0886.d003655, _root_.GD.N0232.N0719.N0886.d003650, _root_.GD.N0232.N0719.N0886.d003651, _root_.GD.N0232.N0719.N0886.d003652, _root_.GD.N0232.N0719.N1016.d003609,
    Fin.sum_univ_succ]
  field_simp [h₁₂, h₁₃, h₂₃]
  ring

set_option maxHeartbeats 1000000 in






theorem d003664
    {p₁ p₂ p₃ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    ∫ z,
        _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ =
      -_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃
        (p₁ * (v₁ : ℝ)) (p₂ * (v₂ : ℝ)) (p₃ * (v₃ : ℝ)) := by
  rw [_root_.GD.N0232.N0719.N0886.d003663 h₁₂ h₁₃ h₂₃,
    _root_.GD.N0232.N0719.N0886.d003661]
  norm_num [_root_.GD.N0232.N0719.N0886.d003658, _root_.GD.N0232.N0719.N0886.d003662,
    Fin.sum_univ_succ, _root_.GD.N0232.N0719.N0886.d003645,
    _root_.GD.N0232.N0719.N0886.d003644, _root_.GD.N0232.N0719.N0886.d003646,
    integral_id_gaussianReal, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_mul, pow_zero, pow_one,
    zero_mul, mul_zero, add_zero]
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N1016.d003608
  field_simp [h₁₂, h₁₃, h₂₃]
  ring

end

end GD.N0232.N0719.N0886
