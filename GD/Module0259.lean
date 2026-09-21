import GD.Module0253
import GD.Module0258



























namespace GD.N0232.N0719.N0879

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N0886

private def d003718 (μ v t : ℝ) : ℝ :=
  Real.exp (μ * t + v * t ^ 2 / 2)

private def d003719 (μ v t : ℝ) : ℝ :=
  (μ + v * t) * _root_.GD.N0232.N0719.N0879.d003718 μ v t

private def d003720 (μ v t : ℝ) : ℝ :=
  ((μ + v * t) ^ 2 + v) * _root_.GD.N0232.N0719.N0879.d003718 μ v t

private def d003721 (μ v t : ℝ) : ℝ :=
  ((μ + v * t) ^ 3 + 3 * v * (μ + v * t)) *
    _root_.GD.N0232.N0719.N0879.d003718 μ v t

private def d003722 (μ v t : ℝ) : ℝ :=
  ((μ + v * t) ^ 4 +
      6 * v * (μ + v * t) ^ 2 + 3 * v ^ 2) *
    _root_.GD.N0232.N0719.N0879.d003718 μ v t

private theorem d003723 (μ v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0879.d003718 μ v) = _root_.GD.N0232.N0719.N0879.d003719 μ v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0879.d003718 _root_.GD.N0232.N0719.N0879.d003719
  rw [_root_.deriv_exp (by fun_prop)]
  have hexponent :
      deriv (fun x : ℝ ↦ μ * x + v * x ^ 2 / 2) t =
        μ + v * t := by
    apply HasDerivAt.deriv
    convert
      ((hasDerivAt_id t).const_mul μ).add
        ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2) using 1
    all_goals first
      | rfl
      | (funext x; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | (simp only [id_eq]; ring)
      | ring
  rw [hexponent]
  unfold _root_.GD.N0232.N0719.N0879.d003718
  ring

private theorem d003724 (μ v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0879.d003719 μ v) = _root_.GD.N0232.N0719.N0879.d003720 μ v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0879.d003719 _root_.GD.N0232.N0719.N0879.d003720
  have hmgf0 :
      DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0879.d003718 μ v) t := by
    unfold _root_.GD.N0232.N0719.N0879.d003718
    fun_prop
  rw [deriv_fun_mul (by fun_prop) hmgf0,
    _root_.GD.N0232.N0719.N0879.d003723]
  have haffine :
      deriv (fun x : ℝ ↦ μ + v * x) t = v := by
    apply HasDerivAt.deriv
    convert
      (hasDerivAt_const t μ).add
        ((hasDerivAt_id t).const_mul v) using 1
    all_goals first
      | rfl
      | (funext x; simp only [Pi.add_apply, id_eq]; ring)
      | ring
  rw [haffine]
  unfold _root_.GD.N0232.N0719.N0879.d003719 _root_.GD.N0232.N0719.N0879.d003718
  ring

private theorem d003725 (μ v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0879.d003720 μ v) = _root_.GD.N0232.N0719.N0879.d003721 μ v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0879.d003720 _root_.GD.N0232.N0719.N0879.d003721
  have hmgf0 :
      DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0879.d003718 μ v) t := by
    unfold _root_.GD.N0232.N0719.N0879.d003718
    fun_prop
  rw [deriv_fun_mul (by fun_prop) hmgf0,
    _root_.GD.N0232.N0719.N0879.d003723]
  have hpoly :
      deriv (fun x : ℝ ↦ (μ + v * x) ^ 2 + v) t =
        2 * v * (μ + v * t) := by
    apply HasDerivAt.deriv
    have haffine :
        HasDerivAt (fun x : ℝ ↦ μ + v * x) v t := by
      convert
        (hasDerivAt_const t μ).add
          ((hasDerivAt_id t).const_mul v) using 1
      all_goals first
        | rfl
        | (funext x; simp only [Pi.add_apply, id_eq]; ring)
        | ring
    convert (haffine.pow 2).add_const v using 1
    all_goals first
      | rfl
      | (funext x; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
  rw [hpoly]
  unfold _root_.GD.N0232.N0719.N0879.d003719 _root_.GD.N0232.N0719.N0879.d003718
  ring

private theorem d003726 (μ v : ℝ) :
    deriv (_root_.GD.N0232.N0719.N0879.d003721 μ v) = _root_.GD.N0232.N0719.N0879.d003722 μ v := by
  ext t
  unfold _root_.GD.N0232.N0719.N0879.d003721 _root_.GD.N0232.N0719.N0879.d003722
  have hmgf0 :
      DifferentiableAt ℝ (_root_.GD.N0232.N0719.N0879.d003718 μ v) t := by
    unfold _root_.GD.N0232.N0719.N0879.d003718
    fun_prop
  rw [deriv_fun_mul (by fun_prop) hmgf0,
    _root_.GD.N0232.N0719.N0879.d003723]
  have hpoly :
      deriv
          (fun x : ℝ ↦
            (μ + v * x) ^ 3 + 3 * v * (μ + v * x)) t =
        3 * v * (μ + v * t) ^ 2 + 3 * v ^ 2 := by
    apply HasDerivAt.deriv
    have haffine :
        HasDerivAt (fun x : ℝ ↦ μ + v * x) v t := by
      convert
        (hasDerivAt_const t μ).add
          ((hasDerivAt_id t).const_mul v) using 1
      all_goals first
        | rfl
        | (funext x; simp only [Pi.add_apply, id_eq]; ring)
        | ring
    convert
      (haffine.pow 3).add
        (haffine.const_mul (3 * v)) using 1
    all_goals first
      | rfl
      | (funext x; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
  rw [hpoly]
  unfold _root_.GD.N0232.N0719.N0879.d003719 _root_.GD.N0232.N0719.N0879.d003718
  ring


@[simp]
theorem d003727 (μ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal μ v =
      μ ^ 2 + (v : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 2 ∂gaussianReal μ v) =
        iteratedDeriv 2
          (mgf (fun x : ℝ ↦ x) (gaussianReal μ v)) 0 := by
      symm
      simpa only [Pi.pow_apply, id_eq] using
        (iteratedDeriv_mgf_zero
          (X := fun x : ℝ ↦ x) (μ := gaussianReal μ v)
          (by simp) 2)
    _ = iteratedDeriv 2 (_root_.GD.N0232.N0719.N0879.d003718 μ v) 0 := by
      rw [mgf_fun_id_gaussianReal]
      rfl
    _ = μ ^ 2 + (v : ℝ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
      rw [_root_.GD.N0232.N0719.N0879.d003723, _root_.GD.N0232.N0719.N0879.d003724]
      simp [_root_.GD.N0232.N0719.N0879.d003720, _root_.GD.N0232.N0719.N0879.d003718]


@[simp]
theorem d003728 (μ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 3 ∂gaussianReal μ v =
      μ ^ 3 + 3 * μ * (v : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 3 ∂gaussianReal μ v) =
        iteratedDeriv 3
          (mgf (fun x : ℝ ↦ x) (gaussianReal μ v)) 0 := by
      symm
      simpa only [Pi.pow_apply, id_eq] using
        (iteratedDeriv_mgf_zero
          (X := fun x : ℝ ↦ x) (μ := gaussianReal μ v)
          (by simp) 3)
    _ = iteratedDeriv 3 (_root_.GD.N0232.N0719.N0879.d003718 μ v) 0 := by
      rw [mgf_fun_id_gaussianReal]
      rfl
    _ = μ ^ 3 + 3 * μ * (v : ℝ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_zero]
      rw [_root_.GD.N0232.N0719.N0879.d003723, _root_.GD.N0232.N0719.N0879.d003724, _root_.GD.N0232.N0719.N0879.d003725]
      simp [_root_.GD.N0232.N0719.N0879.d003721, _root_.GD.N0232.N0719.N0879.d003718]
      ring


@[simp]
theorem d003729 (μ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal μ v =
      μ ^ 4 + 6 * μ ^ 2 * (v : ℝ) + 3 * (v : ℝ) ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal μ v) =
        iteratedDeriv 4
          (mgf (fun x : ℝ ↦ x) (gaussianReal μ v)) 0 := by
      symm
      simpa only [Pi.pow_apply, id_eq] using
        (iteratedDeriv_mgf_zero
          (X := fun x : ℝ ↦ x) (μ := gaussianReal μ v)
          (by simp) 4)
    _ = iteratedDeriv 4 (_root_.GD.N0232.N0719.N0879.d003718 μ v) 0 := by
      rw [mgf_fun_id_gaussianReal]
      rfl
    _ =
        μ ^ 4 + 6 * μ ^ 2 * (v : ℝ) + 3 * (v : ℝ) ^ 2 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
      rw [_root_.GD.N0232.N0719.N0879.d003723, _root_.GD.N0232.N0719.N0879.d003724,
        _root_.GD.N0232.N0719.N0879.d003725, _root_.GD.N0232.N0719.N0879.d003726]
      simp [_root_.GD.N0232.N0719.N0879.d003722, _root_.GD.N0232.N0719.N0879.d003718]
      ring


def d003730
    (μ₁ μ₂ μ₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0) :
    Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal μ₁ v₁).prod
    ((gaussianReal μ₂ v₂).prod (gaussianReal μ₃ v₃))

theorem d003731
    (μ₁ μ₂ μ₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0)
    (e : ℕ × ℕ × ℕ) :
    Integrable (_root_.GD.N0232.N0719.N0886.d003655 e)
      (_root_.GD.N0232.N0719.N0879.d003730 μ₁ μ₂ μ₃ v₁ v₂ v₃) := by
  have h₁ :
      Integrable (fun x : ℝ ↦ x ^ e.1) (gaussianReal μ₁ v₁) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.1
  have h₂ :
      Integrable (fun x : ℝ ↦ x ^ e.2.1) (gaussianReal μ₂ v₂) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.2.1
  have h₃ :
      Integrable (fun x : ℝ ↦ x ^ e.2.2) (gaussianReal μ₃ v₃) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) e.2.2
  change
    Integrable
      (fun z : ℝ × (ℝ × ℝ) ↦
        z.1 ^ e.1 * (z.2.1 ^ e.2.1 * z.2.2 ^ e.2.2))
      ((gaussianReal μ₁ v₁).prod
        ((gaussianReal μ₂ v₂).prod (gaussianReal μ₃ v₃)))
  exact h₁.mul_prod (h₂.mul_prod h₃)

theorem d003732
    (μ₁ μ₂ μ₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0)
    (e : ℕ × ℕ × ℕ) :
    ∫ z, _root_.GD.N0232.N0719.N0886.d003655 e z
        ∂_root_.GD.N0232.N0719.N0879.d003730 μ₁ μ₂ μ₃ v₁ v₂ v₃ =
      (∫ x : ℝ, x ^ e.1 ∂gaussianReal μ₁ v₁) *
        ((∫ x : ℝ, x ^ e.2.1 ∂gaussianReal μ₂ v₂) *
          ∫ x : ℝ, x ^ e.2.2 ∂gaussianReal μ₃ v₃) := by
  unfold _root_.GD.N0232.N0719.N0886.d003655 _root_.GD.N0232.N0719.N0879.d003730 _root_.GD.N0232.N0719.N0886.d003650 _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652
  rw [integral_prod_mul
      (fun x : ℝ ↦ x ^ e.1)
      (fun yz : ℝ × ℝ ↦ yz.1 ^ e.2.1 * yz.2 ^ e.2.2),
    integral_prod_mul
      (fun x : ℝ ↦ x ^ e.2.1)
      (fun x : ℝ ↦ x ^ e.2.2)]

theorem d003733
    (μ₁ μ₂ μ₃ : ℝ) (v₁ v₂ v₃ : ℝ≥0)
    (a : Fin 15 → ℝ) :
    ∫ z, _root_.GD.N0232.N0719.N0886.d003659 a z
        ∂_root_.GD.N0232.N0719.N0879.d003730 μ₁ μ₂ μ₃ v₁ v₂ v₃ =
      ∑ i, a i *
        ((∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).1
            ∂gaussianReal μ₁ v₁) *
          ((∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).2.1
              ∂gaussianReal μ₂ v₂) *
            ∫ x : ℝ, x ^ (_root_.GD.N0232.N0719.N0886.d003658 i).2.2
              ∂gaussianReal μ₃ v₃)) := by
  unfold _root_.GD.N0232.N0719.N0886.d003659
  rw [integral_finset_sum _ fun i _ ↦
    (_root_.GD.N0232.N0719.N0879.d003731 μ₁ μ₂ μ₃ v₁ v₂ v₃
      (_root_.GD.N0232.N0719.N0886.d003658 i)).const_mul (a i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, _root_.GD.N0232.N0719.N0879.d003732]

set_option maxHeartbeats 1000000 in




theorem d003734
    {p₁ p₂ p₃ c u : ℝ} {s₁ s₂ s₃ : ℝ≥0}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    let β₁ := p₁ * (s₁ : ℝ)
    let β₂ := p₂ * (s₂ : ℝ)
    let β₃ := p₃ * (s₃ : ℝ)
    let m := p₁ * β₁ + p₂ * β₂ + p₃ * β₃
    ∫ z,
        _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z
      ∂_root_.GD.N0232.N0719.N0879.d003730
        (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
        s₁ s₂ s₃ =
      -_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ +
        c ^ 2 * u ^ 2 *
          (-m * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ +
            3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃) +
        c ^ 4 * u ^ 4 * m *
          _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃ := by
  dsimp
  rw [_root_.GD.N0232.N0719.N0886.d003663
      h₁₂ h₁₃ h₂₃,
    _root_.GD.N0232.N0719.N0879.d003733]
  norm_num [_root_.GD.N0232.N0719.N0886.d003658, _root_.GD.N0232.N0719.N0886.d003662,
    Fin.sum_univ_succ, _root_.GD.N0232.N0719.N0879.d003729,
    _root_.GD.N0232.N0719.N0879.d003728, _root_.GD.N0232.N0719.N0879.d003727,
    integral_id_gaussianReal, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_mul, pow_zero, pow_one,
    zero_mul, mul_zero, add_zero]
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N1016.d003608 _root_.GD.N0232.N0719.N1016.d003609
  field_simp [h₁₂, h₁₃, h₂₃]
  ring


theorem d003735
    (v : ℝ≥0) (a b c : ℝ) :
    ∫ u : ℝ, a + b * u ^ 2 + c * u ^ 4
        ∂gaussianReal 0 v =
      a + b * (v : ℝ) + 3 * c * (v : ℝ) ^ 2 := by
  have h0 : Integrable (fun _u : ℝ ↦ a) (gaussianReal 0 v) := by
    fun_prop
  have h2 :
      Integrable (fun u : ℝ ↦ b * u ^ 2) (gaussianReal 0 v) :=
    (_root_.GD.N0232.N0719.N0886.d003647 v 2).const_mul b
  have h4 :
      Integrable (fun u : ℝ ↦ c * u ^ 4) (gaussianReal 0 v) :=
    (_root_.GD.N0232.N0719.N0886.d003647 v 4).const_mul c
  change
    (∫ u : ℝ,
      ((((fun _u : ℝ ↦ a) + (fun u : ℝ ↦ b * u ^ 2)) +
        (fun u : ℝ ↦ c * u ^ 4)) u) ∂gaussianReal 0 v) =
      a + b * (v : ℝ) + 3 * c * (v : ℝ) ^ 2
  rw [integral_add' (h0.add h2) h4, integral_add' h0 h2,
    integral_const_mul b, integral_const_mul c]
  simp
  ring







theorem d003736
    {p₁ p₂ p₃ c : ℝ} {s₁ s₂ s₃ ρ : ℝ≥0}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    let β₁ := p₁ * (s₁ : ℝ)
    let β₂ := p₂ * (s₂ : ℝ)
    let β₃ := p₃ * (s₃ : ℝ)
    let m := p₁ * β₁ + p₂ * β₂ + p₃ * β₃
    ∫ u : ℝ,
      (∫ z,
          _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z
        ∂_root_.GD.N0232.N0719.N0879.d003730
          (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
          s₁ s₂ s₃)
      ∂gaussianReal 0 ρ =
      (1 + (ρ : ℝ) * c ^ 2 * m) *
        (-_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ +
          3 * (ρ : ℝ) * c ^ 2 *
            _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃) := by
  dsimp
  apply Eq.trans
    (integral_congr_ae
      (ae_of_all _ fun u ↦
        _root_.GD.N0232.N0719.N0879.d003734
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (c := c) (u := u)
          (s₁ := s₁) (s₂ := s₂) (s₃ := s₃)
          hsum h₁₂ h₁₃ h₂₃))
  let E :=
    _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃
      (p₁ * (s₁ : ℝ)) (p₂ * (s₂ : ℝ)) (p₃ * (s₃ : ℝ))
  let C :=
    _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃
      (p₁ * (s₁ : ℝ)) (p₂ * (s₂ : ℝ)) (p₃ * (s₃ : ℝ))
  let m :=
    p₁ * (p₁ * (s₁ : ℝ)) +
      p₂ * (p₂ * (s₂ : ℝ)) +
      p₃ * (p₃ * (s₃ : ℝ))
  calc
    _ = ∫ u : ℝ,
        (-E) + (c ^ 2 * (-m * E + 3 * C)) * u ^ 2 +
          (c ^ 4 * m * C) * u ^ 4
        ∂gaussianReal 0 ρ := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [E, C, m]
      ring
    _ =
        (-E) +
          (c ^ 2 * (-m * E + 3 * C)) * (ρ : ℝ) +
          3 * (c ^ 4 * m * C) * (ρ : ℝ) ^ 2 :=
      _root_.GD.N0232.N0719.N0879.d003735 ρ
        (-E) (c ^ 2 * (-m * E + 3 * C)) (c ^ 4 * m * C)
    _ =
        (1 + (ρ : ℝ) * c ^ 2 * m) *
          (-E + 3 * (ρ : ℝ) * c ^ 2 * C) := by ring

end

end GD.N0232.N0719.N0879
