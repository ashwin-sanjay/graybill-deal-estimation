import Mathlib











open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0126

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

local instance : DecidableEq ι := Classical.decEq ι


def d006419 : ℝ := Fintype.card ι


def d006420 (x : ι → ℝ) : ℝ :=
  (∑ i, x i) / _root_.GD.N0126.d006419 (ι := ι)


def d006421 (x : ι → ℝ) (i : ι) : ℝ :=
  x i - _root_.GD.N0126.d006420 x


def d006422 (x : ι → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0126.d006421 x i ^ 2

theorem d006423 : 0 < _root_.GD.N0126.d006419 (ι := ι) := by
  simp [_root_.GD.N0126.d006419, Fintype.card_pos]

theorem d006424 : _root_.GD.N0126.d006419 (ι := ι) ≠ 0 :=
  ne_of_gt _root_.GD.N0126.d006423


theorem d006425 (x : ι → ℝ) :
    ∑ i, _root_.GD.N0126.d006421 x i = 0 := by
  unfold _root_.GD.N0126.d006421 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  field_simp [show (Fintype.card ι : ℝ) ≠ 0 by
    exact_mod_cast Fintype.card_ne_zero]
  ring


theorem d006426 (c : ℝ) (x : ι → ℝ) :
    ∑ i, c * _root_.GD.N0126.d006421 x i = 0 := by
  rw [← Finset.mul_sum, _root_.GD.N0126.d006425, mul_zero]


theorem d006427 (x : ι → ℝ) (μ : ℝ) :
    ∑ i, (x i - μ) ^ 2 =
      _root_.GD.N0126.d006422 x + _root_.GD.N0126.d006419 (ι := ι) * (_root_.GD.N0126.d006420 x - μ) ^ 2 := by
  have hx (i : ι) :
      x i - μ = _root_.GD.N0126.d006421 x i + (_root_.GD.N0126.d006420 x - μ) := by
    unfold _root_.GD.N0126.d006421
    ring
  simp_rw [hx]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross :
      (∑ i, 2 * _root_.GD.N0126.d006421 x i * (_root_.GD.N0126.d006420 x - μ)) = 0 := by
    calc
      (∑ i, 2 * _root_.GD.N0126.d006421 x i * (_root_.GD.N0126.d006420 x - μ)) =
          2 * (∑ i, _root_.GD.N0126.d006421 x i) * (_root_.GD.N0126.d006420 x - μ) := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = 0 := by rw [_root_.GD.N0126.d006425]; ring
  rw [hcross, add_zero]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rfl



theorem d006428 (x : ι → ℝ) :
    ∑ i, x i ^ 2 =
      _root_.GD.N0126.d006422 x + _root_.GD.N0126.d006419 (ι := ι) * _root_.GD.N0126.d006420 x ^ 2 := by
  simpa using _root_.GD.N0126.d006427 x 0


theorem d006429 (x : ι → ℝ) (c : ℝ) :
    _root_.GD.N0126.d006422 (fun i => x i + c) = _root_.GD.N0126.d006422 x := by
  have hmean :
      _root_.GD.N0126.d006420 (fun i => x i + c) = _root_.GD.N0126.d006420 x + c := by
    unfold _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    field_simp [show (Fintype.card ι : ℝ) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero]
  unfold _root_.GD.N0126.d006422
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0126.d006421
  rw [hmean]
  ring


def d006430 : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := _root_.GD.N0126.d006420
  map_add' x y := by
    unfold _root_.GD.N0126.d006420
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    unfold _root_.GD.N0126.d006420
    change (∑ i, c * x i) / _root_.GD.N0126.d006419 (ι := ι) =
      c * ((∑ i, x i) / _root_.GD.N0126.d006419 (ι := ι))
    rw [← Finset.mul_sum]
    ring


def d006431 : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := _root_.GD.N0126.d006421
  map_add' x y := by
    funext i
    unfold _root_.GD.N0126.d006421
    change x i + y i - _root_.GD.N0126.d006420 (x + y) =
      (x i - _root_.GD.N0126.d006420 x) + (y i - _root_.GD.N0126.d006420 y)
    rw [show _root_.GD.N0126.d006420 (x + y) = _root_.GD.N0126.d006420 x + _root_.GD.N0126.d006420 y by
      exact (_root_.GD.N0126.d006430 (ι := ι)).map_add x y]
    ring
  map_smul' c x := by
    funext i
    unfold _root_.GD.N0126.d006421
    change c * x i - _root_.GD.N0126.d006420 (c • x) = c * (x i - _root_.GD.N0126.d006420 x)
    rw [show _root_.GD.N0126.d006420 (c • x) = c * _root_.GD.N0126.d006420 x by
      exact (_root_.GD.N0126.d006430 (ι := ι)).map_smul c x]
    ring

@[simp] theorem d006432 (x : ι → ℝ) :
    _root_.GD.N0126.d006430 x = _root_.GD.N0126.d006420 x := rfl

@[simp] theorem d006433 (x : ι → ℝ) :
    _root_.GD.N0126.d006431 x = _root_.GD.N0126.d006421 x := rfl



def d006434 :
    (ι → ℝ) →ₗ[ℝ] ((Unit → ℝ) × (ι → ℝ)) where
  toFun x := (fun _ => _root_.GD.N0126.d006420 x, _root_.GD.N0126.d006421 x)
  map_add' x y := by
    ext i
    · exact (_root_.GD.N0126.d006430 (ι := ι)).map_add x y
    · exact congrFun ((_root_.GD.N0126.d006431 (ι := ι)).map_add x y) i
  map_smul' c x := by
    ext i
    · exact (_root_.GD.N0126.d006430 (ι := ι)).map_smul c x
    · exact congrFun ((_root_.GD.N0126.d006431 (ι := ι)).map_smul c x) i

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X : ι → Ω → ℝ}
variable {v : ℝ}


def d006435 (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => _root_.GD.N0126.d006420 (fun i => X i ω)


def d006436 (X : ι → Ω → ℝ) : Ω → ι → ℝ :=
  fun ω i => _root_.GD.N0126.d006421 (fun j => X j ω) i



theorem d006437
    [IsFiniteMeasure P]
    (hX2 : ∀ i, MemLp (X i) 2 P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0)
    (j : ι) :
    cov[_root_.GD.N0126.d006435 X, X j; P] = v / _root_.GD.N0126.d006419 (ι := ι) := by
  unfold _root_.GD.N0126.d006435 _root_.GD.N0126.d006420
  rw [covariance_fun_div_left, covariance_fun_sum_left hX2 (hX2 j)]
  simp_rw [hcov]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]


theorem d006438
    [IsFiniteMeasure P]
    (hX2 : ∀ i, MemLp (X i) 2 P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0) :
    cov[_root_.GD.N0126.d006435 X, _root_.GD.N0126.d006435 X; P] =
      v / _root_.GD.N0126.d006419 (ι := ι) := by
  unfold _root_.GD.N0126.d006435 _root_.GD.N0126.d006420
  rw [covariance_fun_div_left, covariance_fun_div_right,
    covariance_fun_sum_fun_sum hX2 hX2]
  simp_rw [hcov]
  have hsum :
      (∑ i : ι, ∑ j : ι, if i = j then v else 0) =
        (Fintype.card ι : ℝ) * v := by
    simp
  rw [hsum]
  unfold _root_.GD.N0126.d006419
  field_simp [show (Fintype.card ι : ℝ) ≠ 0 by
    exact_mod_cast Fintype.card_ne_zero]



theorem d006439
    [IsFiniteMeasure P]
    (hX2 : ∀ i, MemLp (X i) 2 P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0)
    (j : ι) :
    cov[_root_.GD.N0126.d006435 X, fun ω => _root_.GD.N0126.d006436 X ω j; P] = 0 := by
  have hmean2 : MemLp (_root_.GD.N0126.d006435 X) 2 P := by
    unfold _root_.GD.N0126.d006435 _root_.GD.N0126.d006420
    simpa only [div_eq_inv_mul] using
      (memLp_finsetSum Finset.univ (fun i _ => hX2 i)).const_mul
        (_root_.GD.N0126.d006419 (ι := ι))⁻¹
  change
    cov[_root_.GD.N0126.d006435 X, fun ω => X j ω - _root_.GD.N0126.d006435 X ω; P] = 0
  rw [covariance_fun_sub_right hmean2 (hX2 j) hmean2,
    _root_.GD.N0126.d006437 hX2 hcov,
    _root_.GD.N0126.d006438 hX2 hcov]
  ring






theorem d006440
    (hGaussian : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0) :
    IndepFun (_root_.GD.N0126.d006435 X) (_root_.GD.N0126.d006436 X) P := by
  letI : IsProbabilityMeasure P := hGaussian.isProbabilityMeasure
  let L : (ι → ℝ) →ₗ[ℝ] ((Unit → ℝ) × (ι → ℝ)) :=
    _root_.GD.N0126.d006434 (ι := ι)
  let LC : (ι → ℝ) →L[ℝ] ((Unit → ℝ) × (ι → ℝ)) :=
    L.toContinuousLinearMap
  have hJoint :
      HasGaussianLaw
        (fun ω => ((fun _ : Unit => _root_.GD.N0126.d006435 X ω), _root_.GD.N0126.d006436 X ω)) P := by
    have hmap := hGaussian.map_fun LC
    convert hmap using 1 <;> rfl
  have hX2 : ∀ i, MemLp (X i) 2 P :=
    fun i => (hGaussian.eval i).memLp_two
  have hFamily :
      IndepFun
        (fun ω (_ : Unit) => _root_.GD.N0126.d006435 X ω)
        (_root_.GD.N0126.d006436 X) P :=
    hJoint.indepFun_of_covariance_eval fun _ j =>
      _root_.GD.N0126.d006439 hX2 hcov j
  have hc := hFamily.comp (measurable_pi_apply ()) measurable_id
  convert hc using 1 <;> rfl



theorem d006441
    (hGaussian : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0) :
    IndepFun (_root_.GD.N0126.d006435 X)
      (fun ω => _root_.GD.N0126.d006422 (fun i => X i ω)) P := by
  letI : IsProbabilityMeasure P := hGaussian.isProbabilityMeasure
  have h :=
    _root_.GD.N0126.d006440
      (X := X) hGaussian hcov
  have hout := h.comp measurable_id
    (show Measurable (fun r : ι → ℝ => ∑ i, r i ^ 2) by
      fun_prop)
  convert hout using 1 <;> rfl

end Probability

end

end GD.N0126
