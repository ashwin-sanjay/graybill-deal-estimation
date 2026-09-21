import Mathlib




















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0230
namespace N0665

variable {I : Type*} [Fintype I]


noncomputable def d000406 (v : I → ℝ) : ℝ :=
  ∑ i, (v i)⁻¹


noncomputable def d000407 (v : I → ℝ) (i : I) : ℝ :=
  (v i)⁻¹ / _root_.GD.N0230.N0665.d000406 v

theorem d000408 [Nonempty I]
    {v : I → ℝ} (hv : ∀ i, 0 < v i) :
    0 < _root_.GD.N0230.N0665.d000406 v := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  unfold _root_.GD.N0230.N0665.d000406
  exact Finset.sum_pos'
    (fun j _ ↦ (inv_pos.mpr (hv j)).le)
    ⟨i, Finset.mem_univ i, inv_pos.mpr (hv i)⟩

theorem d000409 [Nonempty I]
    {v : I → ℝ} (hv : ∀ i, 0 < v i) :
    ∑ i, _root_.GD.N0230.N0665.d000407 v i = 1 := by
  have hW : _root_.GD.N0230.N0665.d000406 v ≠ 0 := (_root_.GD.N0230.N0665.d000408 hv).ne'
  unfold _root_.GD.N0230.N0665.d000407
  rw [← Finset.sum_div]
  exact div_self hW

theorem d000410 [Nonempty I]
    {v : I → ℝ} (hv : ∀ i, 0 < v i) (i : I) :
    v i * _root_.GD.N0230.N0665.d000407 v i = (_root_.GD.N0230.N0665.d000406 v)⁻¹ := by
  have hvi : v i ≠ 0 := (hv i).ne'
  unfold _root_.GD.N0230.N0665.d000407
  rw [div_eq_mul_inv]
  field_simp

theorem d000411 [Nonempty I]
    {v : I → ℝ} (hv : ∀ i, 0 < v i) :
    ∑ i, v i * _root_.GD.N0230.N0665.d000407 v i ^ 2 =
      (_root_.GD.N0230.N0665.d000406 v)⁻¹ := by
  have hW : _root_.GD.N0230.N0665.d000406 v ≠ 0 := (_root_.GD.N0230.N0665.d000408 hv).ne'
  calc
    ∑ i, v i * _root_.GD.N0230.N0665.d000407 v i ^ 2 =
        ∑ i, (_root_.GD.N0230.N0665.d000406 v)⁻¹ * _root_.GD.N0230.N0665.d000407 v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show v i * _root_.GD.N0230.N0665.d000407 v i ^ 2 =
          (v i * _root_.GD.N0230.N0665.d000407 v i) * _root_.GD.N0230.N0665.d000407 v i by ring,
        _root_.GD.N0230.N0665.d000410 hv i]
    _ = (_root_.GD.N0230.N0665.d000406 v)⁻¹ * ∑ i, _root_.GD.N0230.N0665.d000407 v i := by
      rw [Finset.mul_sum]
    _ = (_root_.GD.N0230.N0665.d000406 v)⁻¹ := by
      rw [_root_.GD.N0230.N0665.d000409 hv, mul_one]



theorem d000412 [Nonempty I]
    {v A : I → ℝ} (hv : ∀ i, 0 < v i)
    (hA : ∑ i, A i = 1) :
    ∑ i, v i * A i ^ 2 =
      (_root_.GD.N0230.N0665.d000406 v)⁻¹ +
        ∑ i, v i * (A i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 := by
  have hW : _root_.GD.N0230.N0665.d000406 v ≠ 0 := (_root_.GD.N0230.N0665.d000408 hv).ne'
  have hlinear :
      ∑ i, v i * (A i * _root_.GD.N0230.N0665.d000407 v i) =
        (_root_.GD.N0230.N0665.d000406 v)⁻¹ := by
    calc
      ∑ i, v i * (A i * _root_.GD.N0230.N0665.d000407 v i) =
          ∑ i, (_root_.GD.N0230.N0665.d000406 v)⁻¹ * A i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show v i * (A i * _root_.GD.N0230.N0665.d000407 v i) =
            (v i * _root_.GD.N0230.N0665.d000407 v i) * A i by ring,
          _root_.GD.N0230.N0665.d000410 hv i]
      _ = (_root_.GD.N0230.N0665.d000406 v)⁻¹ * ∑ i, A i := by
        rw [Finset.mul_sum]
      _ = (_root_.GD.N0230.N0665.d000406 v)⁻¹ := by rw [hA, mul_one]
  have hquadratic := _root_.GD.N0230.N0665.d000411 hv
  symm
  calc
    (_root_.GD.N0230.N0665.d000406 v)⁻¹ +
          ∑ i, v i * (A i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 =
        (_root_.GD.N0230.N0665.d000406 v)⁻¹ +
          ∑ i, (v i * A i ^ 2 -
            2 * (v i * (A i * _root_.GD.N0230.N0665.d000407 v i)) +
            v i * _root_.GD.N0230.N0665.d000407 v i ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (_root_.GD.N0230.N0665.d000406 v)⁻¹ +
          ((∑ i, v i * A i ^ 2) -
            2 * (∑ i, v i * (A i * _root_.GD.N0230.N0665.d000407 v i)) +
            ∑ i, v i * _root_.GD.N0230.N0665.d000407 v i ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    _ = ∑ i, v i * A i ^ 2 := by
      rw [hlinear, hquadratic]
      ring





theorem d000413 [Nonempty I]
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) {v : I → ℝ} (A : Omega → I → ℝ)
    (hv : ∀ i, 0 < v i)
    (hA : ∀ᵐ omega ∂P, ∑ i, A omega i = 1) :
    (∫ omega, ∑ i, v i * A omega i ^ 2 ∂P) =
      ∫ omega,
        (_root_.GD.N0230.N0665.d000406 v)⁻¹ +
          ∑ i, v i * (A omega i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 ∂P := by
  apply integral_congr_ae
  filter_upwards [hA] with omega homega
  exact _root_.GD.N0230.N0665.d000412 hv homega



theorem d000414 [Nonempty I]
    {v A : I → ℝ} (hv : ∀ i, 0 < v i)
    (hA : ∑ i, A i = 1)
    (heq : ∑ i, v i * A i ^ 2 = (_root_.GD.N0230.N0665.d000406 v)⁻¹) :
    A = _root_.GD.N0230.N0665.d000407 v := by
  have hid := _root_.GD.N0230.N0665.d000412 hv hA
  have hsum : ∑ i, v i * (A i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 = 0 := by
    linarith
  funext i
  have hi : v i * (A i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_nonneg (hv j).le (sq_nonneg _))).mp
        hsum i (Finset.mem_univ i)
  have hsquare : (A i - _root_.GD.N0230.N0665.d000407 v i) ^ 2 = 0 := by
    exact (mul_eq_zero.mp hi).resolve_left (hv i).ne'
  nlinarith



theorem d000415 [Nonempty I]
    {v A : I → ℝ} (hv : ∀ i, 0 < v i)
    (hA : ∑ i, A i = 1) :
    (_root_.GD.N0230.N0665.d000406 v)⁻¹ ≤ ∑ i, v i * A i ^ 2 := by
  rw [_root_.GD.N0230.N0665.d000412 hv hA]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hv i).le (sq_nonneg _))



theorem d000416 [Nonempty I]
    {v A : I → ℝ} (hv : ∀ i, 0 < v i)
    (hA : ∑ i, A i = 1) :
    (∑ i, v i * A i ^ 2 = (_root_.GD.N0230.N0665.d000406 v)⁻¹) ↔
      A = _root_.GD.N0230.N0665.d000407 v := by
  constructor
  · exact _root_.GD.N0230.N0665.d000414 hv hA
  · rintro rfl
    exact _root_.GD.N0230.N0665.d000411 hv



theorem d000417 [Nonempty I]
    {v : I → ℝ} (hv : ∀ i, 0 < v i)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0230.N0665.d000407 (fun i ↦ c * v i) = _root_.GD.N0230.N0665.d000407 v := by
  have hc0 : c ≠ 0 := hc.ne'
  have hW : _root_.GD.N0230.N0665.d000406 v ≠ 0 := (_root_.GD.N0230.N0665.d000408 hv).ne'
  have htotal :
      _root_.GD.N0230.N0665.d000406 (fun i ↦ c * v i) = c⁻¹ * _root_.GD.N0230.N0665.d000406 v := by
    unfold _root_.GD.N0230.N0665.d000406
    calc
      ∑ i, (c * v i)⁻¹ = ∑ i, c⁻¹ * (v i)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_inv_rev]
        ring
      _ = c⁻¹ * ∑ i, (v i)⁻¹ := by rw [Finset.mul_sum]
  funext i
  unfold _root_.GD.N0230.N0665.d000407
  rw [htotal, mul_inv_rev]
  field_simp



theorem d000418 [Nonempty I]
    {v w : I → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    _root_.GD.N0230.N0665.d000407 v = _root_.GD.N0230.N0665.d000407 w ↔
      ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * v i := by
  constructor
  · intro heq
    let c := _root_.GD.N0230.N0665.d000406 v / _root_.GD.N0230.N0665.d000406 w
    have hWv : 0 < _root_.GD.N0230.N0665.d000406 v := _root_.GD.N0230.N0665.d000408 hv
    have hWw : 0 < _root_.GD.N0230.N0665.d000406 w := _root_.GD.N0230.N0665.d000408 hw
    refine ⟨c, div_pos hWv hWw, ?_⟩
    intro i
    have hi := congrFun heq i
    unfold _root_.GD.N0230.N0665.d000407 at hi
    dsimp [c]
    field_simp [(hv i).ne', (hw i).ne', hWv.ne', hWw.ne'] at hi ⊢
    nlinarith
  · rintro ⟨c, hc, hwv⟩
    have hfun : w = fun i ↦ c * v i := by
      funext i
      exact hwv i
    rw [hfun]
    exact (_root_.GD.N0230.N0665.d000417 hv hc).symm



theorem d000419 [Nonempty I]
    {v w : I → ℝ} (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * v i) :
    _root_.GD.N0230.N0665.d000407 v ≠ _root_.GD.N0230.N0665.d000407 w := by
  exact fun heq ↦ hray ((_root_.GD.N0230.N0665.d000418 hv hw).mp heq)





def d000420 {Theta Rule : Type*}
    (risk : Theta → Rule → ℝ) (benchmark : Rule) : Prop :=
  ∀ d, (∀ theta, risk theta d ≤ risk theta benchmark) → d = benchmark












theorem d000421
    {Theta BaseRule AugmentedRule : Type*}
    (baseRisk : Theta → BaseRule → ℝ)
    (augmentedRisk : Theta → AugmentedRule → ℝ)
    (oracle : BaseRule)
    (compress : AugmentedRule → BaseRule)
    (lift : BaseRule → AugmentedRule)
    (dispersion : Theta → AugmentedRule → ℝ)
    (hbase : _root_.GD.N0230.N0665.d000420 baseRisk oracle)
    (hdispersion : ∀ theta d, 0 ≤ dispersion theta d)
    (hdecompose : ∀ theta d,
      augmentedRisk theta d =
        baseRisk theta (compress d) + dispersion theta d)
    (horacleLift : ∀ theta,
      augmentedRisk theta (lift oracle) = baseRisk theta oracle)
    (hzero : ∀ d,
      compress d = oracle →
      (∀ theta, dispersion theta d = 0) →
      d = lift oracle) :
    _root_.GD.N0230.N0665.d000420 augmentedRisk (lift oracle) := by
  intro d hdom
  have hcompress : compress d = oracle := by
    apply hbase
    intro theta
    calc
      baseRisk theta (compress d) ≤
          baseRisk theta (compress d) + dispersion theta d :=
        le_add_of_nonneg_right (hdispersion theta d)
      _ = augmentedRisk theta d := (hdecompose theta d).symm
      _ ≤ augmentedRisk theta (lift oracle) := hdom theta
      _ = baseRisk theta oracle := horacleLift theta
  apply hzero d hcompress
  intro theta
  have h := hdom theta
  rw [hdecompose, hcompress, horacleLift] at h
  exact le_antisymm (by linarith) (hdispersion theta d)





theorem d000422
    {Rule : Type*} (cap₁ cap₂ : Rule → Prop) (oracle₁ oracle₂ : Rule)
    (hrigid₁ : ∀ d, cap₁ d → d = oracle₁)
    (hrigid₂ : ∀ d, cap₂ d → d = oracle₂)
    (hne : oracle₁ ≠ oracle₂) :
    ¬ ∃ d, cap₁ d ∧ cap₂ d := by
  rintro ⟨d, hd₁, hd₂⟩
  apply hne
  rw [← hrigid₁ d hd₁, ← hrigid₂ d hd₂]

end N0665
end N0230
end GD

#print axioms _root_.GD.N0230.N0665.d000412
#print axioms _root_.GD.N0230.N0665.d000413
#print axioms _root_.GD.N0230.N0665.d000414
#print axioms _root_.GD.N0230.N0665.d000416
#print axioms _root_.GD.N0230.N0665.d000418
#print axioms _root_.GD.N0230.N0665.d000421
#print axioms _root_.GD.N0230.N0665.d000422
