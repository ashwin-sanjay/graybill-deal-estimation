import GD.Module0172

set_option autoImplicit false
set_option warningAsError true















open MeasureTheory Filter
open scoped Topology SchwartzMap

namespace GD.N0227.N0543

noncomputable section

open _root_.GD.N0232.N0720.N1231

section Measure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}



theorem d002028
    {e ρ φ ψ : X → ℝ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 ≤ c)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (hψ : ∀ᵐ x ∂μ, (ψ x) ^ 2 ≤ K * φ x)
    (hTest : Integrable (fun x ↦ e x * ψ x) μ)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / ρ x) μ)
    (hMass : Integrable (fun x ↦ ρ x * φ x) μ)
    (hTransport : c * (∫ x, ρ x * φ x ∂μ) ≤ ∫ x, e x * ψ x ∂μ) :
    c ^ 2 * (∫ x, ρ x * φ x ∂μ) / K ≤
      ∫ x, (e x) ^ 2 / ρ x ∂μ := by
  have hpoint : ∀ᵐ x ∂μ,
      2 * c * (e x * ψ x) ≤
        K * ((e x) ^ 2 / ρ x) + c ^ 2 * (ρ x * φ x) := by
    filter_upwards [hρ, hψ] with x hx hψx
    have hs : (c * ψ x) ^ 2 ≤ K * (c ^ 2 * φ x) := by
      nlinarith [mul_le_mul_of_nonneg_left hψx (sq_nonneg c)]
    have ht := _root_.GD.N0232.N0720.N1231.d001989 hx hK hs (e := e x)
    nlinarith
  have hi := integral_mono_ae (hTest.const_mul (2 * c))
    ((hEnergy.const_mul K).add (hMass.const_mul (c ^ 2))) hpoint
  change (∫ x, 2 * c * (e x * ψ x) ∂μ) ≤
    ∫ x, K * ((e x) ^ 2 / ρ x) + c ^ 2 * (ρ x * φ x) ∂μ at hi
  simp only [integral_add (hEnergy.const_mul K)
    (hMass.const_mul (c ^ 2)), integral_const_mul] at hi
  have ht := mul_le_mul_of_nonneg_left hTransport hc
  apply (div_le_iff₀ hK).2
  nlinarith



theorem d002029
    {e ρ ρ₀ φ ψ : X → ℝ} {K c A : ℝ}
    (hK : 0 < K) (hc : 0 ≤ c)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (hAnchor : ∀ᵐ x ∂μ, ρ₀ x ≤ ρ x)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (hψ : ∀ᵐ x ∂μ, (ψ x) ^ 2 ≤ K * φ x)
    (hTest : Integrable (fun x ↦ e x * ψ x) μ)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / ρ x) μ)
    (hMass : Integrable (fun x ↦ ρ x * φ x) μ)
    (hAnchorMass : Integrable (fun x ↦ ρ₀ x * φ x) μ)
    (hA : A ≤ ∫ x, ρ₀ x * φ x ∂μ)
    (hTransport : c * (∫ x, ρ x * φ x ∂μ) ≤ ∫ x, e x * ψ x ∂μ) :
    c ^ 2 * A / K ≤ ∫ x, (e x) ^ 2 / ρ x ∂μ := by
  have hm : A ≤ ∫ x, ρ x * φ x ∂μ := by
    apply hA.trans (integral_mono_ae hAnchorMass hMass ?_)
    filter_upwards [hAnchor, hφ] with x hx hφx
    exact mul_le_mul_of_nonneg_right hx hφx
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (sq_nonneg c)) hK.le).trans
      (_root_.GD.N0227.N0543.d002028 hK hc hρ hψ hTest hEnergy hMass hTransport)



theorem d002030
    {e ρ ρ₀ φ ψ : X → ℝ} {K δ A : ℝ}
    (hK : 0 < K) (hδ : δ ≤ 1)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (hAnchor : ∀ᵐ x ∂μ, ρ₀ x ≤ ρ x)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (hψ : ∀ᵐ x ∂μ, (ψ x) ^ 2 ≤ K * φ x)
    (hTest : Integrable (fun x ↦ e x * ψ x) μ)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / ρ x) μ)
    (hMass : Integrable (fun x ↦ ρ x * φ x) μ)
    (hAnchorMass : Integrable (fun x ↦ ρ₀ x * φ x) μ)
    (hA : A ≤ ∫ x, ρ₀ x * φ x ∂μ)
    (hResidual : |(∫ x, ρ x * φ x ∂μ) - (∫ x, e x * ψ x ∂μ)| ≤
      δ * (∫ x, ρ x * φ x ∂μ)) :
    (1 - δ) ^ 2 * A / K ≤ ∫ x, (e x) ^ 2 / ρ x ∂μ := by
  apply _root_.GD.N0227.N0543.d002029 hK (sub_nonneg.mpr hδ) hρ hAnchor hφ hψ
    hTest hEnergy hMass hAnchorMass hA
  have h := (abs_le.mp hResidual).2
  linarith


theorem d002031
    {e ρ ρ₀ φ ψ : X → ℝ} {K A : ℝ}
    (hK : 0 < K)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (hAnchor : ∀ᵐ x ∂μ, ρ₀ x ≤ ρ x)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (hψ : ∀ᵐ x ∂μ, (ψ x) ^ 2 ≤ K * φ x)
    (hTest : Integrable (fun x ↦ e x * ψ x) μ)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / ρ x) μ)
    (hMass : Integrable (fun x ↦ ρ x * φ x) μ)
    (hAnchorMass : Integrable (fun x ↦ ρ₀ x * φ x) μ)
    (hA : A ≤ ∫ x, ρ₀ x * φ x ∂μ)
    (hIdentity : (∫ x, ρ x * φ x ∂μ) = ∫ x, e x * ψ x ∂μ) :
    A / K ≤ ∫ x, (e x) ^ 2 / ρ x ∂μ := by
  have h := _root_.GD.N0227.N0543.d002029 (c := 1) hK (by norm_num) hρ hAnchor
    hφ hψ hTest hEnergy hMass hAnchorMass hA (by simpa using hIdentity.le)
  simpa using h



theorem d002032
    {e ρ : ℕ → X → ℝ} {ρ₀ φ ψ : X → ℝ} {K δ A : ℝ}
    (hK : 0 < K) (hδ : δ < 1) (hApos : 0 < A)
    (hρ : ∀ n, ∀ᵐ x ∂μ, 0 < ρ n x)
    (hAnchor : ∀ n, ∀ᵐ x ∂μ, ρ₀ x ≤ ρ n x)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ φ x)
    (hψ : ∀ᵐ x ∂μ, (ψ x) ^ 2 ≤ K * φ x)
    (hTest : ∀ n, Integrable (fun x ↦ e n x * ψ x) μ)
    (hEnergy : ∀ n, Integrable (fun x ↦ (e n x) ^ 2 / ρ n x) μ)
    (hMass : ∀ n, Integrable (fun x ↦ ρ n x * φ x) μ)
    (hAnchorMass : Integrable (fun x ↦ ρ₀ x * φ x) μ)
    (hA : A ≤ ∫ x, ρ₀ x * φ x ∂μ)
    (hResidual : ∀ n,
      |(∫ x, ρ n x * φ x ∂μ) - (∫ x, e n x * ψ x ∂μ)| ≤
        δ * (∫ x, ρ n x * φ x ∂μ)) :
    ¬ Tendsto (fun n ↦ ∫ x, (e n x) ^ 2 / ρ n x ∂μ) atTop (𝓝 0) := by
  intro hzero
  have hfloor n := _root_.GD.N0227.N0543.d002030 hK hδ.le
    (hρ n) (hAnchor n) hφ hψ (hTest n) (hEnergy n) (hMass n)
    hAnchorMass hA (hResidual n)
  have hle : (1 - δ) ^ 2 * A / K ≤ 0 :=
    ge_of_tendsto hzero (Eventually.of_forall hfloor)
  have hpos : 0 < (1 - δ) ^ 2 * A / K :=
    div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr hδ)) hApos) hK
  exact (not_le_of_gt hpos) hle

end Measure

section DifferentialExpression

open _root_.GD.N0227.N0545
open _root_.GD.N0232.N0720.N1233
open _root_.GD.N0232.N0720.N1230

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]



def d002033 (χ : 𝓢(D, ℝ)) (k : ℕ) : 𝓢(D, ℝ) :=
  _root_.GD.N0232.N0720.N1233.d002008 χ (2 * k + 1) χ

@[simp] theorem d002034 (χ : 𝓢(D, ℝ)) (k : ℕ) (x : D) :
    _root_.GD.N0227.N0543.d002033 χ k x = (χ x ^ (k + 1)) ^ 2 := by
  simp only [_root_.GD.N0227.N0543.d002033, _root_.GD.N0232.N0720.N1233.d002009]
  rw [← pow_succ, ← pow_mul]
  congr 1
  omega



theorem d002035
    (a : _root_.GD.N0227.N0545.d002018 D) (χ : 𝓢(D, ℝ)) (k : ℕ) (ha : a.d002019 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      (a.d002021 (_root_.GD.N0227.N0543.d002033 χ k) x) ^ 2 ≤ K * _root_.GD.N0227.N0543.d002033 χ k x := by
  obtain ⟨r, hr⟩ := a.d002023 χ (k + 1) k ha χ
  have he : a.d002021 (_root_.GD.N0227.N0543.d002033 χ k) = _root_.GD.N0232.N0720.N1233.d002008 χ (k + 1) r := by
    simpa only [_root_.GD.N0227.N0543.d002033, show 2 * k + 1 = (k + 1) + k by omega] using hr
  let M := SchwartzMap.seminorm ℝ 0 0 r
  have hb (x : D) : |r x| ≤ M := SchwartzMap.norm_le_seminorm ℝ r x
  have hM : 0 ≤ M := (abs_nonneg (r 0)).trans (hb 0)
  refine ⟨M ^ 2 + 1, by positivity, ?_⟩
  intro x
  have hx := abs_le.mp (hb x)
  have hs : (r x) ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
      (show 0 ≤ M + r x by linarith [hx.1])]
  rw [he, _root_.GD.N0232.N0720.N1233.d002009, _root_.GD.N0227.N0543.d002034]
  calc
    (χ x ^ (k + 1) * r x) ^ 2 = (χ x ^ (k + 1)) ^ 2 * (r x) ^ 2 := by ring
    _ ≤ (χ x ^ (k + 1)) ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ ≤ (M ^ 2 + 1) * (χ x ^ (k + 1)) ^ 2 := by nlinarith [sq_nonneg (χ x ^ (k + 1))]

variable [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
  {μ : Measure D} [μ.IsAddHaarMeasure]




theorem d002036
    (a : _root_.GD.N0227.N0545.d002018 D) (χ error : 𝓢(D, ℝ)) (k : ℕ) (ρ : D → ℝ)
    (hsource : ∀ x ∈ Function.support (χ : D → ℝ), ρ x = a.d002020 error x) :
    (∫ x, ρ x * _root_.GD.N0227.N0543.d002033 χ k x ∂μ) =
      ∫ x, error x * a.d002021 (_root_.GD.N0227.N0543.d002033 χ k) x ∂μ := by
  calc
    _ = ∫ x, _root_.GD.N0227.N0543.d002033 χ k x * a.d002020 error x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : χ x = 0
      · simp [hx]
      · rw [hsource x hx]
        ring
    _ = _ := a.d002027 error (_root_.GD.N0227.N0543.d002033 χ k)





theorem d002037
    {I : Type*} (a : _root_.GD.N0227.N0545.d002018 D) (χ : 𝓢(D, ℝ))
    (k : ℕ) (ha : a.d002019 ≤ k)
    (error : I → 𝓢(D, ℝ)) (ρ : I → D → ℝ) (ρ₀ : D → ℝ)
    (hρ : ∀ i, ∀ᵐ x ∂μ, 0 < ρ i x)
    (hAnchor : ∀ i, ∀ᵐ x ∂μ, ρ₀ x ≤ ρ i x)
    (hEnergy : ∀ i, Integrable (fun x ↦ (error i x) ^ 2 / ρ i x) μ)
    (hAnchorMass : Integrable (fun x ↦ ρ₀ x * _root_.GD.N0227.N0543.d002033 χ k x) μ)
    (hpositive : 0 < ∫ x, ρ₀ x * _root_.GD.N0227.N0543.d002033 χ k x ∂μ)
    (hsource : ∀ i x, x ∈ Function.support (χ : D → ℝ) →
      ρ i x = a.d002020 (error i) x) :
    ∃ K : ℝ, 0 < K ∧
      (∀ x, (a.d002021 (_root_.GD.N0227.N0543.d002033 χ k) x) ^ 2 ≤ K * _root_.GD.N0227.N0543.d002033 χ k x) ∧
      (0 < (∫ x, ρ₀ x * _root_.GD.N0227.N0543.d002033 χ k x ∂μ) / K) ∧
      ∀ i, (∫ x, ρ₀ x * _root_.GD.N0227.N0543.d002033 χ k x ∂μ) / K ≤
        ∫ x, (error i x) ^ 2 / ρ i x ∂μ := by
  obtain ⟨K, hK, hbound⟩ := _root_.GD.N0227.N0543.d002035 a χ k ha
  refine ⟨K, hK, hbound, div_pos hpositive hK, ?_⟩
  intro i
  have hMass : Integrable (fun x ↦ ρ i x * _root_.GD.N0227.N0543.d002033 χ k x) μ := by
    have hi := (_root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0227.N0543.d002033 χ k) (a.d002020 (error i))).integrable (μ := μ)
    apply hi.congr
    filter_upwards with x
    change _root_.GD.N0227.N0543.d002033 χ k x * a.d002020 (error i) x = ρ i x * _root_.GD.N0227.N0543.d002033 χ k x
    by_cases hx : χ x = 0
    · simp [hx]
    · rw [hsource i x hx]
      ring
  have hTest : Integrable
      (fun x ↦ error i x * a.d002021 (_root_.GD.N0227.N0543.d002033 χ k) x) μ :=
    (_root_.GD.N0232.N0720.N1230.d001994 (error i) (a.d002021 (_root_.GD.N0227.N0543.d002033 χ k))).integrable
  apply _root_.GD.N0227.N0543.d002031 hK (hρ i) (hAnchor i)
    (Eventually.of_forall (fun x ↦ by simp only [_root_.GD.N0227.N0543.d002034]; positivity))
    (Eventually.of_forall hbound) hTest (hEnergy i) hMass hAnchorMass le_rfl
  exact _root_.GD.N0227.N0543.d002036 a χ (error i) k (ρ i) (hsource i)

end DifferentialExpression

end
end GD.N0227.N0543

#print axioms _root_.GD.N0227.N0543.d002028
#print axioms _root_.GD.N0227.N0543.d002030
#print axioms _root_.GD.N0227.N0543.d002032
#print axioms _root_.GD.N0227.N0543.d002035
#print axioms _root_.GD.N0227.N0543.d002036
#print axioms _root_.GD.N0227.N0543.d002037
