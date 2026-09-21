import GD.Module0113































open MeasureTheory Filter

namespace GD
namespace N0230
namespace N0692

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} [MeasurableSpace Θ]



theorem d001431
    {μ : Measure Θ} {K : Set Θ} {a R : ℝ} {ψ : Θ → H} {m : H}
    (ha : 0 ≤ a) (hK : μ K < ⊤)
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R) :
    ‖a • ∫ θ in K, (ψ θ - m) ∂μ‖ ≤ a * (R * (μ K).toReal) := by
  have hbound : ‖∫ θ in K, (ψ θ - m) ∂μ‖ ≤ R * (μ K).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ)
      (f := fun θ ↦ ψ θ - m) (s := K) hK (fun θ _ ↦ hR θ)
    simpa [measureReal_def] using this
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hbound ha




theorem d001432
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ}
    {ψ : Θ → H} {m w : H} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hKfin : ∀ n, μ (K n) < ⊤)
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    (hsurface : Tendsto (fun n ↦ a n * (μ (K n)).toReal)
      atTop (nhds 0))
    (hlim : Tendsto (fun n ↦ a n • ∫ θ in K n, (ψ θ - m) ∂μ)
      atTop (nhds w)) :
    w = 0 := by
  have hbound : ∀ n, ‖a n • ∫ θ in K n, (ψ θ - m) ∂μ‖ ≤
      R * (a n * (μ (K n)).toReal) := by
    intro n
    have h := _root_.GD.N0230.N0692.d001431 (ha n) (hKfin n) hR
      (μ := μ) (K := K n) (a := a n) (ψ := ψ) (m := m)
    calc
      ‖a n • ∫ θ in K n, (ψ θ - m) ∂μ‖ ≤
          a n * (R * (μ (K n)).toReal) := h
      _ = R * (a n * (μ (K n)).toReal) := by ring
  have hmaj : Tendsto (fun n ↦ R * (a n * (μ (K n)).toReal))
      atTop (nhds 0) := by
    simpa using hsurface.const_mul R
  have hzero : Tendsto (fun n ↦ a n • ∫ θ in K n, (ψ θ - m) ∂μ)
      atTop (nhds 0) := squeeze_zero_norm hbound hmaj
  exact tendsto_nhds_unique hlim hzero




theorem d001433
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ}
    {ψ : Θ → H} {m w : H}
    (ha : ∀ n, 0 < a n)
    (hμpos : ∀ n, 0 < (μ (K n)).toReal)
    (hnormint : ∀ n, IntegrableOn (fun θ ↦ ‖ψ θ - m‖) (K n) μ)
    (hint : ∀ n, IntegrableOn (fun θ ↦ ψ θ - m) (K n) μ)
    (hsurface : Tendsto (fun n ↦ a n * (μ (K n)).toReal)
      atTop (nhds 0))
    (hlim : Tendsto (fun n ↦ a n • ∫ θ in K n, (ψ θ - m) ∂μ)
      atTop (nhds w))
    (hw : w ≠ 0) :
    Tendsto (fun n ↦ (∫ θ in K n, ‖ψ θ - m‖ ∂μ) /
      (μ (K n)).toReal) atTop atTop := by
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hnormlim : Tendsto
      (fun n ↦ ‖a n • ∫ θ in K n, (ψ θ - m) ∂μ‖)
      atTop (nhds ‖w‖) := hlim.norm
  have hA : ∀ n, ‖a n • ∫ θ in K n, (ψ θ - m) ∂μ‖ ≤
      a n * ∫ θ in K n, ‖ψ θ - m‖ ∂μ := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha n).le]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm _) (ha n).le
  have hAev : ∀ᶠ n in atTop, ‖w‖ / 2 ≤
      a n * ∫ θ in K n, ‖ψ θ - m‖ ∂μ := by
    have hev := hnormlim.eventually_const_lt
      (by linarith : ‖w‖ / 2 < ‖w‖)
    filter_upwards [hev] with n hn
    exact le_trans hn.le (hA n)
  rw [tendsto_atTop]
  intro C
  by_cases hC : C ≤ 0
  · filter_upwards [] with n
    have h1 : 0 ≤ (∫ θ in K n, ‖ψ θ - m‖ ∂μ) /
        (μ (K n)).toReal := by
      apply div_nonneg _ (hμpos n).le
      exact integral_nonneg fun θ ↦ norm_nonneg _
    linarith
  · push Not at hC
    have hBev : ∀ᶠ n in atTop,
        a n * (μ (K n)).toReal < ‖w‖ / 2 / C := by
      exact hsurface.eventually_lt_const (by positivity)
    filter_upwards [hAev, hBev] with n hAn hBn
    have hBpos : 0 < a n * (μ (K n)).toReal :=
      mul_pos (ha n) (hμpos n)
    have hratio : (∫ θ in K n, ‖ψ θ - m‖ ∂μ) /
        (μ (K n)).toReal =
        (a n * ∫ θ in K n, ‖ψ θ - m‖ ∂μ) /
          (a n * (μ (K n)).toReal) := by
      rw [mul_div_mul_left _ _ (ha n).ne']
    rw [hratio, le_div_iff₀ hBpos]
    have h1 : C * (a n * (μ (K n)).toReal) < C * (‖w‖ / 2 / C) :=
      mul_lt_mul_of_pos_left hBn hC
    have h2 : C * (‖w‖ / 2 / C) = ‖w‖ / 2 := by
      field_simp
    nlinarith [hAn, h1, h2.le, h2.symm.le]

end

end N0692
end N0230
end GD

#print axioms _root_.GD.N0230.N0692.d001431
#print axioms _root_.GD.N0230.N0692.d001432
#print axioms _root_.GD.N0230.N0692.d001433
