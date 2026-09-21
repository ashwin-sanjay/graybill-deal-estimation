import GD.Module0109





































open scoped RealInnerProductSpace
open MeasureTheory Filter

namespace GD
namespace N0230
namespace N0572

noncomputable section

open _root_.GD.N0230.N0669

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m w : H)



def d001400 (d : H) : ℝ := -2 * ⟪d - m, w⟫

@[simp]
theorem d001401 : _root_.GD.N0230.N0572.d001400 m w m = 0 := by
  simp [_root_.GD.N0230.N0572.d001400]


theorem d001402 (u : H) (t : ℝ) :
    _root_.GD.N0230.N0572.d001400 m w (m + t • u) = -2 * t * ⟪u, w⟫ := by
  unfold _root_.GD.N0230.N0572.d001400
  rw [show m + t • u - m = t • u from by abel, real_inner_smul_left]
  ring






theorem d001403
    {Θ' : Type*} [MeasurableSpace Θ'] {μ : Measure Θ'}
    {K : ℕ → Set Θ'} {a : ℕ → ℝ} {ψ' : Θ' → H} {Q : H → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hlim : ∀ d, Tendsto
      (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a
        (_root_.GD.N0230.N0673.d001333 ψ'
          (fun _ ↦ m)) n d)
      atTop (nhds (Q d)))
    {d : H} (hd : d ∈ _root_.GD.N0230.N0669.d001375 ψ' m) :
    Q d ≤ 0 := by
  apply le_of_tendsto' (hlim d)
  intro n
  unfold _root_.GD.N0230.N0717.d001329
  have hker := (_root_.GD.N0230.N0669.d001388 ψ' m d).mp hd
  have hI : (∫ θ in K n,
      _root_.GD.N0230.N0673.d001333 ψ'
        (fun _ ↦ m) d θ ∂μ) ≤ 0 :=
    integral_nonpos_of_ae (ae_of_all _ fun θ ↦ hker θ)
  have := mul_le_mul_of_nonneg_left hI (ha n)
  simpa using this







theorem d001404
    {u : H} {c γ t η : ℝ}
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (ht0 : 0 < t)
    (htlo : η / (2 * γ) ≤ t)
    (hthi : t * ‖u‖ ^ 2 ≤ 2 * c) :
    m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m ∧
      _root_.GD.N0230.N0572.d001400 m w (m + t • u) ≤ -η := by
  constructor
  · rw [_root_.GD.N0230.N0669.d001381 ψ m ht0]
    intro θ
    have := hfloor θ
    linarith
  · rw [_root_.GD.N0230.N0572.d001402]
    have h1 : η ≤ 2 * γ * t := by
      have := mul_le_mul_of_nonneg_left htlo (by linarith : (0 : ℝ) ≤ 2 * γ)
      have h2 : 2 * γ * (η / (2 * γ)) = η := by
        field_simp
      linarith [this, h2.symm.le, h2.le]
    have h3 : 2 * t * γ ≤ 2 * t * ⟪u, w⟫ :=
      mul_le_mul_of_nonneg_left hslope (by linarith)
    nlinarith [h1, h3]




theorem d001405
    {u : H} {c γ t η : ℝ}
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (ht0 : 0 < t)
    (htlo : η / (2 * γ) ≤ t)
    (hthi : t * ‖u‖ ^ 2 < 2 * c) :
    (∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖m + t • u - ψ θ‖ ^ 2) ∧
      _root_.GD.N0230.N0572.d001400 m w (m + t • u) ≤ -η := by
  refine ⟨?_, (_root_.GD.N0230.N0572.d001404 ψ m w hfloor hslope hγ ht0
    htlo hthi.le).2⟩
  intro θ
  rw [_root_.GD.N0230.N0669.d001382 ψ m u t θ]
  have hf := hfloor θ
  nlinarith [mul_le_mul_of_nonneg_left hf
    (by linarith : (0 : ℝ) ≤ 2 * t),
    mul_pos ht0 (by linarith : (0 : ℝ) < 2 * c - t * ‖u‖ ^ 2)]



theorem d001406
    {u : H} {c γ η : ℝ} (hu : u ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ) (hc : 0 < c)
    (hη : 0 < η) (hbudget : η ≤ 4 * γ * c / ‖u‖ ^ 2) :
    ∃ t : ℝ, 0 < t ∧ m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m ∧
      _root_.GD.N0230.N0572.d001400 m w (m + t • u) ≤ -η := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  refine ⟨2 * c / ‖u‖ ^ 2, by positivity, ?_⟩
  have hthi : 2 * c / ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤ 2 * c := by
    rw [div_mul_cancel₀ _ hn.ne']
  have htlo : η / (2 * γ) ≤ 2 * c / ‖u‖ ^ 2 := by
    rw [div_le_div_iff₀ (by linarith) hn]
    have hb : η * ‖u‖ ^ 2 ≤ 4 * γ * c := by
      have := mul_le_mul_of_nonneg_right hbudget hn.le
      have h2 : 4 * γ * c / ‖u‖ ^ 2 * ‖u‖ ^ 2 = 4 * γ * c := by
        rw [div_mul_cancel₀ _ hn.ne']
      linarith [this, h2.le, h2.symm.le]
    nlinarith [hb]
  exact _root_.GD.N0230.N0572.d001404 ψ m w hfloor hslope hγ
    (by positivity) htlo hthi




theorem d001407
    {u : H} {c : ℝ} (hu : u ≠ 0) :
    _root_.GD.N0230.N0572.d001400 m w (m + (c / ‖u‖ ^ 2) • u) =
      -(2 * c * ⟪u, w⟫) / ‖u‖ ^ 2 := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  rw [_root_.GD.N0230.N0572.d001402]
  field_simp
  try ring

end

end N0572
end N0230
end GD

#print axioms _root_.GD.N0230.N0572.d001403
#print axioms _root_.GD.N0230.N0572.d001404
#print axioms _root_.GD.N0230.N0572.d001405
#print axioms _root_.GD.N0230.N0572.d001406
#print axioms _root_.GD.N0230.N0572.d001407
