import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import GD.Module0104









































open Filter

namespace GD
namespace N0230
namespace N0684

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (Q : H → ℝ) (v ρ : ℝ)




theorem d001351
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) :
    Q 0 = 0 := by
  have h := hchar ρ⁻¹ 0
  rw [smul_zero, mul_inv_cancel₀ hρ] at h
  have hgt : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have h2 : (Real.exp 1 - 1) * Q 0 = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact h3


theorem d001352
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0)
    (t : ℝ) (d : H) :
    Q (t • d) = t * Q d - v * (t * (1 - t) * ‖d‖ ^ 2) := by
  have h := hcomb d 0 t
  rw [smul_zero, add_zero, sub_zero, _root_.GD.N0230.N0684.d001351 Q ρ hchar hρ] at h
  linarith [h]






theorem d001353
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv : v ≠ 0)
    {d₀ : H} (hd₀ : d₀ ≠ 0) :
    ρ = 2 := by
  have hs := _root_.GD.N0230.N0684.d001352 Q v ρ hcomb hchar hρ 2 d₀
  have h1 : Q (Real.exp 1 • ((2 : ℝ) • d₀)) =
      Real.exp (ρ * 1) *
        (2 * Q d₀ - v * (2 * (1 - 2) * ‖d₀‖ ^ 2)) := by
    rw [hchar 1 ((2 : ℝ) • d₀), hs]
  have hswap : Real.exp 1 • ((2 : ℝ) • d₀) =
      (2 : ℝ) • (Real.exp 1 • d₀) := by
    rw [smul_smul, smul_smul, mul_comm (Real.exp 1) 2]
  have hnorm : ‖Real.exp 1 • d₀‖ ^ 2 = Real.exp 2 * ‖d₀‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
      mul_pow, sq, ← Real.exp_add]
    norm_num
  have h2 : Q (Real.exp 1 • ((2 : ℝ) • d₀)) =
      2 * (Real.exp (ρ * 1) * Q d₀) -
        v * (2 * (1 - 2) * (Real.exp 2 * ‖d₀‖ ^ 2)) := by
    rw [hswap,
      _root_.GD.N0230.N0684.d001352 Q v ρ hcomb hchar hρ 2 (Real.exp 1 • d₀),
      hchar 1 d₀, hnorm]
  have heq := h1.symm.trans h2
  have hfactor :
      (Real.exp (ρ * 1) - Real.exp 2) * (2 * v * ‖d₀‖ ^ 2) = 0 := by
    linear_combination heq
  have hn : 0 < ‖d₀‖ ^ 2 := by
    have := norm_pos_iff.mpr hd₀
    positivity
  have hne : (2 : ℝ) * v * ‖d₀‖ ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hv) hn.ne'
  rcases mul_eq_zero.mp hfactor with h | h
  · have hexp : Real.exp (ρ * 1) = Real.exp 2 := by linarith [h]
    have := Real.exp_injective hexp
    linarith [this]
  · exact absurd h hne



theorem d001354
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv : v ≠ 0)
    {d₀ : H} (hd₀ : d₀ ≠ 0) (d : H) :
    Q d = v * ‖d‖ ^ 2 := by
  have hρ2 : ρ = 2 :=
    _root_.GD.N0230.N0684.d001353 Q v ρ hcomb hchar hρ hv hd₀
  have h1 : Q (Real.exp 1 • d) = Real.exp (ρ * 1) * Q d := hchar 1 d
  have h2 := _root_.GD.N0230.N0684.d001352 Q v ρ hcomb hchar hρ (Real.exp 1) d
  rw [hρ2] at h1
  have hE : Real.exp (2 * 1) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hE] at h1
  have heq := h1.symm.trans h2
  have hfac :
      Real.exp 1 * (Real.exp 1 - 1) * (Q d - v * ‖d‖ ^ 2) = 0 := by
    linear_combination heq
  have hgt : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hpos : 0 < Real.exp 1 * (Real.exp 1 - 1) :=
    mul_pos (Real.exp_pos 1) (by linarith)
  have hzero := (mul_eq_zero.mp hfac).resolve_left hpos.ne'
  linarith [hzero]






theorem d001355
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv0 : 0 ≤ v)
    {d₀ : H} (hseed : Q d₀ < 0) :
    v = 0 := by
  by_contra hv
  have hd₀ : d₀ ≠ 0 := by
    intro h0
    rw [h0, _root_.GD.N0230.N0684.d001351 Q ρ hchar hρ] at hseed
    exact lt_irrefl 0 hseed
  have hQ := _root_.GD.N0230.N0684.d001354 Q v ρ hcomb hchar hρ hv hd₀ d₀
  have hnn : 0 ≤ v * ‖d₀‖ ^ 2 := mul_nonneg hv0 (sq_nonneg _)
  linarith [hQ]


theorem d001356
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv : v = 0)
    (t : ℝ) (d : H) :
    Q (t • d) = t * Q d := by
  have h := _root_.GD.N0230.N0684.d001352 Q v ρ hcomb hchar hρ t d
  rw [hv] at h
  linarith [h]


theorem d001357
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv0 : 0 ≤ v)
    {d₀ : H} (hseed : Q d₀ < 0) :
    ρ = 1 := by
  have hv := _root_.GD.N0230.N0684.d001355 Q v ρ hcomb hchar hρ hv0 hseed
  have hs := _root_.GD.N0230.N0684.d001356 Q v ρ hcomb hchar hρ hv (Real.exp 1) d₀
  have hc := hchar 1 d₀
  have heq : Real.exp (ρ * 1) * Q d₀ = Real.exp 1 * Q d₀ := by
    linarith [hs, hc]
  have hQne : Q d₀ ≠ 0 := ne_of_lt hseed
  have hexp := mul_right_cancel₀ hQne heq
  have := Real.exp_injective hexp
  linarith [this]



theorem d001358
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv0 : 0 ≤ v)
    {d₀ : H} (hseed : Q d₀ < 0) :
    IsLinearMap ℝ Q := by
  have hv := _root_.GD.N0230.N0684.d001355 Q v ρ hcomb hchar hρ hv0 hseed
  have hsmul := _root_.GD.N0230.N0684.d001356 Q v ρ hcomb hchar hρ hv
  refine ⟨?_, ?_⟩
  · intro x y
    have hxy : (2 : ℝ) • ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • y) = x + y := by
      rw [smul_add, smul_smul, smul_smul]
      norm_num
    have h2 := hsmul 2 ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • y)
    rw [hxy] at h2
    have hmid := hcomb x y 2⁻¹
    rw [hv, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num] at hmid
    linarith [h2, hmid]
  · intro c x
    rw [smul_eq_mul]
    exact hsmul c x



theorem d001359
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv0 : 0 ≤ v)
    {d₀ : H} (hseed : Q d₀ < 0)
    {C : ℝ}
    (hLip : ∀ d e : H, ‖d‖ ≤ 1 → ‖e‖ ≤ 1 →
      |Q d - Q e| ≤ C * ‖d - e‖) :
    ∀ d : H, |Q d| ≤ C * ‖d‖ := by
  have hv := _root_.GD.N0230.N0684.d001355 Q v ρ hcomb hchar hρ hv0 hseed
  have hsmul := _root_.GD.N0230.N0684.d001356 Q v ρ hcomb hchar hρ hv
  intro d
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, _root_.GD.N0230.N0684.d001351 Q ρ hchar hρ]
    simp
  · have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr h0
    have hu : ‖(‖d‖⁻¹ : ℝ) • d‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ‖d‖⁻¹)]
      field_simp
    have hQu : |Q ((‖d‖⁻¹ : ℝ) • d)| ≤ C := by
      have h := hLip ((‖d‖⁻¹ : ℝ) • d) 0 (le_of_eq hu) (by simp)
      rw [_root_.GD.N0230.N0684.d001351 Q ρ hchar hρ, sub_zero, sub_zero, hu] at h
      simpa using h
    have hrec : d = (‖d‖ : ℝ) • ((‖d‖⁻¹ : ℝ) • d) := by
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne']
      simp
    calc
      |Q d| = |Q ((‖d‖ : ℝ) • ((‖d‖⁻¹ : ℝ) • d))| := by rw [← hrec]
      _ = |‖d‖ * Q ((‖d‖⁻¹ : ℝ) • d)| := by rw [hsmul]
      _ = ‖d‖ * |Q ((‖d‖⁻¹ : ℝ) • d)| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg d)]
      _ ≤ ‖d‖ * C := mul_le_mul_of_nonneg_left hQu (norm_nonneg d)
      _ = C * ‖d‖ := by ring








theorem d001360
    (hcomb : ∀ (d e : H) (t : ℝ),
      Q (t • d + (1 - t) • e) =
        t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2))
    (hchar : ∀ (s : ℝ) (d : H),
      Q (Real.exp s • d) = Real.exp (ρ * s) * Q d)
    (hρ : ρ ≠ 0) (hv0 : 0 ≤ v)
    {d₀ : H} (hseed : Q d₀ < 0)
    {C : ℝ}
    (hLip : ∀ d e : H, ‖d‖ ≤ 1 → ‖e‖ ≤ 1 →
      |Q d - Q e| ≤ C * ‖d - e‖) :
    v = 0 ∧ ρ = 1 ∧ ∃ φ : H →L[ℝ] ℝ, ∀ d, Q d = φ d := by
  have hv := _root_.GD.N0230.N0684.d001355 Q v ρ hcomb hchar hρ hv0 hseed
  refine ⟨hv,
    _root_.GD.N0230.N0684.d001357 Q v ρ hcomb hchar hρ hv0 hseed, ?_⟩
  have hlin := _root_.GD.N0230.N0684.d001358 Q v ρ hcomb hchar hρ
    hv0 hseed
  have hbound := _root_.GD.N0230.N0684.d001359 Q v ρ hcomb hchar hρ
    hv0 hseed hLip
  refine ⟨LinearMap.mkContinuous (IsLinearMap.mk' Q hlin) C ?_, ?_⟩
  · intro x
    rw [IsLinearMap.mk'_apply]
    simpa [Real.norm_eq_abs] using hbound x
  · intro d
    rfl

end

end N0684
end N0230
end GD

#print axioms _root_.GD.N0230.N0684.d001353
#print axioms _root_.GD.N0230.N0684.d001354
#print axioms _root_.GD.N0230.N0684.d001355
#print axioms _root_.GD.N0230.N0684.d001357
#print axioms _root_.GD.N0230.N0684.d001358
#print axioms _root_.GD.N0230.N0684.d001360
