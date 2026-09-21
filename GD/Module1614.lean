import GD.Module1608






























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped Interval

namespace GD.N0106.N0428.N0770.N1736
noncomputable section

open _root_.GD.N0118
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1731




theorem d027546 {g' g'' : ℝ → ℝ} {c w M : ℝ} (hw : 0 < w)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    (hM : ∀ x ∈ Icc (c - w) (c + w), |g'' x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (c - w) (c + w)) :
    |g' x - g' c| ≤ M * |x - c| := by
  have hc : c ∈ Icc (c - w) (c + w) := ⟨by linarith, by linarith⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hg' y hy).hasDerivWithinAt)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy) (convex_Icc _ _) hc hx
  simpa only [Real.norm_eq_abs] using h


def d027547 (g g' : ℝ → ℝ) (c x : ℝ) : ℝ := g x - g c - g' c * (x - c)



theorem d027548 {g g' g'' : ℝ → ℝ} {c w : ℝ} (hw : 0 < w)
    (hg : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    {x : ℝ} (hx : x ∈ Icc (c - w) (c + w)) :
    _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x = ∫ t in c..x, (g' t - g' c) := by
  have hc : c ∈ Icc (c - w) (c + w) := ⟨by linarith, by linarith⟩
  have hsub : uIcc c x ⊆ Icc (c - w) (c + w) := Set.uIcc_subset_Icc hc hx
  have hderiv : ∀ t ∈ uIcc c x, HasDerivAt (fun t => g t - g' c * t) (g' t - g' c) t := by
    intro t ht
    have h1 := hg t (hsub ht)
    have h2 := (hasDerivAt_id t).const_mul (g' c)
    exact (h1.sub h2).congr_deriv (by simp only [mul_one])
  have hcont : ContinuousOn g' (Icc (c - w) (c + w)) :=
    fun t ht => (hg' t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t => g' t - g' c) volume c x :=
    ((hcont.mono hsub).sub continuousOn_const).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold _root_.GD.N0106.N0428.N0770.N1736.d027547
  first
  | ring
  | (beta_reduce; ring)
  | (simp only []; ring)


theorem d027549 {g g' g'' : ℝ → ℝ} {c w M : ℝ} (hw : 0 < w)
    (hg : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    (hM : ∀ x ∈ Icc (c - w) (c + w), |g'' x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (c - w) (c + w)) :
    |_root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x| ≤ M / 2 * (x - c) ^ 2 := by
  have hc : c ∈ Icc (c - w) (c + w) := ⟨by linarith, by linarith⟩
  have hsub : uIcc c x ⊆ Icc (c - w) (c + w) := Set.uIcc_subset_Icc hc hx
  have hlip : ∀ t ∈ Icc (c - w) (c + w), |g' t - g' c| ≤ M * |t - c| :=
    fun t ht => _root_.GD.N0106.N0428.N0770.N1736.d027546 hw hg' hM ht
  rw [_root_.GD.N0106.N0428.N0770.N1736.d027548 hw hg hg' hx]
  rcases le_total c x with hcx | hxc
  · have hbound : ∀ᵐ t ∂volume, t ∈ Ioc c x → ‖g' t - g' c‖ ≤ M * (t - c) := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht2 : t ∈ Icc (c - w) (c + w) :=
        hsub (by rw [Set.uIcc_of_le hcx]; exact Set.Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs]
      calc |g' t - g' c| ≤ M * |t - c| := hlip t ht2
        _ = M * (t - c) := by rw [abs_of_nonneg (by linarith [ht.1])]
    have hGint : IntervalIntegrable (fun t => M * (t - c)) volume c x :=
      (by fun_prop : Continuous fun t : ℝ => M * (t - c)).continuousOn.intervalIntegrable
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hcx hbound hGint
    have h2 : (∫ t in c..x, M * (t - c)) = M / 2 * (x - c) ^ 2 := by
      have hd : ∀ t ∈ uIcc c x,
          HasDerivAt (fun t => M / 2 * (t - c) ^ 2) (M * (t - c)) t := by
        intro t _
        have := (((hasDerivAt_id t).sub (hasDerivAt_const (x := t) (c := c))).pow 2).const_mul (M / 2)
        exact this.congr_deriv (by
          first
          | (simp only [Pi.sub_apply, id_eq, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat, sub_zero]
             ring)
          | (simp; ring)
          | (norm_num; ring))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hGint]
      ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans_eq h2
  · have hxc' : x ≤ c := hxc
    rw [intervalIntegral.integral_symm, abs_neg]
    have hbound : ∀ᵐ t ∂volume, t ∈ Ioc x c → ‖g' t - g' c‖ ≤ M * (c - t) := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht2 : t ∈ Icc (c - w) (c + w) :=
        hsub (by rw [Set.uIcc_of_ge hxc']; exact Set.Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs]
      calc |g' t - g' c| ≤ M * |t - c| := hlip t ht2
        _ = M * (c - t) := by rw [abs_of_nonpos (by linarith [ht.2])]; ring
    have hGint : IntervalIntegrable (fun t => M * (c - t)) volume x c :=
      (by fun_prop : Continuous fun t : ℝ => M * (c - t)).continuousOn.intervalIntegrable
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hxc' hbound hGint
    have h2 : (∫ t in x..c, M * (c - t)) = M / 2 * (x - c) ^ 2 := by
      have hd : ∀ t ∈ uIcc x c,
          HasDerivAt (fun t => -(M / 2) * (c - t) ^ 2) (M * (c - t)) t := by
        intro t _
        have := (((hasDerivAt_id t).const_sub c).pow 2).const_mul (-(M / 2))
        exact this.congr_deriv (by
          first
          | (simp only [Pi.sub_apply, id_eq, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
             ring)
          | (simp; ring)
          | (norm_num; ring))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hGint]
      ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans_eq h2





theorem d027550 {g ρ : ℝ → ℝ} {c w : ℝ}
    (hg : ContinuousOn g (Icc (c - w) (c + w))) (hρ : Continuous ρ)
    (hρz : ∀ x ∉ Icc (c - w) (c + w), ρ x = 0) :
    Integrable (fun x => g x * ρ x) := by
  have hcont : ContinuousOn (fun x => g x * ρ x) (Icc (c - w) (c + w)) :=
    hg.mul hρ.continuousOn
  exact hcont.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
    (fun x hx => by rw [hρz x hx, mul_zero])




theorem d027551 {g g' g'' ρ : ℝ → ℝ} {c w M m₀ m₂ : ℝ}
    (hw : 0 < w)
    (hg : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    (hM : ∀ x ∈ Icc (c - w) (c + w), |g'' x| ≤ M)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρc : Continuous ρ) (hρz : ∀ x ∉ Icc (c - w) (c + w), ρ x = 0)
    (hm0 : (∫ x, ρ x) = m₀) (hm1 : (∫ x, (x - c) * ρ x) = 0)
    (hm2 : (∫ x, (x - c) ^ 2 * ρ x) = m₂) :
    |(∫ x, g x * ρ x) - g c * m₀| ≤ M / 2 * m₂ := by
  have hgc : ContinuousOn g (Icc (c - w) (c + w)) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hIg : Integrable (fun x => g x * ρ x) := _root_.GD.N0106.N0428.N0770.N1736.d027550 hgc hρc hρz
  have hIρ : Integrable ρ := by
    have h := _root_.GD.N0106.N0428.N0770.N1736.d027550 (g := fun _ => (1 : ℝ)) continuousOn_const hρc hρz
    simpa only [one_mul] using h
  have hI1 : Integrable (fun x => (x - c) * ρ x) :=
    _root_.GD.N0106.N0428.N0770.N1736.d027550 (by fun_prop : Continuous fun x : ℝ => x - c).continuousOn hρc hρz
  have hI2 : Integrable (fun x => (x - c) ^ 2 * ρ x) :=
    _root_.GD.N0106.N0428.N0770.N1736.d027550 (by fun_prop : Continuous fun x : ℝ => (x - c) ^ 2).continuousOn
      hρc hρz
  have hIr : Integrable (fun x => _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x) := by
    have heq : (fun x => _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x) =
        fun x => g x * ρ x - g c * ρ x - g' c * ((x - c) * ρ x) := by
      funext x; unfold _root_.GD.N0106.N0428.N0770.N1736.d027547; ring
    rw [heq]
    exact (hIg.sub (hIρ.const_mul (g c))).sub (hI1.const_mul (g' c))
  have hdecomp : (∫ x, g x * ρ x) = g c * m₀ + ∫ x, _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x := by
    have heq : (fun x => g x * ρ x) =
        fun x => (g c * ρ x + g' c * ((x - c) * ρ x)) + _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x := by
      funext x; unfold _root_.GD.N0106.N0428.N0770.N1736.d027547; ring
    have hs := integral_add ((hIρ.const_mul (g c)).add (hI1.const_mul (g' c))) hIr
    have hs₁ := integral_add (hIρ.const_mul (g c)) (hI1.const_mul (g' c))
    simp only [Pi.add_apply] at hs hs₁
    rw [heq, hs, hs₁, integral_const_mul, integral_const_mul, hm0, hm1,
      mul_zero, add_zero]
  have hbound : ∀ x,
      ‖_root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x‖ ≤ M / 2 * ((x - c) ^ 2 * ρ x) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    by_cases hx : x ∈ Icc (c - w) (c + w)
    · calc |_root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x| * ρ x ≤ M / 2 * (x - c) ^ 2 * ρ x :=
            mul_le_mul_of_nonneg_right (_root_.GD.N0106.N0428.N0770.N1736.d027549 hw hg hg' hM hx) (hρ0 x)
        _ = M / 2 * ((x - c) ^ 2 * ρ x) := by ring
    · rw [hρz x hx]
      simp
  have hnorm := norm_integral_le_of_norm_le (hI2.const_mul (M / 2))
    (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul, hm2, Real.norm_eq_abs] at hnorm
  rw [hdecomp]
  calc |g c * m₀ + (∫ x, _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x) - g c * m₀|
      = |∫ x, _root_.GD.N0106.N0428.N0770.N1736.d027547 g g' c x * ρ x| := by congr 1; ring
    _ ≤ M / 2 * m₂ := hnorm



theorem d027552 {c w x : ℝ} (hw : 0 < w) (hx : x ∉ Icc (c - w) (c + w)) :
    _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x = 0 := by
  have habs : w ≤ |x - c| := by
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with h | h
    · rw [not_le] at h
      rw [abs_of_neg (by linarith)]
      linarith
    · rw [not_le] at h
      rw [abs_of_pos (by linarith)]
      linarith
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024124
  apply max_eq_right
  rw [sub_nonpos, le_div_iff₀ hw, one_mul]
  exact habs

theorem d027553 (c w : ℝ) (hw : 0 < w) : (∫ x, _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x) = w := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  rw [integral_const_mul, _root_.GD.N0118.d008594 c w hw, mul_one]

theorem d027554 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x) = 0 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027430 c w 1 hw one_pos
  simp only [pow_one] at h
  have heq : (fun x => (x - c) * (w * _root_.GD.N0118.d008582 c w x)) =
      fun x => w * ((x - c) * _root_.GD.N0118.d008582 c w x) := by
    funext x; ring
  rw [heq, integral_const_mul, h, mul_zero]

theorem d027555 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x) = w ^ 3 / 6 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  have heq : (fun x => (x - c) ^ 2 * (w * _root_.GD.N0118.d008582 c w x)) =
      fun x => w * ((x - c) ^ 2 * _root_.GD.N0118.d008582 c w x) := by
    funext x; ring
  rw [heq, integral_const_mul, _root_.GD.N0106.N0428.N0770.N1731.d027433 c w hw]
  ring

theorem d027556 (c w : ℝ) (hw : 0 < w) : (∫ x, _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) = 2 * w / 3 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  have heq : (fun x => (w * _root_.GD.N0118.d008582 c w x) ^ 2) = fun x => w ^ 2 * _root_.GD.N0118.d008582 c w x ^ 2 := by
    funext x; ring
  rw [heq, integral_const_mul, _root_.GD.N0118.d008599 c w hw]
  field_simp
  <;> ring

theorem d027557 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) = 0 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027430 c w 2 hw two_pos
  have heq : (fun x => (x - c) * (w * _root_.GD.N0118.d008582 c w x) ^ 2) =
      fun x => w ^ 2 * ((x - c) * _root_.GD.N0118.d008582 c w x ^ 2) := by
    funext x; ring
  rw [heq, integral_const_mul, h, mul_zero]

theorem d027558 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) = w ^ 3 / 15 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1725.d024150 c w _ hw]
  have heq : (fun x => (x - c) ^ 2 * (w * _root_.GD.N0118.d008582 c w x) ^ 2) =
      fun x => w ^ 2 * ((x - c) ^ 2 * _root_.GD.N0118.d008582 c w x ^ 2) := by
    funext x; ring
  rw [heq, integral_const_mul, _root_.GD.N0106.N0428.N0770.N1731.d027434 c w hw]
  ring


theorem d027559 {g g' g'' : ℝ → ℝ} {c w M : ℝ} (hw : 0 < w)
    (hg : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    (hM : ∀ x ∈ Icc (c - w) (c + w), |g'' x| ≤ M) :
    |(∫ x, g x * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x) - g c * w| ≤ M * w ^ 3 / 12 := by
  have h := _root_.GD.N0106.N0428.N0770.N1736.d027551 hw hg hg' hM (_root_.GD.N0106.N0428.N0770.N1725.d024139 c w) (_root_.GD.N0106.N0428.N0770.N1725.d024133 c w)
    (fun x hx => _root_.GD.N0106.N0428.N0770.N1736.d027552 hw hx) (_root_.GD.N0106.N0428.N0770.N1736.d027553 c w hw)
    (_root_.GD.N0106.N0428.N0770.N1736.d027554 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027555 c w hw)
  calc |(∫ x, g x * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x) - g c * w| ≤ M / 2 * (w ^ 3 / 6) := h
    _ = M * w ^ 3 / 12 := by ring


theorem d027560 {g g' g'' : ℝ → ℝ} {c w M : ℝ} (hw : 0 < w)
    (hg : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc (c - w) (c + w), HasDerivAt g' (g'' x) x)
    (hM : ∀ x ∈ Icc (c - w) (c + w), |g'' x| ≤ M) :
    |(∫ x, g x * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) - g c * (2 * w / 3)| ≤ M * w ^ 3 / 30 := by
  have h := _root_.GD.N0106.N0428.N0770.N1736.d027551 (ρ := fun x => _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) hw hg hg' hM
    (fun x => pow_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024139 c w x) 2) ((_root_.GD.N0106.N0428.N0770.N1725.d024133 c w).pow 2)
    (fun x hx => by
      show _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2 = 0
      rw [_root_.GD.N0106.N0428.N0770.N1736.d027552 hw hx]
      simp)
    (_root_.GD.N0106.N0428.N0770.N1736.d027556 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027557 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027558 c w hw)
  calc |(∫ x, g x * _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2) - g c * (2 * w / 3)| ≤ M / 2 * (w ^ 3 / 15) := h
    _ = M * w ^ 3 / 30 := by ring



theorem d027561 {ρe ρF : ℝ → ℝ} {c f w : ℝ}
    (hρe : ∀ x ∉ Icc (c - w) (c + w), ρe x = 0)
    (hρF : ∀ y ∉ Icc (f - w) (f + w), ρF y = 0)
    {p : ℝ × ℝ} (hp : p ∉ Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)) :
    ρe p.1 * ρF p.2 = 0 := by
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [hρe p.1 h, zero_mul]
  · rw [hρF p.2 h, mul_zero]

theorem d027562 {g : ℝ × ℝ → ℝ} {ρe ρF : ℝ → ℝ} {c f w : ℝ}
    (hg : ContinuousOn g (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)))
    (hρec : Continuous ρe) (hρFc : Continuous ρF)
    (hρe : ∀ x ∉ Icc (c - w) (c + w), ρe x = 0)
    (hρF : ∀ y ∉ Icc (f - w) (f + w), ρF y = 0) :
    Integrable (fun p => g p * (ρe p.1 * ρF p.2)) (volume.prod volume) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => g p * (ρe p.1 * ρF p.2))
      (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)) :=
    hg.mul ((hρec.comp continuous_fst).mul (hρFc.comp continuous_snd)).continuousOn
  have hI : IntegrableOn (fun p : ℝ × ℝ => g p * (ρe p.1 * ρF p.2))
      (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)) (volume.prod volume) :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hI.integrable_of_forall_notMem_eq_zero
    (fun p hp => by rw [_root_.GD.N0106.N0428.N0770.N1736.d027561 hρe hρF hp, mul_zero])




theorem d027563 {g : ℝ × ℝ → ℝ} {gE gEE : ℝ → ℝ}
    {gF gFF : ℝ → ℝ → ℝ} {ρe ρF : ℝ → ℝ} {c f w ME MF me0 me2 mF0 mF2 : ℝ} (hw : 0 < w)
    (hcont : ContinuousOn g (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)))
    (hF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => g (e, F)) (gF e F) F)
    (hF' : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => gF e F) (gFF e F) F)
    (hMF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w), |gFF e F| ≤ MF)
    (hE : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt (fun e => g (e, f)) (gE e) e)
    (hE' : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt gE (gEE e) e)
    (hME : ∀ e ∈ Icc (c - w) (c + w), |gEE e| ≤ ME)
    (hρe0 : ∀ x, 0 ≤ ρe x) (hρec : Continuous ρe)
    (hρez : ∀ x ∉ Icc (c - w) (c + w), ρe x = 0)
    (hρF0 : ∀ y, 0 ≤ ρF y) (hρFc : Continuous ρF)
    (hρFz : ∀ y ∉ Icc (f - w) (f + w), ρF y = 0)
    (he0 : (∫ x, ρe x) = me0) (he1 : (∫ x, (x - c) * ρe x) = 0)
    (he2 : (∫ x, (x - c) ^ 2 * ρe x) = me2)
    (hF0 : (∫ y, ρF y) = mF0) (hF1 : (∫ y, (y - f) * ρF y) = 0)
    (hF2 : (∫ y, (y - f) ^ 2 * ρF y) = mF2) :
    |(∫ p, g p * (ρe p.1 * ρF p.2) ∂(volume.prod volume)) - g (c, f) * (me0 * mF0)| ≤
      (ME / 2 * me2) * mF0 + (MF / 2 * mF2) * me0 := by
  have hf : f ∈ Icc (f - w) (f + w) := ⟨by linarith, by linarith⟩
  have hIG : Integrable (fun p : ℝ × ℝ => g p * (ρe p.1 * ρF p.2)) (volume.prod volume) :=
    _root_.GD.N0106.N0428.N0770.N1736.d027562 hcont hρec hρFc hρez hρFz

  have hinner : ∀ e, (∫ F, g (e, F) * (ρe e * ρF F)) = ρe e * ∫ F, g (e, F) * ρF F := by
    intro e
    have heq : (fun F => g (e, F) * (ρe e * ρF F)) = fun F => ρe e * (g (e, F) * ρF F) := by
      funext F; ring
    rw [heq, integral_const_mul]
  have hinnerBound : ∀ e ∈ Icc (c - w) (c + w),
      |(∫ F, g (e, F) * ρF F) - g (e, f) * mF0| ≤ MF / 2 * mF2 := fun e he =>
    _root_.GD.N0106.N0428.N0770.N1736.d027551 hw (hF e he) (hF' e he) (hMF e he) hρF0 hρFc hρFz
      hF0 hF1 hF2

  have hIouter : Integrable (fun e => ρe e * ∫ F, g (e, F) * ρF F) := by
    have h := hIG.integral_prod_left
    simpa only [hinner] using h
  have hgline : ContinuousOn (fun e => g (e, f)) (Icc (c - w) (c + w)) := by
    have hmaps : MapsTo (fun e : ℝ => (e, f)) (Icc (c - w) (c + w))
        (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)) :=
      fun e he => Set.mk_mem_prod he hf
    exact hcont.comp (continuous_id.prodMk continuous_const).continuousOn hmaps
  have hIline : Integrable (fun e => g (e, f) * ρe e) := _root_.GD.N0106.N0428.N0770.N1736.d027550 hgline hρec hρez
  have hIeps : Integrable (fun e => ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)) := by
    have heq : (fun e => ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)) =
        fun e => (ρe e * ∫ F, g (e, F) * ρF F) - mF0 * (g (e, f) * ρe e) := by
      funext e; ring
    rw [heq]
    exact hIouter.sub (hIline.const_mul mF0)
  have hsplit : (∫ e, ρe e * ∫ F, g (e, F) * ρF F) =
      mF0 * (∫ e, g (e, f) * ρe e) +
        ∫ e, ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0) := by
    have heq : (fun e => ρe e * ∫ F, g (e, F) * ρF F) =
        fun e => mF0 * (g (e, f) * ρe e) +
          ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0) := by
      funext e; ring
    rw [heq, integral_add (hIline.const_mul mF0) hIeps, integral_const_mul]

  have houter : |(∫ e, g (e, f) * ρe e) - g (c, f) * me0| ≤ ME / 2 * me2 :=
    _root_.GD.N0106.N0428.N0770.N1736.d027551 hw hE hE' hME hρe0 hρec hρez he0 he1 he2

  have hepsBound : ∀ e,
      ‖ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)‖ ≤ ρe e * (MF / 2 * mF2) := by
    intro e
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρe0 e)]
    by_cases he : e ∈ Icc (c - w) (c + w)
    · exact mul_le_mul_of_nonneg_left (hinnerBound e he) (hρe0 e)
    · rw [hρez e he]
      simp
  have hIρe : Integrable ρe := by
    have h := _root_.GD.N0106.N0428.N0770.N1736.d027550 (g := fun _ => (1 : ℝ)) continuousOn_const hρec hρez
    simpa only [one_mul] using h
  have hepsInt := norm_integral_le_of_norm_le (hIρe.mul_const (MF / 2 * mF2))
    (Filter.Eventually.of_forall hepsBound)
  rw [integral_mul_const, he0, Real.norm_eq_abs] at hepsInt
  have hmF0 : 0 ≤ mF0 := by
    rw [← hF0]
    exact integral_nonneg hρF0
  have hA : |mF0 * ((∫ e, g (e, f) * ρe e) - g (c, f) * me0)| ≤ mF0 * (ME / 2 * me2) := by
    rw [abs_mul, abs_of_nonneg hmF0]
    exact mul_le_mul_of_nonneg_left houter hmF0

  rw [integral_prod _ hIG]
  simp only [hinner]
  rw [hsplit]
  calc |mF0 * (∫ e, g (e, f) * ρe e) +
        (∫ e, ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)) - g (c, f) * (me0 * mF0)|
      = |mF0 * ((∫ e, g (e, f) * ρe e) - g (c, f) * me0) +
          ∫ e, ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)| := by
        congr 1; ring
    _ ≤ |mF0 * ((∫ e, g (e, f) * ρe e) - g (c, f) * me0)| +
          |∫ e, ρe e * ((∫ F, g (e, F) * ρF F) - g (e, f) * mF0)| := by
        first
        | exact abs_add_le _ _
        | exact abs_add _ _
    _ ≤ mF0 * (ME / 2 * me2) + me0 * (MF / 2 * mF2) := add_le_add hA hepsInt
    _ = (ME / 2 * me2) * mF0 + (MF / 2 * mF2) * me0 := by ring


theorem d027564 {g : ℝ × ℝ → ℝ} {gE gEE : ℝ → ℝ}
    {gF gFF : ℝ → ℝ → ℝ} {c f w ME MF : ℝ} (hw : 0 < w)
    (hcont : ContinuousOn g (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)))
    (hF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => g (e, F)) (gF e F) F)
    (hF' : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => gF e F) (gFF e F) F)
    (hMF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w), |gFF e F| ≤ MF)
    (hE : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt (fun e => g (e, f)) (gE e) e)
    (hE' : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt gE (gEE e) e)
    (hME : ∀ e ∈ Icc (c - w) (c + w), |gEE e| ≤ ME) :
    |(∫ p, g p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) - g (c, f) * w ^ 2| ≤
      (ME + MF) * w ^ 4 / 12 := by
  have h := _root_.GD.N0106.N0428.N0770.N1736.d027563 hw hcont hF hF' hMF hE hE' hME
    (_root_.GD.N0106.N0428.N0770.N1725.d024139 c w) (_root_.GD.N0106.N0428.N0770.N1725.d024133 c w) (fun x hx => _root_.GD.N0106.N0428.N0770.N1736.d027552 hw hx)
    (_root_.GD.N0106.N0428.N0770.N1725.d024139 f w) (_root_.GD.N0106.N0428.N0770.N1725.d024133 f w) (fun y hy => _root_.GD.N0106.N0428.N0770.N1736.d027552 hw hy)
    (_root_.GD.N0106.N0428.N0770.N1736.d027553 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027554 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027555 c w hw)
    (_root_.GD.N0106.N0428.N0770.N1736.d027553 f w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027554 f w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027555 f w hw)
  have heq : (fun p : ℝ × ℝ => g p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p) =
      fun p => g p * (_root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2) := by
    funext p; rfl
  have hc : g (c, f) * (w * w) = g (c, f) * w ^ 2 := by ring
  rw [heq, ← hc]
  calc _ ≤ (ME / 2 * (w ^ 3 / 6)) * w + (MF / 2 * (w ^ 3 / 6)) * w := h
    _ = (ME + MF) * w ^ 4 / 12 := by ring


theorem d027565 {g : ℝ × ℝ → ℝ} {gE gEE : ℝ → ℝ}
    {gF gFF : ℝ → ℝ → ℝ} {c f w ME MF : ℝ} (hw : 0 < w)
    (hcont : ContinuousOn g (Icc (c - w) (c + w) ×ˢ Icc (f - w) (f + w)))
    (hF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => g (e, F)) (gF e F) F)
    (hF' : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w),
      HasDerivAt (fun F => gF e F) (gFF e F) F)
    (hMF : ∀ e ∈ Icc (c - w) (c + w), ∀ F ∈ Icc (f - w) (f + w), |gFF e F| ≤ MF)
    (hE : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt (fun e => g (e, f)) (gE e) e)
    (hE' : ∀ e ∈ Icc (c - w) (c + w), HasDerivAt gE (gEE e) e)
    (hME : ∀ e ∈ Icc (c - w) (c + w), |gEE e| ≤ ME) :
    |(∫ p, g p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) - g (c, f) * (4 * w ^ 2 / 9)| ≤
      (ME + MF) * w ^ 4 / 45 := by
  have h := _root_.GD.N0106.N0428.N0770.N1736.d027563 (ρe := fun x => _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2)
    (ρF := fun y => _root_.GD.N0106.N0428.N0770.N1725.d024124 f w y ^ 2) hw hcont hF hF' hMF hE hE' hME
    (fun x => pow_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024139 c w x) 2) ((_root_.GD.N0106.N0428.N0770.N1725.d024133 c w).pow 2)
    (fun x hx => by
      show _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ^ 2 = 0
      rw [_root_.GD.N0106.N0428.N0770.N1736.d027552 hw hx]
      simp)
    (fun y => pow_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024139 f w y) 2) ((_root_.GD.N0106.N0428.N0770.N1725.d024133 f w).pow 2)
    (fun y hy => by
      show _root_.GD.N0106.N0428.N0770.N1725.d024124 f w y ^ 2 = 0
      rw [_root_.GD.N0106.N0428.N0770.N1736.d027552 hw hy]
      simp)
    (_root_.GD.N0106.N0428.N0770.N1736.d027556 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027557 c w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027558 c w hw)
    (_root_.GD.N0106.N0428.N0770.N1736.d027556 f w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027557 f w hw) (_root_.GD.N0106.N0428.N0770.N1736.d027558 f w hw)
  have heq : (fun p : ℝ × ℝ => g p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2) =
      fun p => g p * (_root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2 ^ 2) := by
    funext p
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024125
    ring
  have hc : g (c, f) * (2 * w / 3 * (2 * w / 3)) = g (c, f) * (4 * w ^ 2 / 9) := by ring
  rw [heq, ← hc]
  calc _ ≤ (ME / 2 * (w ^ 3 / 15)) * (2 * w / 3) + (MF / 2 * (w ^ 3 / 15)) * (2 * w / 3) := h
    _ = (ME + MF) * w ^ 4 / 45 := by ring

end
end GD.N0106.N0428.N0770.N1736

#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027549
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027551
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027559
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027560
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027563
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027564
#print axioms _root_.GD.N0106.N0428.N0770.N1736.d027565
