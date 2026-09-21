import Mathlib.Analysis.InnerProductSpace.Basic
import GD.Module0106

































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0607

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]



def d001361 (w : H) (η : ℝ) : Set H :=
  {x : H | ⟪x, w⟫ ≤ -η}



def d001362 (w : H) (η : ℝ) (d : H) : H :=
  d - (max 0 (⟪d, w⟫ + η) / ‖w‖ ^ 2) • w




theorem d001363 (a b : ℝ) :
    0 ≤ (max 0 a - max 0 b) * (a - b) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_left ha, max_eq_left hb]
  · rw [max_eq_left ha, max_eq_right hb]
    nlinarith [mul_nonneg hb (by linarith : (0 : ℝ) ≤ b - a)]
  · rw [max_eq_right ha, max_eq_left hb]
    nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ a - b)]
  · rw [max_eq_right ha, max_eq_right hb]
    nlinarith [sq_nonneg (a - b)]


theorem d001364 (a b : ℝ) :
    (max 0 a - max 0 b) ^ 2 ≤ (max 0 a - max 0 b) * (a - b) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_left ha, max_eq_left hb]
  · rw [max_eq_left ha, max_eq_right hb]
    nlinarith [mul_nonneg hb (by linarith : (0 : ℝ) ≤ -a)]
  · rw [max_eq_right ha, max_eq_left hb]
    nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ -b)]
  · rw [max_eq_right ha, max_eq_right hb]
    nlinarith [sq_nonneg (a - b)]




theorem d001365 (w : H) (η : ℝ) (hw : w ≠ 0) (d : H) :
    ⟪_root_.GD.N0230.N0607.d001362 w η d, w⟫ = min ⟪d, w⟫ (-η) := by
  have hN : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  unfold _root_.GD.N0230.N0607.d001362
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ hN.ne']
  rcases le_total (⟪d, w⟫ + η) 0 with h | h
  · rw [max_eq_left h, min_eq_left (by linarith), sub_zero]
  · rw [max_eq_right h, min_eq_right (by linarith)]
    ring


theorem d001366 (w : H) (η : ℝ) (hw : w ≠ 0) (d : H) :
    _root_.GD.N0230.N0607.d001362 w η d ∈ _root_.GD.N0230.N0607.d001361 w η := by
  unfold _root_.GD.N0230.N0607.d001361
  rw [Set.mem_setOf_eq, _root_.GD.N0230.N0607.d001365 w η hw d]
  exact min_le_right _ _


theorem d001367 (w : H) (η : ℝ)
    {x : H} (hx : x ∈ _root_.GD.N0230.N0607.d001361 w η) :
    _root_.GD.N0230.N0607.d001362 w η x = x := by
  have hx' : ⟪x, w⟫ + η ≤ 0 := by
    have := hx
    rw [_root_.GD.N0230.N0607.d001361, Set.mem_setOf_eq] at this
    linarith
  unfold _root_.GD.N0230.N0607.d001362
  rw [max_eq_left hx', zero_div, zero_smul, sub_zero]


theorem d001368 (w : H) (η : ℝ) (hw : w ≠ 0) (d : H) :
    _root_.GD.N0230.N0607.d001362 w η (_root_.GD.N0230.N0607.d001362 w η d) =
      _root_.GD.N0230.N0607.d001362 w η d :=
  _root_.GD.N0230.N0607.d001367 w η (_root_.GD.N0230.N0607.d001366 w η hw d)




theorem d001369 (w : H) (η : ℝ) (d : H) :
    d - _root_.GD.N0230.N0607.d001362 w η d =
      (max 0 (⟪d, w⟫ + η) / ‖w‖ ^ 2) • w := by
  unfold _root_.GD.N0230.N0607.d001362
  exact sub_sub_cancel d _


theorem d001370 (w : H) (η : ℝ) (hw : w ≠ 0)
    (d : H) {y : H} (hy : y ∈ _root_.GD.N0230.N0607.d001361 w η) :
    ‖d - _root_.GD.N0230.N0607.d001362 w η d‖ ≤ ‖d - y‖ := by
  have hN : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  set lam := max 0 (⟪d, w⟫ + η) / ‖w‖ ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    exact div_nonneg (le_max_left 0 _) hN.le
  have hdP := _root_.GD.N0230.N0607.d001369 w η d
  have hcross : 0 ≤ lam * ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫ := by
    rcases eq_or_lt_of_le hlam0 with h0 | hpos
    · rw [← h0, zero_mul]
    · have hmax : 0 < ⟪d, w⟫ + η := by
        by_contra hc
        push Not at hc
        rw [hlam, max_eq_left hc, zero_div] at hpos
        exact lt_irrefl 0 hpos
      have hP : ⟪_root_.GD.N0230.N0607.d001362 w η d, w⟫ = -η := by
        rw [_root_.GD.N0230.N0607.d001365 w η hw d,
          min_eq_right (by linarith)]
      have hy' : ⟪y, w⟫ ≤ -η := hy
      have hinner : 0 ≤ ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫ := by
        rw [inner_sub_left, hP]
        linarith
      exact mul_nonneg hpos.le hinner
  have hdecomp : d - y = lam • w + (_root_.GD.N0230.N0607.d001362 w η d - y) := by
    rw [← hdP]
    abel
  have hexp : ‖d - y‖ ^ 2 =
      lam ^ 2 * ‖w‖ ^ 2 +
        2 * (lam * ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫) +
        ‖_root_.GD.N0230.N0607.d001362 w η d - y‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, real_inner_smul_left, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    try ring
  have hnormP : ‖d - _root_.GD.N0230.N0607.d001362 w η d‖ ^ 2 = lam ^ 2 * ‖w‖ ^ 2 := by
    rw [hdP, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h2 : ‖d - _root_.GD.N0230.N0607.d001362 w η d‖ ^ 2 ≤ ‖d - y‖ ^ 2 := by
    rw [hnormP]
    nlinarith [hexp, hcross,
      sq_nonneg ‖_root_.GD.N0230.N0607.d001362 w η d - y‖]
  have hsq := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    at hsq


theorem d001371 (w : H) (η : ℝ) (hw : w ≠ 0)
    (d : H) {y : H} (hy : y ∈ _root_.GD.N0230.N0607.d001361 w η)
    (heq : ‖d - y‖ = ‖d - _root_.GD.N0230.N0607.d001362 w η d‖) :
    y = _root_.GD.N0230.N0607.d001362 w η d := by
  have hN : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  set lam := max 0 (⟪d, w⟫ + η) / ‖w‖ ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    exact div_nonneg (le_max_left 0 _) hN.le
  have hdP := _root_.GD.N0230.N0607.d001369 w η d
  have hcross : 0 ≤ lam * ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫ := by
    rcases eq_or_lt_of_le hlam0 with h0 | hpos
    · rw [← h0, zero_mul]
    · have hmax : 0 < ⟪d, w⟫ + η := by
        by_contra hc
        push Not at hc
        rw [hlam, max_eq_left hc, zero_div] at hpos
        exact lt_irrefl 0 hpos
      have hP : ⟪_root_.GD.N0230.N0607.d001362 w η d, w⟫ = -η := by
        rw [_root_.GD.N0230.N0607.d001365 w η hw d,
          min_eq_right (by linarith)]
      have hy' : ⟪y, w⟫ ≤ -η := hy
      have hinner : 0 ≤ ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫ := by
        rw [inner_sub_left, hP]
        linarith
      exact mul_nonneg hpos.le hinner
  have hdecomp : d - y = lam • w + (_root_.GD.N0230.N0607.d001362 w η d - y) := by
    rw [← hdP]
    abel
  have hexp : ‖d - y‖ ^ 2 =
      lam ^ 2 * ‖w‖ ^ 2 +
        2 * (lam * ⟪_root_.GD.N0230.N0607.d001362 w η d - y, w⟫) +
        ‖_root_.GD.N0230.N0607.d001362 w η d - y‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, real_inner_smul_left, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    try ring
  have hnormP : ‖d - _root_.GD.N0230.N0607.d001362 w η d‖ ^ 2 = lam ^ 2 * ‖w‖ ^ 2 := by
    rw [hdP, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hzero : ‖_root_.GD.N0230.N0607.d001362 w η d - y‖ ^ 2 ≤ 0 := by
    have hsq : ‖d - y‖ ^ 2 = ‖d - _root_.GD.N0230.N0607.d001362 w η d‖ ^ 2 := by
      rw [heq]
    nlinarith [hexp, hnormP, hcross, hsq]
  have : _root_.GD.N0230.N0607.d001362 w η d - y = 0 := by
    have h0 : ‖_root_.GD.N0230.N0607.d001362 w η d - y‖ = 0 := by
      nlinarith [norm_nonneg (_root_.GD.N0230.N0607.d001362 w η d - y), hzero]
    exact norm_eq_zero.mp h0
  have := sub_eq_zero.mp this
  exact this.symm




theorem d001372 (w : H) (η : ℝ) (hw : w ≠ 0)
    (d e : H) :
    ‖_root_.GD.N0230.N0607.d001362 w η d - _root_.GD.N0230.N0607.d001362 w η e‖ ≤ ‖d - e‖ := by
  have hN : (0 : ℝ) < ‖w‖ ^ 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  set a := ⟪d, w⟫ + η with ha
  set b := ⟪e, w⟫ + η with hb
  set m := max 0 a - max 0 b with hm
  have hPd : _root_.GD.N0230.N0607.d001362 w η d - _root_.GD.N0230.N0607.d001362 w η e =
      (d - e) - (m / ‖w‖ ^ 2) • w := by
    unfold _root_.GD.N0230.N0607.d001362
    rw [hm, sub_div, sub_smul]
    abel
  have hs : ⟪d - e, w⟫ = a - b := by
    rw [inner_sub_left, ha, hb]
    ring
  have hkey : (m / ‖w‖ ^ 2) ^ 2 * ‖w‖ ^ 2 ≤
      (m / ‖w‖ ^ 2) * (a - b) := by
    have h1 : (m / ‖w‖ ^ 2) ^ 2 * ‖w‖ ^ 2 = m ^ 2 / ‖w‖ ^ 2 := by
      field_simp
      try ring
    have h2 : (m / ‖w‖ ^ 2) * (a - b) = m * (a - b) / ‖w‖ ^ 2 := by
      ring
    rw [h1, h2]
    gcongr
    rw [hm]
    exact _root_.GD.N0230.N0607.d001364 a b
  have hpos : 0 ≤ (m / ‖w‖ ^ 2) * (a - b) := by
    have h2 : (m / ‖w‖ ^ 2) * (a - b) = m * (a - b) / ‖w‖ ^ 2 := by
      ring
    rw [h2]
    apply div_nonneg _ hN.le
    rw [hm]
    exact _root_.GD.N0230.N0607.d001363 a b
  have hexp : ‖_root_.GD.N0230.N0607.d001362 w η d - _root_.GD.N0230.N0607.d001362 w η e‖ ^ 2 =
      ‖d - e‖ ^ 2 - 2 * ((m / ‖w‖ ^ 2) * (a - b)) +
        (m / ‖w‖ ^ 2) ^ 2 * ‖w‖ ^ 2 := by
    rw [hPd, norm_sub_sq_real, real_inner_smul_right, hs, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    try ring
  have h2 : ‖_root_.GD.N0230.N0607.d001362 w η d - _root_.GD.N0230.N0607.d001362 w η e‖ ^ 2 ≤
      ‖d - e‖ ^ 2 := by
    nlinarith [hexp, hkey, hpos]
  have hsq := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    at hsq




theorem d001373 (w : H) (η : ℝ) :
    Continuous (_root_.GD.N0230.N0607.d001362 w η) := by
  unfold _root_.GD.N0230.N0607.d001362
  have h1 : Continuous fun d : H ↦ ⟪d, w⟫ := by
    have hlip : LipschitzWith ‖w‖₊ fun d : H ↦ ⟪d, w⟫ := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, dist_eq_norm, ← inner_sub_left]
      calc
        |⟪x - y, w⟫| ≤ ‖x - y‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ↑‖w‖₊ * ‖x - y‖ := by rw [coe_nnnorm]; ring
    exact hlip.continuous
  exact continuous_id.sub
    ((((continuous_const.max (h1.add continuous_const)).div_const
      (‖w‖ ^ 2)).smul continuous_const))




theorem d001374 (w : H) (η : ℝ)
    {u : H} (hu : ⟪u, w⟫ = 0) (d : H) :
    _root_.GD.N0230.N0607.d001362 w η (d + u) = _root_.GD.N0230.N0607.d001362 w η d + u := by
  unfold _root_.GD.N0230.N0607.d001362
  rw [inner_add_left, hu, add_zero]
  abel

end

end N0607
end N0230
end GD

#print axioms _root_.GD.N0230.N0607.d001365
#print axioms _root_.GD.N0230.N0607.d001366
#print axioms _root_.GD.N0230.N0607.d001370
#print axioms _root_.GD.N0230.N0607.d001371
#print axioms _root_.GD.N0230.N0607.d001372
#print axioms _root_.GD.N0230.N0607.d001373
