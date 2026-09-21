import GD.Module0638
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0980

open _root_.GD.N0232.N0719.N0885

noncomputable section

variable {I : Type*} [Fintype I]

def d009696 (f : (I → ℝ) → ℝ) : Prop :=
  ∀ c : ℝ, ∀ x, f (fun i => c + x i) = c + f x

abbrev d009697 (m : ℝ) (v : I → ℝ≥0) := Measure.pi (fun i => gaussianReal m (v i))

def d009698 (v : I → ℝ≥0) : (I → ℝ) → ℝ := _root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 v)

@[fun_prop] theorem d009699 (v : I → ℝ≥0) : Measurable (_root_.GD.N0232.N0719.N0980.d009698 v) := by
  unfold _root_.GD.N0232.N0719.N0980.d009698 _root_.GD.N0232.N0719.N0885.d009311
  fun_prop

theorem d009700 (m : ℝ) (v : I → ℝ≥0) (p : I → ℝ) :
    (∫ x, _root_.GD.N0232.N0719.N0885.d009311 p x ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = (∑ i, p i) * m := by
  unfold _root_.GD.N0232.N0719.N0885.d009311
  rw [integral_finsetSum _ (fun i _ =>
    ((_root_.GD.N0232.N0719.N0885.d009315 m v i).memLp_two.integrable (by norm_num)).const_mul (p i))]
  simp_rw [integral_const_mul]
  have hm (i : I) : (∫ x, x i ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = m := by
    calc
      _ = ∫ t : ℝ, t ∂(_root_.GD.N0232.N0719.N0980.d009697 m v).map (fun x => x i) :=
        (integral_map (μ := _root_.GD.N0232.N0719.N0980.d009697 m v) (φ := fun x : I → ℝ => x i)
          (f := fun t : ℝ => t) (measurable_pi_apply i).aemeasurable
          measurable_id.aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ∂gaussianReal m (v i) := by
        rw [(measurePreserving_eval (fun j => gaussianReal m (v j)) i).map_eq]
      _ = m := integral_id_gaussianReal
  simp_rw [hm]
  rw [Finset.sum_mul]

theorem d009701 [Nonempty I] (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i) :
    (∫ x, _root_.GD.N0232.N0719.N0980.d009698 v x ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = m := by
  rw [_root_.GD.N0232.N0719.N0980.d009698, _root_.GD.N0232.N0719.N0980.d009700, _root_.GD.N0232.N0719.N0885.d009325 v hv, one_mul]

theorem d009702 (p : I → ℝ) (f : (I → ℝ) → ℝ)
    (hf : _root_.GD.N0232.N0719.N0980.d009696 f) (x : I → ℝ) :
    f x = _root_.GD.N0232.N0719.N0885.d009311 p x + f (_root_.GD.N0232.N0719.N0885.d009312 p x) := by
  have h := hf (_root_.GD.N0232.N0719.N0885.d009311 p x) (_root_.GD.N0232.N0719.N0885.d009312 p x)
  have heq : (fun i => _root_.GD.N0232.N0719.N0885.d009311 p x + _root_.GD.N0232.N0719.N0885.d009312 p x i) = x := by
    funext i
    simp [_root_.GD.N0232.N0719.N0885.d009312]
  rwa [heq] at h



theorem d009703 [Nonempty I] (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (hequiv : _root_.GD.N0232.N0719.N0980.d009696 f)
    (hL2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v)) :
    (∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) =
      (∫ x, (_root_.GD.N0232.N0719.N0980.d009698 v x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) +
        ∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009698 v x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v := by
  let D : (I → ℝ) → ℝ := fun x => f (_root_.GD.N0232.N0719.N0885.d009312 (_root_.GD.N0232.N0719.N0885.d009323 v) x)
  have hD (x : I → ℝ) : D x = f x - _root_.GD.N0232.N0719.N0980.d009698 v x := by
    have h := _root_.GD.N0232.N0719.N0980.d009702 (_root_.GD.N0232.N0719.N0885.d009323 v) f hequiv x
    dsimp [D, _root_.GD.N0232.N0719.N0980.d009698]
    linarith
  have hM2 : MemLp (_root_.GD.N0232.N0719.N0980.d009698 v) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    (_root_.GD.N0232.N0719.N0885.d009318 m v (_root_.GD.N0232.N0719.N0885.d009323 v)).memLp_two
  have hD2 : MemLp D 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    MemLp.ae_eq (ae_of_all _ fun x => (hD x).symm) (hL2.sub hM2)
  have hC2 : MemLp (fun x => _root_.GD.N0232.N0719.N0980.d009698 v x - m) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    hM2.sub (memLp_const m)
  have hi : IndepFun (fun x => _root_.GD.N0232.N0719.N0980.d009698 v x - m) D (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    (_root_.GD.N0232.N0719.N0885.d009327 m v hv).comp
      (show Measurable (fun t : ℝ => t - m) by fun_prop) hf
  have hmean : (∫ x, (_root_.GD.N0232.N0719.N0980.d009698 v x - m) ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = 0 := by
    rw [integral_sub (hM2.integrable (by norm_num)) (integrable_const m),
      _root_.GD.N0232.N0719.N0980.d009701 m v hv]
    simp
  have hcross : (∫ x, (_root_.GD.N0232.N0719.N0980.d009698 v x - m) * D x ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = 0 := by
    rw [hi.integral_fun_mul_eq_mul_integral hC2.aestronglyMeasurable hD2.aestronglyMeasurable,
      hmean, zero_mul]
  calc
    _ = ∫ x, ((_root_.GD.N0232.N0719.N0980.d009698 v x - m) ^ 2 + D x ^ 2) +
        2 * ((_root_.GD.N0232.N0719.N0980.d009698 v x - m) * D x) ∂_root_.GD.N0232.N0719.N0980.d009697 m v := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change (f x - m) ^ 2 = (_root_.GD.N0232.N0719.N0980.d009698 v x - m) ^ 2 + D x ^ 2 +
          2 * ((_root_.GD.N0232.N0719.N0980.d009698 v x - m) * D x)
        rw [hD x]
        ring
    _ = _ := by
      have hsplit := integral_add (hC2.integrable_sq.add hD2.integrable_sq)
        ((hC2.integrable_mul hD2).const_mul 2)
      have hsquares := integral_add hC2.integrable_sq hD2.integrable_sq
      simp only [Pi.add_apply, Pi.mul_apply] at hsplit hsquares
      rw [hsplit, hsquares, integral_const_mul, hcross]
      simp only [mul_zero, add_zero]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change D x ^ 2 = (f x - _root_.GD.N0232.N0719.N0980.d009698 v x) ^ 2
        rw [hD x]

def d009704 (lower upper f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ :=
  max (lower x) (min (upper x) (f x))

theorem d009705 {l u t a : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    |max l (min u a) - t| ≤ |a - t| := by
  by_cases hal : a ≤ l
  · rw [min_eq_right (hal.trans (hl.trans hu)), max_eq_left hal,
      abs_of_nonpos (sub_nonpos.mpr hl), abs_of_nonpos (sub_nonpos.mpr (hal.trans hl))]
    linarith
  · by_cases hua : u ≤ a
    · rw [min_eq_left hua, max_eq_right (hl.trans hu),
        abs_of_nonneg (sub_nonneg.mpr hu), abs_of_nonneg (sub_nonneg.mpr (hu.trans hua))]
      linarith
    · rw [min_eq_right (le_of_not_ge hua), max_eq_right (le_of_not_ge hal)]

omit [Fintype I] in
theorem d009706 {lower upper f : (I → ℝ) → ℝ}
    (hl : Measurable lower) (hu : Measurable upper) (hf : Measurable f) :
    Measurable (_root_.GD.N0232.N0719.N0980.d009704 lower upper f) := hl.max (hu.min hf)

omit [Fintype I] in
theorem d009707 {lower upper f : (I → ℝ) → ℝ}
    (hl : _root_.GD.N0232.N0719.N0980.d009696 lower) (hu : _root_.GD.N0232.N0719.N0980.d009696 upper)
    (hf : _root_.GD.N0232.N0719.N0980.d009696 f) : _root_.GD.N0232.N0719.N0980.d009696 (_root_.GD.N0232.N0719.N0980.d009704 lower upper f) := by
  intro c x
  simp only [_root_.GD.N0232.N0719.N0980.d009704, hl c x, hu c x, hf c x, add_min, add_max]



theorem d009708 [Nonempty I] (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (lower upper f : (I → ℝ) → ℝ)
    (hlm : Measurable lower) (hum : Measurable upper) (hfm : Measurable f)
    (hle : _root_.GD.N0232.N0719.N0980.d009696 lower) (hue : _root_.GD.N0232.N0719.N0980.d009696 upper)
    (hfe : _root_.GD.N0232.N0719.N0980.d009696 f)
    (hl : ∀ x, lower x ≤ _root_.GD.N0232.N0719.N0980.d009698 v x) (hu : ∀ x, _root_.GD.N0232.N0719.N0980.d009698 v x ≤ upper x)
    (hf2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v)) :
    MemLp (_root_.GD.N0232.N0719.N0980.d009704 lower upper f) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) ∧
      (∫ x, (_root_.GD.N0232.N0719.N0980.d009704 lower upper f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) ≤
        ∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v := by
  have hM2 : MemLp (_root_.GD.N0232.N0719.N0980.d009698 v) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    (_root_.GD.N0232.N0719.N0885.d009318 m v (_root_.GD.N0232.N0719.N0885.d009323 v)).memLp_two
  have hD2 := hf2.sub hM2
  have hcm := _root_.GD.N0232.N0719.N0980.d009706 hlm hum hfm
  have hbound (x : I → ℝ) :
      |_root_.GD.N0232.N0719.N0980.d009704 lower upper f x - _root_.GD.N0232.N0719.N0980.d009698 v x| ≤ |f x - _root_.GD.N0232.N0719.N0980.d009698 v x| :=
    _root_.GD.N0232.N0719.N0980.d009705 (hl x) (hu x)
  have hC2 : MemLp (fun x => _root_.GD.N0232.N0719.N0980.d009704 lower upper f x - _root_.GD.N0232.N0719.N0980.d009698 v x) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    hD2.mono (hcm.sub (_root_.GD.N0232.N0719.N0980.d009699 v)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hbound x)
  have hc2 : MemLp (_root_.GD.N0232.N0719.N0980.d009704 lower upper f) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) := by
    apply MemLp.ae_eq (hf_Lp := hC2.add hM2)
    exact ae_of_all _ fun x => by simp only [Pi.add_apply, sub_add_cancel]
  refine ⟨hc2, ?_⟩
  rw [_root_.GD.N0232.N0719.N0980.d009703 m v hv _ hcm (_root_.GD.N0232.N0719.N0980.d009707 hle hue hfe) hc2,
    _root_.GD.N0232.N0719.N0980.d009703 m v hv f hfm hfe hf2]
  apply add_le_add le_rfl
  apply integral_mono hC2.integrable_sq hD2.integrable_sq
  intro x
  simpa only [sq_abs, Pi.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) (hbound x) 2

end
end GD.N0232.N0719.N0980

#print axioms _root_.GD.N0232.N0719.N0980.d009703
#print axioms _root_.GD.N0232.N0719.N0980.d009708
