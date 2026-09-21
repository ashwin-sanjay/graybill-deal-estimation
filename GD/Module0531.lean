import GD.Module0530
import Mathlib.MeasureTheory.Group.LIntegral

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0208
namespace N0455

noncomputable section

def d007937 (N x : ℝ) : ℝ := min 1 (max 0 (2 - |x| / N))

theorem d007938 (N : ℝ) : Measurable (_root_.GD.N0208.N0455.d007937 N) := by
  unfold _root_.GD.N0208.N0455.d007937
  fun_prop

theorem d007939 {N : ℝ} (hN : 0 < N) :
    (∀ x, 0 ≤ _root_.GD.N0208.N0455.d007937 N x ∧ _root_.GD.N0208.N0455.d007937 N x ≤ 1) ∧
    (∀ x, _root_.GD.N0208.N0455.d007937 N (-x) = _root_.GD.N0208.N0455.d007937 N x) ∧
    (∀ x, |x| ≤ N → _root_.GD.N0208.N0455.d007937 N x = 1) ∧
    (∀ x, 2 * N ≤ |x| → _root_.GD.N0208.N0455.d007937 N x = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · intro x
    simp [_root_.GD.N0208.N0455.d007937]
  · intro x hx
    have hdiv := (div_le_one hN).mpr hx
    unfold _root_.GD.N0208.N0455.d007937
    apply min_eq_left
    exact (by linarith : (1 : ℝ) ≤ 2 - |x| / N).trans (le_max_right _ _)
  · intro x hx
    have hdiv : 2 ≤ |x| / N := (le_div_iff₀ hN).mpr hx
    simp [_root_.GD.N0208.N0455.d007937, max_eq_left (by linarith : 2 - |x| / N ≤ 0)]

theorem d007940 {N : ℝ} (hN : 0 < N) (x y : ℝ) :
    |_root_.GD.N0208.N0455.d007937 N x - _root_.GD.N0208.N0455.d007937 N y| ≤ |x - y| / N := by
  have hm := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - |x| / N))
    1 (max 0 (2 - |y| / N))
  have hx := abs_max_sub_max_le_max (0 : ℝ) (2 - |x| / N) 0 (2 - |y| / N)
  simp only [sub_self, abs_zero] at hm hx
  rw [max_eq_right (abs_nonneg (max 0 (2 - |x| / N) - max 0 (2 - |y| / N)))] at hm
  rw [max_eq_right (abs_nonneg ((2 - |x| / N) - (2 - |y| / N)))] at hx
  unfold _root_.GD.N0208.N0455.d007937
  refine (hm.trans hx).trans ?_
  rw [show (2 - |x| / N) - (2 - |y| / N) = (|y| - |x|) / N by ring,
    abs_div, abs_of_pos hN]
  exact (div_le_div_iff_of_pos_right hN).mpr
    ((abs_abs_sub_abs_le_abs_sub y x).trans_eq (abs_sub_comm y x))

theorem d007941
    (h : ℝ → ℝ) (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hsupp : ∀ x, R ≤ |x| → h x = 0)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) (a : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((h (x + a) - h x) ^ 2)) ≤
      ENNReal.ofReal (4 * R * (L * a) ^ 2) := by
  let I := Icc (-R) R
  let c := ENNReal.ofReal ((L * a) ^ 2)
  let b : ℝ → ℝ≥0∞ := I.indicator (fun _ ↦ c)
  have hb : Measurable b := measurable_const.indicator measurableSet_Icc
  have hpt (x : ℝ) : ENNReal.ofReal ((h (x+a)-h x)^2) ≤ b (x+a) + b x := by
    have hsq : ENNReal.ofReal ((h (x+a)-h x)^2) ≤ c := by
      apply ENNReal.ofReal_le_ofReal
      have hi := hlip (x+a) x
      rw [add_sub_cancel_left] at hi
      have hla : 0 ≤ L * |a| := mul_nonneg hL (abs_nonneg a)
      have hi2 := sq_le_sq₀ (abs_nonneg (h (x+a)-h x)) hla |>.mpr hi
      simpa [sq_abs, mul_pow] using hi2
    by_cases hx : x ∈ I
    · rw [show b x = c by exact indicator_of_mem hx _]
      exact hsq.trans (le_add_left le_rfl)
    · by_cases hxa : x+a ∈ I
      · rw [show b (x+a) = c by exact indicator_of_mem hxa _]
        exact hsq.trans (le_add_right le_rfl)
      · have hxabs : R ≤ |x| := by
          by_contra hn
          exact hx (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
        have hxaabs : R ≤ |x+a| := by
          by_contra hn
          exact hxa (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
        simp [hsupp x hxabs, hsupp (x+a) hxaabs]
  calc
    _ ≤ ∫⁻ x : ℝ, b (x+a) + b x := lintegral_mono hpt
    _ = (∫⁻ x : ℝ, b (x+a)) + ∫⁻ x : ℝ, b x :=
      lintegral_add_left (hb.comp (measurable_id.add_const a)) _
    _ = (∫⁻ x : ℝ, b x) + ∫⁻ x : ℝ, b x := by
      rw [lintegral_add_right_eq_self b a]
    _ = _ := by
      simp only [b, I, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
      dsimp [c]
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_add
        (mul_nonneg (sq_nonneg _) (by linarith)) (mul_nonneg (sq_nonneg _) (by linarith))]
      congr 1
      ring

theorem d007942 {N : ℝ} (hN : 0 < N) (a : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N (x+a) - _root_.GD.N0208.N0455.d007937 N x)^2)) ≤
      ENNReal.ofReal (8 * a^2 / N) := by
  have h := _root_.GD.N0208.N0455.d007941 (_root_.GD.N0208.N0455.d007937 N) (2*N) (1/N)
    (by positivity) (by positivity) (_root_.GD.N0208.N0455.d007939 hN).2.2.2
    (fun x y ↦ by simpa [div_eq_mul_inv, mul_comm] using _root_.GD.N0208.N0455.d007940 hN x y) a
  convert h using 1
  congr 1
  field_simp
  ring

end
end N0455
end GD.N0208

#print axioms _root_.GD.N0208.N0455.d007939
#print axioms _root_.GD.N0208.N0455.d007940
#print axioms _root_.GD.N0208.N0455.d007941
#print axioms _root_.GD.N0208.N0455.d007942
