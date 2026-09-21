import GD.Module1665
import GD.Module1672
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0085
noncomputable section
open _root_.GD.N0102.N0420 _root_.GD.N0033

variable {k : ℕ}

theorem d028681 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (h : Fin k) (hh : 0 < p h) :
    0 < _root_.GD.N0102.N0420.d028253 p q := by
  exact (div_pos hh (hq h)).trans_le
    (Finset.single_le_sum (fun i _ => div_nonneg (hp i) (hq i).le) (Finset.mem_univ h))

theorem d028682 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : Fin k) : 0 ≤ _root_.GD.N0102.N0420.d028255 p q i := by
  unfold _root_.GD.N0102.N0420.d028255
  exact div_nonneg (div_nonneg (hp i) (sq_nonneg _)) (sq_nonneg _)

theorem d028683 (p q : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ _root_.GD.N0102.N0420.d028256 p q :=
  Finset.sum_nonneg (fun i _ => _root_.GD.N0085.d028682 p q hp i)


theorem d028684 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (i : Fin k) (hi : 0 < p i) :
    _root_.GD.N0102.N0420.d028255 p q i ≤ 1 / p i := by
  have hd : p i / q i ≤ _root_.GD.N0102.N0420.d028253 p q :=
    Finset.single_le_sum (fun j _ => div_nonneg (hp j) (hq j).le) (Finset.mem_univ i)
  have hs : (p i / q i)^2 ≤ _root_.GD.N0102.N0420.d028253 p q ^2 :=
    pow_le_pow_left₀ (div_pos hi (hq i)).le hd 2
  calc
    _root_.GD.N0102.N0420.d028255 p q i ≤ (p i / q i^2) / (p i / q i)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (div_pos hi (hq i))) hs
    _ = 1 / p i := by field_simp [hi.ne', (hq i).ne']


theorem d028685 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (h i : Fin k) (hih : i ≠ h) (hh : 0 < p h) :
    _root_.GD.N0102.N0420.d028255 p q i ≤ (q h / q i) / (4 * p h) := by
  have ha : 0 < p h / q h := div_pos hh (hq h)
  have hx : 0 ≤ p i / q i := div_nonneg (hp i) (hq i).le
  have hd := _root_.GD.N0085.d028681 p q hp hq h hh
  have hpair : p h / q h + p i / q i ≤ _root_.GD.N0102.N0420.d028253 p q := by
    have hb := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({h, i} : Finset (Fin k)))
      (fun j _ _ => div_nonneg (hp j) (hq j).le)
    simpa [_root_.GD.N0102.N0420.d028253, Finset.sum_pair hih.symm] using hb
  have hs : (p h / q h + p i / q i)^2 ≤ _root_.GD.N0102.N0420.d028253 p q ^2 :=
    pow_le_pow_left₀ (add_nonneg ha.le hx) hpair 2
  have hfour : 4 * (p h / q h) * (p i / q i) ≤ _root_.GD.N0102.N0420.d028253 p q ^2 := by
    nlinarith [sq_nonneg (p h / q h - p i / q i)]
  have hbound : (p i / q i) / _root_.GD.N0102.N0420.d028253 p q ^2 ≤ 1 / (4 * (p h / q h)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (mul_pos (by norm_num) ha)).mpr
    nlinarith
  calc
    _root_.GD.N0102.N0420.d028255 p q i = ((p i / q i) / _root_.GD.N0102.N0420.d028253 p q ^2) / q i := by
      unfold _root_.GD.N0102.N0420.d028255
      ring
    _ ≤ (1 / (4 * (p h / q h))) / q i :=
      div_le_div_of_nonneg_right hbound (hq i).le
    _ = (q h / q i) / (4 * p h) := by field_simp [hh.ne', (hq h).ne', (hq i).ne']

def d028686 (S : Finset (Fin k)) (h : Fin k) (p0 q : Fin k → ℝ) : ℝ :=
  ∑ i, if i ∈ S then 1 / p0 i else (q h / q i) / (4 * p0 h)

theorem d028687 (S : Finset (Fin k)) (h : Fin k) (hh : h ∈ S)
    (p0 p q : Fin k → ℝ) (hp0 : ∀ i ∈ S, 0 < p0 i)
    (hp : ∀ i, 0 ≤ p i) (hkeep : ∀ i ∈ S, p i = p0 i)
    (hq : ∀ i, 0 < q i) : _root_.GD.N0102.N0420.d028256 p q ≤ _root_.GD.N0085.d028686 S h p0 q := by
  unfold _root_.GD.N0102.N0420.d028256 _root_.GD.N0085.d028686
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · rw [if_pos hi, ← hkeep i hi]
    exact _root_.GD.N0085.d028684 p q hp hq i (by rw [hkeep i hi]; exact hp0 i hi)
  · rw [if_neg hi, ← hkeep h hh]
    exact _root_.GD.N0085.d028685 p q hp hq h i
      (by intro heq; exact hi (heq.symm ▸ hh)) (by rw [hkeep h hh]; exact hp0 h hh)

theorem d028688 (p0 q : Fin k → ℝ) (p : ℕ → Fin k → ℝ)
    (hlim : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p0 i)))
    (hd : _root_.GD.N0102.N0420.d028253 p0 q ≠ 0) :
    Tendsto (fun n => _root_.GD.N0102.N0420.d028256 (p n) q) atTop (𝓝 (_root_.GD.N0102.N0420.d028256 p0 q)) := by
  have hden : Tendsto (fun n => _root_.GD.N0102.N0420.d028253 (p n) q) atTop (𝓝 (_root_.GD.N0102.N0420.d028253 p0 q)) :=
    tendsto_finsetSum Finset.univ (fun i _ => (hlim i).div_const (q i))
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    ((hlim i).div_const (q i^2)).div (hden.pow 2) (pow_ne_zero _ hd))

theorem d028689 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (S : Finset (Fin k)) (h : Fin k) (hh : h ∈ S) (p0 : Fin k → ℝ)
    (hshape : ∀ i ∉ S, 1 < shape i) :
    Integrable (_root_.GD.N0085.d028686 S h p0) (_root_.GD.N0033.d028239 shape) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (shape i) (shape i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  unfold _root_.GD.N0085.d028686
  apply integrable_finsetSum
  intro i _
  by_cases hi : i ∈ S
  · simp only [if_pos hi]
    exact integrable_const _
  · simp only [if_neg hi]
    have hih : i ≠ h := by intro heq; exact hi (heq.symm ▸ hh)
    have hint := _root_.GD.N0033.d028323 shape hs h i (hshape i hi)
    simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hih] using
      hint.div_const (4 * p0 h)


theorem d028690 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (S : Finset (Fin k)) (h : Fin k) (hh : h ∈ S)
    (p0 p : Fin k → ℝ) (hp0 : ∀ i ∈ S, 0 < p0 i)
    (hp : ∀ i, 0 ≤ p i) (hkeep : ∀ i ∈ S, p i = p0 i)
    (hshape : ∀ i ∉ S, 1 < shape i) :
    Integrable (_root_.GD.N0102.N0420.d028256 p) (_root_.GD.N0033.d028239 shape) := by
  apply (_root_.GD.N0085.d028689 shape hs S h hh p0 hshape).mono'
  · exact (show Measurable (_root_.GD.N0102.N0420.d028256 p) by
      unfold _root_.GD.N0102.N0420.d028256 _root_.GD.N0102.N0420.d028255 _root_.GD.N0102.N0420.d028253
      fun_prop).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0085.d028683 p q hp)]
    exact _root_.GD.N0085.d028687 S h hh p0 p q hp0 hp hkeep hq



theorem d028691
    (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (S : Finset (Fin k)) (h : Fin k) (hh : h ∈ S)
    (p0 : Fin k → ℝ) (hp0 : ∀ i ∈ S, 0 < p0 i) (hz : ∀ i ∉ S, p0 i = 0)
    (p : ℕ → Fin k → ℝ) (hp : ∀ n i, 0 ≤ p n i)
    (hkeep : ∀ n, ∀ i ∈ S, p n i = p0 i)
    (hlim : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p0 i)))
    (hshape : ∀ i ∉ S, 1 < shape i) :
    Tendsto (fun n => ∫ q, _root_.GD.N0102.N0420.d028256 (p n) q ∂_root_.GD.N0033.d028239 shape) atTop
      (𝓝 (∫ q, _root_.GD.N0102.N0420.d028256 p0 q ∂_root_.GD.N0033.d028239 shape)) := by
  have hp0nn (i : Fin k) : 0 ≤ p0 i := by
    by_cases hi : i ∈ S
    · exact (hp0 i hi).le
    · simp [hz i hi]
  apply tendsto_integral_of_dominated_convergence (_root_.GD.N0085.d028686 S h p0)
  · intro n
    exact (_root_.GD.N0085.d028690 shape hs S h hh p0 (p n)
      hp0 (hp n) (hkeep n) hshape).aestronglyMeasurable
  · exact _root_.GD.N0085.d028689 shape hs S h hh p0 hshape
  · intro n
    filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0085.d028683 (p n) q (hp n))]
    exact _root_.GD.N0085.d028687 S h hh p0 (p n) q hp0 (hp n) (hkeep n) hq
  · filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
    exact _root_.GD.N0085.d028688 p0 q p hlim
      (_root_.GD.N0085.d028681 p0 q hp0nn hq h (hp0 h hh)).ne'

end
end GD.N0085

#print axioms _root_.GD.N0085.d028684
#print axioms _root_.GD.N0085.d028685
#print axioms _root_.GD.N0085.d028687
#print axioms _root_.GD.N0085.d028688
#print axioms _root_.GD.N0085.d028689
#print axioms _root_.GD.N0085.d028690
#print axioms _root_.GD.N0085.d028691
