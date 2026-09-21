import GD.Module0363
import GD.Module0372
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic




























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set intervalIntegral Filter Topology Polynomial

namespace GD.N0106.N0428.N0765.N1556
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1547 _root_.GD.N0106.N0428.N0765.N1614
noncomputable section


def d005641 (η u s : ℝ) : ℝ := (1 - u) * η / (η + s)

def d005642 (η u s : ℝ) : ℝ := (1 - u) * s / (η + s)

def d005643 (η u s : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1534.d005330 η u (_root_.GD.N0106.N0428.N0765.N1556.d005641 η u s) (_root_.GD.N0106.N0428.N0765.N1556.d005642 η u s)

def d005644 (η u s : ℝ) : ℝ := 10 * (1 + η) * u / (_root_.GD.N0106.N0428.N0765.N1556.d005641 η u s + η * _root_.GD.N0106.N0428.N0765.N1556.d005642 η u s)

def d005645 (η : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2, _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2)

def d005646 : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2}

def d005647 (η f s : ℝ) : ℝ := f * η * (1 + s) / (10 * (1 + η) * (η + s))

def d005648 (η f s : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s / (1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s)

def d005649 (η f s : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1556.d005643 η (_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s) s




def d005650 (η s : ℝ) : ℝ := max (η + s) (η / 2)

def d005651 (η u s l : ℝ) : ℝ :=
  (1 - u) * η / _root_.GD.N0106.N0428.N0765.N1556.d005650 η s * (1 - l) + η * ((1 - u) * s / _root_.GD.N0106.N0428.N0765.N1556.d005650 η s) * l + (1 + η) * u * l * (1 - l)

def d005652 (m η u s l : ℝ) : ℝ := (l * (1 - l)) ^ ((9 : ℝ) / 2) * (max (_root_.GD.N0106.N0428.N0765.N1556.d005651 η u s l) m) ^ (-((21 : ℝ) / 2))

def d005653 (m η u s : ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l) / ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l

section Clamp
variable {η : ℝ} (hη : 0 < η)
include hη

theorem d005654 (s : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1556.d005650 η s := lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem d005655 {s : ℝ} (hs : -(η / 2) ≤ s) : _root_.GD.N0106.N0428.N0765.N1556.d005650 η s = η + s := max_eq_left (by linarith)

theorem d005656 : Continuous fun p : (ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005651 η p.1.1 p.1.2 p.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005651
  have hd : Continuous fun p : (ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005650 η p.1.2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005650
    fun_prop
  have hdne : ∀ p : (ℝ × ℝ) × ℝ, _root_.GD.N0106.N0428.N0765.N1556.d005650 η p.1.2 ≠ 0 := fun p => (_root_.GD.N0106.N0428.N0765.N1556.d005654 hη _).ne'
  apply Continuous.add
  apply Continuous.add
  · exact (Continuous.div (by fun_prop) hd hdne).mul (by fun_prop)
  · exact (continuous_const.mul (Continuous.div (by fun_prop) hd hdne)).mul (by fun_prop)
  · fun_prop

theorem d005657 {m : ℝ} (hm : 0 < m) :
    Continuous fun p : (ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005652 m η p.1.1 p.1.2 p.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005652
  apply Continuous.mul
  · exact (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  · apply Continuous.rpow_const ((_root_.GD.N0106.N0428.N0765.N1556.d005656 hη).max continuous_const)
    intro p
    left
    exact (lt_of_lt_of_le hm (le_max_right _ _)).ne'

theorem d005658 {m : ℝ} (hm : 0 < m) (u s : ℝ) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le hm (le_max_right _ _)) _)

theorem d005659 {m : ℝ} (hm : 0 < m) :
    Continuous fun p : ℝ × ℝ => ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1556.d005652 m η p.1 p.2 l := by
  apply continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun p : ℝ × ℝ => fun l => l * _root_.GD.N0106.N0428.N0765.N1556.d005652 m η p.1 p.2 l)
  have h := _root_.GD.N0106.N0428.N0765.N1556.d005657 hη hm
  exact continuous_snd.mul h

theorem d005660 {m : ℝ} (hm : 0 < m) :
    Continuous fun p : ℝ × ℝ => ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1556.d005652 m η p.1 p.2 l := by
  apply continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun p : ℝ × ℝ => fun l => _root_.GD.N0106.N0428.N0765.N1556.d005652 m η p.1 p.2 l)
  exact _root_.GD.N0106.N0428.N0765.N1556.d005657 hη hm

theorem d005661 {m : ℝ} (hm : 0 < m) (u s : ℝ) :
    Continuous fun l : ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l := by
  have h := (_root_.GD.N0106.N0428.N0765.N1556.d005657 hη hm).comp
    (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => (u, s)) continuous_id)
  simpa [Function.comp_def] using h

theorem d005662 {m : ℝ} (hm : 0 < m) (u s : ℝ) : 0 < ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l := by
  apply intervalIntegral_pos_of_pos_on
  · exact (_root_.GD.N0106.N0428.N0765.N1556.d005661 hη hm u s).continuousOn.intervalIntegrable_of_Icc zero_le_one
  · exact fun l hl => _root_.GD.N0106.N0428.N0765.N1556.d005658 hη hm u s hl
  · exact zero_lt_one

theorem d005663 {m : ℝ} (hm : 0 < m) : Continuous fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005653 m η p.1 p.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005653
  exact (_root_.GD.N0106.N0428.N0765.N1556.d005659 hη hm).div (_root_.GD.N0106.N0428.N0765.N1556.d005660 hη hm) (fun p => (_root_.GD.N0106.N0428.N0765.N1556.d005662 hη hm _ _).ne')


theorem d005664 {m u s : ℝ} (hs : -(η / 2) ≤ s)
    (hb : ∀ l ∈ Icc (0 : ℝ) 1, m ≤ _root_.GD.N0106.N0428.N0765.N1556.d005651 η u s l) : _root_.GD.N0106.N0428.N0765.N1556.d005643 η u s = _root_.GD.N0106.N0428.N0765.N1556.d005653 m η u s := by
  have hk : ∀ l ∈ Icc (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u (_root_.GD.N0106.N0428.N0765.N1556.d005641 η u s) (_root_.GD.N0106.N0428.N0765.N1556.d005642 η u s) l = _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l := by
    intro l hl
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1556.d005652
    congr 1
    rw [max_eq_left (hb l hl)]
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005328 _root_.GD.N0106.N0428.N0765.N1556.d005651 _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
    rw [_root_.GD.N0106.N0428.N0765.N1556.d005655 hη hs]
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005643 _root_.GD.N0106.N0428.N0765.N1534.d005330 _root_.GD.N0106.N0428.N0765.N1556.d005653
  congr 1
  · apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    show l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u (_root_.GD.N0106.N0428.N0765.N1556.d005641 η u s) (_root_.GD.N0106.N0428.N0765.N1556.d005642 η u s) l = l * _root_.GD.N0106.N0428.N0765.N1556.d005652 m η u s l
    rw [hk l hl]
  · apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    exact hk l hl

end Clamp



section Inverse
variable {η : ℝ} (hη : 0 < η)
include hη

theorem d005665 {u s : ℝ} (hu : u < 1) (hs : 0 < s) : 0 < _root_.GD.N0106.N0428.N0765.N1556.d005641 η u s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005641
  have : 0 < 1 - u := by linarith
  positivity

theorem d005666 {u s : ℝ} (hu : u < 1) (hs : 0 < s) : 0 < _root_.GD.N0106.N0428.N0765.N1556.d005642 η u s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005642
  have : 0 < 1 - u := by linarith
  positivity

theorem d005667 (u : ℝ) {s : ℝ} (hs : 0 < s) : u + _root_.GD.N0106.N0428.N0765.N1556.d005641 η u s + _root_.GD.N0106.N0428.N0765.N1556.d005642 η u s = 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
  have : η + s ≠ 0 := by positivity
  field_simp
  ring

theorem d005668 {u s : ℝ} (hu : u < 1) (hs : 0 < s) : η * _root_.GD.N0106.N0428.N0765.N1556.d005642 η u s / _root_.GD.N0106.N0428.N0765.N1556.d005641 η u s = s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
  have h1 : 1 - u ≠ 0 := by linarith
  have h2 : η + s ≠ 0 := by positivity
  field_simp

theorem d005669 {f s : ℝ} (hf : 0 ≤ f) (hs : 0 < s) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005647
  positivity

theorem d005670 {f s : ℝ} (hf : 0 < f) (hs : 0 < s) : 0 < _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005647
  positivity

theorem d005671 {f s : ℝ} (hf : 0 < f) (hs : 0 < s) : _root_.GD.N0106.N0428.N0765.N1556.d005648 η f s ∈ Ioo (0 : ℝ) 1 := by
  have hg := _root_.GD.N0106.N0428.N0765.N1556.d005670 hη hf hs
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005648
  constructor
  · exact div_pos hg (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

theorem d005672 (s : ℝ) : _root_.GD.N0106.N0428.N0765.N1556.d005648 η 0 s = 0 := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005648 _root_.GD.N0106.N0428.N0765.N1556.d005647
  simp

theorem d005673 {f s : ℝ} (hf : 0 ≤ f) (hs : 0 < s) : _root_.GD.N0106.N0428.N0765.N1556.d005644 η (_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s) s = f := by
  have hg := _root_.GD.N0106.N0428.N0765.N1556.d005669 hη hf hs
  have h1g : (1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s) ≠ 0 := by positivity
  have hes : η + s ≠ 0 := by positivity
  have hsum : _root_.GD.N0106.N0428.N0765.N1556.d005641 η (_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s) s + η * _root_.GD.N0106.N0428.N0765.N1556.d005642 η (_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s) s
      = (1 - _root_.GD.N0106.N0428.N0765.N1556.d005648 η f s) * η * (1 + s) / (η + s) := by
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
    field_simp
  have h1u : 1 - _root_.GD.N0106.N0428.N0765.N1556.d005648 η f s = 1 / (1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s) := by
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005648
    field_simp
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005644
  rw [hsum, h1u]
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005648
  have h10 : (10 * (1 + η) * (η + s)) ≠ 0 := by positivity
  rw [div_eq_iff (by positivity)]
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005647
  field_simp

theorem d005674 {s : ℝ} (hs : 0 < s) : _root_.GD.N0106.N0428.N0765.N1556.d005649 η 0 s = _root_.GD.N0106.N0428.N0765.N1547.d005450 s := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005649 _root_.GD.N0106.N0428.N0765.N1556.d005643
  rw [_root_.GD.N0106.N0428.N0765.N1556.d005672 hη]
  have hv := _root_.GD.N0106.N0428.N0765.N1556.d005665 hη (u := 0) (by norm_num) hs
  have hw := _root_.GD.N0106.N0428.N0765.N1556.d005666 hη (u := 0) (by norm_num) hs
  rw [_root_.GD.N0106.N0428.N0765.N1547.d005456 hη hv hw, _root_.GD.N0106.N0428.N0765.N1556.d005668 hη (by norm_num) hs]

end Inverse



section Continuity
variable {η : ℝ} (hη : 0 < η)
include hη


theorem d005675 {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) {u s l : ℝ}
    (hu : |u| ≤ min (1 / 4) (4 * (η * min 1 (s₁ / 2) / (η + 2 * s₂) / 4) / (1 + η)))
    (hs : s₁ / 2 ≤ s) (hs' : s ≤ 2 * s₂) (hl : l ∈ Icc (0 : ℝ) 1) :
    2 * (η * min 1 (s₁ / 2) / (η + 2 * s₂) / 4) ≤ _root_.GD.N0106.N0428.N0765.N1556.d005651 η u s l := by
  set m₁ := η * min 1 (s₁ / 2) / (η + 2 * s₂) / 4 with hm₁
  have hm₁pos : 0 < m₁ := by
    have h1 : 0 < min 1 (s₁ / 2) := lt_min one_pos (by positivity)
    have h2 : 0 < η + 2 * s₂ := by linarith
    rw [hm₁]
    exact div_pos (div_pos (mul_pos hη h1) h2) (by norm_num)
  have hu1 : |u| ≤ 1 / 4 := hu.trans (min_le_left _ _)
  have hu2 : |u| ≤ 4 * m₁ / (1 + η) := hu.trans (min_le_right _ _)
  have hul := abs_le.mp hu1
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hden : _root_.GD.N0106.N0428.N0765.N1556.d005650 η s = η + s := _root_.GD.N0106.N0428.N0765.N1556.d005655 hη (by linarith)
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005651
  rw [hden]
  have hl0 := hl.1
  have hl1 := hl.2

  have hA : (1 - u) * η / (η + s) * (1 - l) + η * ((1 - u) * s / (η + s)) * l
      = (1 - u) * η / (η + s) * ((1 - l) + s * l) := by ring
  have hmin : min 1 (s₁ / 2) ≤ (1 - l) + s * l := by
    have h1 : min 1 (s₁ / 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 (s₁ / 2) ≤ s := (min_le_right _ _).trans hs
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hl1), mul_le_mul_of_nonneg_left h2 hl0]
  have hfrac : 3 * m₁ ≤ (1 - u) * η / (η + s) * ((1 - l) + s * l) := by
    have h34 : 3 / 4 ≤ 1 - u := by linarith [hul.2]
    have hη' : η / (η + 2 * s₂) ≤ η / (η + s) := by
      apply div_le_div_of_nonneg_left hη.le (by linarith) (by linarith)
    have hm : 0 ≤ min 1 (s₁ / 2) := le_min zero_le_one (by positivity)
    have hstep := mul_le_mul (mul_le_mul h34 hη' (div_nonneg hη.le (by linarith)) (by linarith))
      hmin hm (mul_nonneg (by linarith) (div_nonneg hη.le (by linarith)))
    calc 3 * m₁ = (3 / 4) * (η / (η + 2 * s₂)) * min 1 (s₁ / 2) := by rw [hm₁]; ring
      _ ≤ (1 - u) * (η / (η + s)) * ((1 - l) + s * l) := hstep
      _ = (1 - u) * η / (η + s) * ((1 - l) + s * l) := by ring

  have hB : -m₁ ≤ (1 + η) * u * l * (1 - l) := by
    have hll : l * (1 - l) ≤ 1 / 4 := by nlinarith [sq_nonneg (l - 1 / 2)]
    have hll0 : 0 ≤ l * (1 - l) := mul_nonneg hl0 (sub_nonneg.mpr hl1)
    have habs : |(1 + η) * u * l * (1 - l)| ≤ m₁ := by
      rw [show (1 + η) * u * l * (1 - l) = ((1 + η) * u) * (l * (1 - l)) by ring, abs_mul,
        abs_of_nonneg hll0, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + η)]
      calc (1 + η) * |u| * (l * (1 - l)) ≤ (1 + η) * (4 * m₁ / (1 + η)) * (1 / 4) := by
            gcongr
        _ = m₁ := by field_simp
    linarith [(abs_le.mp habs).1]
  linarith [hA, hfrac, hB]

end Continuity



section Main
variable {η : ℝ} (hη : 0 < η)
include hη



theorem d005676 :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ _root_.GD.N0106.N0428.N0765.N1556.d005645 η '' _root_.GD.N0106.N0428.N0765.N1556.d005646 := by

  set s₁ : ℝ := 1 with hs₁def
  set s₂ : ℝ := 2 with hs₂def
  have hs₁ : 0 < s₁ := by rw [hs₁def]; norm_num
  have hs₁₂ : s₁ < s₂ := by rw [hs₁def, hs₂def]; norm_num
  set m₁ := η * min 1 (s₁ / 2) / (η + 2 * s₂) / 4 with hm₁
  have hm₁pos : 0 < m₁ := by
    have h1 : 0 < min 1 (s₁ / 2) := lt_min one_pos (by positivity)
    have h2 : 0 < η + 2 * s₂ := by linarith
    rw [hm₁]
    exact div_pos (div_pos (mul_pos hη h1) h2) (by norm_num)
  set δ := min (1 / 4) (4 * m₁ / (1 + η)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  set K := η * (1 + 2 * s₂) / (10 * (1 + η) * (η + s₁ / 2)) with hK
  have hKpos : 0 < K := by positivity
  set f₁ := δ / (2 * K) with hf₁
  have hf₁pos : 0 < f₁ := by positivity

  have hgg : ∀ f s : ℝ, s₁ / 2 ≤ s → s ≤ 2 * s₂ → |_root_.GD.N0106.N0428.N0765.N1556.d005647 η f s| ≤ K * |f| := by
    intro f s hs hs'
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005647
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 10 * (1 + η) * (η + s)),
      abs_mul, abs_mul, abs_of_pos hη, abs_of_pos (by positivity : (0 : ℝ) < 1 + s),
      div_le_iff₀ (by positivity), hK]
    have h1 : 1 + s ≤ 1 + 2 * s₂ := by linarith
    have h2 : η + s₁ / 2 ≤ η + s := by linarith
    calc |f| * η * (1 + s) ≤ |f| * η * (1 + 2 * s₂) := by gcongr
      _ = η * (1 + 2 * s₂) / (10 * (1 + η) * (η + s₁ / 2)) * |f| * (10 * (1 + η) * (η + s₁ / 2)) := by
          field_simp
      _ ≤ η * (1 + 2 * s₂) / (10 * (1 + η) * (η + s₁ / 2)) * |f| * (10 * (1 + η) * (η + s)) := by
          gcongr
  have huOf : ∀ f s : ℝ, |f| < f₁ → s₁ / 2 ≤ s → s ≤ 2 * s₂ → |_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s| ≤ δ := by
    intro f s hf hs hs'
    have hg := hgg f s hs hs'
    have hgle : |_root_.GD.N0106.N0428.N0765.N1556.d005647 η f s| ≤ δ / 2 := by
      calc |_root_.GD.N0106.N0428.N0765.N1556.d005647 η f s| ≤ K * |f| := hg
        _ ≤ K * f₁ := by gcongr
        _ = δ / 2 := by rw [hf₁]; field_simp
    have hδ8 : δ / 2 ≤ 1 / 8 := by
      have : δ ≤ 1 / 4 := min_le_left _ _
      linarith
    have hgl := abs_le.mp hgle
    have h1g : 7 / 8 ≤ 1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s := by linarith
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005648
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η f s), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (_root_.GD.N0106.N0428.N0765.N1556.d005647 η f s), mul_le_mul_of_nonneg_left h1g hδpos.le]

  set O' : Set (ℝ × ℝ) := Ioo (-f₁) f₁ ×ˢ Ioo (s₁ / 2) (2 * s₂) with hO'
  have hO'open : IsOpen O' := isOpen_Ioo.prod isOpen_Ioo
  have hψeq : ∀ p ∈ O', _root_.GD.N0106.N0428.N0765.N1556.d005649 η p.1 p.2 = _root_.GD.N0106.N0428.N0765.N1556.d005653 (2 * m₁) η (_root_.GD.N0106.N0428.N0765.N1556.d005648 η p.1 p.2) p.2 := by
    intro p hp
    obtain ⟨hpf, hps⟩ := hp
    have hf : |p.1| < f₁ := abs_lt.mpr ⟨hpf.1, hpf.2⟩
    have hu := huOf p.1 p.2 hf hps.1.le hps.2.le
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005649
    apply _root_.GD.N0106.N0428.N0765.N1556.d005664 hη (by linarith [hps.1])
    intro l hl
    exact _root_.GD.N0106.N0428.N0765.N1556.d005675 hη hs₁ hs₁₂ hu hps.1.le hps.2.le hl
  have huOf_cont : ContinuousOn (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1556.d005648 η p.1 p.2, p.2)) O' := by
    apply ContinuousOn.prodMk _ continuousOn_snd
    intro p hp
    obtain ⟨hpf, hps⟩ := hp
    have hf : |p.1| < f₁ := abs_lt.mpr ⟨hpf.1, hpf.2⟩
    have hg := hgg p.1 p.2 hps.1.le hps.2.le
    have hgle : |_root_.GD.N0106.N0428.N0765.N1556.d005647 η p.1 p.2| ≤ δ / 2 := by
      calc |_root_.GD.N0106.N0428.N0765.N1556.d005647 η p.1 p.2| ≤ K * |p.1| := hg
        _ ≤ K * f₁ := by gcongr
        _ = δ / 2 := by rw [hf₁]; field_simp
    have hδ8 : δ / 2 ≤ 1 / 8 := by
      have : δ ≤ 1 / 4 := min_le_left _ _
      linarith
    have h1g : (1 + _root_.GD.N0106.N0428.N0765.N1556.d005647 η p.1 p.2) ≠ 0 := by linarith [(abs_le.mp hgle).1]
    have hes : η + p.2 ≠ 0 := by linarith [hps.1]
    apply ContinuousAt.continuousWithinAt
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005648 _root_.GD.N0106.N0428.N0765.N1556.d005647
    apply ContinuousAt.div
    · apply ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    · apply ContinuousAt.add continuousAt_const
      apply ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    · exact h1g
  have hψcont : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005649 η p.1 p.2) O' := by
    have h := (_root_.GD.N0106.N0428.N0765.N1556.d005663 hη (by positivity : 0 < 2 * m₁)).comp_continuousOn huOf_cont
    refine ContinuousOn.congr h ?_
    intro p hp
    exact hψeq p hp

  have hq : _root_.GD.N0106.N0428.N0765.N1547.d005450 s₂ < _root_.GD.N0106.N0428.N0765.N1547.d005450 s₁ := _root_.GD.N0106.N0428.N0765.N1547.d005472 (by simpa using hs₁)
    (by show (0 : ℝ) < s₂; linarith) hs₁₂
  set c₁ := (2 * _root_.GD.N0106.N0428.N0765.N1547.d005450 s₁ + _root_.GD.N0106.N0428.N0765.N1547.d005450 s₂) / 3 with hc₁
  set c₂ := (_root_.GD.N0106.N0428.N0765.N1547.d005450 s₁ + 2 * _root_.GD.N0106.N0428.N0765.N1547.d005450 s₂) / 3 with hc₂
  have hc₁₂ : c₂ < c₁ := by rw [hc₁, hc₂]; linarith
  have hmem₁ : ((0 : ℝ), s₁) ∈ O' := ⟨⟨by linarith, hf₁pos⟩, ⟨by linarith, by linarith⟩⟩
  have hmem₂ : ((0 : ℝ), s₂) ∈ O' := ⟨⟨by linarith, hf₁pos⟩, ⟨by linarith, by linarith⟩⟩

  have hcont₁ : ContinuousAt (fun f : ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₁) 0 := by
    have h := (hψcont.continuousAt (hO'open.mem_nhds hmem₁))
    have hf : ContinuousAt (fun f : ℝ => (f, s₁)) 0 :=
      (continuous_id.prodMk continuous_const).continuousAt
    have h2 := ContinuousAt.comp (f := fun f : ℝ => (f, s₁)) (x := 0) h hf
    simpa [Function.comp_def] using h2
  have hcont₂ : ContinuousAt (fun f : ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₂) 0 := by
    have h := (hψcont.continuousAt (hO'open.mem_nhds hmem₂))
    have hf : ContinuousAt (fun f : ℝ => (f, s₂)) 0 :=
      (continuous_id.prodMk continuous_const).continuousAt
    have h2 := ContinuousAt.comp (f := fun f : ℝ => (f, s₂)) (x := 0) h hf
    simpa [Function.comp_def] using h2
  have hev₁ : ∀ᶠ f in 𝓝 (0 : ℝ), c₁ < _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₁ := by
    apply ContinuousAt.eventually_lt continuousAt_const hcont₁
    rw [_root_.GD.N0106.N0428.N0765.N1556.d005674 hη hs₁, hc₁]
    linarith
  have hev₂ : ∀ᶠ f in 𝓝 (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₂ < c₂ := by
    apply ContinuousAt.eventually_lt hcont₂ continuousAt_const
    rw [_root_.GD.N0106.N0428.N0765.N1556.d005674 hη (by linarith), hc₂]
    linarith
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.mp hev₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff.mp hev₂
  set f₀ := min f₁ (min ε₁ ε₂) with hf₀
  have hf₀pos : 0 < f₀ := lt_min hf₁pos (lt_min hε₁ hε₂)
  refine ⟨Ioo c₂ c₁ ×ˢ Ioo 0 f₀, isOpen_Ioo.prod isOpen_Ioo, ⟨((c₁ + c₂) / 2, f₀ / 2),
    ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩, ?_⟩
  rintro ⟨h, f⟩ ⟨hh, hf⟩
  have hff₁ : f < f₁ := lt_of_lt_of_le hf.2 (min_le_left _ _)
  have hfε₁ : f < ε₁ := lt_of_lt_of_le hf.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hfε₂ : f < ε₂ := lt_of_lt_of_le hf.2 ((min_le_right _ _).trans (min_le_right _ _))
  have hdist₁ : dist f 0 < ε₁ := by rw [Real.dist_eq, sub_zero, abs_of_pos hf.1]; exact hfε₁
  have hdist₂ : dist f 0 < ε₂ := by rw [Real.dist_eq, sub_zero, abs_of_pos hf.1]; exact hfε₂
  have hup := hb₁ hdist₁
  have hlow := hb₂ hdist₂

  have hcontS : ContinuousOn (fun s : ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s) (Icc s₁ s₂) := by
    intro s hs
    have hmem : (f, s) ∈ O' := ⟨⟨by linarith [hf.1], hff₁⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
    have h := hψcont.continuousAt (hO'open.mem_nhds hmem)
    have hf' : ContinuousAt (fun s : ℝ => (f, s)) s :=
      (continuous_const.prodMk continuous_id).continuousAt
    have h2 := ContinuousAt.comp (f := fun s : ℝ => (f, s)) (x := s) h hf'
    have h3 : ContinuousAt (fun s : ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s) s := by simpa [Function.comp_def] using h2
    exact h3.continuousWithinAt
  have hIVT := intermediate_value_Icc' hs₁₂.le hcontS
  have hhmem : h ∈ Icc (_root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₂) (_root_.GD.N0106.N0428.N0765.N1556.d005649 η f s₁) := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  obtain ⟨s, hs, hψs⟩ := hIVT hhmem
  have hspos : 0 < s := lt_of_lt_of_le hs₁ hs.1
  refine ⟨(_root_.GD.N0106.N0428.N0765.N1556.d005648 η f s, s), ?_, ?_⟩
  · have hu := _root_.GD.N0106.N0428.N0765.N1556.d005671 hη hf.1 hspos
    exact ⟨hu.1, hu.2, hspos⟩
  · unfold _root_.GD.N0106.N0428.N0765.N1556.d005645
    simp only
    rw [_root_.GD.N0106.N0428.N0765.N1556.d005673 hη hf.1.le hspos]
    have hψs' : _root_.GD.N0106.N0428.N0765.N1556.d005649 η f s = h := hψs
    show (_root_.GD.N0106.N0428.N0765.N1556.d005649 η f s, f) = (h, f)
    rw [hψs']



theorem d005677 {A B : ℝ[X]}
    (h : ∀ p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646, A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) = 0) :
    A = 0 ∧ B = 0 := by
  obtain ⟨U, hU, hne, hsub⟩ := _root_.GD.N0106.N0428.N0765.N1556.d005676 hη
  apply _root_.GD.N0106.N0428.N0765.N1614.d005638 hU hne
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hsub hq
  exact h p hp



theorem d005678 : IsOpen _root_.GD.N0106.N0428.N0765.N1556.d005646 := by
  have h1 : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × ℝ | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have h3 : IsOpen {p : ℝ × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have : _root_.GD.N0106.N0428.N0765.N1556.d005646 = {p : ℝ × ℝ | 0 < p.1} ∩ ({p | p.1 < 1} ∩ {p | 0 < p.2}) := by
    ext p
    simp [_root_.GD.N0106.N0428.N0765.N1556.d005646, and_assoc]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem d005679 : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) _root_.GD.N0106.N0428.N0765.N1556.d005646 := by
  intro p₀ hp₀
  obtain ⟨hu₀, hu₁, hs₀⟩ := hp₀
  set m := (1 - p₀.1) / 2 * η * min 1 (p₀.2 / 2) / (η + 2 * p₀.2) with hm
  have hmpos : 0 < m := by
    have h1 : 0 < min 1 (p₀.2 / 2) := lt_min one_pos (by positivity)
    have h2 : 0 < 1 - p₀.1 := by linarith
    rw [hm]
    positivity
  set O : Set (ℝ × ℝ) := Ioo 0 ((1 + p₀.1) / 2) ×ˢ Ioo (p₀.2 / 2) (2 * p₀.2) with hO
  have hOopen : IsOpen O := isOpen_Ioo.prod isOpen_Ioo
  have hp₀O : p₀ ∈ O := ⟨⟨hu₀, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have heq : ∀ p ∈ O, _root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2 = _root_.GD.N0106.N0428.N0765.N1556.d005653 m η p.1 p.2 := by
    intro p hp
    obtain ⟨hpu, hps⟩ := hp
    apply _root_.GD.N0106.N0428.N0765.N1556.d005664 hη (by linarith [hps.1])
    intro l hl
    have hden : _root_.GD.N0106.N0428.N0765.N1556.d005650 η p.2 = η + p.2 := _root_.GD.N0106.N0428.N0765.N1556.d005655 hη (by linarith [hps.1])
    unfold _root_.GD.N0106.N0428.N0765.N1556.d005651
    rw [hden]
    have hl0 := hl.1
    have hl1 := hl.2
    have hspos : 0 < p.2 := by linarith [hps.1]
    have hA : (1 - p.1) * η / (η + p.2) * (1 - l) + η * ((1 - p.1) * p.2 / (η + p.2)) * l
        = (1 - p.1) * η / (η + p.2) * ((1 - l) + p.2 * l) := by ring
    have hmin : min 1 (p₀.2 / 2) ≤ (1 - l) + p.2 * l := by
      have h1 : min 1 (p₀.2 / 2) ≤ 1 := min_le_left _ _
      have h2 : min 1 (p₀.2 / 2) ≤ p.2 := (min_le_right _ _).trans hps.1.le
      nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hl1),
        mul_le_mul_of_nonneg_left h2 hl0]
    have hη' : η / (η + 2 * p₀.2) ≤ η / (η + p.2) :=
      div_le_div_of_nonneg_left hη.le (by linarith) (by linarith [hps.2])
    have hhalf : (1 - p₀.1) / 2 ≤ 1 - p.1 := by linarith [hpu.2]
    have hmn : 0 ≤ min 1 (p₀.2 / 2) := le_min zero_le_one (by positivity)
    have hstep := mul_le_mul (mul_le_mul hhalf hη' (div_nonneg hη.le (by linarith))
      (by linarith [hpu.2])) hmin hmn (mul_nonneg (by linarith [hpu.2]) (div_nonneg hη.le (by linarith)))
    have hB : 0 ≤ (1 + η) * p.1 * l * (1 - l) := by
      have := mul_nonneg hl0 (sub_nonneg.mpr hl1)
      have : 0 ≤ (1 + η) * p.1 := mul_nonneg (by linarith) hpu.1.le
      nlinarith
    calc m = (1 - p₀.1) / 2 * (η / (η + 2 * p₀.2)) * min 1 (p₀.2 / 2) := by rw [hm]; ring
      _ ≤ (1 - p.1) * (η / (η + p.2)) * ((1 - l) + p.2 * l) := hstep
      _ = (1 - p.1) * η / (η + p.2) * (1 - l) + η * ((1 - p.1) * p.2 / (η + p.2)) * l := by
          rw [hA]; ring
      _ ≤ _ := by linarith [hB]
  have hcont : ContinuousAt (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) p₀ := by
    have h := (_root_.GD.N0106.N0428.N0765.N1556.d005663 hη hmpos).continuousAt (x := p₀)
    apply h.congr
    filter_upwards [hOopen.mem_nhds hp₀O] with p hp
    exact (heq p hp).symm
  exact hcont.continuousWithinAt

theorem d005680 : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2) _root_.GD.N0106.N0428.N0765.N1556.d005646 := by
  intro p hp
  obtain ⟨hu₀, hu₁, hs₀⟩ := hp
  apply ContinuousAt.continuousWithinAt
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005644 _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
  have hes' : 0 < η + p.2 := by positivity
  have hes : η + p.2 ≠ 0 := hes'.ne'
  have h1u : 0 < 1 - p.1 := by linarith
  have hden : (1 - p.1) * η / (η + p.2) + η * ((1 - p.1) * p.2 / (η + p.2)) ≠ 0 :=
    (add_pos (div_pos (mul_pos h1u hη) hes') (mul_pos hη (div_pos (mul_pos h1u hs₀) hes'))).ne'
  fun_prop (disch := assumption)




theorem d005681 {μ : Measure (ℝ × ℝ)}
    (hμ : ∀ V : Set (ℝ × ℝ), IsOpen V → (V ∩ _root_.GD.N0106.N0428.N0765.N1556.d005646).Nonempty → 0 < μ V)
    {A B : ℝ[X]}
    (h : ∀ᵐ p ∂μ, p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646 →
      A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) = 0) :
    A = 0 ∧ B = 0 := by
  set g : ℝ × ℝ → ℝ := fun p => A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2)
    with hg
  have hgcont : ContinuousOn g _root_.GD.N0106.N0428.N0765.N1556.d005646 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2)) _root_.GD.N0106.N0428.N0765.N1556.d005646 :=
      A.continuous.comp_continuousOn (_root_.GD.N0106.N0428.N0765.N1556.d005679 hη)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2)) _root_.GD.N0106.N0428.N0765.N1556.d005646 :=
      B.continuous.comp_continuousOn (_root_.GD.N0106.N0428.N0765.N1556.d005679 hη)
    exact (h1.mul (_root_.GD.N0106.N0428.N0765.N1556.d005680 hη)).sub h2
  apply _root_.GD.N0106.N0428.N0765.N1556.d005677 hη
  intro p₀ hp₀
  by_contra hne

  set _root_.GD.N0106.N0428.N0765.N1534.d005331 : Set (ℝ × ℝ) := _root_.GD.N0106.N0428.N0765.N1556.d005646 ∩ g ⁻¹' {y | y ≠ 0} with hV
  have hVopen : IsOpen _root_.GD.N0106.N0428.N0765.N1534.d005331 :=
    hgcont.isOpen_inter_preimage (_root_.GD.N0106.N0428.N0765.N1556.d005678 hη) isOpen_ne
  have hp₀V : p₀ ∈ _root_.GD.N0106.N0428.N0765.N1534.d005331 := ⟨hp₀, hne⟩
  have hpos := hμ _root_.GD.N0106.N0428.N0765.N1534.d005331 hVopen ⟨p₀, hp₀V, hp₀⟩
  have hnull : μ _root_.GD.N0106.N0428.N0765.N1534.d005331 = 0 := by
    have h0 := ae_iff.mp h
    apply measure_mono_null _ h0
    intro p hp
    exact fun himp => hp.2 (himp hp.1)
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

end Main

end
end GD.N0106.N0428.N0765.N1556
