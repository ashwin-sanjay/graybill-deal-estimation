import GD.Module0387
import GD.Module0384
import GD.Module0386
import GD.Module0183
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic



























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1681
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1679 _root_.GD.N0106.N0428.N0765.N1662 _root_.GD.N0106.N0428.N0765.N1674
open _root_.GD.N0232.N0720.N1248
noncomputable section


def d005916 (L t : ℝ) : ℝ := (1 + L * t) ^ (-((21 : ℝ) / 2))

def d005917 (r x : ℝ) : ℝ := (x + _root_.GD.N0106.N0428.N0765.N1679.d005883 r x * _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) / (1 + _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5)

def d005918 (r L x : ℝ) : ℝ := (1 + _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x

def d005919 (r x : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1679.d005880 r x / _root_.GD.N0106.N0428.N0765.N1679.d005884 r

def d005920 (r z : ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1679.d005884 r * (z + z ^ 9) - r * (1 + z ^ 10)) / ((1 - 2 * r) * (1 + z ^ 10))

def d005921 (z : ℝ) : ℝ :=
  1 + z ^ 2 + z ^ 4 + z ^ 6 + 10 * z ^ 8 + z ^ 10 + z ^ 12 + z ^ 14 + z ^ 16

theorem d005922 (z : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1681.d005921 z := by
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005921
  positivity

theorem d005923 {L : ℝ} (hL : 0 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    _root_.GD.N0106.N0428.N0765.N1681.d005916 L t ≤ _root_.GD.N0106.N0428.N0765.N1681.d005916 L s := by
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005916
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
  nlinarith

theorem d005924 {L : ℝ} (hL : 0 ≤ L) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1681.d005916 L) (Ici 0) := by
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005916
  exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (by
    have : (0 : ℝ) ≤ t := ht
    positivity))

section Basic
variable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
include hr0 hr1

theorem d005925 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005882 r x :=
  div_nonneg (_root_.GD.N0106.N0428.N0765.N1679.d005889 hx) (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx).le

theorem d005926 : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1679.d005882 r) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005882
  exact _root_.GD.N0106.N0428.N0765.N1679.d005901.continuousOn.div (_root_.GD.N0106.N0428.N0765.N1679.d005900 r).continuousOn
    (fun x hx => (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx).ne')

theorem d005927 {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x = _root_.GD.N0106.N0428.N0765.N1679.d005887 r 0 x * _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx
  have hT := _root_.GD.N0106.N0428.N0765.N1681.d005925 hr0 hr1 hx
  have e : _root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x = _root_.GD.N0106.N0428.N0765.N1679.d005880 r x * (1 + L * _root_.GD.N0106.N0428.N0765.N1679.d005882 r x) := by
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005882
    field_simp
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005887 _root_.GD.N0106.N0428.N0765.N1681.d005916
  rw [e, Real.mul_rpow hc.le (by positivity), zero_mul, add_zero]
  ring


theorem d005928 : (1 - 2 * r) * _root_.GD.N0106.N0428.N0765.N1679.d005885 r ^ 2 + 2 * r * _root_.GD.N0106.N0428.N0765.N1679.d005885 r - r = 0 := by
  have h := _root_.GD.N0106.N0428.N0765.N1679.d005905 hr0 hr1
  have hs := (_root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1).ne'
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883 at h
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005904 hr0 hr1, div_eq_iff hs] at h
  have hc := _root_.GD.N0106.N0428.N0765.N1679.d005904 hr0 hr1
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880 at hc
  rw [← hc] at h
  linear_combination -h

theorem d005929 : MonotoneOn (_root_.GD.N0106.N0428.N0765.N1679.d005882 r) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  intro x hx y hy hxy
  have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hstar.2.le⟩
  have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hstar.2.le⟩
  have hcx := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx1
  have hcy := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hy1
  have hcs := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 (Ioo_subset_Icc_self hstar)
  have hq := _root_.GD.N0106.N0428.N0765.N1681.d005928 hr0 hr1
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005882
  rw [div_le_div_iff₀ hcx hcy]
  have key : _root_.GD.N0106.N0428.N0765.N1679.d005881 y * _root_.GD.N0106.N0428.N0765.N1679.d005880 r x - _root_.GD.N0106.N0428.N0765.N1679.d005881 x * _root_.GD.N0106.N0428.N0765.N1679.d005880 r y
      = (y - x) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) * (_root_.GD.N0106.N0428.N0765.N1679.d005885 r - x) + _root_.GD.N0106.N0428.N0765.N1679.d005880 r x * (_root_.GD.N0106.N0428.N0765.N1679.d005885 r - y)
          - ((1 - 2 * r) * _root_.GD.N0106.N0428.N0765.N1679.d005885 r ^ 2 + 2 * r * _root_.GD.N0106.N0428.N0765.N1679.d005885 r - r)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005881 _root_.GD.N0106.N0428.N0765.N1679.d005880
    ring
  rw [hq, sub_zero] at key
  have h1 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005880 r (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) * (_root_.GD.N0106.N0428.N0765.N1679.d005885 r - x) := mul_nonneg hcs.le (by linarith [hx.2])
  have h2 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005880 r x * (_root_.GD.N0106.N0428.N0765.N1679.d005885 r - y) := mul_nonneg hcx.le (by linarith [hy.2])
  nlinarith [key, mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg h1 h2)]

theorem d005930 {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x :=
  mul_nonneg (by have := _root_.GD.N0106.N0428.N0765.N1679.d005906 hr0 hr1 hx; positivity) (_root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 hL hx)

theorem d005931 {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x :=
  mul_pos (by have := _root_.GD.N0106.N0428.N0765.N1679.d005906 hr0 hr1 (Ioo_subset_Icc_self hx); positivity)
    (_root_.GD.N0106.N0428.N0765.N1679.d005909 hr0 hr1 hL hx)

theorem d005932 : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1679.d005886 r) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005886
  exact ((_root_.GD.N0106.N0428.N0765.N1679.d005900 r).pow 2).continuousOn.div continuousOn_const
    (fun x _ => (_root_.GD.N0106.N0428.N0765.N1679.d005891 hr0 hr1).ne')

theorem d005933 {L : ℝ} (hL : 0 ≤ L) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1681.d005918 r L) (Icc 0 1) :=
  (continuousOn_const.add ((_root_.GD.N0106.N0428.N0765.N1681.d005932 hr0 hr1).pow 5)).mul (_root_.GD.N0106.N0428.N0765.N1679.d005910 hr0 hr1 hL)

theorem d005934 : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1681.d005917 r) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005917
  apply ContinuousOn.div
  · exact continuousOn_id.add ((_root_.GD.N0106.N0428.N0765.N1679.d005902 hr0 hr1).mul ((_root_.GD.N0106.N0428.N0765.N1681.d005932 hr0 hr1).pow 5))
  · exact continuousOn_const.add ((_root_.GD.N0106.N0428.N0765.N1681.d005932 hr0 hr1).pow 5)
  · intro x hx
    have := _root_.GD.N0106.N0428.N0765.N1679.d005906 hr0 hr1 hx
    positivity

theorem d005935 {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x = _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x * _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) := by
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005918
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005927 hr0 hr1 hL hx]
  ring

theorem d005936 {L : ℝ} (hL : 0 ≤ L) : 0 < ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  apply intervalIntegral_pos_of_pos_on
  · exact ((_root_.GD.N0106.N0428.N0765.N1681.d005933 hr0 hr1 hL).mono (Icc_subset_Icc le_rfl hstar.2.le)).intervalIntegrable_of_Icc
      hstar.1.le
  · intro x hx
    exact _root_.GD.N0106.N0428.N0765.N1681.d005931 hr0 hr1 hL ⟨hx.1, hx.2.trans hstar.2⟩
  · exact hstar.1


theorem d005937 {L : ℝ} (hL : 0 ≤ L) :
    _root_.GD.N0106.N0428.N0765.N1679.d005888 r L = (∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x) / ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x := by
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005914 hr0 hr1 hL]
  congr 1
  apply integral_congr
  intro x hx
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  rw [uIcc_of_le hstar.1.le] at hx
  have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hstar.2.le⟩
  have hz := _root_.GD.N0106.N0428.N0765.N1679.d005906 hr0 hr1 hx1
  show (x + _root_.GD.N0106.N0428.N0765.N1679.d005883 r x * _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x = _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005917 _root_.GD.N0106.N0428.N0765.N1681.d005918
  field_simp

end Basic

section Zform
variable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
include hr0 hr1

theorem d005938 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1679.d005883 r x = (_root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x - r) / (1 - 2 * r) ∨ r = 1 / 2 := by
  by_cases hne : r = 1 / 2
  · exact Or.inr hne
  · left
    have hc := (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx).ne'
    have h12 : (1 - 2 * r) ≠ 0 := by
      intro h; apply hne; linarith
    rw [_root_.GD.N0106.N0428.N0765.N1679.d005893 hr0 hr1]
    have h := _root_.GD.N0106.N0428.N0765.N1679.d005894 (r := r) hc
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880 at h ⊢
    rw [eq_div_iff h12]
    linarith [h]

theorem d005939 (hne : r ≠ 1 / 2) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1681.d005917 r x = _root_.GD.N0106.N0428.N0765.N1681.d005920 r (_root_.GD.N0106.N0428.N0765.N1681.d005919 r x) := by
  have hc := (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx).ne'
  have hs := (_root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1).ne'
  have h12 : (1 - 2 * r) ≠ 0 := by
    intro h; apply hne; linarith
  rcases _root_.GD.N0106.N0428.N0765.N1681.d005938 hr0 hr1 hx with hrefl | h
  · have hz : _root_.GD.N0106.N0428.N0765.N1679.d005886 r x = _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2 := by
      unfold _root_.GD.N0106.N0428.N0765.N1679.d005886
      rw [_root_.GD.N0106.N0428.N0765.N1679.d005893 hr0 hr1]
    have hxeq : x = (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x - r) / (1 - 2 * r) := by
      rw [eq_div_iff h12]
      unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
      ring
    have key : ∀ c : ℝ, c ≠ 0 →
        ((c - r) / (1 - 2 * r) + ((_root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2 / c - r) / (1 - 2 * r)) * (c ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2) ^ 5) /
          (1 + (c ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2) ^ 5) = _root_.GD.N0106.N0428.N0765.N1681.d005920 r (c / _root_.GD.N0106.N0428.N0765.N1679.d005884 r) := by
      intro c hc
      unfold _root_.GD.N0106.N0428.N0765.N1681.d005920
      field_simp
      ring
    calc _root_.GD.N0106.N0428.N0765.N1681.d005917 r x = ((_root_.GD.N0106.N0428.N0765.N1679.d005880 r x - r) / (1 - 2 * r)
          + ((_root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x - r) / (1 - 2 * r)) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2) ^ 5) /
          (1 + (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 / _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2) ^ 5) := by
          unfold _root_.GD.N0106.N0428.N0765.N1681.d005917
          rw [hrefl, hz, ← hxeq]
      _ = _root_.GD.N0106.N0428.N0765.N1681.d005920 r (_root_.GD.N0106.N0428.N0765.N1681.d005919 r x) := by
          unfold _root_.GD.N0106.N0428.N0765.N1681.d005919
          exact key _ hc
  · exact absurd h hne

theorem d005940 (hne : r ≠ 1 / 2) (z : ℝ) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1681.d005920 r) (_root_.GD.N0106.N0428.N0765.N1679.d005884 r * (1 - z ^ 2) * _root_.GD.N0106.N0428.N0765.N1681.d005921 z / ((1 - 2 * r) * (1 + z ^ 10) ^ 2)) z := by
  have h12 : (1 - 2 * r) ≠ 0 := by
    intro h; apply hne; linarith
  have hd : (1 - 2 * r) * (1 + z ^ 10) ≠ 0 := mul_ne_zero h12 (by positivity)
  have h9 : HasDerivAt (fun z : ℝ => z ^ 9) (9 * z ^ 8) z := by
    simpa using hasDerivAt_pow 9 z
  have h10 : HasDerivAt (fun z : ℝ => z ^ 10) (10 * z ^ 9) z := by
    simpa using hasDerivAt_pow 10 z
  have hN : HasDerivAt (fun z : ℝ => _root_.GD.N0106.N0428.N0765.N1679.d005884 r * (z + z ^ 9) - r * (1 + z ^ 10))
      (_root_.GD.N0106.N0428.N0765.N1679.d005884 r * (1 + 9 * z ^ 8) - r * (0 + 10 * z ^ 9)) z :=
    (((hasDerivAt_id z).add h9).const_mul (_root_.GD.N0106.N0428.N0765.N1679.d005884 r)).sub (((hasDerivAt_const z (1 : ℝ)).add h10).const_mul r)
  have hD : HasDerivAt (fun z : ℝ => (1 - 2 * r) * (1 + z ^ 10)) ((1 - 2 * r) * (0 + 10 * z ^ 9)) z :=
    ((hasDerivAt_const z (1 : ℝ)).add h10).const_mul (1 - 2 * r)
  refine (hN.div hD hd).congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005921
  field_simp
  ring

theorem d005941 (hr : r < 1 / 2) {x : ℝ} (hx : x ∈ Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) :
    _root_.GD.N0106.N0428.N0765.N1681.d005919 r x ∈ Icc (r / _root_.GD.N0106.N0428.N0765.N1679.d005884 r) 1 := by
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  have hcs := _root_.GD.N0106.N0428.N0765.N1679.d005904 hr0 hr1
  have h12 : 0 ≤ 1 - 2 * r := by linarith
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005919
  constructor
  · rw [div_le_div_iff_of_pos_right hs]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
    nlinarith [mul_nonneg h12 hx.1]
  · rw [div_le_one hs, ← hcs]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
    nlinarith [mul_le_mul_of_nonneg_left hx.2 h12]

theorem d005942 (hr : 1 / 2 < r) {x : ℝ} (hx : x ∈ Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) :
    _root_.GD.N0106.N0428.N0765.N1681.d005919 r x ∈ Icc 1 (r / _root_.GD.N0106.N0428.N0765.N1679.d005884 r) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  have hcs := _root_.GD.N0106.N0428.N0765.N1679.d005904 hr0 hr1
  have h21 : 0 ≤ 2 * r - 1 := by linarith
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005919
  constructor
  · rw [le_div_iff₀ hs, one_mul, ← hcs]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
    nlinarith [mul_nonneg h21 (sub_nonneg.mpr hx.2)]
  · rw [div_le_div_iff_of_pos_right hs]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
    nlinarith [mul_nonneg h21 hx.1]

theorem d005943 (hr : r < 1 / 2) : MonotoneOn (_root_.GD.N0106.N0428.N0765.N1681.d005920 r) (Icc (r / _root_.GD.N0106.N0428.N0765.N1679.d005884 r) 1) := by
  have hne : r ≠ 1 / 2 := hr.ne
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun z _ => (_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).continuousAt.continuousWithinAt
  · exact fun z _ => (_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    rw [(_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).deriv]
    have hz0 : 0 < z := lt_trans (by positivity) hz.1
    have h1 : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.2, hz0]
    have h12 : 0 < 1 - 2 * r := by linarith
    have := _root_.GD.N0106.N0428.N0765.N1681.d005922 z
    positivity

theorem d005944 (hr : 1 / 2 < r) : MonotoneOn (_root_.GD.N0106.N0428.N0765.N1681.d005920 r) (Icc 1 (r / _root_.GD.N0106.N0428.N0765.N1679.d005884 r)) := by
  have hne : r ≠ 1 / 2 := hr.ne'
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun z _ => (_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).continuousAt.continuousWithinAt
  · exact fun z _ => (_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    rw [(_root_.GD.N0106.N0428.N0765.N1681.d005940 hr0 hr1 hne z).deriv]
    have h1 : 1 - z ^ 2 ≤ 0 := by nlinarith [hz.1]
    have h12 : 1 - 2 * r < 0 := by linarith
    have hP := _root_.GD.N0106.N0428.N0765.N1681.d005922 z
    have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
    have hnum : _root_.GD.N0106.N0428.N0765.N1679.d005884 r * (1 - z ^ 2) * _root_.GD.N0106.N0428.N0765.N1681.d005921 z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs.le h1) hP.le
    have hden : (1 - 2 * r) * (1 + z ^ 10) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos h12 (by positivity)
    exact div_nonneg_of_nonpos hnum hden.le

theorem d005945 (hr : r < 1 / 2) : MonotoneOn (_root_.GD.N0106.N0428.N0765.N1679.d005880 r) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := by
  intro x _ y _ hxy
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  nlinarith

theorem d005946 (hr : 1 / 2 < r) : AntitoneOn (_root_.GD.N0106.N0428.N0765.N1679.d005880 r) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := by
  intro x _ y _ hxy
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  nlinarith

theorem d005947 (hr : r < 1 / 2) : MonotoneOn (_root_.GD.N0106.N0428.N0765.N1681.d005917 r) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  intro x hx y hy hxy
  have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hstar.2.le⟩
  have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hstar.2.le⟩
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005939 hr0 hr1 hr.ne hx1, _root_.GD.N0106.N0428.N0765.N1681.d005939 hr0 hr1 hr.ne hy1]
  apply _root_.GD.N0106.N0428.N0765.N1681.d005943 hr0 hr1 hr (_root_.GD.N0106.N0428.N0765.N1681.d005941 hr0 hr1 hr hx) (_root_.GD.N0106.N0428.N0765.N1681.d005941 hr0 hr1 hr hy)
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005919
  exact div_le_div_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1681.d005945 hr0 hr1 hr hx hy hxy) hs.le

theorem d005948 (hr : 1 / 2 < r) : AntitoneOn (_root_.GD.N0106.N0428.N0765.N1681.d005917 r) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  intro x hx y hy hxy
  have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hstar.2.le⟩
  have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hstar.2.le⟩
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005939 hr0 hr1 hr.ne' hx1, _root_.GD.N0106.N0428.N0765.N1681.d005939 hr0 hr1 hr.ne' hy1]
  apply _root_.GD.N0106.N0428.N0765.N1681.d005944 hr0 hr1 hr (_root_.GD.N0106.N0428.N0765.N1681.d005942 hr0 hr1 hr hy) (_root_.GD.N0106.N0428.N0765.N1681.d005942 hr0 hr1 hr hx)
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005919
  exact div_le_div_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1681.d005946 hr0 hr1 hr hx hy hxy) hs.le

theorem d005949 (hr : r = 1 / 2) (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1681.d005917 r x = 1 / 2 := by
  subst hr
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005917 _root_.GD.N0106.N0428.N0765.N1679.d005883 _root_.GD.N0106.N0428.N0765.N1679.d005886 _root_.GD.N0106.N0428.N0765.N1679.d005880
  norm_num

theorem d005950 : _root_.GD.N0106.N0428.N0765.N1681.d005917 r 0 = r ^ 5 / (r ^ 5 + (1 - r) ^ 5) := by
  have h1 : (1 - r) ≠ 0 := by linarith
  have hz : _root_.GD.N0106.N0428.N0765.N1679.d005886 r 0 = r / (1 - r) := by
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005886 _root_.GD.N0106.N0428.N0765.N1679.d005880
    field_simp
    ring
  have h5 : (1 - r) ^ 5 ≠ 0 := pow_ne_zero 5 h1
  unfold _root_.GD.N0106.N0428.N0765.N1681.d005917
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005897 hr0, hz, div_pow, one_mul, zero_add]
  have e : 1 + r ^ 5 / (1 - r) ^ 5 = (r ^ 5 + (1 - r) ^ 5) / (1 - r) ^ 5 := by
    rw [eq_div_iff h5, add_mul, one_mul, div_mul_cancel₀ _ h5]
    ring
  rw [e, div_div_div_cancel_right₀ h5]

end Zform

section Kernel
variable {r : ℝ}

theorem d005951 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1674.d005875 r x = _root_.GD.N0106.N0428.N0765.N1679.d005887 r 0 x := by
  simp only [_root_.GD.N0106.N0428.N0765.N1674.d005875, _root_.GD.N0106.N0428.N0765.N1679.d005887, _root_.GD.N0106.N0428.N0765.N1679.d005881, _root_.GD.N0106.N0428.N0765.N1679.d005880, zero_mul, add_zero]

theorem d005952 (φ : ℝ → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1674.d005876 r φ = (∫ x in (0 : ℝ)..1, φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r 0 x) / ∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1679.d005887 r 0 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1674.d005876
  simp_rw [_root_.GD.N0106.N0428.N0765.N1681.d005951]

theorem d005953 : _root_.GD.N0106.N0428.N0765.N1679.d005888 r 0 = _root_.GD.N0106.N0428.N0765.N1674.d005876 r (fun x => x) := by
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005952]
  rfl

end Kernel

section Premises
variable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
include hr0 hr1

theorem d005954 {L : ℝ} (hL : 0 ≤ L) : _root_.GD.N0106.N0428.N0765.N1679.d005888 r L ≤ 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005888
  have hk := (_root_.GD.N0106.N0428.N0765.N1679.d005910 hr0 hr1 hL).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hD : 0 < ∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x :=
    intervalIntegral_pos_of_pos_on hk (fun x hx => _root_.GD.N0106.N0428.N0765.N1679.d005909 hr0 hr1 hL hx) zero_lt_one
  rw [div_le_one hD]
  have hk1 : IntervalIntegrable (fun x => x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) volume 0 1 :=
    (continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1679.d005910 hr0 hr1 hL)).intervalIntegrable_of_Icc zero_le_one
  apply integral_mono_on zero_le_one hk1 hk
  intro x hx
  have := _root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 hL hx
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) this]

theorem d005955 {L : ℝ} (hL : 0 ≤ L) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005888 r L := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005888
  apply div_nonneg
  · exact integral_nonneg zero_le_one (fun x hx => mul_nonneg hx.1 (_root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 hL hx))
  · exact integral_nonneg zero_le_one (fun x hx => _root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 hL hx)

theorem d005956 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1674.d005876 r (fun x => x ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005952]
  apply div_nonneg
  · exact integral_nonneg zero_le_one
      (fun x hx => mul_nonneg (sq_nonneg _) (_root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 le_rfl hx))
  · exact integral_nonneg zero_le_one (fun x hx => _root_.GD.N0106.N0428.N0765.N1679.d005908 hr0 hr1 le_rfl hx)

theorem d005957 (hr : r = 1 / 2) {L : ℝ} (hL : 0 ≤ L) : _root_.GD.N0106.N0428.N0765.N1679.d005888 r L = 1 / 2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005937 hr0 hr1 hL]
  have hW := (_root_.GD.N0106.N0428.N0765.N1681.d005936 hr0 hr1 hL).ne'
  have h : (∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x) = 1 / 2 * ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [_root_.GD.N0106.N0428.N0765.N1681.d005949 hr0 hr1 hr]
  rw [h, mul_div_assoc, div_self hW, mul_one]


theorem d005958 (hr : r ≤ 1 / 2) {L : ℝ} (hL : 0 ≤ L) : _root_.GD.N0106.N0428.N0765.N1679.d005888 r L ≤ _root_.GD.N0106.N0428.N0765.N1679.d005888 r 0 := by
  rcases eq_or_lt_of_le hr with heq | hlt
  · rw [_root_.GD.N0106.N0428.N0765.N1681.d005957 hr0 hr1 heq hL, _root_.GD.N0106.N0428.N0765.N1681.d005957 hr0 hr1 heq le_rfl]
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005937 hr0 hr1 hL, _root_.GD.N0106.N0428.N0765.N1681.d005937 hr0 hr1 le_rfl]
  have hW0 := _root_.GD.N0106.N0428.N0765.N1681.d005936 hr0 hr1 (L := 0) le_rfl
  have hWL := _root_.GD.N0106.N0428.N0765.N1681.d005936 hr0 hr1 hL
  have hsub : Icc (0 : ℝ) (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hstar.2.le

  have hfac : ∀ x ∈ uIcc (0 : ℝ) (_root_.GD.N0106.N0428.N0765.N1679.d005885 r), _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x = _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x * _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) := by
    intro x hx
    rw [uIcc_of_le hstar.1.le] at hx
    exact _root_.GD.N0106.N0428.N0765.N1681.d005935 hr0 hr1 hL (hsub hx)
  have e1 : (∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x)
      = ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) * _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x := by
    apply integral_congr
    intro x hx
    show _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x = _root_.GD.N0106.N0428.N0765.N1681.d005917 r x * _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) * _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x
    rw [hfac x hx]
    ring
  have e2 : (∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x)
      = ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) * _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x := by
    apply integral_congr
    intro x hx
    show _root_.GD.N0106.N0428.N0765.N1681.d005918 r L x = _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x) * _root_.GD.N0106.N0428.N0765.N1681.d005918 r 0 x
    rw [hfac x hx]
    ring
  rw [e2] at hWL
  rw [e1, e2, div_le_div_iff₀ hWL hW0]
  have hg : ContinuousOn (fun x => _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x)) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) :=
    (_root_.GD.N0106.N0428.N0765.N1681.d005924 hL).comp ((_root_.GD.N0106.N0428.N0765.N1681.d005926 hr0 hr1).mono hsub)
      (fun x hx => _root_.GD.N0106.N0428.N0765.N1681.d005925 hr0 hr1 (hsub hx))
  have hga : AntitoneOn (fun x => _root_.GD.N0106.N0428.N0765.N1681.d005916 L (_root_.GD.N0106.N0428.N0765.N1679.d005882 r x)) (Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r)) := fun x hx y hy hxy =>
    _root_.GD.N0106.N0428.N0765.N1681.d005923 hL (_root_.GD.N0106.N0428.N0765.N1681.d005925 hr0 hr1 (hsub hx)) (_root_.GD.N0106.N0428.N0765.N1681.d005929 hr0 hr1 hx hy hxy)
  have h := _root_.GD.N0106.N0428.N0765.N1662.d005829 hstar.1 ((_root_.GD.N0106.N0428.N0765.N1681.d005933 hr0 hr1 le_rfl).mono hsub)
    (fun x hx => _root_.GD.N0106.N0428.N0765.N1681.d005930 hr0 hr1 le_rfl (hsub hx)) hW0 ((_root_.GD.N0106.N0428.N0765.N1681.d005934 hr0 hr1).mono hsub) hg
    (_root_.GD.N0106.N0428.N0765.N1681.d005947 hr0 hr1 hlt) hga
  linarith [h]


theorem d005959 (hr : 1 / 2 ≤ r) {L : ℝ} (hL : 0 ≤ L) :
    _root_.GD.N0106.N0428.N0765.N1679.d005888 r L ≤ r ^ 5 / (r ^ 5 + (1 - r) ^ 5) := by
  rcases eq_or_lt_of_le hr with heq | hlt
  · rw [_root_.GD.N0106.N0428.N0765.N1681.d005957 hr0 hr1 heq.symm hL, ← heq]
    norm_num
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  rw [_root_.GD.N0106.N0428.N0765.N1681.d005937 hr0 hr1 hL, ← _root_.GD.N0106.N0428.N0765.N1681.d005950 hr0 hr1]
  have hWL := _root_.GD.N0106.N0428.N0765.N1681.d005936 hr0 hr1 hL
  rw [div_le_iff₀ hWL, ← intervalIntegral.integral_const_mul]
  have hsub : Icc (0 : ℝ) (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hstar.2.le
  apply integral_mono_on hstar.1.le
  · exact (((_root_.GD.N0106.N0428.N0765.N1681.d005934 hr0 hr1).mono hsub).mul ((_root_.GD.N0106.N0428.N0765.N1681.d005933 hr0 hr1 hL).mono hsub)).intervalIntegrable_of_Icc
      hstar.1.le
  · exact (((_root_.GD.N0106.N0428.N0765.N1681.d005933 hr0 hr1 hL).mono hsub).const_mul _).intervalIntegrable_of_Icc hstar.1.le
  intro x hx
  have h0 : (0 : ℝ) ∈ Icc 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) := ⟨le_rfl, hstar.1.le⟩
  exact mul_le_mul_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1681.d005948 hr0 hr1 hlt h0 hx hx.1)
    (_root_.GD.N0106.N0428.N0765.N1681.d005930 hr0 hr1 hL (hsub hx))


theorem d005960 {L : ℝ} (hL : 0 ≤ L) : _root_.GD.N0106.N0428.N0765.N1679.d005888 r L ≤ (3 / 2 : ℝ) * r := by
  have hm := _root_.GD.N0106.N0428.N0765.N1674.d005879 hr0 hr1
  rw [← _root_.GD.N0106.N0428.N0765.N1681.d005953] at hm
  exact _root_.GD.N0232.N0720.N1248.d002189 hr0 (_root_.GD.N0106.N0428.N0765.N1681.d005954 hr0 hr1 hL)
    (_root_.GD.N0106.N0428.N0765.N1681.d005955 hr0 hr1 le_rfl) (_root_.GD.N0106.N0428.N0765.N1681.d005956 hr0 hr1) hm
    (fun hr => _root_.GD.N0106.N0428.N0765.N1681.d005958 hr0 hr1 hr hL) (fun hr => _root_.GD.N0106.N0428.N0765.N1681.d005959 hr0 hr1 hr hL)

end Premises

section Printed


theorem d005961 {η u v w : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) : _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w ≤ (3 / 2 : ℝ) * (v / (v + η * w)) := by
  have hS : 0 < v + η * w := by positivity
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005915 hη hu hv hw]
  exact _root_.GD.N0106.N0428.N0765.N1681.d005960 (div_pos hv hS) (by rw [div_lt_one hS]; nlinarith [mul_pos hη hw])
    (by positivity)


theorem d005962 {η u v w : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    η * _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w ≤ (3 / 2 : ℝ) * (v / (η⁻¹ * v + w)) := by
  have h := _root_.GD.N0232.N0720.N1248.d002190 hη.le (_root_.GD.N0106.N0428.N0765.N1681.d005961 hη hu hv hw)
  have e : η * (v / (v + η * w)) = v / (η⁻¹ * v + w) := by
    field_simp
  rw [e] at h
  exact h

end Printed

end
end GD.N0106.N0428.N0765.N1681
