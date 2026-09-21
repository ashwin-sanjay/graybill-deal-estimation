import GD.Module1522

















noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Finset
open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1509

open _root_.GD.N0106.N0428.N0765.N1634 _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1569
  _root_.GD.N0106.N0428.N0765.N1562 _root_.GD.N0106.N0428.N0765.N1619

theorem d023668 : _root_.GD.N0106.N0428.N0765.N1634.d023650 0 = (1 / 4 : ℝ) := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1634.d023650, _root_.GD.N0106.N0428.N0765.N1634.d023649, _root_.GD.N0106.N0428.N0765.N1634.d023648]


theorem d023669 (eta u v w : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 = v / 2 + eta * w / 2 + (1 + eta) * u / 4 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1634.d023651, _root_.GD.N0106.N0428.N0765.N1634.d023648, _root_.GD.N0106.N0428.N0765.N1634.d023649, _root_.GD.N0106.N0428.N0765.N1634.d023650] <;> ring



theorem d023670 (eta u v w : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w 0 =
      1 / (2048 * _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ^ 10 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0)) := by
  have hroot : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023652, _root_.GD.N0106.N0428.N0765.N1509.d023668, hroot]
  simp only [one_div, mul_inv_rev]
  ring



theorem d023671 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (B : ℚ) (hB : 1 ≤ B) (hPB : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ≤ (B : ℝ)) :
    (1 : ℝ) / (2048 * (B : ℝ) ^ 11) ≤ _root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w 0 := by
  have hp := _root_.GD.N0106.N0428.N0765.N1634.d023659 heta hu hv hw (0 : ℝ)
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hB0 : 0 ≤ (B : ℝ) := by linarith
  have hBsq : (B : ℝ) ≤ (B : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hBR)]
  have hroot : Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0) ≤ (B : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hB0, hPB.trans hBsq⟩
  have hpow : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ^ 10 ≤ (B : ℝ) ^ 10 :=
    pow_le_pow_left₀ hp.le hPB 10
  have hprod : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ^ 10 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0) ≤
      (B : ℝ) ^ 10 * (B : ℝ) :=
    mul_le_mul hpow hroot (Real.sqrt_nonneg _) (pow_nonneg hB0 _)
  have hden : 0 < 2048 * _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ^ 10 *
      Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0) := by
    exact mul_pos (mul_pos (by norm_num) (pow_pos hp _)) (Real.sqrt_pos.2 hp)
  rw [_root_.GD.N0106.N0428.N0765.N1509.d023670]
  apply one_div_le_one_div_of_le hden
  nlinarith [mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2048 by norm_num)]


def d023672 (h B : ℚ) : ℚ := h / (2048 * B ^ 11)

theorem d023673 (h B : ℚ) (hh : 0 < h) (hB : 1 ≤ B) :
    0 < _root_.GD.N0106.N0428.N0765.N1509.d023672 h B := by
  unfold _root_.GD.N0106.N0428.N0765.N1509.d023672
  apply div_pos hh
  exact mul_pos (by norm_num) (pow_pos (by linarith) _)



theorem d023674 {eta u v w c₀ : ℝ} {N j : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (h B : ℚ) (hh : 0 < h) (hB : 1 ≤ B)
    (hPB : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ≤ (B : ℝ))
    (hj : j < N) (hcenter : c₀ + (j : ℝ) * (h : ℝ) = 0) :
    (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B : ℝ) ≤
      ∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * (h : ℝ)) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hterm : (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B : ℝ) ≤ (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w 0 := by
    rw [← _root_.GD.N0106.N0428.N0765.N1634.d023662 heta hu hv hw]
    have hl := mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1509.d023671 heta hu hv hw B hB hPB) hhR.le
    simpa only [_root_.GD.N0106.N0428.N0765.N1509.d023672, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, mul_one_div] using hl
  calc
    (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B : ℝ) ≤ (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w 0 := hterm
    _ = (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (j : ℝ) * (h : ℝ)) := by rw [hcenter]
    _ ≤ ∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w
        (c₀ + (i : ℝ) * (h : ℝ)) := by
      exact Finset.single_le_sum (s := range N)
        (f := fun i : ℕ => (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w
          (c₀ + (i : ℝ) * (h : ℝ)))
        (fun i _ => mul_nonneg hhR.le (_root_.GD.N0106.N0428.N0765.N1569.d021038 heta hu hv hw _))
        (Finset.mem_range.mpr hj)


def d023675 (h B : ℚ) (S : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨max (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B) S.lo, S.hi⟩


def d023676 (S : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨max 0 S.lo, S.hi⟩

theorem d023677 {eta u v w c₀ : ℝ} {N j : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (h B : ℚ) (hh : 0 < h) (hB : 1 ≤ B)
    (hPB : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w 0 ≤ (B : ℝ))
    (hj : j < N) (hcenter : c₀ + (j : ℝ) * (h : ℝ) = 0)
    (S : _root_.GD.N0232.N0720.N1164.d006809) (hS : S.d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * (h : ℝ)))) :
    (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S).d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) := by
  refine ⟨?_, hS.2⟩
  change ((max (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B) S.lo : ℚ) : ℝ) ≤ _
  rw [Rat.cast_max]
  exact max_le (_root_.GD.N0106.N0428.N0765.N1509.d023674 heta hu hv hw h B hh hB hPB hj hcenter) hS.1

theorem d023678 (h B : ℚ) (S : _root_.GD.N0232.N0720.N1164.d006809)
    (hh : 0 < h) (hB : 1 ≤ B) : 0 < (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S).lo :=
  lt_of_lt_of_le (_root_.GD.N0106.N0428.N0765.N1509.d023673 h B hh hB) (le_max_left _ _)

theorem d023679 {eta u v w c₀ : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (h : ℚ) (hh : 0 < h) (S : _root_.GD.N0232.N0720.N1164.d006809) (hS : S.d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * (h : ℝ)))) :
    (_root_.GD.N0106.N0428.N0765.N1509.d023676 S).d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) := by
  refine ⟨?_, hS.2⟩
  change ((max 0 S.lo : ℚ) : ℝ) ≤ _
  rw [Rat.cast_max, Rat.cast_zero]
  apply max_le _ hS.1
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast hh.le) (_root_.GD.N0106.N0428.N0765.N1569.d021039 heta hu hv hw _)

theorem d023680 (S : _root_.GD.N0232.N0720.N1164.d006809) :
    0 ≤ (_root_.GD.N0106.N0428.N0765.N1509.d023676 S).lo := le_max_left _ _



theorem d023681
    (h B : ℚ) (S : _root_.GD.N0232.N0720.N1164.d006809) (hh : 0 < h) (hB : 1 ≤ B)
    {d : ℝ} (hd : 0 < d) (hdpi : d < Real.pi / 2) :
    0 < ((_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S).lo : ℝ) /
      (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ)) := by
  apply div_pos
  · exact_mod_cast _root_.GD.N0106.N0428.N0765.N1509.d023678 h B S hh hB
  · have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    linarith [_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hhR]


theorem d023682 (h B : ℚ) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) :
    (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀).hi = S₀.hi ∧ (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁).hi = S₁.hi :=
  ⟨rfl, rfl⟩




theorem d023683
    {eta a b c₀ d : ℝ} {N j : ℕ}
    (heta : 0 < eta) (hd : 0 < d) (hdpi : d < Real.pi / 2)
    (h B : ℚ) (hh : 0 < h) (hB : 1 ≤ B)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ) < 1)
    (hPB : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 0 ≤ (B : ℝ))
    (hj : j < N) (hcenter : c₀ + (j : ℝ) * (h : ℝ) = 0)
    (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809)
    (hS₀ : S₀.d006810 (∑ i ∈ range N,
      (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * (h : ℝ))))
    (hS₁ : S₁.d006810 (∑ i ∈ range N,
      (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * (h : ℝ)))) :
    let D := _root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀
    let A := _root_.GD.N0106.N0428.N0765.N1509.d023676 S₁
    max ((A.lo : ℝ) / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ)) /
      (((D.hi : ℝ) + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta (Real.exp b) 1 c₀ (h : ℝ) N) /
        (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ)))) 0 ≤
      _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ∧
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ≤
      min ((((A.hi : ℝ) + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta (Real.exp b) 1 c₀ (h : ℝ) N) /
        (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ))) /
        ((D.lo : ℝ) / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ)))) 1 := by
  apply _root_.GD.N0106.N0428.N0765.N1634.d023667 heta hd hdpi
    (by exact_mod_cast hh) hε (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁)
  · exact _root_.GD.N0106.N0428.N0765.N1509.d023677 heta (by positivity) (Real.exp_pos b) one_pos
      h B hh hB hPB hj hcenter S₀ hS₀
  · exact _root_.GD.N0106.N0428.N0765.N1509.d023679 heta (by positivity) (Real.exp_pos b) one_pos
      h hh S₁ hS₁
  · exact _root_.GD.N0106.N0428.N0765.N1509.d023678 h B S₀ hh hB
  · exact _root_.GD.N0106.N0428.N0765.N1509.d023680 S₁

end GD.N0106.N0428.N0765.N1509

#print axioms _root_.GD.N0106.N0428.N0765.N1509.d023670
#print axioms _root_.GD.N0106.N0428.N0765.N1509.d023674
#print axioms _root_.GD.N0106.N0428.N0765.N1509.d023677
#print axioms _root_.GD.N0106.N0428.N0765.N1509.d023683
