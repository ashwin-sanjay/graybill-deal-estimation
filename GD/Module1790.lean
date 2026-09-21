import GD.Module1785
import GD.Module1786
import GD.Module1788









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open Finset

namespace GD.N0106.N0428.N0765.N1519
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1687 _root_.GD.N0106.N0428.N0765.N1507 _root_.GD.N0106.N0428.N0765.N1629


def d029771 (channel : Bool) (d h : ℝ) : ℝ :=
  if channel then (1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 d h) / 6 else 1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 d h

theorem d029772 (channel : Bool) {d h : ℝ}
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (c : ℝ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029704 channel h c i) ≤ _root_.GD.N0106.N0428.N0765.N1519.d029771 channel d h := by
  cases channel
  · simpa only [_root_.GD.N0106.N0428.N0765.N1514.d029704,
      _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1519.d029771, Bool.false_eq_true, if_false] using
      _root_.GD.N0106.N0428.N0765.N1507.d029686 hd hdpi hh c
  · simpa only [_root_.GD.N0106.N0428.N0765.N1514.d029704,
      _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1519.d029771, if_true] using
      _root_.GD.N0106.N0428.N0765.N1507.d029689 hd hdpi hh c



private theorem d029773
    (channel : Bool) {f : ℤ × ℤ → ℝ} {C dA dB hA hB : ℝ}
    (hC : 0 ≤ C) (hdA : 0 < dA) (hdApi : dA < Real.pi / 2)
    (hdB : 0 < dB) (hdBpi : dB < Real.pi / 2)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ)
    (hdom : ∀ p, ‖f p‖ ≤
      (C * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ p.1) *
        _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ p.2) :
    ‖(∑' p, f p) - ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, f p‖ ≤
      C * (_root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA * (1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB) +
        _root_.GD.N0106.N0428.N0765.N1519.d029771 channel dA hA * _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB) := by
  have ha0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhA.le
      (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) a₀
  have hb0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhB.le 0 b₀
  have ha : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel)
      (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀
  have hb : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀
  have hta : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) -
      _root_.GD.N0106.N0428.N0765.N1514.d029706 channel hA a₀ NA ≤
        _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel)
      (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀ NA
  have htb : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i) -
      _root_.GD.N0106.N0428.N0765.N1514.d029707 hB b₀ NB ≤
        _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀ NB
  have hma : (∑' i, C * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) ≤
      C * _root_.GD.N0106.N0428.N0765.N1519.d029771 channel dA hA := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1519.d029772 channel hdA hdApi hhA a₀) hC
  have hmb : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i) ≤
      1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB := _root_.GD.N0106.N0428.N0765.N1507.d029687 hdB hdBpi hhB b₀
  have htac : (∑' i, C * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) -
      (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA, C * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) ≤
        C * _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA := by
    rw [tsum_mul_left, ← Finset.mul_sum, ← mul_sub]
    exact mul_le_mul_of_nonneg_left hta hC
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008249 (_root_.GD.N0106.N0428.N0765.N1687.d029647 NA) (_root_.GD.N0106.N0428.N0765.N1687.d029647 NB)
    (fun i => mul_nonneg hC (ha0 i)) hb0 (ha.mul_left _) hb hdom hma hmb htac htb
  exact h.trans_eq (by ring)



theorem d029774
    {eta dA dB hA hB : ℝ} (heta : 0 < eta)
    (hdA : 0 < dA) (hdApi : dA < Real.pi / 2)
    (hdB : 0 < dB) (hdBpi : dB < Real.pi / 2)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p‖ ≤
      _root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 0 hA a₀ NA * (1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB) +
        (1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 dA hA) * _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 0 hB b₀ NB := by
  have hdom (p : ℤ × ℤ) :
      ‖_root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p‖ ≤
        ((1 : ℝ) * _root_.GD.N0106.N0428.N0765.N1514.d029704 false hA a₀ p.1) *
          _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ p.2 := by
    rw [_root_.GD.N0106.N0428.N0765.N1515.d029739, norm_mul, Real.norm_eq_abs,
      abs_of_pos (mul_pos hhA hhB)]
    apply (mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1515.d029759 heta _) (mul_pos hhA hhB).le).trans_eq
    unfold _root_.GD.N0106.N0428.N0765.N1514.d029704 _root_.GD.N0106.N0428.N0765.N1514.d029705
      _root_.GD.N0106.N0428.N0765.N1514.d029697 _root_.GD.N0106.N0428.N0765.N1687.d029646 _root_.GD.N0106.N0428.N0765.N1687.d029645 _root_.GD.N0106.N0428.N0765.N1521.d020868
    simp only [Bool.false_eq_true, if_false, zero_mul, Real.exp_zero, one_mul,
      Prod.fst, Prod.snd]
    ring
  have h := _root_.GD.N0106.N0428.N0765.N1519.d029773 false (by norm_num : (0 : ℝ) ≤ 1)
    hdA hdApi hdB hdBpi hhA hhB a₀ b₀ NA NB hdom
  simpa only [_root_.GD.N0106.N0428.N0765.N1514.d029708, _root_.GD.N0106.N0428.N0765.N1514.d029709,
    _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1519.d029771, Bool.false_eq_true, if_false, one_mul] using h



theorem d029775 (channel : Bool) (k : Fin 5)
    {eta dA dB hA hB : ℝ} (heta : 1 ≤ eta)
    (hdA : 0 < dA) (hdApi : dA < Real.pi / 2)
    (hdB : 0 < dB) (hdBpi : dB < Real.pi / 2)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p‖ ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta *
        (_root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA * (1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB) +
          _root_.GD.N0106.N0428.N0765.N1519.d029771 channel dA hA * _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB) :=
  _root_.GD.N0106.N0428.N0765.N1519.d029773 channel
    (_root_.GD.N0106.N0428.N0765.N1514.d029700 channel k.val
      (lt_of_lt_of_le zero_lt_one heta))
    hdA hdApi hdB hdBpi hhA hhB a₀ b₀ NA NB
    (_root_.GD.N0106.N0428.N0765.N1514.d029712 channel k heta hhA hhB a₀ b₀)


theorem d029776 (k : Fin 5)
    {eta dA dB hA hB : ℝ} (heta : 1 ≤ eta)
    (hdA : 0 < dA) (hdApi : dA < Real.pi / 2)
    (hdB : 0 < dB) (hdBpi : dB < Real.pi / 2)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 false k eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1514.d029710 false k eta hA hB a₀ b₀ p‖ ≤
      ((1 + eta) / 11) * (1 / (4 * (2 : ℝ) ^ k.val)) *
        (_root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 0 hA a₀ NA * (1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB) +
          (1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 dA hA) * _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 0 hB b₀ NB) := by
  simpa [_root_.GD.N0106.N0428.N0765.N1514.d029699, _root_.GD.N0106.N0428.N0765.N1514.d029690,
    _root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029708,
    _root_.GD.N0106.N0428.N0765.N1514.d029709, _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1519.d029771] using
    _root_.GD.N0106.N0428.N0765.N1519.d029775 false k heta hdA hdApi hdB hdBpi hhA hhB a₀ b₀ NA NB


theorem d029777 (k : Fin 5)
    {eta dA dB hA hB : ℝ} (heta : 1 ≤ eta)
    (hdA : 0 < dA) (hdApi : dA < Real.pi / 2)
    (hdB : 0 < dB) (hdBpi : dB < Real.pi / 2)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 true k eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1514.d029710 true k eta hA hB a₀ b₀ p‖ ≤
      (10 * (1 + eta) ^ 2 / 11) * (1 / (4 * (2 : ℝ) ^ k.val)) *
        (_root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 1 hA a₀ NA * (1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 dB hB) +
          ((1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 dA hA) / 6) * _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 0 hB b₀ NB) := by
  have h := _root_.GD.N0106.N0428.N0765.N1519.d029775 true k heta hdA hdApi hdB hdBpi hhA hhB a₀ b₀ NA NB
  simp only [_root_.GD.N0106.N0428.N0765.N1514.d029699, _root_.GD.N0106.N0428.N0765.N1514.d029690,
    _root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029708,
    _root_.GD.N0106.N0428.N0765.N1514.d029709, _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1519.d029771, if_true] at h
  exact h.trans_eq (by ring)

end
end GD.N0106.N0428.N0765.N1519

#print axioms _root_.GD.N0106.N0428.N0765.N1519.d029774
#print axioms _root_.GD.N0106.N0428.N0765.N1519.d029776
#print axioms _root_.GD.N0106.N0428.N0765.N1519.d029777
