import GD.Module1775
import GD.Module1784
import GD.Module0554








set_option autoImplicit false
set_option warningAsError true

open Finset

namespace GD.N0106.N0428.N0765.N1518
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1687 _root_.GD.N0106.N0428.N0765.N1629

def d029717 (h a₀ : ℝ) : ℤ → ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 0 h a₀
def d029718 (h b₀ : ℝ) : ℤ → ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029646 5 5 0 h b₀
def d029719 (h a₀ : ℝ) (N : ℕ) : ℝ := ∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1518.d029717 h a₀ i
def d029720 (h b₀ : ℝ) (N : ℕ) : ℝ := ∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1518.d029718 h b₀ i
def d029721 (h a₀ : ℝ) (N : ℕ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 0 h a₀ N
def d029722 (h b₀ : ℝ) (N : ℕ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 0 h b₀ N

def d029723 (eta hA hB a₀ b₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  (hA * hB) * _root_.GD.N0106.N0428.N0765.N1516.d029220 eta
    (a₀ + (p.1 : ℝ) * hA, b₀ + (p.2 : ℝ) * hB)

def d029724 (eta hA hB a₀ b₀ : ℝ) (NA NB : ℕ) : ℝ :=
  (1 + eta) / 11 *
    (_root_.GD.N0106.N0428.N0765.N1518.d029721 hA a₀ NA * (_root_.GD.N0106.N0428.N0765.N1518.d029720 hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB) +
      _root_.GD.N0106.N0428.N0765.N1518.d029719 hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB)

theorem d029725 {eta hA hB : ℝ} (heta : 0 < eta)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (p : ℤ × ℤ) :
    ‖_root_.GD.N0106.N0428.N0765.N1518.d029723 eta hA hB a₀ b₀ p‖ ≤
      ((1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀ p.1) * _root_.GD.N0106.N0428.N0765.N1518.d029718 hB b₀ p.2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1518.d029723, norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos hhA hhB)]
  apply (mul_le_mul_of_nonneg_left
    (_root_.GD.N0106.N0428.N0765.N1516.d029244 heta _) (mul_pos hhA hhB).le).trans_eq
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029717 _root_.GD.N0106.N0428.N0765.N1518.d029718 _root_.GD.N0106.N0428.N0765.N1687.d029646 _root_.GD.N0106.N0428.N0765.N1687.d029645 _root_.GD.N0106.N0428.N0765.N1521.d020868
  simp only [zero_mul, Real.exp_zero, one_mul, Prod.fst, Prod.snd]
  ring

theorem d029726 {eta hA hB : ℝ} (heta : 0 < eta)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta hA hB a₀ b₀ p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1518.d029724 eta hA hB a₀ b₀ NA NB := by
  have hV : 0 ≤ (1 + eta) / 11 := by positivity
  have ha0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhA.le 0 a₀
  have hb0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1518.d029718 hB b₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhB.le 0 b₀
  have ha : Summable (_root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhA a₀
  have hb : Summable (_root_.GD.N0106.N0428.N0765.N1518.d029718 hB b₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀
  have hta : (∑' i, _root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀ i) - _root_.GD.N0106.N0428.N0765.N1518.d029719 hA a₀ NA ≤ _root_.GD.N0106.N0428.N0765.N1518.d029721 hA a₀ NA :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhA a₀ NA
  have htb : (∑' i, _root_.GD.N0106.N0428.N0765.N1518.d029718 hB b₀ i) - _root_.GD.N0106.N0428.N0765.N1518.d029720 hB b₀ NB ≤ _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀ NB
  have htav :
      (∑' i, (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀ i) -
        (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA, (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1518.d029717 hA a₀ i) ≤
          (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1518.d029721 hA a₀ NA := by
    rw [tsum_mul_left, ← Finset.mul_sum, ← mul_sub]
    exact mul_le_mul_of_nonneg_left hta hV
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008248 (_root_.GD.N0106.N0428.N0765.N1687.d029647 NA) (_root_.GD.N0106.N0428.N0765.N1687.d029647 NB)
    (fun i => mul_nonneg hV (ha0 i)) hb0 (ha.mul_left _) hb
    (_root_.GD.N0106.N0428.N0765.N1518.d029725 heta hhA hhB a₀ b₀)
    (show (∑' i, _root_.GD.N0106.N0428.N0765.N1518.d029718 hB b₀ i) ≤ _root_.GD.N0106.N0428.N0765.N1518.d029720 hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB by linarith)
    htav htb
  apply h.trans_eq
  rw [← Finset.mul_sum]
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029724 _root_.GD.N0106.N0428.N0765.N1518.d029719
  ring

theorem d029727 (eta h a₀ b₀ : ℝ) :
    (∑' p, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta h h a₀ b₀ p) =
      h ^ 2 * (∑' p : ℤ × ℤ,
        _root_.GD.N0106.N0428.N0765.N1516.d029220 eta (a₀ + h * p.1, b₀ + h * p.2)) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1518.d029723, tsum_mul_left, pow_two, mul_comm h]



theorem d029728 (location : ℝ) {eta h d0 d1 : ℝ}
    (heta : 0 < eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021120 location eta -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta h h a₀ b₀ p| ≤
      ((2 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta d0 0 + 2 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta 0 d0) /
        (Real.exp (2 * Real.pi * d0 / h) - 1) +
        4 * _root_.GD.N0106.N0428.N0765.N1516.d029223 eta d1 d1 / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2) +
      _root_.GD.N0106.N0428.N0765.N1518.d029724 eta h h a₀ b₀ NA NB := by
  have hp := _root_.GD.N0106.N0428.N0765.N1517.d029382 location
    heta hh hd0 hd1 haxis hmixed a₀ b₀
  rw [← _root_.GD.N0106.N0428.N0765.N1518.d029727] at hp
  have ht := _root_.GD.N0106.N0428.N0765.N1518.d029726 heta hh hh a₀ b₀ NA NB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (_root_.GD.N0106.N0428.N0765.N1627.d021120 location eta)
    (∑' p, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta h h a₀ b₀ p)
    (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1518.d029723 eta h h a₀ b₀ p)
  simp only [Real.norm_eq_abs] at ht htriangle
  exact htriangle.trans (add_le_add hp ht)

end
end GD.N0106.N0428.N0765.N1518

#print axioms _root_.GD.N0106.N0428.N0765.N1518.d029726
#print axioms _root_.GD.N0106.N0428.N0765.N1518.d029728
