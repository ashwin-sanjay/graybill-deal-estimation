import GD.Module1795












set_option autoImplicit false
set_option warningAsError true

open Finset Set

namespace GD.N0106.N0428.N0765.N1631
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1627
open _root_.GD.N0106.N0428.N0765.N1687 _root_.GD.N0106.N0428.N0765.N1629 _root_.GD.N0106.N0428.N0765.N1630
open _root_.GD.N0106.N0428.N0765.N1514
open _root_.GD.N0232.N0720.N1249

def d029906 (channel : Bool) (eta x : ℝ) : ℝ :=
  if channel then (1 + Real.exp x) / (Real.exp x + eta) else 1

def d029907 (channel : Bool) (eta h b₀ : ℝ) (i : ℤ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1514.d029705 h b₀ i * _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta (b₀ + (i : ℝ) * h)

def d029908 (channel : Bool) (eta h b₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀ i

def d029909 (channel : Bool) (k : ℕ) (eta : ℝ) : ℝ :=
  (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1630.d029893 k * _root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta

def d029910 (channel : Bool) (k : ℕ) (eta hA hB a₀ b₀ : ℝ) (NA NB : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k eta *
    (_root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA * (_root_.GD.N0106.N0428.N0765.N1631.d029908 channel eta hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB) +
      _root_.GD.N0106.N0428.N0765.N1514.d029706 channel hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB)

theorem d029911 (channel : Bool) {eta : ℝ} (heta : 0 < eta) (x : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta x := by
  cases channel <;> dsimp [_root_.GD.N0106.N0428.N0765.N1631.d029906] <;> positivity

theorem d029912 (channel : Bool) {eta : ℝ} (heta : 1 ≤ eta) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta x ≤ 1 := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  cases channel
  · simp [_root_.GD.N0106.N0428.N0765.N1631.d029906]
  · dsimp [_root_.GD.N0106.N0428.N0765.N1631.d029906]
    apply (div_le_one (by positivity : 0 < Real.exp x + eta)).mpr
    linarith

theorem d029913 (channel : Bool) (k : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k eta := by
  have hq := _root_.GD.N0106.N0428.N0765.N1630.d029896 k
  cases channel <;> dsimp [_root_.GD.N0106.N0428.N0765.N1631.d029909, _root_.GD.N0106.N0428.N0765.N1514.d029698] <;> positivity

theorem d029914 (channel : Bool) (k : Fin 5)
    (hk : k.val = 1 ∨ k.val = 3) {eta : ℝ} (heta : 1 ≤ eta) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta q‖ ≤
      _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k.val eta *
        _root_.GD.N0106.N0428.N0765.N1687.d029645 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) q.1 *
        (_root_.GD.N0106.N0428.N0765.N1687.d029645 5 5 0 q.2 * _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta q.2) := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hp := _root_.GD.N0106.N0428.N0765.N1630.d029905 k hk heta0 q
  have hC : |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, if channel then 1 else 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤
      _root_.GD.N0106.N0428.N0765.N1630.d029893 k.val *
        (_root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta * Real.exp (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel * q.1) *
          _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta q.2) := by
    cases channel
    · simpa [_root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102,
        _root_.GD.N0106.N0428.N0765.N1512.d029174, mul_neg, abs_neg,
        _root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1631.d029906] using hp
    · have hf0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) := by
        rw [_root_.GD.N0106.N0428.N0765.N1512.d029176 heta0]
        positivity
      change |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, 1) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤
        _root_.GD.N0106.N0428.N0765.N1630.d029893 k.val * (_root_.GD.N0106.N0428.N0765.N1514.d029698 true eta *
          Real.exp (_root_.GD.N0106.N0428.N0765.N1514.d029697 true * q.1) * _root_.GD.N0106.N0428.N0765.N1631.d029906 true eta q.2)
      rw [_root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102,
        _root_.GD.N0106.N0428.N0765.N1512.d029175, ← mul_assoc, abs_mul,
        abs_of_nonneg hf0]
      apply (mul_le_mul_of_nonneg_right hp hf0).trans_eq
      rw [_root_.GD.N0106.N0428.N0765.N1512.d029176 heta0]
      simp only [_root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029697, _root_.GD.N0106.N0428.N0765.N1631.d029906, if_true, one_mul]
      ring
  have hρ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
    unfold _root_.GD.N0106.N0428.N0765.N1521.d020868
    exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
      (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  have hV : 0 ≤ (1 + eta) / 11 := by positivity
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta q‖ =
        (1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q *
          |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, if channel then 1 else 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)|) := by
      simp only [_root_.GD.N0106.N0428.N0765.N1513.d029315, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hV, abs_of_nonneg hρ]
    _ ≤ (1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q * (_root_.GD.N0106.N0428.N0765.N1630.d029893 k.val *
        (_root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta * Real.exp (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel * q.1) *
          _root_.GD.N0106.N0428.N0765.N1631.d029906 channel eta q.2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hρ) hV
    _ = _ := by
      unfold _root_.GD.N0106.N0428.N0765.N1631.d029909 _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1687.d029645
      simp only [zero_mul, Real.exp_zero, one_mul]
      ring

theorem d029915 (channel : Bool) (k : Fin 5)
    (hk : k.val = 1 ∨ k.val = 3) {eta hA hB : ℝ}
    (heta : 1 ≤ eta) (hhA : 0 < hA) (hhB : 0 < hB)
    (a₀ b₀ : ℝ) (p : ℤ × ℤ) :
    ‖_root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1631.d029909 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ p.1) *
        _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta hB b₀ p.2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1514.d029710, norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos hhA hhB)]
  apply (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1631.d029914 channel k hk heta _)
    (mul_pos hhA hhB).le).trans_eq
  unfold _root_.GD.N0106.N0428.N0765.N1514.d029704 _root_.GD.N0106.N0428.N0765.N1631.d029907 _root_.GD.N0106.N0428.N0765.N1514.d029705 _root_.GD.N0106.N0428.N0765.N1687.d029646
  simp only [Prod.fst, Prod.snd]
  ring

theorem d029916 (channel : Bool) {eta h : ℝ}
    (heta : 0 < eta) (hh : 0 ≤ h) (b₀ : ℝ) (i : ℤ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀ i :=
  mul_nonneg
    (_root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hh 0 b₀ i)
    (_root_.GD.N0106.N0428.N0765.N1631.d029911 channel heta _)

theorem d029917 (channel : Bool) {eta h : ℝ}
    (heta : 1 ≤ eta) (hh : 0 ≤ h) (b₀ : ℝ) (i : ℤ) :
    ‖_root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀ i‖ ≤ _root_.GD.N0106.N0428.N0765.N1514.d029705 h b₀ i := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1631.d029916 channel heta0 hh b₀ i)]
  exact (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1631.d029912 channel heta _)
    (_root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hh 0 b₀ i)).trans_eq (mul_one _)

theorem d029918 (channel : Bool) {eta h : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (b₀ : ℝ) :
    Summable (_root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀) :=
  (_root_.GD.N0106.N0428.N0765.N1687.d029661 (a := 5) (b := 5) (j := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh b₀).of_norm_bounded
      (_root_.GD.N0106.N0428.N0765.N1631.d029917 channel heta hh.le b₀)



theorem d029919 (channel : Bool) {eta h : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (b₀ : ℝ) (N : ℕ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀ i) - _root_.GD.N0106.N0428.N0765.N1631.d029908 channel eta h b₀ N ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029709 h b₀ N := by
  have hb := _root_.GD.N0106.N0428.N0765.N1687.d029661 (a := 5) (b := 5) (j := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh b₀
  have hcomp := _root_.GD.N0106.N0428.N0765.N1629.d008244 (_root_.GD.N0106.N0428.N0765.N1687.d029647 N) hb
    (_root_.GD.N0106.N0428.N0765.N1631.d029917 channel heta hh.le b₀)
  have htail := _root_.GD.N0106.N0428.N0765.N1687.d029663 (a := 5) (b := 5) (j := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh b₀ N
  have hnorm : |(∑' i, _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta h b₀ i) - _root_.GD.N0106.N0428.N0765.N1631.d029908 channel eta h b₀ N| ≤
      (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029705 h b₀ i) -
        _root_.GD.N0106.N0428.N0765.N1514.d029707 h b₀ N := by
    simpa only [Real.norm_eq_abs, _root_.GD.N0106.N0428.N0765.N1631.d029908, _root_.GD.N0106.N0428.N0765.N1514.d029707,
      _root_.GD.N0106.N0428.N0765.N1514.d029705] using hcomp
  exact (le_abs_self _).trans (hnorm.trans htail)



theorem d029920 (channel : Bool) (k : Fin 5)
    (hk : k.val = 1 ∨ k.val = 3) {eta hA hB : ℝ}
    (heta : 1 ≤ eta) (hhA : 0 < hA) (hhB : 0 < hB)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1631.d029910 channel k.val eta hA hB a₀ b₀ NA NB := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hC := _root_.GD.N0106.N0428.N0765.N1631.d029913 channel k.val heta0
  have ha0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhA.le (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) a₀
  have hb0 := _root_.GD.N0106.N0428.N0765.N1631.d029916 channel heta0 hhB.le b₀
  have ha : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel) (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀
  have hb := _root_.GD.N0106.N0428.N0765.N1631.d029918 channel heta hhB b₀
  have hta : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) - _root_.GD.N0106.N0428.N0765.N1514.d029706 channel hA a₀ NA ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel) (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀ NA
  have htb := _root_.GD.N0106.N0428.N0765.N1631.d029919 channel heta hhB b₀ NB
  have htac : (∑' i, _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) -
      (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA, _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) ≤
        _root_.GD.N0106.N0428.N0765.N1631.d029909 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA := by
    rw [tsum_mul_left, ← Finset.mul_sum, ← mul_sub]
    exact mul_le_mul_of_nonneg_left hta hC
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008248 (_root_.GD.N0106.N0428.N0765.N1687.d029647 NA) (_root_.GD.N0106.N0428.N0765.N1687.d029647 NB)
    (fun i => mul_nonneg hC (ha0 i)) hb0 (ha.mul_left _) hb
    (_root_.GD.N0106.N0428.N0765.N1631.d029915 channel k hk heta hhA hhB a₀ b₀)
    (show (∑' i, _root_.GD.N0106.N0428.N0765.N1631.d029907 channel eta hB b₀ i) ≤
      _root_.GD.N0106.N0428.N0765.N1631.d029908 channel eta hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB by linarith)
    htac htb
  apply h.trans_eq
  rw [← Finset.mul_sum]
  unfold _root_.GD.N0106.N0428.N0765.N1631.d029910 _root_.GD.N0106.N0428.N0765.N1514.d029706
  ring



theorem d029921 (channel : Bool) (k : Fin 5)
    (hk : k.val = 1 ∨ k.val = 3) (location : ℝ)
    {eta h d0 d1 : ℝ} (heta : 1 ≤ eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p| ≤
      ((2 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta d0 0 +
          2 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta 0 d0) /
        (Real.exp (2 * Real.pi * d0 / h) - 1) +
        4 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta d1 d1 /
          (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2) +
      _root_.GD.N0106.N0428.N0765.N1631.d029910 channel k.val eta h h a₀ b₀ NA NB := by
  have hp := _root_.GD.N0106.N0428.N0765.N1513.d029317 channel k location
    heta hh hd0 hd1 haxis hmixed a₀ b₀
  rw [← _root_.GD.N0106.N0428.N0765.N1514.d029715] at hp
  have ht := _root_.GD.N0106.N0428.N0765.N1631.d029920 channel k hk heta hh hh a₀ b₀ NA NB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0))
    (∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p)
    (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p)
  simp only [Real.norm_eq_abs] at ht htriangle
  exact htriangle.trans (add_le_add hp ht)

end
end GD.N0106.N0428.N0765.N1631

#print axioms _root_.GD.N0106.N0428.N0765.N1631.d029914
#print axioms _root_.GD.N0106.N0428.N0765.N1631.d029919
#print axioms _root_.GD.N0106.N0428.N0765.N1631.d029920
#print axioms _root_.GD.N0106.N0428.N0765.N1631.d029921
