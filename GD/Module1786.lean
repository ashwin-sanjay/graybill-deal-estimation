import GD.Module1768
import GD.Module1784
import GD.Module0554




















set_option autoImplicit false
set_option warningAsError true

open Finset Set

namespace GD.N0106.N0428.N0765.N1514
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1627
open _root_.GD.N0106.N0428.N0765.N1687 _root_.GD.N0106.N0428.N0765.N1629
open _root_.GD.N0232.N0720.N1249


def d029690 (k : ℕ) : ℝ := 1 / (4 * (2 : ℝ) ^ k)

theorem d029691 (k : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029690 k := by
  unfold _root_.GD.N0106.N0428.N0765.N1514.d029690
  positivity

theorem d029692 (k : ℕ) {H : ℝ} (hH : H ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1249.d002197 k H| ≤ _root_.GD.N0106.N0428.N0765.N1514.d029690 k := by
  have hHprod : 0 ≤ H * (1 - H) := mul_nonneg hH.1 (sub_nonneg.mpr hH.2)
  have hprod : |H * (1 - H)| ≤ 1 / 4 := by
    rw [abs_of_nonneg hHprod]
    nlinarith [sq_nonneg (H - 1 / 2)]
  have hcenter : |H - 1 / 2| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith [hH.1], by linarith [hH.2]⟩
  calc
    |_root_.GD.N0232.N0720.N1249.d002197 k H| = |H * (1 - H)| * |H - 1 / 2| ^ k := by
      rw [_root_.GD.N0232.N0720.N1249.d002197, abs_mul, abs_pow]
    _ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k :=
      mul_le_mul hprod (pow_le_pow_left₀ (abs_nonneg _) hcenter k)
        (pow_nonneg (abs_nonneg _) k) (by norm_num)
    _ = _root_.GD.N0106.N0428.N0765.N1514.d029690 k := by
      simp only [_root_.GD.N0106.N0428.N0765.N1514.d029690, div_pow, one_pow]
      field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)] <;> ring


theorem d029693 (k : ℕ) {H O : ℝ}
    (hH : H ∈ Icc (0 : ℝ) 1) (hO : O ∈ Icc (0 : ℝ) 1) :
    |(H - O) * _root_.GD.N0232.N0720.N1249.d002197 k H| ≤ _root_.GD.N0106.N0428.N0765.N1514.d029690 k := by
  have hdiff : |H - O| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hH.1, hO.2], by linarith [hH.2, hO.1]⟩
  rw [abs_mul]
  exact (mul_le_mul hdiff (_root_.GD.N0106.N0428.N0765.N1514.d029692 k hH)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem d029694 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) ∈ Icc (0 : ℝ) 1 := by
  have hu : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020862 q 0 := (Real.sigmoid_pos q.1).le
  have hv : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 q 1 :=
    mul_pos (sub_pos.mpr (Real.sigmoid_lt_one q.1)) (Real.sigmoid_pos q.2)
  have hw : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 q 2 :=
    mul_pos (sub_pos.mpr (Real.sigmoid_lt_one q.1))
      (sub_pos.mpr (Real.sigmoid_lt_one q.2))
  have hh := _root_.GD.N0106.N0428.N0765.N1534.d005345 heta hu hv hw
  exact ⟨hh.1.le, hh.2.le⟩

theorem d029695 (k : Fin 5) {eta : ℝ}
    (heta : 0 < eta) (q : ℝ × ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤ _root_.GD.N0106.N0428.N0765.N1514.d029690 k.val := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102,
    _root_.GD.N0106.N0428.N0765.N1512.d029174, mul_neg, abs_neg]
  exact _root_.GD.N0106.N0428.N0765.N1514.d029693 k.val (_root_.GD.N0106.N0428.N0765.N1514.d029694 heta q)
    (_root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta)

theorem d029696 (k : Fin 5) {eta : ℝ}
    (heta : 1 ≤ eta) (q : ℝ × ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, 1) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029690 k.val * (10 * (1 + eta) * Real.exp q.1) := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hF0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) := by
    rw [_root_.GD.N0106.N0428.N0765.N1512.d029176 heta0]
    positivity
  have hF : _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) ≤
      10 * (1 + eta) * Real.exp q.1 := by
    rw [_root_.GD.N0106.N0428.N0765.N1512.d029176 heta0]
    exact _root_.GD.N0106.N0428.N0765.N1512.d029149 heta q.1 q.2
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102,
    _root_.GD.N0106.N0428.N0765.N1512.d029175, ← mul_assoc, abs_mul, abs_of_nonneg hF0]
  exact mul_le_mul
    (_root_.GD.N0106.N0428.N0765.N1514.d029693 k.val (_root_.GD.N0106.N0428.N0765.N1514.d029694 heta0 q)
      (_root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta0))
    hF hF0 (_root_.GD.N0106.N0428.N0765.N1514.d029691 k.val)


def d029697 (channel : Bool) : ℝ := if channel then 1 else 0


def d029698 (channel : Bool) (eta : ℝ) : ℝ :=
  if channel then 10 * (1 + eta) else 1


def d029699 (channel : Bool) (k : ℕ) (eta : ℝ) : ℝ :=
  (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1514.d029690 k * _root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta

theorem d029700 (channel : Bool) (k : ℕ) {eta : ℝ}
    (heta : 0 < eta) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k eta := by
  cases channel <;> dsimp [_root_.GD.N0106.N0428.N0765.N1514.d029699, _root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029690] <;> positivity

theorem d029701 (channel : Bool) : 0 < (3 : ℝ) / 2 + _root_.GD.N0106.N0428.N0765.N1514.d029697 channel := by
  cases channel <;> norm_num [_root_.GD.N0106.N0428.N0765.N1514.d029697]

theorem d029702 (channel : Bool) : 0 < (10 : ℝ) - _root_.GD.N0106.N0428.N0765.N1514.d029697 channel := by
  cases channel <;> norm_num [_root_.GD.N0106.N0428.N0765.N1514.d029697]



theorem d029703 (channel : Bool) (k : Fin 5) {eta : ℝ}
    (heta : 1 ≤ eta) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta q‖ ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta *
        _root_.GD.N0106.N0428.N0765.N1687.d029645 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) q.1 *
        _root_.GD.N0106.N0428.N0765.N1687.d029645 5 5 0 q.2 := by
  have heta0 : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hC : |_root_.GD.N0106.N0428.N0765.N1627.d021104 (k, if channel then 1 else 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029690 k.val *
        (_root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta * Real.exp (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel * q.1)) := by
    cases channel
    · simpa [_root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029697] using
        _root_.GD.N0106.N0428.N0765.N1514.d029695 k heta0 q
    · simpa [_root_.GD.N0106.N0428.N0765.N1514.d029698, _root_.GD.N0106.N0428.N0765.N1514.d029697] using
        _root_.GD.N0106.N0428.N0765.N1514.d029696 k heta q
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
    _ ≤ (1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q * (_root_.GD.N0106.N0428.N0765.N1514.d029690 k.val *
        (_root_.GD.N0106.N0428.N0765.N1514.d029698 channel eta * Real.exp (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel * q.1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hρ) hV
    _ = _ := by
      unfold _root_.GD.N0106.N0428.N0765.N1514.d029699 _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1687.d029645
      simp only [zero_mul, Real.exp_zero, one_mul]
      ring

def d029704 (channel : Bool) (h a₀ : ℝ) : ℤ → ℝ :=
  _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) h a₀

def d029705 (h b₀ : ℝ) : ℤ → ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029646 5 5 0 h b₀

def d029706 (channel : Bool) (h a₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1514.d029704 channel h a₀ i

def d029707 (h b₀ : ℝ) (N : ℕ) : ℝ := ∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1514.d029705 h b₀ i

def d029708 (channel : Bool) (h a₀ : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) h a₀ N

def d029709 (h b₀ : ℝ) (N : ℕ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 0 h b₀ N


def d029710 (channel : Bool) (k : Fin 5) (eta hA hB a₀ b₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  (hA * hB) * _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta
    (a₀ + (p.1 : ℝ) * hA, b₀ + (p.2 : ℝ) * hB)



def d029711 (channel : Bool) (k : ℕ) (eta hA hB a₀ b₀ : ℝ) (NA NB : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k eta *
    (_root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA * (_root_.GD.N0106.N0428.N0765.N1514.d029707 hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB) +
      _root_.GD.N0106.N0428.N0765.N1514.d029706 channel hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB)

theorem d029712 (channel : Bool) (k : Fin 5) {eta hA hB : ℝ}
    (heta : 1 ≤ eta) (hhA : 0 < hA) (hhB : 0 < hB)
    (a₀ b₀ : ℝ) (p : ℤ × ℤ) :
    ‖_root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ p.1) *
        _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ p.2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1514.d029710, norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos hhA hhB)]
  apply (mul_le_mul_of_nonneg_left
    (_root_.GD.N0106.N0428.N0765.N1514.d029703 channel k heta _) (mul_pos hhA hhB).le).trans_eq
  unfold _root_.GD.N0106.N0428.N0765.N1514.d029704 _root_.GD.N0106.N0428.N0765.N1514.d029705 _root_.GD.N0106.N0428.N0765.N1687.d029646
  simp only [Prod.fst, Prod.snd]
  ring

theorem d029713 (channel : Bool) (k : Fin 5) {eta hA hB : ℝ}
    (heta : 1 ≤ eta) (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) :
    Summable (_root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀) := by
  have hC := _root_.GD.N0106.N0428.N0765.N1514.d029700 channel k.val (lt_of_lt_of_le zero_lt_one heta)
  have ha0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhA.le (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) a₀
  have hb0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhB.le 0 b₀
  have ha : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel) (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀
  have hb : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀
  exact _root_.GD.N0106.N0428.N0765.N1629.d008245 (fun i => mul_nonneg hC (ha0 i)) hb0
    (ha.mul_left _) hb (_root_.GD.N0106.N0428.N0765.N1514.d029712 channel k heta hhA hhB a₀ b₀)



theorem d029714 (channel : Bool) (k : Fin 5) {eta hA hB : ℝ}
    (heta : 1 ≤ eta) (hhA : 0 < hA) (hhB : 0 < hB)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta hA hB a₀ b₀ p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1514.d029711 channel k.val eta hA hB a₀ b₀ NA NB := by
  have hC := _root_.GD.N0106.N0428.N0765.N1514.d029700 channel k.val (lt_of_lt_of_le zero_lt_one heta)
  have ha0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhA.le (_root_.GD.N0106.N0428.N0765.N1514.d029697 channel) a₀
  have hb0 : ∀ i, 0 ≤ _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i :=
    _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hhB.le 0 b₀
  have ha : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel) (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀
  have hb : Summable (_root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀) :=
    _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀
  have hta : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) - _root_.GD.N0106.N0428.N0765.N1514.d029706 channel hA a₀ NA ≤
      _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num)
      (_root_.GD.N0106.N0428.N0765.N1514.d029701 channel) (_root_.GD.N0106.N0428.N0765.N1514.d029702 channel) hhA a₀ NA
  have htb : (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i) - _root_.GD.N0106.N0428.N0765.N1514.d029707 hB b₀ NB ≤ _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB :=
    _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hhB b₀ NB
  have htac :
      (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) -
        (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA, _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029704 channel hA a₀ i) ≤
          _root_.GD.N0106.N0428.N0765.N1514.d029699 channel k.val eta * _root_.GD.N0106.N0428.N0765.N1514.d029708 channel hA a₀ NA := by
    rw [tsum_mul_left, ← Finset.mul_sum, ← mul_sub]
    exact mul_le_mul_of_nonneg_left hta hC
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008248 (_root_.GD.N0106.N0428.N0765.N1687.d029647 NA) (_root_.GD.N0106.N0428.N0765.N1687.d029647 NB)
    (fun i => mul_nonneg hC (ha0 i)) hb0 (ha.mul_left _) hb
    (_root_.GD.N0106.N0428.N0765.N1514.d029712 channel k heta hhA hhB a₀ b₀)
    (show (∑' i, _root_.GD.N0106.N0428.N0765.N1514.d029705 hB b₀ i) ≤ _root_.GD.N0106.N0428.N0765.N1514.d029707 hB b₀ NB + _root_.GD.N0106.N0428.N0765.N1514.d029709 hB b₀ NB by linarith)
    htac htb
  apply h.trans_eq
  rw [← Finset.mul_sum]
  unfold _root_.GD.N0106.N0428.N0765.N1514.d029711 _root_.GD.N0106.N0428.N0765.N1514.d029706
  ring

theorem d029715 (channel : Bool) (k : Fin 5) (eta h a₀ b₀ : ℝ) :
    (∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p) =
      h ^ 2 * (∑' p : ℤ × ℤ,
        _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta (a₀ + h * p.1, b₀ + h * p.2)) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1514.d029710, tsum_mul_left, pow_two, mul_comm h]



theorem d029716 (channel : Bool) (k : Fin 5) (location : ℝ)
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
      _root_.GD.N0106.N0428.N0765.N1514.d029711 channel k.val eta h h a₀ b₀ NA NB := by
  have hp := _root_.GD.N0106.N0428.N0765.N1513.d029317 channel k location
    heta hh hd0 hd1 haxis hmixed a₀ b₀
  rw [← _root_.GD.N0106.N0428.N0765.N1514.d029715] at hp
  have ht := _root_.GD.N0106.N0428.N0765.N1514.d029714 channel k heta hh hh a₀ b₀ NA NB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0))
    (∑' p, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p)
    (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1514.d029710 channel k eta h h a₀ b₀ p)
  simp only [Real.norm_eq_abs] at ht htriangle
  exact htriangle.trans (add_le_add hp ht)

end
end GD.N0106.N0428.N0765.N1514

#print axioms _root_.GD.N0106.N0428.N0765.N1514.d029692
#print axioms _root_.GD.N0106.N0428.N0765.N1514.d029703
#print axioms _root_.GD.N0106.N0428.N0765.N1514.d029713
#print axioms _root_.GD.N0106.N0428.N0765.N1514.d029714
#print axioms _root_.GD.N0106.N0428.N0765.N1514.d029716
