import GD.Module0445





































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Finset
open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1545




def d006828 (x : ℚ) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨x, x⟩

theorem d006829 (x : ℚ) : (_root_.GD.N0106.N0428.N0765.N1545.d006828 x).d006810 (x : ℝ) := ⟨le_rfl, le_rfl⟩


theorem d006830 {I J : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ}
    (h : I.d006810 x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) : J.d006810 x := by
  have hlo' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hhi' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hlo'.trans h.1, h.2.trans hhi'⟩


theorem d006831 {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} (h : I.d006810 x) : I.lo ≤ I.hi := by
  exact_mod_cast h.1.trans h.2


theorem d006832 {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ} {b : ℚ}
    (hx : I.d006810 x) (hy : J.d006810 y)
    (h1 : I.hi - J.lo ≤ b) (h2 : J.hi - I.lo ≤ b) : |x - y| ≤ (b : ℝ) := by
  have h1R : (I.hi : ℝ) - (J.lo : ℝ) ≤ (b : ℝ) := by exact_mod_cast h1
  have h2R : (J.hi : ℝ) - (I.lo : ℝ) ≤ (b : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]


def d006833 (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if 0 ≤ I.lo then ⟨I.lo ^ 2, I.hi ^ 2⟩
  else if I.hi ≤ 0 then ⟨I.hi ^ 2, I.lo ^ 2⟩
  else ⟨0, max (I.lo ^ 2) (I.hi ^ 2)⟩

theorem d006834 {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} (hx : I.d006810 x) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006833 I).d006810 (x ^ 2) := by
  obtain ⟨hlo, hhi⟩ := hx
  by_cases h1 : 0 ≤ I.lo
  · have h1R : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h1
    have hx0 : 0 ≤ x := h1R.trans hlo
    simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_pos h1]
    constructor
    · push_cast
      exact pow_le_pow_left₀ h1R hlo 2
    · push_cast
      exact pow_le_pow_left₀ hx0 hhi 2
  · by_cases h2 : I.hi ≤ 0
    · have h2R : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h2
      have hx0 : x ≤ 0 := hhi.trans h2R
      simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_neg h1, if_pos h2]
      constructor
      · push_cast
        have h := pow_le_pow_left₀ (neg_nonneg.mpr h2R) (neg_le_neg hhi) 2
        rwa [neg_sq, neg_sq] at h
      · push_cast
        have h := pow_le_pow_left₀ (neg_nonneg.mpr hx0) (neg_le_neg hlo) 2
        rwa [neg_sq, neg_sq] at h
    · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_neg h1, if_neg h2]
      constructor
      · push_cast
        exact sq_nonneg x
      · show x ^ 2 ≤ ((max (I.lo ^ 2) (I.hi ^ 2) : ℚ) : ℝ)
        rw [Rat.cast_max]
        push_cast
        rcases le_total 0 x with hx0 | hx0
        · exact (pow_le_pow_left₀ hx0 hhi 2).trans (le_max_right _ _)
        · have h := pow_le_pow_left₀ (neg_nonneg.mpr hx0) (neg_le_neg hlo) 2
          rw [neg_sq, neg_sq] at h
          exact h.trans (le_max_left _ _)


def d006835 (n : ℕ) (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨I.lo ^ n, I.hi ^ n⟩

theorem d006836 {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} (n : ℕ) (hI : 0 ≤ I.lo)
    (hx : I.d006810 x) : (_root_.GD.N0106.N0428.N0765.N1545.d006835 n I).d006810 (x ^ n) := by
  have hI0 : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hI
  have hx0 : 0 ≤ x := hI0.trans hx.1
  simp only [_root_.GD.N0106.N0428.N0765.N1545.d006835]
  constructor
  · push_cast
    exact pow_le_pow_left₀ hI0 hx.1 n
  · push_cast
    exact pow_le_pow_left₀ hx0 hx.2 n


def d006837 (f : ℕ → _root_.GD.N0232.N0720.N1164.d006809) : ℕ → _root_.GD.N0232.N0720.N1164.d006809
  | 0 => ⟨0, 0⟩
  | n + 1 => (d006837 f n).d006812 (f n)

theorem d006838 (f : ℕ → _root_.GD.N0232.N0720.N1164.d006809) (g : ℕ → ℝ) (n : ℕ)
    (h : ∀ i, i < n → (f i).d006810 (g i)) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006837 f n).d006810 (∑ i ∈ range n, g i) := by
  induction n with
  | zero =>
    simp only [_root_.GD.N0106.N0428.N0765.N1545.d006837, Finset.sum_range_zero]
    constructor <;> norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact _root_.GD.N0232.N0720.N1164.d006809.d006819 (ih (fun i hi => h i (by omega))) (h n (by omega))




def d006839 (m : ℤ) (e : ℕ) : ℚ := m / 2 ^ e

theorem d006840 (m : ℤ) (e : ℕ) : ((_root_.GD.N0106.N0428.N0765.N1545.d006839 m e : ℚ) : ℝ) = (m : ℝ) / 2 ^ e := by
  push_cast [_root_.GD.N0106.N0428.N0765.N1545.d006839] <;> rfl




def d006841 (y : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, y ^ i / (i.factorial : ℚ)


def d006842 (y : ℚ) (n : ℕ) : ℚ := |y| ^ n * ((n + 1 : ℚ) / ((n.factorial : ℚ) * n))

theorem d006843 (y : ℚ) (n : ℕ) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006841 y n : ℚ) : ℝ) = ∑ i ∈ range n, (y : ℝ) ^ i / (i.factorial : ℝ) := by
  push_cast [_root_.GD.N0106.N0428.N0765.N1545.d006841] <;> rfl

theorem d006844 (y : ℚ) (n : ℕ) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006842 y n : ℚ) : ℝ) =
      |(y : ℝ)| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
  push_cast [_root_.GD.N0106.N0428.N0765.N1545.d006842, Nat.succ_eq_add_one] <;> rfl


theorem d006845 {y : ℚ} {n : ℕ} (hy : |y| ≤ 1) (hn : 0 < n) :
    (_root_.GD.N0232.N0720.N1164.d006809.mk (_root_.GD.N0106.N0428.N0765.N1545.d006841 y n - _root_.GD.N0106.N0428.N0765.N1545.d006842 y n) (_root_.GD.N0106.N0428.N0765.N1545.d006841 y n + _root_.GD.N0106.N0428.N0765.N1545.d006842 y n)).d006810
      (Real.exp y) := by
  have hyR : |(y : ℝ)| ≤ 1 := by exact_mod_cast hy
  have h := Real.exp_bound hyR hn
  rw [← _root_.GD.N0106.N0428.N0765.N1545.d006843, ← _root_.GD.N0106.N0428.N0765.N1545.d006844, abs_le] at h
  constructor
  · push_cast
    linarith [h.1]
  · push_cast
    linarith [h.2]




def d006846 (x : ℚ) (k n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨(_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n) ^ (2 ^ k),
   (_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n + _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n) ^ (2 ^ k)⟩

theorem d006847 {x : ℚ} {k n : ℕ} (hx : |x / 2 ^ k| ≤ 1)
    (hpos : 0 ≤ _root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n) (hn : 0 < n) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006846 x k n).d006810 (Real.exp x) := by
  have hmem := _root_.GD.N0106.N0428.N0765.N1545.d006845 hx hn
  have hlo : ((_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n : ℚ) : ℝ) ≤
      Real.exp ((x / 2 ^ k : ℚ) : ℝ) := hmem.1
  have hhi : Real.exp ((x / 2 ^ k : ℚ) : ℝ) ≤
      ((_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n + _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n : ℚ) : ℝ) := hmem.2
  have hposR : (0 : ℝ) ≤ ((_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n : ℚ) : ℝ) := by
    exact_mod_cast hpos
  have hepos : 0 ≤ Real.exp ((x / 2 ^ k : ℚ) : ℝ) := (Real.exp_pos _).le
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hxy : (x : ℝ) = ((2 ^ k : ℕ) : ℝ) * ((x / 2 ^ k : ℚ) : ℝ) := by
    push_cast
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self h2k, mul_one]
  have hpow : Real.exp x = Real.exp ((x / 2 ^ k : ℚ) : ℝ) ^ (2 ^ k) := by
    rw [hxy, Real.exp_nat_mul]
  rw [hpow]
  constructor
  · show (((_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n) ^ (2 ^ k) : ℚ) : ℝ) ≤ _
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ hposR hlo _
  · show _ ≤ (((_root_.GD.N0106.N0428.N0765.N1545.d006841 (x / 2 ^ k) n + _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ k) n) ^ (2 ^ k) : ℚ) : ℝ)
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ hepos hhi _


def d006848 (A : _root_.GD.N0232.N0720.N1164.d006809) (k n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨(_root_.GD.N0106.N0428.N0765.N1545.d006846 A.lo k n).lo, (_root_.GD.N0106.N0428.N0765.N1545.d006846 A.hi k n).hi⟩

theorem d006849 {A : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} {k n : ℕ} (hA : A.d006810 x)
    (hlo : |A.lo / 2 ^ k| ≤ 1) (hhi : |A.hi / 2 ^ k| ≤ 1)
    (plo : 0 ≤ _root_.GD.N0106.N0428.N0765.N1545.d006841 (A.lo / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (A.lo / 2 ^ k) n)
    (phi : 0 ≤ _root_.GD.N0106.N0428.N0765.N1545.d006841 (A.hi / 2 ^ k) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (A.hi / 2 ^ k) n)
    (hn : 0 < n) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006848 A k n).d006810 (Real.exp x) := by
  have h1 := _root_.GD.N0106.N0428.N0765.N1545.d006847 hlo plo hn
  have h2 := _root_.GD.N0106.N0428.N0765.N1545.d006847 hhi phi hn
  exact ⟨h1.1.trans (Real.exp_le_exp.2 hA.1), (Real.exp_le_exp.2 hA.2).trans h2.2⟩




theorem d006850 {q l u : ℚ} {El Eu : _root_.GD.N0232.N0720.N1164.d006809} (hq : 0 < q)
    (hl : El.d006810 (Real.exp l)) (hu : Eu.d006810 (Real.exp u))
    (hl' : El.hi ≤ q) (hu' : q ≤ Eu.lo) :
    (_root_.GD.N0232.N0720.N1164.d006809.mk l u).d006810 (Real.log q) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  constructor
  · show (l : ℝ) ≤ Real.log q
    rw [Real.le_log_iff_exp_le hqR]
    have h : (El.hi : ℝ) ≤ q := by exact_mod_cast hl'
    exact hl.2.trans h
  · show Real.log q ≤ (u : ℝ)
    rw [Real.log_le_iff_le_exp hqR]
    have h : (q : ℝ) ≤ Eu.lo := by exact_mod_cast hu'
    exact h.trans hu.1




def d006851 : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨314159265358979323846 / 10 ^ 20, 314159265358979323847 / 10 ^ 20⟩

theorem d006852 : _root_.GD.N0106.N0428.N0765.N1545.d006851.d006810 Real.pi := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · show ((314159265358979323846 / 10 ^ 20 : ℚ) : ℝ) ≤ Real.pi
    norm_num at h1 ⊢
    linarith
  · show Real.pi ≤ ((314159265358979323847 / 10 ^ 20 : ℚ) : ℝ)
    norm_num at h2 ⊢
    linarith

theorem d006853 {a : ℚ} (h : a ≤ _root_.GD.N0106.N0428.N0765.N1545.d006851.lo) : (a : ℝ) ≤ Real.pi := by
  have h' : (a : ℝ) ≤ (_root_.GD.N0106.N0428.N0765.N1545.d006851.lo : ℝ) := by exact_mod_cast h
  exact h'.trans _root_.GD.N0106.N0428.N0765.N1545.d006852.1




def d006854 (m : ℕ) : ℚ := if m % 4 = 0 then 1 else if m % 4 = 2 then -1 else 0


def d006855 (m : ℕ) : ℚ := _root_.GD.N0106.N0428.N0765.N1545.d006854 m / (m.factorial : ℚ)


def d006856 (y : ℚ) (n : ℕ) : ℚ := ∑ m ∈ range n, _root_.GD.N0106.N0428.N0765.N1545.d006855 m * y ^ m

theorem d006857 (m : ℕ) : Complex.I ^ m = Complex.I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem d006858 (m : ℕ) : (Complex.I ^ m).re = ((_root_.GD.N0106.N0428.N0765.N1545.d006854 m : ℚ) : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1545.d006857]
  have hm : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold _root_.GD.N0106.N0428.N0765.N1545.d006854
  generalize m % 4 = r at hm ⊢
  interval_cases r
  · simp
  · simp
  · simp [Complex.I_sq]
  · simp [pow_three, Complex.I_mul_I]

theorem d006859 (y : ℚ) (n : ℕ) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006856 y n : ℚ) : ℝ) =
      ∑ m ∈ range n, ((_root_.GD.N0106.N0428.N0765.N1545.d006854 m : ℚ) : ℝ) / (m.factorial : ℝ) * (y : ℝ) ^ m := by
  push_cast [_root_.GD.N0106.N0428.N0765.N1545.d006856, _root_.GD.N0106.N0428.N0765.N1545.d006855] <;> rfl



theorem d006860 {y : ℚ} {n : ℕ} (hy : |y| ≤ 1) (hn : 0 < n) :
    |Real.cos y - ((_root_.GD.N0106.N0428.N0765.N1545.d006856 y n : ℚ) : ℝ)| ≤
      |(y : ℝ)| ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) := by
  have hnorm : ‖((y : ℝ) : ℂ) * Complex.I‖ = |(y : ℝ)| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hz1 : ‖((y : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [hnorm]
    exact_mod_cast hy
  have hb := Complex.exp_bound hz1 hn
  have hre : (Complex.exp (((y : ℝ) : ℂ) * Complex.I)).re = Real.cos y :=
    Complex.exp_ofReal_mul_I_re (y : ℝ)
  have hterm : ∀ m : ℕ,
      ((((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
        ((_root_.GD.N0106.N0428.N0765.N1545.d006854 m : ℚ) : ℝ) / (m.factorial : ℝ) * (y : ℝ) ^ m := by
    intro m
    have h1 : (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        ((((y : ℝ) ^ m / (m.factorial : ℝ) : ℝ)) : ℂ) * Complex.I ^ m := by
      rw [mul_pow]
      push_cast
      ring
    rw [h1, Complex.re_ofReal_mul, _root_.GD.N0106.N0428.N0765.N1545.d006858]
    ring
  have hsum : (∑ m ∈ range n, (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
      ((_root_.GD.N0106.N0428.N0765.N1545.d006856 y n : ℚ) : ℝ) := by
    rw [Complex.re_sum, _root_.GD.N0106.N0428.N0765.N1545.d006859]
    exact Finset.sum_congr rfl (fun m _ => hterm m)
  calc |Real.cos y - ((_root_.GD.N0106.N0428.N0765.N1545.d006856 y n : ℚ) : ℝ)|
      = |(Complex.exp (((y : ℝ) : ℂ) * Complex.I) -
          ∑ m ∈ range n, (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re| := by
        rw [Complex.sub_re, hre, hsum]
    _ ≤ ‖Complex.exp (((y : ℝ) : ℂ) * Complex.I) -
          ∑ m ∈ range n, (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖((y : ℝ) : ℂ) * Complex.I‖ ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) := hb
    _ = |(y : ℝ)| ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) := by rw [hnorm]


theorem d006861 {y : ℚ} {n : ℕ} (hy : |y| ≤ 1) (hn : 0 < n) :
    (_root_.GD.N0232.N0720.N1164.d006809.mk (_root_.GD.N0106.N0428.N0765.N1545.d006856 y n - _root_.GD.N0106.N0428.N0765.N1545.d006842 y n) (_root_.GD.N0106.N0428.N0765.N1545.d006856 y n + _root_.GD.N0106.N0428.N0765.N1545.d006842 y n)).d006810
      (Real.cos y) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006860 hy hn
  have hR : ((_root_.GD.N0106.N0428.N0765.N1545.d006842 y n : ℚ) : ℝ) =
      |(y : ℝ)| ^ n * ((n.succ : ℝ) * ((n.factorial : ℝ) * n)⁻¹) := by
    rw [_root_.GD.N0106.N0428.N0765.N1545.d006844, div_eq_mul_inv]
  rw [← hR, abs_le] at h
  constructor
  · push_cast
    linarith [h.1]
  · push_cast
    linarith [h.2]


def d006862 (C : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 := ((_root_.GD.N0106.N0428.N0765.N1545.d006833 C).d006817 2).d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811

theorem d006863 {C : _root_.GD.N0232.N0720.N1164.d006809} {t : ℝ} (hC : C.d006810 (Real.cos t)) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006862 C).d006810 (Real.cos (2 * t)) := by
  rw [Real.cos_two_mul]
  have h := _root_.GD.N0232.N0720.N1164.d006809.d006820
    (_root_.GD.N0232.N0720.N1164.d006809.d006824 (2 : ℚ) (_root_.GD.N0106.N0428.N0765.N1545.d006834 hC)) _root_.GD.N0232.N0720.N1164.d006809.d006818
  have h2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [h2] at h
  exact h


def d006864 : ℕ → _root_.GD.N0232.N0720.N1164.d006809 → _root_.GD.N0232.N0720.N1164.d006809
  | 0, C => C
  | j + 1, C => _root_.GD.N0106.N0428.N0765.N1545.d006862 (d006864 j C)

theorem d006865 {C : _root_.GD.N0232.N0720.N1164.d006809} {t : ℝ} (hC : C.d006810 (Real.cos t))
    (j : ℕ) : (_root_.GD.N0106.N0428.N0765.N1545.d006864 j C).d006810 (Real.cos ((2 : ℝ) ^ j * t)) := by
  induction j with
  | zero => simpa [_root_.GD.N0106.N0428.N0765.N1545.d006864] using hC
  | succ j ih =>
    have h := _root_.GD.N0106.N0428.N0765.N1545.d006863 ih
    have e : (2 : ℝ) * ((2 : ℝ) ^ j * t) = (2 : ℝ) ^ (j + 1) * t := by ring
    rw [e] at h
    exact h



def d006866 (x : ℚ) (j n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1545.d006864 j ⟨_root_.GD.N0106.N0428.N0765.N1545.d006856 (x / 2 ^ j) n - _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ j) n,
    _root_.GD.N0106.N0428.N0765.N1545.d006856 (x / 2 ^ j) n + _root_.GD.N0106.N0428.N0765.N1545.d006842 (x / 2 ^ j) n⟩

theorem d006867 {x : ℚ} {j n : ℕ} (hx : |x / 2 ^ j| ≤ 1) (hn : 0 < n) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006866 x j n).d006810 (Real.cos x) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006865 (_root_.GD.N0106.N0428.N0765.N1545.d006861 hx hn) j
  have h2j : ((2 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ two_ne_zero
  have e : (2 : ℝ) ^ j * ((x / 2 ^ j : ℚ) : ℝ) = (x : ℝ) := by
    push_cast
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self h2j, mul_one]
  rw [e] at h
  exact h


def d006868 (A : _root_.GD.N0232.N0720.N1164.d006809) (j n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨(_root_.GD.N0106.N0428.N0765.N1545.d006866 A.hi j n).lo, (_root_.GD.N0106.N0428.N0765.N1545.d006866 A.lo j n).hi⟩

theorem d006869 {A : _root_.GD.N0232.N0720.N1164.d006809} {t : ℝ} {j n : ℕ} (hA : A.d006810 t)
    (h0 : 0 ≤ A.lo) (hpi : (A.hi : ℝ) ≤ Real.pi)
    (hlo : |A.lo / 2 ^ j| ≤ 1) (hhi : |A.hi / 2 ^ j| ≤ 1) (hn : 0 < n) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006868 A j n).d006810 (Real.cos t) := by
  have h1 := _root_.GD.N0106.N0428.N0765.N1545.d006867 hlo hn
  have h2 := _root_.GD.N0106.N0428.N0765.N1545.d006867 hhi hn
  have h0R : (0 : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h0
  have ht0 : 0 ≤ t := h0R.trans hA.1
  have c1 : Real.cos (A.hi : ℝ) ≤ Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht0 hpi hA.2
  have c2 : Real.cos t ≤ Real.cos (A.lo : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0R (hA.2.trans hpi) hA.1
  exact ⟨h2.1.trans c1, c2.trans h1.2⟩




noncomputable def d006870 (k : ℕ) : ℝ :=
  Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 28)


def d006871 (k : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006851.d006817 ((2 * k + 1 : ℚ) / 28)

theorem d006872 (k : ℕ) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006871 k).d006810 (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 28) := by
  have h := _root_.GD.N0232.N0720.N1164.d006809.d006824 ((2 * k + 1 : ℚ) / 28) _root_.GD.N0106.N0428.N0765.N1545.d006852
  have e : ((((2 * k + 1 : ℚ) / 28 : ℚ)) : ℝ) * Real.pi =
      ((2 * k + 1 : ℕ) : ℝ) * Real.pi / 28 := by
    push_cast
    ring
  rw [e] at h
  exact h


def d006873 (k j n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006868 (_root_.GD.N0106.N0428.N0765.N1545.d006871 k) j n

theorem d006874 (k j n : ℕ)
    (h0 : 0 ≤ (_root_.GD.N0106.N0428.N0765.N1545.d006871 k).lo) (hpi : (_root_.GD.N0106.N0428.N0765.N1545.d006871 k).hi ≤ _root_.GD.N0106.N0428.N0765.N1545.d006851.lo)
    (hlo : |(_root_.GD.N0106.N0428.N0765.N1545.d006871 k).lo / 2 ^ j| ≤ 1) (hhi : |(_root_.GD.N0106.N0428.N0765.N1545.d006871 k).hi / 2 ^ j| ≤ 1)
    (hn : 0 < n) :
    (_root_.GD.N0106.N0428.N0765.N1545.d006873 k j n).d006810 (_root_.GD.N0106.N0428.N0765.N1545.d006870 k) :=
  _root_.GD.N0106.N0428.N0765.N1545.d006869 (_root_.GD.N0106.N0428.N0765.N1545.d006872 k) h0 (_root_.GD.N0106.N0428.N0765.N1545.d006853 hpi) hlo hhi hn



theorem d006875 {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ ((m : ℝ) / 2) = Real.sqrt (x ^ m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring



theorem d006876 {C R : _root_.GD.N0232.N0720.N1164.d006809} {d : ℝ} (m : ℕ) (hC : C.d006810 (Real.cos d))
    (hCpos : 0 < C.lo) (hR0 : 0 ≤ R.lo) (hRle : R.lo ≤ R.hi)
    (hlower : R.lo ^ 2 ≤ (_root_.GD.N0106.N0428.N0765.N1545.d006835 m C.d006815).lo)
    (hupper : (_root_.GD.N0106.N0428.N0765.N1545.d006835 m C.d006815).hi ≤ R.hi ^ 2) :
    R.d006810 ((1 / Real.cos d) ^ ((m : ℝ) / 2)) := by
  have hinv := _root_.GD.N0232.N0720.N1164.d006809.d006822 hCpos hC
  have hChi : 0 < C.hi := lt_of_lt_of_le hCpos (_root_.GD.N0106.N0428.N0765.N1545.d006831 hC)
  have hinvlo : 0 ≤ C.d006815.lo := by
    show 0 ≤ 1 / C.hi
    exact div_nonneg zero_le_one hChi.le
  have hpow := _root_.GD.N0106.N0428.N0765.N1545.d006836 m hinvlo hinv
  have hcos : 0 < Real.cos d := by
    have h0 : (0 : ℝ) < (C.lo : ℝ) := by exact_mod_cast hCpos
    exact h0.trans_le hC.1
  have hx : 0 ≤ 1 / Real.cos d := div_nonneg zero_le_one hcos.le
  rw [_root_.GD.N0106.N0428.N0765.N1545.d006875 hx]
  exact _root_.GD.N0232.N0720.N1164.d006827 hpow hR0 hRle hlower hupper



theorem d006877 {K E : _root_.GD.N0232.N0720.N1164.d006809} {κ e : ℝ} (hK : K.d006810 κ) (hE : E.d006810 e)
    (hK0 : 0 ≤ K.lo) (hE1 : 0 < (E.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).lo) :
    ((K.d006814 (E.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006815).d006817 2).d006810 (2 * (κ * (1 / (e - 1)))) := by
  have h1 := _root_.GD.N0232.N0720.N1164.d006809.d006820 hE _root_.GD.N0232.N0720.N1164.d006809.d006818
  have h2 := _root_.GD.N0232.N0720.N1164.d006809.d006822 hE1 h1
  have hinvlo : 0 ≤ (E.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006815.lo := by
    show 0 ≤ 1 / (E.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).hi
    exact div_nonneg zero_le_one (hE1.trans_le (_root_.GD.N0106.N0428.N0765.N1545.d006831 h1)).le
  have h3 := _root_.GD.N0232.N0720.N1164.d006809.d006821 hK0 hinvlo hK h2
  have h4 := _root_.GD.N0232.N0720.N1164.d006809.d006824 (2 : ℚ) h3
  have h2R : ((2 : ℚ) : ℝ) = 2 := by norm_num
  rw [h2R] at h4
  exact h4

end GD.N0106.N0428.N0765.N1545

#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006830
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006832
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006834
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006836
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006838
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006845
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006847
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006849
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006850
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006852
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006858
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006860
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006861
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006863
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006867
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006869
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006874
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006875
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006876
#print axioms _root_.GD.N0106.N0428.N0765.N1545.d006877
