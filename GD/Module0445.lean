import Mathlib










open Set
namespace GD.N0232.N0720.N1164




structure d006809 where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

namespace d006809


def d006810 (I : _root_.GD.N0232.N0720.N1164.d006809) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def d006811 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨1, 1⟩

def d006812 (I J : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

def d006813 (I J : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨I.lo - J.hi, I.hi - J.lo⟩



def d006814 (I J : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨I.lo * J.lo, I.hi * J.hi⟩


def d006815 (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨1 / I.hi, 1 / I.lo⟩



def d006816 (I J : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if 0 ≤ I.lo then
    _root_.GD.N0232.N0720.N1164.d006809.d006814 I J
  else if I.hi ≤ 0 then
    ⟨I.lo * J.hi, I.hi * J.lo⟩
  else
    ⟨I.lo * J.hi, I.hi * J.hi⟩



def d006817 (c : ℚ) (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if 0 ≤ c then ⟨c * I.lo, c * I.hi⟩
  else ⟨c * I.hi, c * I.lo⟩

theorem d006818 : _root_.GD.N0232.N0720.N1164.d006809.d006811.d006810 (1 : ℝ) := by
  norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006811, _root_.GD.N0232.N0720.N1164.d006809.d006810]

theorem d006819
    {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ}
    (hx : I.d006810 x) (hy : J.d006810 y) :
    (I.d006812 J).d006810 (x + y) := by
  constructor <;> norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006812, _root_.GD.N0232.N0720.N1164.d006809.d006810] at hx hy ⊢ <;> linarith

theorem d006820
    {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ}
    (hx : I.d006810 x) (hy : J.d006810 y) :
    (I.d006813 J).d006810 (x - y) := by
  constructor <;> norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006813, _root_.GD.N0232.N0720.N1164.d006809.d006810] at hx hy ⊢ <;> linarith

theorem d006821
    {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ}
    (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (hx : I.d006810 x) (hy : J.d006810 y) :
    (I.d006814 J).d006810 (x * y) := by
  have hI0 : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hI
  have hJ0 : (0 : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hJ
  have hx0 : 0 ≤ x := hI0.trans hx.1
  have hy0 : 0 ≤ y := hJ0.trans hy.1
  constructor
  · norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006814, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    exact mul_le_mul hx.1 hy.1 hJ0 hx0
  · norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006814, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    exact mul_le_mul hx.2 hy.2 hy0 (hx0.trans hx.2)

theorem d006822
    {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ}
    (hI : 0 < I.lo) (hx : I.d006810 x) :
    I.d006815.d006810 (1 / x) := by
  have hI0 : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
  have hx0 : 0 < x := hI0.trans_le hx.1
  constructor
  · norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006815, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    simpa only [one_div] using one_div_le_one_div_of_le hx0 hx.2
  · norm_num [_root_.GD.N0232.N0720.N1164.d006809.d006815, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    simpa only [one_div] using one_div_le_one_div_of_le hI0 hx.1

theorem d006823
    {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ}
    (hJ : 0 ≤ J.lo)
    (hx : I.d006810 x) (hy : J.d006810 y) :
    (I.d006816 J).d006810 (x * y) := by
  have hJ0 : (0 : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hJ
  have hy0 : 0 ≤ y := hJ0.trans hy.1
  have hJhi0 : 0 ≤ (J.hi : ℝ) := hy0.trans hy.2
  by_cases hIlo : 0 ≤ I.lo
  · simp only [_root_.GD.N0232.N0720.N1164.d006809.d006816, if_pos hIlo]
    exact _root_.GD.N0232.N0720.N1164.d006809.d006821 hIlo hJ hx hy
  · have hIloR : (I.lo : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_not_ge hIlo)
    by_cases hIhi : I.hi ≤ 0
    · have hIhiR : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hIhi
      simp only [_root_.GD.N0232.N0720.N1164.d006809.d006816, if_neg hIlo, if_pos hIhi, _root_.GD.N0232.N0720.N1164.d006809.d006810]
      constructor
      · norm_num
        calc
          (I.lo : ℝ) * (J.hi : ℝ) ≤ (I.lo : ℝ) * y :=
            mul_le_mul_of_nonpos_left hy.2 hIloR
          _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      · norm_num
        calc
          x * y ≤ (I.hi : ℝ) * y :=
            mul_le_mul_of_nonneg_right hx.2 hy0
          _ ≤ (I.hi : ℝ) * (J.lo : ℝ) :=
            mul_le_mul_of_nonpos_left hy.1 hIhiR
    · have hIhiR : (0 : ℝ) ≤ (I.hi : ℝ) := by
        exact_mod_cast (le_of_not_ge hIhi)
      simp only [_root_.GD.N0232.N0720.N1164.d006809.d006816, if_neg hIlo, if_neg hIhi, _root_.GD.N0232.N0720.N1164.d006809.d006810]
      constructor
      · norm_num
        by_cases hxsign : 0 ≤ x
        · exact (mul_nonpos_of_nonpos_of_nonneg hIloR hJhi0).trans
            (mul_nonneg hxsign hy0)
        · have hxnonpos : x ≤ 0 := le_of_not_ge hxsign
          calc
            (I.lo : ℝ) * (J.hi : ℝ) ≤ (I.lo : ℝ) * y :=
              mul_le_mul_of_nonpos_left hy.2 hIloR
            _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      · norm_num
        by_cases hxsign : x ≤ 0
        · exact (mul_nonpos_of_nonpos_of_nonneg hxsign hy0).trans
            (mul_nonneg hIhiR hJhi0)
        · have hxpos : 0 ≤ x := le_of_not_ge hxsign
          exact mul_le_mul hx.2 hy.2 hy0 hIhiR

theorem d006824
    (c : ℚ) {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} (hx : I.d006810 x) :
    (I.d006817 c).d006810 ((c : ℝ) * x) := by
  by_cases hc : 0 ≤ c
  · have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    simp only [_root_.GD.N0232.N0720.N1164.d006809.d006817, if_pos hc, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    constructor <;> norm_num
    · exact mul_le_mul_of_nonneg_left hx.1 hcR
    · exact mul_le_mul_of_nonneg_left hx.2 hcR
  · have hcR : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hc)
    simp only [_root_.GD.N0232.N0720.N1164.d006809.d006817, if_neg hc, _root_.GD.N0232.N0720.N1164.d006809.d006810]
    constructor <;> norm_num
    · exact mul_le_mul_of_nonpos_left hx.2 hcR
    · exact mul_le_mul_of_nonpos_left hx.1 hcR

end d006809







def d006825 (a b : ℚ) : Decidable (a < b) :=
  decidable_of_iff
    (a.num * b.den < b.num * a.den) (Rat.lt_iff a b).symm


def d006826 (a b : ℚ) : Decidable (a ≤ b) :=
  decidable_of_iff
    (a.num * b.den ≤ b.num * a.den) (Rat.le_iff a b).symm

theorem d006827
    {I R : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ}
    (hx : I.d006810 x)
    (hR0 : 0 ≤ R.lo) (hRle : R.lo ≤ R.hi)
    (hlower : R.lo ^ 2 ≤ I.lo)
    (hupper : I.hi ≤ R.hi ^ 2) :
    R.d006810 (Real.sqrt x) := by
  have hLowerSq : (R.lo : ℝ) ^ 2 ≤ x := by
    have hlowerR : (R.lo : ℝ) ^ 2 ≤ (I.lo : ℝ) := by
      exact_mod_cast hlower
    exact hlowerR.trans hx.1
  have hUpperSq : x ≤ (R.hi : ℝ) ^ 2 := by
    have hupperR : (I.hi : ℝ) ≤ (R.hi : ℝ) ^ 2 := by
      exact_mod_cast hupper
    exact hx.2.trans hupperR
  have hRhi : (0 : ℝ) ≤ (R.hi : ℝ) := by
    exact_mod_cast hR0.trans hRle
  exact ⟨Real.le_sqrt_of_sq_le hLowerSq,
    (Real.sqrt_le_iff).2 ⟨hRhi, hUpperSq⟩⟩

end GD.N0232.N0720.N1164

#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006818
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006819
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006820
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006821
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006822
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006823
#print axioms _root_.GD.N0232.N0720.N1164.d006809.d006824
#print axioms _root_.GD.N0232.N0720.N1164.d006827
