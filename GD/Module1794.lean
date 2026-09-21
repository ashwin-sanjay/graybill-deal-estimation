import GD.Module0501
import GD.Module1296
import GD.Module1788
import GD.Module1768










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0765.N1545

namespace GD.N0106.N0428.N0765.N1620
open _root_.GD.N0106.N0428.N0765.N1621 _root_.GD.N0106.N0428.N0765.N1512 _root_.GD.N0106.N0428.N0765.N1538

noncomputable def d029846 (j : Fin 3) : ℝ := ![7 / 50, 0, 7 / 100] j
noncomputable def d029847 (j : Fin 3) : ℝ := ![0, 7 / 50, 7 / 100] j

def d029848 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(1 : ℚ), (1 : ℚ)⟩

theorem d029849 : _root_.GD.N0106.N0428.N0765.N1620.d029848.d006810 ((Real.cos ((0 : ℚ) : ℝ))⁻¹) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (0 : ℚ) 0 12).d006810 (Real.cos ((0 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel) hc
  simpa only [one_div] using
    (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := _root_.GD.N0106.N0428.N0765.N1620.d029848) hs (by decide +kernel) (by decide +kernel))

def d029850 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(1 : ℚ), (10000000001 / 10000000000 : ℚ)⟩

theorem d029851 : _root_.GD.N0106.N0428.N0765.N1620.d029850.d006810
    (Real.cos ((0 : ℚ) : ℝ) ^ (-((23 : ℝ) / 2))) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (0 : ℚ) 0 12).d006810 (Real.cos ((0 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs : _root_.GD.N0106.N0428.N0765.N1620.d029850.d006810 ((1 / Real.cos ((0 : ℚ) : ℝ)) ^ ((23 : ℝ) / 2)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006876 23 hc (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Real.rpow_neg_eq_inv_rpow, one_div] using hs

def d029852 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(10006128127 / 10000000000 : ℚ), (19543219 / 19531250 : ℚ)⟩

theorem d029853 : _root_.GD.N0106.N0428.N0765.N1620.d029852.d006810 ((Real.cos ((7 / 200 : ℚ) : ℝ))⁻¹) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (7 / 200 : ℚ) 0 12).d006810 (Real.cos ((7 / 200 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel) hc
  simpa only [one_div] using
    (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := _root_.GD.N0106.N0428.N0765.N1620.d029852) hs (by decide +kernel) (by decide +kernel))

def d029854 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(5035350321 / 5000000000 : ℚ), (10070700643 / 10000000000 : ℚ)⟩

theorem d029855 : _root_.GD.N0106.N0428.N0765.N1620.d029854.d006810
    (Real.cos ((7 / 200 : ℚ) : ℝ) ^ (-((23 : ℝ) / 2))) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (7 / 200 : ℚ) 0 12).d006810 (Real.cos ((7 / 200 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs : _root_.GD.N0106.N0428.N0765.N1620.d029854.d006810 ((1 / Real.cos ((7 / 200 : ℚ) : ℝ)) ^ ((23 : ℝ) / 2)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006876 23 hc (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Real.rpow_neg_eq_inv_rpow, one_div] using hs

def d029856 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(250613753 / 250000000 : ℚ), (10024550121 / 10000000000 : ℚ)⟩

theorem d029857 : _root_.GD.N0106.N0428.N0765.N1620.d029856.d006810 ((Real.cos ((7 / 100 : ℚ) : ℝ))⁻¹) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (7 / 100 : ℚ) 0 12).d006810 (Real.cos ((7 / 100 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel) hc
  simpa only [one_div] using
    (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := _root_.GD.N0106.N0428.N0765.N1620.d029856) hs (by decide +kernel) (by decide +kernel))

def d029858 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(10285993677 / 10000000000 : ℚ), (5142996839 / 5000000000 : ℚ)⟩

theorem d029859 : _root_.GD.N0106.N0428.N0765.N1620.d029858.d006810
    (Real.cos ((7 / 100 : ℚ) : ℝ) ^ (-((23 : ℝ) / 2))) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (7 / 100 : ℚ) 0 12).d006810 (Real.cos ((7 / 100 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs : _root_.GD.N0106.N0428.N0765.N1620.d029858.d006810 ((1 / Real.cos ((7 / 100 : ℚ) : ℝ)) ^ ((23 : ℝ) / 2)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006876 23 hc (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Real.rpow_neg_eq_inv_rpow, one_div] using hs

def d029860 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(3370040927 / 2500000000 : ℚ), (13480163711 / 10000000000 : ℚ)⟩

theorem d029861 : _root_.GD.N0106.N0428.N0765.N1620.d029860.d006810 ((Real.cos ((147 / 200 : ℚ) : ℝ))⁻¹) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (147 / 200 : ℚ) 0 12).d006810 (Real.cos ((147 / 200 : ℚ) : ℝ)) :=
    _root_.GD.N0106.N0428.N0765.N1545.d006867 (by decide +kernel) (by norm_num)
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel) hc
  simpa only [one_div] using
    (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := _root_.GD.N0106.N0428.N0765.N1620.d029860) hs (by decide +kernel) (by decide +kernel))

def d029862 (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 := ![_root_.GD.N0106.N0428.N0765.N1620.d029858, _root_.GD.N0106.N0428.N0765.N1620.d029850, _root_.GD.N0106.N0428.N0765.N1620.d029854] j
def d029863 (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 := ![_root_.GD.N0106.N0428.N0765.N1620.d029848, _root_.GD.N0106.N0428.N0765.N1620.d029856, _root_.GD.N0106.N0428.N0765.N1620.d029852] j
def d029864 (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006835 10 (_root_.GD.N0106.N0428.N0765.N1620.d029863 j)

theorem d029865 (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029862 j).d006810
    (Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029846 j / 2) ^ (-((23 : ℝ) / 2))) := by
  fin_cases j
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029859 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029862, _root_.GD.N0106.N0428.N0765.N1620.d029846]
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029851 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029862, _root_.GD.N0106.N0428.N0765.N1620.d029846]
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029855 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029862, _root_.GD.N0106.N0428.N0765.N1620.d029846]

theorem d029866 (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029863 j).d006810 ((Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029847 j / 2))⁻¹) := by
  fin_cases j
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029849 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029863, _root_.GD.N0106.N0428.N0765.N1620.d029847]
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029857 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029863, _root_.GD.N0106.N0428.N0765.N1620.d029847]
  · convert _root_.GD.N0106.N0428.N0765.N1620.d029853 using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029863, _root_.GD.N0106.N0428.N0765.N1620.d029847]

theorem d029867 (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029864 j).d006810
    (Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029847 j / 2) ^ (-(10 : ℝ))) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006836 10
    (by fin_cases j <;> decide +kernel : 0 ≤ (_root_.GD.N0106.N0428.N0765.N1620.d029863 j).lo) (_root_.GD.N0106.N0428.N0765.N1620.d029866 j)
  simpa only [_root_.GD.N0106.N0428.N0765.N1620.d029864, Real.rpow_neg_eq_inv_rpow, Real.rpow_ofNat, Real.rpow_natCast] using h

theorem d029868 (j : Fin 3) : _root_.GD.N0106.N0428.N0765.N1620.d029860.d006810 (_root_.GD.N0106.N0428.N0765.N1512.d029183 (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j)) := by
  fin_cases j <;> convert _root_.GD.N0106.N0428.N0765.N1620.d029861 using 1 <;>
    norm_num [_root_.GD.N0106.N0428.N0765.N1512.d029183, _root_.GD.N0106.N0428.N0765.N1538.d021231, _root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847]

def d029869 (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 := (_root_.GD.N0106.N0428.N0765.N1620.d029862 j).d006814 (_root_.GD.N0106.N0428.N0765.N1620.d029864 j)

theorem d029870 (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029869 j).d006810
    (Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029846 j / 2) ^ (-((23 : ℝ) / 2)) *
      Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029847 j / 2) ^ (-(10 : ℝ))) :=
  _root_.GD.N0232.N0720.N1164.d006809.d006821 (by fin_cases j <;> decide +kernel)
    (by fin_cases j <;> decide +kernel) (_root_.GD.N0106.N0428.N0765.N1620.d029865 j) (_root_.GD.N0106.N0428.N0765.N1620.d029867 j)

def d029871 (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ((_root_.GD.N0106.N0428.N0765.N1545.d006835 2 ((_root_.GD.N0106.N0428.N0765.N1620.d029863 j).d006812 _root_.GD.N0232.N0720.N1164.d006809.d006811)).d006812
    (_root_.GD.N0106.N0428.N0765.N1545.d006835 2 (_root_.GD.N0106.N0428.N0765.N1620.d029860.d006812 _root_.GD.N0232.N0720.N1164.d006809.d006811))).d006814 (_root_.GD.N0106.N0428.N0765.N1620.d029869 j)

theorem d029872 (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029871 j).d006810
    (_root_.GD.N0106.N0428.N0765.N1515.d029737 (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j)) := by
  have hb := _root_.GD.N0106.N0428.N0765.N1545.d006836 2 (by fin_cases j <;> decide +kernel :
    0 ≤ ((_root_.GD.N0106.N0428.N0765.N1620.d029863 j).d006812 _root_.GD.N0232.N0720.N1164.d006809.d006811).lo)
    (_root_.GD.N0232.N0720.N1164.d006809.d006819 (_root_.GD.N0106.N0428.N0765.N1620.d029866 j) _root_.GD.N0232.N0720.N1164.d006809.d006818)
  have hk := _root_.GD.N0106.N0428.N0765.N1545.d006836 2 (by decide +kernel : 0 ≤ (_root_.GD.N0106.N0428.N0765.N1620.d029860.d006812 _root_.GD.N0232.N0720.N1164.d006809.d006811).lo)
    (_root_.GD.N0232.N0720.N1164.d006809.d006819 (_root_.GD.N0106.N0428.N0765.N1620.d029868 j) _root_.GD.N0232.N0720.N1164.d006809.d006818)
  exact _root_.GD.N0232.N0720.N1164.d006809.d006821 (by fin_cases j <;> decide +kernel)
    (by fin_cases j <;> decide +kernel) (_root_.GD.N0232.N0720.N1164.d006809.d006819 hb hk)
    (_root_.GD.N0106.N0428.N0765.N1620.d029870 j)


theorem d029873 (j : Fin 3) :
    _root_.GD.N0106.N0428.N0765.N1515.d029737 (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) < (979 / 100 : ℝ) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1620.d029872 j
  have hb : (_root_.GD.N0106.N0428.N0765.N1620.d029871 j).hi < (979 / 100 : ℚ) := by fin_cases j <;> decide +kernel
  have hr : ((_root_.GD.N0106.N0428.N0765.N1620.d029871 j).hi : ℝ) < ((979 / 100 : ℚ) : ℝ) := by exact_mod_cast hb
  exact hc.2.trans_lt (by simpa using hr)

def d029874 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨1, 2685 / 14⟩
def d029875 (b : Bool) : ℕ := if b then 3 else 1
def d029876 (b : Bool) : _root_.GD.N0232.N0720.N1164.d006809 :=
  (_root_.GD.N0106.N0428.N0765.N1620.d029860.d006814 (_root_.GD.N0232.N0720.N1164.d006809.d006811.d006812 _root_.GD.N0106.N0428.N0765.N1620.d029860)).d006814
    (_root_.GD.N0106.N0428.N0765.N1545.d006835 (_root_.GD.N0106.N0428.N0765.N1620.d029875 b) (_root_.GD.N0106.N0428.N0765.N1620.d029860.d006812 (_root_.GD.N0106.N0428.N0765.N1545.d006828 (1 / 2))))

theorem d029877 (b : Bool) (j : Fin 3) : (_root_.GD.N0106.N0428.N0765.N1620.d029876 b).d006810
    (_root_.GD.N0106.N0428.N0765.N1512.d029143 (_root_.GD.N0106.N0428.N0765.N1620.d029875 b) (_root_.GD.N0106.N0428.N0765.N1512.d029183 (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j))) := by
  have hk := _root_.GD.N0106.N0428.N0765.N1620.d029868 j
  have hp := _root_.GD.N0106.N0428.N0765.N1545.d006836 (_root_.GD.N0106.N0428.N0765.N1620.d029875 b)
    (by decide +kernel : 0 ≤ (_root_.GD.N0106.N0428.N0765.N1620.d029860.d006812 (_root_.GD.N0106.N0428.N0765.N1545.d006828 (1 / 2))).lo)
    (_root_.GD.N0232.N0720.N1164.d006809.d006819 hk
      (by norm_num [_root_.GD.N0106.N0428.N0765.N1545.d006828, _root_.GD.N0232.N0720.N1164.d006809.d006810] : (_root_.GD.N0106.N0428.N0765.N1545.d006828 (1 / 2)).d006810 (1 / 2 : ℝ)))
  have hf := _root_.GD.N0232.N0720.N1164.d006809.d006821 (by decide +kernel) (by decide +kernel)
    hk (_root_.GD.N0232.N0720.N1164.d006809.d006819 _root_.GD.N0232.N0720.N1164.d006809.d006818 hk)
  exact _root_.GD.N0232.N0720.N1164.d006809.d006821 (by decide +kernel)
    (by cases b <;> decide +kernel) hf hp

def d029878 (b : Bool) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ((_root_.GD.N0232.N0720.N1164.d006809.d006811.d006812 _root_.GD.N0106.N0428.N0765.N1620.d029874).d006817 (1 / 11)).d006814
    ((_root_.GD.N0106.N0428.N0765.N1620.d029860.d006812 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006814 (_root_.GD.N0106.N0428.N0765.N1620.d029876 b))

theorem d029879 (b : Bool) (j : Fin 3) {eta : ℝ}
    (heta : 1 ≤ eta) (hmax : eta ≤ 2685 / 14) :
    (_root_.GD.N0106.N0428.N0765.N1620.d029878 b).d006810 (_root_.GD.N0106.N0428.N0765.N1512.d029197 (_root_.GD.N0106.N0428.N0765.N1620.d029875 b) eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j)) := by
  have he : _root_.GD.N0106.N0428.N0765.N1620.d029874.d006810 eta := by
    constructor
    · simpa [_root_.GD.N0106.N0428.N0765.N1620.d029874] using heta
    · simpa [_root_.GD.N0106.N0428.N0765.N1620.d029874] using hmax
  have h1 := _root_.GD.N0232.N0720.N1164.d006809.d006824 (1 / 11 : ℚ)
    (_root_.GD.N0232.N0720.N1164.d006809.d006819 _root_.GD.N0232.N0720.N1164.d006809.d006818 he)
  have h2 := _root_.GD.N0232.N0720.N1164.d006809.d006821 (by decide +kernel)
    (by cases b <;> decide +kernel)
    (_root_.GD.N0232.N0720.N1164.d006809.d006819 (_root_.GD.N0106.N0428.N0765.N1620.d029868 j) _root_.GD.N0232.N0720.N1164.d006809.d006818)
    (_root_.GD.N0106.N0428.N0765.N1620.d029877 b j)
  have h3 := _root_.GD.N0232.N0720.N1164.d006809.d006821 (by decide +kernel)
    (by cases b <;> decide +kernel) h1 h2
  convert h3 using 1
  · rfl
  · unfold _root_.GD.N0106.N0428.N0765.N1512.d029197
    push_cast
    ring

def d029880 (channel : Bool) (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if channel then (_root_.GD.N0106.N0428.N0765.N1620.d029863 j).d006814 ((_root_.GD.N0232.N0720.N1164.d006809.d006811.d006812 _root_.GD.N0106.N0428.N0765.N1620.d029874).d006817 (5 / 3))
  else _root_.GD.N0232.N0720.N1164.d006809.d006811

theorem d029881 (channel : Bool) (j : Fin 3) {eta : ℝ}
    (heta : 1 ≤ eta) (hmax : eta ≤ 2685 / 14) :
    (_root_.GD.N0106.N0428.N0765.N1620.d029880 channel j).d006810
      (if channel then (Real.cos (_root_.GD.N0106.N0428.N0765.N1620.d029847 j / 2))⁻¹ * ((5 / 3) * (1 + eta)) else 1) := by
  have he : _root_.GD.N0106.N0428.N0765.N1620.d029874.d006810 eta := by
    constructor
    · simpa [_root_.GD.N0106.N0428.N0765.N1620.d029874] using heta
    · simpa [_root_.GD.N0106.N0428.N0765.N1620.d029874] using hmax
  cases channel
  · exact _root_.GD.N0232.N0720.N1164.d006809.d006818
  · convert (_root_.GD.N0232.N0720.N1164.d006809.d006821 (by fin_cases j <;> decide +kernel)
      (by decide +kernel) (_root_.GD.N0106.N0428.N0765.N1620.d029866 j)
      (_root_.GD.N0232.N0720.N1164.d006809.d006824 (5 / 3 : ℚ) (_root_.GD.N0232.N0720.N1164.d006809.d006819 _root_.GD.N0232.N0720.N1164.d006809.d006818 he)))
      using 1 <;> norm_num [_root_.GD.N0106.N0428.N0765.N1620.d029880]

def d029882 (b channel : Bool) (j : Fin 3) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ((_root_.GD.N0106.N0428.N0765.N1620.d029878 b).d006814 (_root_.GD.N0106.N0428.N0765.N1620.d029869 j)).d006814 (_root_.GD.N0106.N0428.N0765.N1620.d029880 channel j)

theorem d029883 (b channel : Bool) (j : Fin 3) {eta : ℝ}
    (heta : 1 ≤ eta) (hmax : eta ≤ 2685 / 14) :
    (_root_.GD.N0106.N0428.N0765.N1620.d029882 b channel j).d006810 (_root_.GD.N0106.N0428.N0765.N1512.d029199 channel (_root_.GD.N0106.N0428.N0765.N1620.d029875 b) eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j)) := by
  have h := _root_.GD.N0232.N0720.N1164.d006809.d006821 (by cases b <;> decide +kernel)
    (by fin_cases j <;> decide +kernel)
    (_root_.GD.N0106.N0428.N0765.N1620.d029879 b j heta hmax) (_root_.GD.N0106.N0428.N0765.N1620.d029870 j)
  exact _root_.GD.N0232.N0720.N1164.d006809.d006821 (by cases b <;> fin_cases j <;> decide +kernel)
    (by cases channel <;> fin_cases j <;> decide +kernel) h
    (_root_.GD.N0106.N0428.N0765.N1620.d029881 channel j heta hmax)


theorem d029884 (channel : Bool) (k : ℕ) (hk : k = 1 ∨ k = 3)
    (j : Fin 3) {eta : ℝ} (heta : 1 ≤ eta) (hmax : eta ≤ 2685 / 14) :
    _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) < (272000 : ℝ) := by
  have hsmall (b : Bool) : _root_.GD.N0106.N0428.N0765.N1512.d029199 channel (_root_.GD.N0106.N0428.N0765.N1620.d029875 b) eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) < (272000 : ℝ) := by
    have hc := _root_.GD.N0106.N0428.N0765.N1620.d029883 b channel j heta hmax
    have hb : (_root_.GD.N0106.N0428.N0765.N1620.d029882 b channel j).hi < (272000 : ℚ) := by
      cases b <;> cases channel <;> fin_cases j <;> decide +kernel
    exact hc.2.trans_lt (by exact_mod_cast hb)
  rcases hk with rfl | rfl
  · exact hsmall false
  · exact hsmall true


theorem d029885 :
    _root_.GD.N0106.N0428.N0765.N1562.d021061 (7 / 50) (1 / 40) <
      (117 / 100000000000000000 : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1621.d007638
  simpa only [_root_.GD.N0106.N0428.N0765.N1562.d021061,
    show (-21 / 2 : ℝ) = -((21 : ℝ) / 2) by ring,
    Real.rpow_neg_eq_inv_rpow, one_div] using h




theorem d029886 (j : Fin 3) :
    ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) < Real.pi := by
  fin_cases j <;> norm_num [_root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] <;> linarith [Real.pi_gt_three]

private theorem d029887 {A B C M : ℝ} (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) :
    (2 * A + 2 * B) / (Real.exp (2 * Real.pi * (7 / 50) / (1 / 40)) - 1) +
      4 * C / (Real.exp (2 * Real.pi * (7 / 100) / (1 / 40)) - 1) ^ 2 ≤
      _root_.GD.N0106.N0428.N0765.N1621.d007639 M := by
  have hd : 0 ≤ Real.exp (2 * Real.pi * (7 / 50 : ℝ) / (1 / 40)) - 1 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).le
  unfold _root_.GD.N0106.N0428.N0765.N1621.d007639
  exact add_le_add (div_le_div_of_nonneg_right (by linarith) hd)
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

theorem d029888 {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1515.d029738 eta (1 / 40) (7 / 50) (7 / 100) <
      (503 / 10000000000000000 : ℝ) := by
  have hb (j : Fin 3) : _root_.GD.N0106.N0428.N0765.N1515.d029736 eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) ≤ 12 := by
    have h := (_root_.GD.N0106.N0428.N0765.N1515.d029762 heta (_root_.GD.N0106.N0428.N0765.N1620.d029886 j)).trans_lt
      (_root_.GD.N0106.N0428.N0765.N1620.d029873 j)
    linarith
  have h0 : _root_.GD.N0106.N0428.N0765.N1515.d029736 eta (7 / 50) 0 ≤ 12 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 0
  have h1 : _root_.GD.N0106.N0428.N0765.N1515.d029736 eta 0 (7 / 50) ≤ 12 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 1
  have h2 : _root_.GD.N0106.N0428.N0765.N1515.d029736 eta (7 / 100) (7 / 100) ≤ 12 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 2
  exact (_root_.GD.N0106.N0428.N0765.N1620.d029887 h0 h1 h2).trans_lt _root_.GD.N0106.N0428.N0765.N1621.d007642


theorem d029889 (location : ℝ) {eta : ℝ} (heta : 0 < eta)
    (a₀ b₀ : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
      (1 / 40 : ℝ) ^ 2 * (∑' p : ℤ × ℤ,
        _root_.GD.N0106.N0428.N0765.N1515.d029732 eta
          (a₀ + (1 / 40) * p.1, b₀ + (1 / 40) * p.2))| <
        (503 / 10000000000000000 : ℝ) := by
  exact (_root_.GD.N0106.N0428.N0765.N1515.d029764 location heta
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]) a₀ b₀).trans_lt
      (_root_.GD.N0106.N0428.N0765.N1620.d029888 heta)


theorem d029890 (channel : Bool) (k : Fin 5)
    (hk : k.val = 1 ∨ k.val = 3) (location : ℝ) {eta : ℝ}
    (heta : 1 ≤ eta) (hmax : eta ≤ 2685 / 14) (a₀ b₀ : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0) -
      (1 / 40 : ℝ) ^ 2 * (∑' p : ℤ × ℤ,
        _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta
          (a₀ + (1 / 40) * p.1, b₀ + (1 / 40) * p.2))| <
        (126 / 100000000000 : ℝ) := by
  have hb (j : Fin 3) : _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta (_root_.GD.N0106.N0428.N0765.N1620.d029846 j) (_root_.GD.N0106.N0428.N0765.N1620.d029847 j) ≤ 300000 := by
    have h := _root_.GD.N0106.N0428.N0765.N1620.d029884 channel k.val hk j heta hmax
    linarith
  have h0 : _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta (7 / 50) 0 ≤ 300000 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 0
  have h1 : _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta 0 (7 / 50) ≤ 300000 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 1
  have h2 : _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta (7 / 100) (7 / 100) ≤ 300000 := by
    simpa [_root_.GD.N0106.N0428.N0765.N1620.d029846, _root_.GD.N0106.N0428.N0765.N1620.d029847] using hb 2
  exact (_root_.GD.N0106.N0428.N0765.N1513.d029317 channel k location heta
    (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]) a₀ b₀).trans_lt
      ((_root_.GD.N0106.N0428.N0765.N1620.d029887 h0 h1 h2).trans_lt _root_.GD.N0106.N0428.N0765.N1621.d007643)

end GD.N0106.N0428.N0765.N1620

#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029865
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029866
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029867
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029868
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029872
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029873
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029877
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029879
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029881
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029883
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029884
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029885
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029886
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029888
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029889
#print axioms _root_.GD.N0106.N0428.N0765.N1620.d029890
