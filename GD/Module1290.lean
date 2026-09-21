import GD.Module1288
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0106.N0428.N0765.N1564
noncomputable section

open MeasureTheory Set _root_.GD.N0106.N0428.N0765.N1616

private theorem d020996 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    0 ≤ v + eta * w + (1 + eta) * u := by
  have hew : 0 ≤ eta * w := (mul_pos heta hw).le
  have heu : 0 ≤ (1 + eta) * u := mul_nonneg (by linarith) hu
  linarith

theorem d020997 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    v ≤ _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c := by
  have hb := _root_.GD.N0106.N0428.N0765.N1564.d020996 heta hu hv hw
  have hew : 0 ≤ eta * w := (mul_pos heta hw).le
  have hr := (Real.exp_pos c).le
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  have h1 : 0 ≤ (v + eta * w + (1 + eta) * u) * Real.exp c := mul_nonneg hb hr
  have h2 : 0 ≤ eta * w * (Real.exp c) ^ 2 :=
    mul_nonneg hew (sq_nonneg _)
  linarith

theorem d020998 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    eta * w * (Real.exp c) ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c := by
  have hb := _root_.GD.N0106.N0428.N0765.N1564.d020996 heta hu hv hw
  have hr := (Real.exp_pos c).le
  have h1 : 0 ≤ (v + eta * w + (1 + eta) * u) * Real.exp c := mul_nonneg hb hr
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  linarith

private theorem d020999 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (a : ℝ) (n : ℕ) {c : ℝ} (hc : c ≤ 0) :
    Real.exp (a * c) * (1 + Real.exp c) ^ n *
        _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-21 / 2 : ℝ) ≤
      (2 : ℝ) ^ n * v ^ (-21 / 2 : ℝ) * Real.exp (a * c) := by
  have he : Real.exp c ≤ 1 := Real.exp_le_one_iff.mpr hc
  have hnum : (1 + Real.exp c) ^ n ≤ (2 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hden := Real.rpow_le_rpow_of_nonpos hv (_root_.GD.N0106.N0428.N0765.N1564.d020997 heta hu hv hw c)
    (by norm_num : (-21 / 2 : ℝ) ≤ 0)
  calc
    Real.exp (a * c) * (1 + Real.exp c) ^ n *
        _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-21 / 2 : ℝ) ≤
      Real.exp (a * c) * (1 + Real.exp c) ^ n * v ^ (-21 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hden
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by positivity) _))
    _ ≤ Real.exp (a * c) * (2 : ℝ) ^ n * v ^ (-21 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le)
        (Real.rpow_nonneg hv.le _)
    _ = _ := by ring

private theorem d021000 {eta w : ℝ} (heta : 0 < eta) (hw : 0 < w)
    (c : ℝ) :
    (eta * w * (Real.exp c) ^ 2) ^ (-21 / 2 : ℝ) =
      (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-21 * c) := by
  have hew : 0 < eta * w := mul_pos heta hw
  rw [Real.mul_rpow hew.le (sq_nonneg (Real.exp c))]
  have hs : ((Real.exp c) ^ 2) ^ (-21 / 2 : ℝ) = Real.exp (-21 * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.exp_pos c).le]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hs]

private theorem d021001 (a : ℝ) (n : ℕ)
    (hsum : a + (n : ℝ) = 31 / 2) (c : ℝ) :
    Real.exp (a * c) * (Real.exp c) ^ n * Real.exp (-21 * c) =
      Real.exp (-11 * c / 2) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  calc
    a * c + (n : ℝ) * c + -21 * c = (a + (n : ℝ) - 21) * c := by ring
    _ = -11 * c / 2 := by rw [hsum]; ring

private theorem d021002 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (a : ℝ) (n : ℕ) (hsum : a + (n : ℝ) = 31 / 2)
    {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (a * c) * (1 + Real.exp c) ^ n *
        _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-21 / 2 : ℝ) ≤
      (2 : ℝ) ^ n * (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-11 * c / 2) := by
  have he : 1 ≤ Real.exp c := Real.one_le_exp_iff.mpr hc
  have hnum : (1 + Real.exp c) ^ n ≤ (2 * Real.exp c) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hew : 0 < eta * w := mul_pos heta hw
  have hbase : 0 < eta * w * (Real.exp c) ^ 2 :=
    mul_pos hew (sq_pos_of_pos (Real.exp_pos c))
  have hden := Real.rpow_le_rpow_of_nonpos hbase
    (_root_.GD.N0106.N0428.N0765.N1564.d020998 heta hu hv hw c)
    (by norm_num : (-21 / 2 : ℝ) ≤ 0)
  calc
    Real.exp (a * c) * (1 + Real.exp c) ^ n *
        _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-21 / 2 : ℝ) ≤
      Real.exp (a * c) * (1 + Real.exp c) ^ n *
        (eta * w * (Real.exp c) ^ 2) ^ (-21 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hden
            (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by positivity) _))
    _ ≤ Real.exp (a * c) * (2 * Real.exp c) ^ n *
          (eta * w * (Real.exp c) ^ 2) ^ (-21 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le)
            (Real.rpow_nonneg hbase.le _)
    _ = (2 : ℝ) ^ n * (eta * w) ^ (-21 / 2 : ℝ) *
          (Real.exp (a * c) * (Real.exp c) ^ n * Real.exp (-21 * c)) := by
          rw [mul_pow, _root_.GD.N0106.N0428.N0765.N1564.d021000 heta hw c]
          ring
    _ = _ := by rw [_root_.GD.N0106.N0428.N0765.N1564.d021001 a n hsum c]

theorem d021003 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    {c : ℝ} (hc : c ≤ 0) :
    _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c ≤
      (2 : ℝ) ^ 10 * v ^ (-21 / 2 : ℝ) * Real.exp (11 * c / 2) := by
  have h := _root_.GD.N0106.N0428.N0765.N1564.d020999 heta hu hv hw (11 / 2) 10 hc
  simpa [_root_.GD.N0106.N0428.N0765.N1616.d020957, show (-21 / 2 : ℝ) = -(21 / 2) by ring, show (11 / 2 : ℝ) * c = 11 * c / 2 by ring] using h

theorem d021004 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    {c : ℝ} (hc : c ≤ 0) :
    _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c ≤
      (2 : ℝ) ^ 9 * v ^ (-21 / 2 : ℝ) * Real.exp (13 * c / 2) := by
  have h := _root_.GD.N0106.N0428.N0765.N1564.d020999 heta hu hv hw (13 / 2) 9 hc
  simpa [_root_.GD.N0106.N0428.N0765.N1616.d020958, show (-21 / 2 : ℝ) = -(21 / 2) by ring, show (13 / 2 : ℝ) * c = 13 * c / 2 by ring] using h

theorem d021005 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    {c : ℝ} (hc : 0 ≤ c) :
    _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c ≤
      (2 : ℝ) ^ 10 * (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-11 * c / 2) := by
  have h := _root_.GD.N0106.N0428.N0765.N1564.d021002 heta hu hv hw (11 / 2) 10 (by norm_num) hc
  simpa [_root_.GD.N0106.N0428.N0765.N1616.d020957, show (-21 / 2 : ℝ) = -(21 / 2) by ring, show (11 / 2 : ℝ) * c = 11 * c / 2 by ring] using h

theorem d021006 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    {c : ℝ} (hc : 0 ≤ c) :
    _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c ≤
      (2 : ℝ) ^ 9 * (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-11 * c / 2) := by
  have h := _root_.GD.N0106.N0428.N0765.N1564.d021002 heta hu hv hw (13 / 2) 9 (by norm_num) hc
  simpa [_root_.GD.N0106.N0428.N0765.N1616.d020958, show (-21 / 2 : ℝ) = -(21 / 2) by ring, show (13 / 2 : ℝ) * c = 13 * c / 2 by ring] using h

private theorem d021007 (eta u v w : ℝ) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w) := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  fun_prop

private theorem d021008 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) := by
  have hpow : Continuous (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-(21 / 2) : ℝ)) :=
    (_root_.GD.N0106.N0428.N0765.N1564.d021007 eta u v w).rpow_const
      (fun c => Or.inl (ne_of_gt (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c)))
  have hnum : Continuous (fun c : ℝ =>
      Real.exp (11 * c / 2) * (1 + Real.exp c) ^ 10) := by fun_prop
  exact hnum.mul hpow

private theorem d021009 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) := by
  have hpow : Continuous (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-(21 / 2) : ℝ)) :=
    (_root_.GD.N0106.N0428.N0765.N1564.d021007 eta u v w).rpow_const
      (fun c => Or.inl (ne_of_gt (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c)))
  have hnum : Continuous (fun c : ℝ =>
      Real.exp (13 * c / 2) * (1 + Real.exp c) ^ 9) := by fun_prop
  exact hnum.mul hpow

private theorem d021010 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hq := (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020957
  positivity

private theorem d021011 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hq := (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020958
  positivity

theorem d021012 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) := by
  have hf := _root_.GD.N0106.N0428.N0765.N1564.d021008 heta hu hv hw
  have hleft : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) (Iic (0 : ℝ)) := by
    have hg : IntegrableOn
        (fun c : ℝ => (2 : ℝ) ^ 10 * v ^ (-21 / 2 : ℝ) *
          Real.exp ((11 / 2 : ℝ) * c)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (a := (11 / 2 : ℝ)) (by norm_num) 0).const_mul _
    refine Integrable.mono' hg hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1564.d021010 heta hu hv hw c)]
    simpa [show (11 / 2 : ℝ) * c = 11 * c / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021003 heta hu hv hw hc
  have hright : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn
        (fun c : ℝ => (2 : ℝ) ^ 10 * (eta * w) ^ (-21 / 2 : ℝ) *
          Real.exp ((-11 / 2 : ℝ) * c)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := (-11 / 2 : ℝ)) (by norm_num) 0).const_mul _
    refine Integrable.mono' hg hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1564.d021010 heta hu hv hw c)]
    simpa [show (-11 / 2 : ℝ) * c = -11 * c / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021005 heta hu hv hw hc.le
  have hall := (integrableOn_union.mpr ⟨hleft, hright⟩)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hall

theorem d021013 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) := by
  have hf := _root_.GD.N0106.N0428.N0765.N1564.d021009 heta hu hv hw
  have hleft : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) (Iic (0 : ℝ)) := by
    have hg : IntegrableOn
        (fun c : ℝ => (2 : ℝ) ^ 9 * v ^ (-21 / 2 : ℝ) *
          Real.exp ((13 / 2 : ℝ) * c)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (a := (13 / 2 : ℝ)) (by norm_num) 0).const_mul _
    refine Integrable.mono' hg hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1564.d021011 heta hu hv hw c)]
    simpa [show (13 / 2 : ℝ) * c = 13 * c / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021004 heta hu hv hw hc
  have hright : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn
        (fun c : ℝ => (2 : ℝ) ^ 9 * (eta * w) ^ (-21 / 2 : ℝ) *
          Real.exp ((-11 / 2 : ℝ) * c)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := (-11 / 2 : ℝ)) (by norm_num) 0).const_mul _
    refine Integrable.mono' hg hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1564.d021011 heta hu hv hw c)]
    simpa [show (-11 / 2 : ℝ) * c = -11 * c / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021006 heta hu hv hw hc.le
  have hall := (integrableOn_union.mpr ⟨hleft, hright⟩)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hall

end
end GD.N0106.N0428.N0765.N1564

#print axioms _root_.GD.N0106.N0428.N0765.N1564.d020997
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d020998
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021003
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021004
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021005
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021006
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021012
#print axioms _root_.GD.N0106.N0428.N0765.N1564.d021013
