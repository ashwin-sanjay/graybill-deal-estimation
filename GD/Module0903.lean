import GD.Module0884

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0028
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

theorem d014047 (q r : ℝ) (hq : 2 ≤ q) (hr : 2*q ≤ r) :
    0<q ∧ 0<r ∧ 4≤r^2 ∧ 0<1/r^2 ∧ 1/r^2≤1/4 ∧
      0<q^2/r^2 ∧ q^2/r^2≤1/4 ∧ 0<q^2/r^4 ∧ q^2/r^4≤1/4 := by
  have hq0 : 0<q := by linarith
  have hr0 : 0<r := by linarith
  have hsq : 4*q^2 ≤ r^2 := by nlinarith
  have hr2 : 4≤r^2 := by nlinarith
  have hdelta : q^2/r^2≤1/4 := (div_le_iff₀ (sq_pos_of_pos hr0)).mpr (by nlinarith)
  have hsmall : q^2/r^4 ≤ q^2/r^2 := div_le_div_of_nonneg_left (sq_nonneg q)
    (sq_pos_of_pos hr0) (by nlinarith [sq_nonneg (r^2-1)])
  exact ⟨hq0,hr0,hr2,by positivity,
    one_div_le_one_div_of_le (by norm_num) hr2, by positivity,hdelta,
    by positivity,hsmall.trans hdelta⟩

def d014048 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1/r^2, by have h := _root_.GD.N0028.d014047 q r hq hr; exact ⟨h.2.2.2.1, by linarith [h.2.2.2.2.1]⟩⟩

def d014049 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1-q^2/r^4, by
    have h := _root_.GD.N0028.d014047 q r hq hr
    constructor <;> linarith [h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2]⟩

def d014050 (q r : ℝ) : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Icc (1-2*q^2/r^2) (1-q^2/r^2) ×ˢ Icc (r^2) (2*r^2)

theorem d014051 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    z∈_root_.GD.N0232.N0720.N1436.d013218 ∧ (1/2:ℝ)≤z.1 ∧ q^2/r^2≤1-z.1 ∧ 1-z.1≤2*q^2/r^2 := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hδp := h.2.2.2.2.2.1
  have hδu := h.2.2.2.2.2.2.1
  have hhalf : (1/2:ℝ)≤z.1 := by
    have hzlo := hz.1.1
    rw [show 2*q^2/r^2=2*(q^2/r^2) by ring] at hzlo
    linarith
  have hz1 : z.1<1 := by linarith [hz.1.2]
  refine ⟨⟨⟨by linarith,hz1⟩,(sq_pos_of_pos h.2.1).trans_le hz.2.1⟩,hhalf,?_,?_⟩
  · linarith [hz.1.2]
  · linarith [hz.1.1]

theorem d014052 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r) :
    _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0028.d014050 q r)=ENNReal.ofReal (q^2) := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hr0 := h.2.1
  have hs : MeasurableSet (_root_.GD.N0028.d014050 q r) := measurableSet_Icc.prod measurableSet_Icc
  rw [_root_.GD.N0232.N0720.N1436.d013288,Measure.restrict_apply hs,
    inter_eq_self_of_subset_left (fun z hz => (_root_.GD.N0028.d014051 q r hq hr z hz).1),
    _root_.GD.N0028.d014050,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc,Real.volume_Icc,
    show (1-q^2/r^2)-(1-2*q^2/r^2)=q^2/r^2 by ring,
    show 2*r^2-r^2=r^2 by ring,
    ← ENNReal.ofReal_mul (by positivity : 0≤q^2/r^2)]
  congr 1
  field_simp

theorem d014053 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    _root_.GD.N0232.N0720.N1436.d013268 2 5 (_root_.GD.N0028.d014048 q r hq hr) z ≤ 8*r^2 := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hzD := (_root_.GD.N0028.d014051 q r hq hr z hz).1
  have hfirst : (1-z.1)/(1-1/r^2)≤2 := by
    apply (div_le_iff₀ (by linarith [h.2.2.2.2.1])).mpr
    linarith [hzD.1.1,h.2.2.2.2.1]
  have hsecond : 4*z.1/(1/r^2)≤4*r^2 := by
    rw [div_div_eq_mul_div,div_one]
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hzD.1.2.le)]
  have heq : _root_.GD.N0232.N0720.N1436.d013268 2 5 (_root_.GD.N0028.d014048 q r hq hr) z =
      (z.2+(1-z.1)/(1-1/r^2)+4*z.1/(1/r^2))/2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013268,_root_.GD.N0232.N0720.N1436.d013267,_root_.GD.N0028.d014048]
  rw [heq]
  nlinarith [hz.2.2,h.2.2.1]

theorem d014054 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    _root_.GD.N0232.N0720.N1436.d013268 2 5 (_root_.GD.N0028.d014049 q r hq hr) z ≤ 8*r^2 := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hr0 := h.2.1
  have hzb := _root_.GD.N0028.d014051 q r hq hr z hz
  have hfirst : (1-z.1)/(q^2/r^4)≤2*r^2 := by
    apply (div_le_iff₀ h.2.2.2.2.2.2.2.1).mpr
    calc
      _ ≤ 2*q^2/r^2 := hzb.2.2.2
      _ = _ := by field_simp
  have hsecond : 4*z.1/(1-q^2/r^4)≤8 := by
    apply (div_le_iff₀ (by linarith [h.2.2.2.2.2.2.2.2])).mpr
    linarith [hzb.1.1.2,h.2.2.2.2.2.2.2.2]
  have heq : _root_.GD.N0232.N0720.N1436.d013268 2 5 (_root_.GD.N0028.d014049 q r hq hr) z =
      (z.2+(1-z.1)/(q^2/r^4)+4*z.1/(1-q^2/r^4))/2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013268,_root_.GD.N0232.N0720.N1436.d013267,_root_.GD.N0028.d014049]
  rw [heq]
  nlinarith [hz.2.2,h.2.2.1]

end
end GD.N0028

#print axioms _root_.GD.N0028.d014052
#print axioms _root_.GD.N0028.d014053
#print axioms _root_.GD.N0028.d014054
