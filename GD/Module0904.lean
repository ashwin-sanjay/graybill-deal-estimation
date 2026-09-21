import GD.Module0903

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set

namespace GD.N0028
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

def d014055 : ℝ := _root_.GD.N0232.N0720.N1436.d013271 2 5*Real.Gamma 4
def d014056 : ℝ := 1/(2*Real.sqrt 2)
def d014057 : ℝ := 1/(8:ℝ)^4
def d014058 : ℝ := _root_.GD.N0028.d014055*_root_.GD.N0028.d014056*_root_.GD.N0028.d014057

theorem d014059 : 0<_root_.GD.N0028.d014055 :=
  mul_pos (_root_.GD.N0232.N0720.N1436.d013284 (by omega) (by omega))
    (Real.Gamma_pos_of_pos (by norm_num))
theorem d014060 : 0<_root_.GD.N0028.d014056 := by unfold _root_.GD.N0028.d014056; positivity
theorem d014061 : 0<_root_.GD.N0028.d014057 := by norm_num [_root_.GD.N0028.d014057]
theorem d014062 : 0<_root_.GD.N0028.d014058 :=
  mul_pos (mul_pos _root_.GD.N0028.d014059 _root_.GD.N0028.d014060) _root_.GD.N0028.d014061

theorem d014063 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013273 2 5 t z = _root_.GD.N0028.d014055*
      _root_.GD.N0232.N0720.N1436.d013270 2 5 t*_root_.GD.N0232.N0720.N1436.d013269 2 5 z /
        _root_.GD.N0232.N0720.N1436.d013268 2 5 t z^4 := by
  have ht : _root_.GD.N0232.N0720.N1436.d013210 2 5=4 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013210,_root_.GD.N0232.N0720.N1436.d013207,_root_.GD.N0232.N0720.N1436.d013208,_root_.GD.N0232.N0720.N1436.d013209]
  unfold _root_.GD.N0232.N0720.N1436.d013273 _root_.GD.N0028.d014055
  rw [ht,Real.rpow_ofNat,one_div,inv_pow]
  ring

theorem d014064 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    _root_.GD.N0028.d014056*r^2/q ≤ _root_.GD.N0232.N0720.N1436.d013269 2 5 z := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := h.1
  have hr0 := h.2.1
  have hb := _root_.GD.N0028.d014051 q r hq hr z hz
  have hU := sub_pos.mpr hb.1.1.2
  have hsU := Real.sqrt_pos.mpr hU
  have hs : Real.sqrt (1-z.1) ≤ Real.sqrt 2*q/r := by
    calc
      _ ≤ Real.sqrt (2*q^2/r^2) := Real.sqrt_le_sqrt hb.2.2.2
      _ = _ := by
        rw [Real.sqrt_div (by positivity : 0≤2*q^2),Real.sqrt_mul (by norm_num),
          Real.sqrt_sq hq0.le,Real.sqrt_sq hr0.le]
  have hw : r≤Real.sqrt z.2 := by
    have hh := Real.sqrt_le_sqrt hz.2.1
    rwa [Real.sqrt_sq hr0.le] at hh
  have hinv : r/(Real.sqrt 2*q)≤(Real.sqrt (1-z.1))⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hsU).mpr
    have hmul := mul_le_mul_of_nonneg_left hs
      (by positivity : 0≤r/(Real.sqrt 2*q))
    have heq : r/(Real.sqrt 2*q)*(Real.sqrt 2*q/r)=1 := by field_simp
    linarith
  have hform : _root_.GD.N0232.N0720.N1436.d013269 2 5 z =
      (Real.sqrt (1-z.1))⁻¹*z.1*Real.sqrt z.2 := by
    norm_num only [_root_.GD.N0232.N0720.N1436.d013269,_root_.GD.N0232.N0720.N1436.d013207,_root_.GD.N0232.N0720.N1436.d013208,_root_.GD.N0232.N0720.N1436.d013209,
      Nat.reduceSub,Nat.cast_ofNat]
    rw [Real.rpow_neg hU.le,← Real.sqrt_eq_rpow,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hform]
  calc
    _ = (r/(Real.sqrt 2*q))*(1/2)*r := by unfold _root_.GD.N0028.d014056; ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul hinv hb.2.1 (by norm_num) (inv_nonneg.mpr hsU.le)) hw hr0.le
      (mul_nonneg (inv_nonneg.mpr hsU.le) hb.1.1.1.le)

theorem d014065 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r) :
    r^4 ≤ _root_.GD.N0232.N0720.N1436.d013270 2 5 (_root_.GD.N0028.d014048 q r hq hr) := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hr0 := h.2.1
  have ht := (_root_.GD.N0028.d014048 q r hq hr).property
  have hfirst : 1≤(1-(_root_.GD.N0028.d014048 q r hq hr:ℝ))^(-(1/2:ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr ht.2) (by linarith [ht.1])
      (by norm_num)
  have hp : (1/r^2)^(-(2:ℝ))=r^4 := by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    field_simp
  have heq : _root_.GD.N0232.N0720.N1436.d013270 2 5 (_root_.GD.N0028.d014048 q r hq hr)=
      (1-(_root_.GD.N0028.d014048 q r hq hr:ℝ))^(-(1/2:ℝ))*(1/r^2)^(-(2:ℝ)) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013270,_root_.GD.N0232.N0720.N1436.d013207,_root_.GD.N0232.N0720.N1436.d013208,_root_.GD.N0028.d014048]
  rw [heq,hp]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfirst (pow_nonneg hr0.le 4)

theorem d014066 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r) :
    r^2/q ≤ _root_.GD.N0232.N0720.N1436.d013270 2 5 (_root_.GD.N0028.d014049 q r hq hr) := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := h.1
  have hr0 := h.2.1
  have ht := (_root_.GD.N0028.d014049 q r hq hr).property
  have hsecond : 1≤(_root_.GD.N0028.d014049 q r hq hr:ℝ)^(-(2:ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le (by norm_num)
  have hp : (q^2/r^4)^(-(1/2:ℝ))=r^2/q := by
    rw [Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow,Real.sqrt_div (sq_nonneg q),
      Real.sqrt_sq hq0.le,show r^4=(r^2)^2 by ring,Real.sqrt_sq (sq_nonneg r)]
    field_simp
  have heq : _root_.GD.N0232.N0720.N1436.d013270 2 5 (_root_.GD.N0028.d014049 q r hq hr)=
      (q^2/r^4)^(-(1/2:ℝ))*(_root_.GD.N0028.d014049 q r hq hr:ℝ)^(-(2:ℝ)) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013270,_root_.GD.N0232.N0720.N1436.d013207,_root_.GD.N0232.N0720.N1436.d013208,_root_.GD.N0028.d014049]
  rw [heq,hp]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsecond (by positivity : 0≤r^2/q)

theorem d014067 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r)
    (hbound : _root_.GD.N0232.N0720.N1436.d013268 2 5 t z≤8*r^2) :
    _root_.GD.N0028.d014057/r^8 ≤ (_root_.GD.N0232.N0720.N1436.d013268 2 5 t z^4)⁻¹ := by
  have hr0 := (_root_.GD.N0028.d014047 q r hq hr).2.1
  have hp := _root_.GD.N0232.N0720.N1436.d013281 (by omega : 2≤2) (by omega : 2≤5)
    t.property.1 t.property.2 (_root_.GD.N0028.d014051 q r hq hr z hz).1
  have heq : _root_.GD.N0028.d014057/r^8=((8*r^2)^4)⁻¹ := by unfold _root_.GD.N0028.d014057; ring
  rw [heq]
  exact inv_anti₀ (pow_pos hp 4) (pow_le_pow_left₀ hp.le hbound 4)

theorem d014068 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r)
    (hbound : _root_.GD.N0232.N0720.N1436.d013268 2 5 t z≤8*r^2)
    (P : ℝ) (hparam : P≤_root_.GD.N0232.N0720.N1436.d013270 2 5 t) :
    _root_.GD.N0028.d014055*P*(_root_.GD.N0028.d014056*r^2/q)*(_root_.GD.N0028.d014057/r^8) ≤
      _root_.GD.N0232.N0720.N1436.d013273 2 5 t z := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := h.1
  have hr0 := h.2.1
  have hp := _root_.GD.N0232.N0720.N1436.d013283 (m:=2) (n:=5) t.property.1 t.property.2
  have hs := _root_.GD.N0232.N0720.N1436.d013282 (m:=2) (n:=5) (_root_.GD.N0028.d014051 q r hq hr z hz).1
  have ho := _root_.GD.N0028.d014060
  have hrad := _root_.GD.N0028.d014061
  rw [_root_.GD.N0028.d014063,div_eq_mul_inv]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hparam _root_.GD.N0028.d014059.le)
      (_root_.GD.N0028.d014064 q r hq hr z hz) (by positivity)
      (mul_nonneg _root_.GD.N0028.d014059.le hp.le))
    (_root_.GD.N0028.d014067 q r hq hr t z hz hbound) (by positivity)
    (mul_nonneg (mul_nonneg _root_.GD.N0028.d014059.le hp.le) hs.le)

theorem d014069 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    _root_.GD.N0028.d014058/(q*r^2) ≤ _root_.GD.N0232.N0720.N1436.d013273 2 5 (_root_.GD.N0028.d014048 q r hq hr) z := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := h.1
  have hr0 := h.2.1
  calc
    _ = _root_.GD.N0028.d014055*r^4*(_root_.GD.N0028.d014056*r^2/q)*(_root_.GD.N0028.d014057/r^8) := by
      unfold _root_.GD.N0028.d014058
      field_simp
    _ ≤ _ := _root_.GD.N0028.d014068 q r hq hr _ z hz (_root_.GD.N0028.d014053 q r hq hr z hz)
      (r^4) (_root_.GD.N0028.d014065 q r hq hr)

theorem d014070 (q r : ℝ) (hq : 2≤q) (hr : 2*q≤r)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z∈_root_.GD.N0028.d014050 q r) :
    _root_.GD.N0028.d014058/(q^2*r^4) ≤ _root_.GD.N0232.N0720.N1436.d013273 2 5 (_root_.GD.N0028.d014049 q r hq hr) z := by
  have h := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := h.1
  have hr0 := h.2.1
  calc
    _ = _root_.GD.N0028.d014055*(r^2/q)*(_root_.GD.N0028.d014056*r^2/q)*(_root_.GD.N0028.d014057/r^8) := by
      unfold _root_.GD.N0028.d014058
      field_simp
    _ ≤ _ := _root_.GD.N0028.d014068 q r hq hr _ z hz (_root_.GD.N0028.d014054 q r hq hr z hz)
      (r^2/q) (_root_.GD.N0028.d014066 q r hq hr)

end
end GD.N0028

#print axioms _root_.GD.N0028.d014069
#print axioms _root_.GD.N0028.d014070
