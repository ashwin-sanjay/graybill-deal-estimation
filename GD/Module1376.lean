import GD.Module0573
import GD.Module1358

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set

namespace GD.N0062
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

def d022142 (t u : ℝ) : ℝ := 2*(1-u)/(1-t)+2*u/t

theorem d022143 {t u : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hu : u∈Ioo (0:ℝ) 1) :
    0<_root_.GD.N0062.d022142 t u := by
  exact add_pos (div_pos (mul_pos (by norm_num) (sub_pos.mpr hu.2)) (sub_pos.mpr ht.2))
    (div_pos (mul_pos (by norm_num) hu.1) ht.1)

private theorem d022144 :
    Real.Gamma (7/2:ℝ)=(5/2)*(3/2)*Real.Gamma (3/2:ℝ) := by
  rw [show (7/2:ℝ)=5/2+1 by norm_num,Real.Gamma_add_one (by norm_num : (5/2:ℝ)≠0),
    show (5/2:ℝ)=3/2+1 by norm_num,Real.Gamma_add_one (by norm_num : (3/2:ℝ)≠0)]
  ring


theorem d022145 {t u s : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hu : u∈Ioo (0:ℝ) 1) (hs : 0<s) :
    _root_.GD.N0232.N0720.N1436.d013273 3 3 t (u,s)=
      15*Real.sqrt s/(t*(1-t)*(s+_root_.GD.N0062.d022142 t u)^3*Real.sqrt (s+_root_.GD.N0062.d022142 t u)) := by
  have hq : 0<s+_root_.GD.N0062.d022142 t u := add_pos hs (_root_.GD.N0062.d022143 ht hu)
  have h1t := sub_pos.mpr ht.2
  have hf : _root_.GD.N0232.N0720.N1436.d013207 3=1 := by norm_num [_root_.GD.N0232.N0720.N1436.d013207]
  have hg : _root_.GD.N0232.N0720.N1436.d013208 3=1 := by norm_num [_root_.GD.N0232.N0720.N1436.d013208]
  have htotal : _root_.GD.N0232.N0720.N1436.d013210 3 3=7/2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013210,hf,hg,_root_.GD.N0232.N0720.N1436.d013209]
  have hrate : _root_.GD.N0232.N0720.N1436.d013268 3 3 t (u,s)=(s+_root_.GD.N0062.d022142 t u)/2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013268,_root_.GD.N0232.N0720.N1436.d013267,_root_.GD.N0062.d022142]
    ring
  have hparam : _root_.GD.N0232.N0720.N1436.d013270 3 3 t=1/(t*(1-t)) := by
    rw [_root_.GD.N0232.N0720.N1436.d013270,hf,hg,Real.rpow_neg_one,Real.rpow_neg_one]
    simp [mul_inv_rev, mul_comm]
  have hshape : _root_.GD.N0232.N0720.N1436.d013269 3 3 (u,s)=Real.sqrt s := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013269,hf,hg,_root_.GD.N0232.N0720.N1436.d013209,← Real.sqrt_eq_rpow]
  have hnormal : _root_.GD.N0232.N0720.N1436.d013271 3 3=(1/2:ℝ)^(3/2:ℝ)/Real.Gamma (3/2:ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013271,hf,hg,_root_.GD.N0232.N0720.N1436.d013209]
  rw [_root_.GD.N0232.N0720.N1436.d013273,htotal,hrate,hparam,hshape,hnormal,_root_.GD.N0062.d022144]
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (by norm_num : (0:ℝ)<1/2),
    Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [show (7/2:ℝ)=3+1/2 by norm_num,Real.rpow_add (by positivity : 0<1/((s+_root_.GD.N0062.d022142 t u)/2)),
    Real.rpow_ofNat,← Real.sqrt_eq_rpow]
  rw [show 1/((s+_root_.GD.N0062.d022142 t u)/2)=2/(s+_root_.GD.N0062.d022142 t u) by field_simp,
    Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,
    Real.sqrt_div (by norm_num : (0:ℝ)≤2)]
  have hgamma := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<3/2)).ne'
  have hroot := (Real.sqrt_pos.2 hq).ne'
  have htwo := (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  field_simp
  ring


theorem d022146 {t u z : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hu : u∈Ioo (0:ℝ) 1) (hz : 0<z) :
    (2*z)*_root_.GD.N0232.N0720.N1436.d013273 3 3 t (u,z^2)=
      30*z^2/(t*(1-t)*(z^2+_root_.GD.N0062.d022142 t u)^3*Real.sqrt (z^2+_root_.GD.N0062.d022142 t u)) := by
  rw [_root_.GD.N0062.d022145 ht hu (sq_pos_of_pos hz),Real.sqrt_sq hz.le]
  ring

end
end GD.N0062

#print axioms _root_.GD.N0062.d022145
#print axioms _root_.GD.N0062.d022146
