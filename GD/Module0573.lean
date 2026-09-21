import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0062
noncomputable section

theorem d008422 (z z₀ : ℝ) (hz : 0≤z) (hz₀ : 0<z₀) :
    z^2≤z₀^2+2/(3*z₀)*(z^3-z₀^3) := by
  have h := mul_nonneg (sq_nonneg (z-z₀)) (show 0≤2*z+z₀ by linarith)
  apply (mul_le_mul_iff_left₀ (show 0<3*z₀ by positivity)).mp
  field_simp
  nlinarith

private theorem d008423 (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    0≤7*x^9-9*y^2*x^7+2*y^9 := by
  have h : 0≤(x-y)^2*(7*x^7+14*x^6*y+12*x^5*y^2+10*x^4*y^3+
      8*x^3*y^4+6*x^2*y^5+4*x*y^6+2*y^7) := by positivity
  nlinarith only [h]

theorem d008424 (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (1/(b^3*Real.sqrt b))*(1-7/(2*b)*(a-b))≤1/(a^3*Real.sqrt a) := by
  have hsa : 0<Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0<Real.sqrt b := Real.sqrt_pos.2 hb
  have ha7 : (Real.sqrt a)^7=a^3*Real.sqrt a := by
    rw [show 7=2*3+1 by norm_num, pow_add, pow_mul, Real.sq_sqrt ha.le, pow_one]
  have ha9 : (Real.sqrt a)^9=a^4*Real.sqrt a := by
    rw [show 9=2*4+1 by norm_num, pow_add, pow_mul, Real.sq_sqrt ha.le, pow_one]
  have hb9 : (Real.sqrt b)^9=b^4*Real.sqrt b := by
    rw [show 9=2*4+1 by norm_num, pow_add, pow_mul, Real.sq_sqrt hb.le, pow_one]
  have hp := _root_.GD.N0062.d008423 (Real.sqrt a) (Real.sqrt b) hsa.le hsb.le
  rw [ha7,ha9,hb9,Real.sq_sqrt hb.le] at hp
  have heq : (1/(b^3*Real.sqrt b))*(1-7/(2*b)*(a-b))=
      (9*b-7*a)/(2*b^4*Real.sqrt b) := by field_simp; ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : 0<2*b^4*Real.sqrt b)
    (by positivity : 0<a^3*Real.sqrt a)).mpr
  nlinarith only [hp]



theorem d008425 (z z₀ A A₀ : ℝ) (hz : 0≤z) (hz₀ : 0<z₀)
    (hq : 0<z^2+A) (hq₀ : 0<z₀^2+A₀) :
    (1/((z₀^2+A₀)^3*Real.sqrt (z₀^2+A₀)))*
      (1-7/(2*(z₀^2+A₀))*((A-A₀)+2/(3*z₀)*(z^3-z₀^3))) ≤
      1/((z^2+A)^3*Real.sqrt (z^2+A)) := by
  have hc := _root_.GD.N0062.d008422 z z₀ hz hz₀
  have hp := _root_.GD.N0062.d008424 (z^2+A) (z₀^2+A₀) hq hq₀
  have hdiff : z^2+A-(z₀^2+A₀)≤(A-A₀)+2/(3*z₀)*(z^3-z₀^3) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff
    (by positivity : 0≤7/(2*(z₀^2+A₀)))
  have houter := mul_le_mul_of_nonneg_left (sub_le_sub_left hmul 1)
    (by positivity : 0≤1/((z₀^2+A₀)^3*Real.sqrt (z₀^2+A₀)))
  exact houter.trans hp

end
end GD.N0062

#print axioms _root_.GD.N0062.d008422
#print axioms _root_.GD.N0062.d008424
#print axioms _root_.GD.N0062.d008425
