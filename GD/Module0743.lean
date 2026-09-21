


























import GD.Module0731
import GD.Module0079

open Filter MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0864

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0230.N0655
open _root_.GD.N0232.N0719.N0828
open _root_.GD.N0230.N0641

variable (k : ℕ) (sizes : Fin k → ℕ)



theorem d011071 (loc s x : ℝ) (hs : 0 < s) :
    gaussianPDFReal loc (_root_.GD.N0232.N0719.N0932.d009193 s) x
      = s⁻¹ * gaussianPDFReal 0 1 x *
          Real.exp (x ^ 2 / 2 - (x - loc) ^ 2 / (2 * s ^ 2)) := by
  unfold gaussianPDFReal
  rw [_root_.GD.N0232.N0719.N0932.d009194]
  have hsq : Real.sqrt (2 * Real.pi * s ^ 2) = Real.sqrt (2 * Real.pi) * s := by
    rw [Real.sqrt_mul (by positivity) (s ^ 2), Real.sqrt_sq hs.le]
  rw [hsq]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hexp : Real.exp (-x ^ 2 / 2) *
      Real.exp (x ^ 2 / 2 - (x - loc) ^ 2 / (2 * s ^ 2))
        = Real.exp (-(x - loc) ^ 2 / (2 * s ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hexp, mul_inv]
  ring

theorem d011072 (loc s x : ℝ) (hs : 0 < s) :
    _root_.GD.N0232.N0719.N0932.d009204 loc s x
      = s⁻¹ * Real.exp (x ^ 2 / 2 - (x - loc) ^ 2 / (2 * s ^ 2)) := by
  have h0 : 0 < gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x one_ne_zero
  have h1 : 0 ≤ gaussianPDFReal loc (_root_.GD.N0232.N0719.N0932.d009193 s) x := gaussianPDFReal_nonneg _ _ _
  unfold _root_.GD.N0232.N0719.N0932.d009204 _root_.GD.N0232.N0719.N0932.d009197 gaussianPDF
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h0.le,
    _root_.GD.N0232.N0719.N0864.d011071 loc s x hs]
  field_simp


theorem d011073 (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 (-((2 : ℝ)⁻¹ * 0)) (2 : ℝ)⁻¹ x ≤ 2 := by
  rw [_root_.GD.N0232.N0719.N0864.d011072 _ _ _ (by norm_num)]
  have hE : x ^ 2 / 2 - (x - -((2 : ℝ)⁻¹ * 0)) ^ 2 / (2 * ((2 : ℝ)⁻¹) ^ 2) ≤ 0 := by
    norm_num
    nlinarith [sq_nonneg x]
  calc ((2 : ℝ)⁻¹)⁻¹ * Real.exp (x ^ 2 / 2 - (x - -((2 : ℝ)⁻¹ * 0)) ^ 2 / (2 * ((2 : ℝ)⁻¹) ^ 2))
      ≤ ((2 : ℝ)⁻¹)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hE) (by norm_num)
    _ = 2 := by norm_num



theorem d011074 (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 (-((3 : ℝ)⁻¹ * 1)) (3 : ℝ)⁻¹ x ≤ 3 * Real.exp (1 / 16) := by
  rw [_root_.GD.N0232.N0719.N0864.d011072 _ _ _ (by norm_num)]
  have hE : x ^ 2 / 2 - (x - -((3 : ℝ)⁻¹ * 1)) ^ 2 / (2 * ((3 : ℝ)⁻¹) ^ 2) ≤ 1 / 16 := by
    norm_num
    nlinarith [sq_nonneg (2 * x + 3 / 4)]
  calc ((3 : ℝ)⁻¹)⁻¹ * Real.exp (x ^ 2 / 2 - (x - -((3 : ℝ)⁻¹ * 1)) ^ 2 / (2 * ((3 : ℝ)⁻¹) ^ 2))
      ≤ ((3 : ℝ)⁻¹)⁻¹ * Real.exp (1 / 16) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (by norm_num)
    _ = 3 * Real.exp (1 / 16) := by norm_num



theorem d011075 (loc s x : ℝ) (hs : s ≠ 0) :
    0 < _root_.GD.N0232.N0719.N0932.d009204 loc s x :=
  ENNReal.toReal_pos (_root_.GD.N0232.N0719.N0932.d009200 loc s x hs).ne'
    (_root_.GD.N0232.N0719.N0932.d009199 loc s x)

theorem d011076 (g : _root_.GD.N0230.N0655.d000349)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 < _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega := by
  unfold _root_.GD.N0232.N0719.N0828.d010991 _root_.GD.N0232.N0719.N0932.d009219
    _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  exact _root_.GD.N0232.N0719.N0864.d011075 _ _ _
    (inv_ne_zero (ne_of_gt g.2.property))


theorem d011077 (g : _root_.GD.N0230.N0655.d000349) {c : ℝ}
    (hc0 : 0 ≤ c)
    (hc : ∀ x, _root_.GD.N0232.N0719.N0932.d009204 (_root_.GD.N0232.N0719.N0842.d010906 g.1 (g.2 : ℝ)) ((g.2 : ℝ)⁻¹) x ≤ c)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega ≤ c ^ (∑ i, sizes i) := by
  unfold _root_.GD.N0232.N0719.N0828.d010991 _root_.GD.N0232.N0719.N0932.d009219
    _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  calc (∏ i, ∏ j, _root_.GD.N0232.N0719.N0932.d009204 (_root_.GD.N0232.N0719.N0828.d010989 k g).1
          ((_root_.GD.N0232.N0719.N0828.d010989 k g).2 i) (omega i j))
      ≤ ∏ i : Fin k, ∏ _j : Fin (sizes i), c := by
        refine Finset.prod_le_prod
          (fun i _ => Finset.prod_nonneg fun j _ => _root_.GD.N0232.N0719.N0932.d009205 _ _ _)
          (fun i _ => Finset.prod_le_prod
            (fun j _ => _root_.GD.N0232.N0719.N0932.d009205 _ _ _)
            (fun j _ => hc _))
    _ = ∏ i : Fin k, c ^ (sizes i) := by
        simp [Finset.prod_const]
    _ = c ^ (∑ i, sizes i) := Finset.prod_pow_eq_pow_sum _ _ _


def d011078 : _root_.GD.N0230.N0655.d000349 := (0, ⟨2, by norm_num⟩)
def d011079 : _root_.GD.N0230.N0655.d000349 := (1, ⟨3, by norm_num⟩)

theorem d011080 (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0828.d010991 k sizes _root_.GD.N0232.N0719.N0864.d011078 omega ≤ 2 ^ (∑ i, sizes i) :=
  _root_.GD.N0232.N0719.N0864.d011077 k sizes _root_.GD.N0232.N0719.N0864.d011078 (by norm_num)
    (fun x => _root_.GD.N0232.N0719.N0864.d011073 x) omega

theorem d011081 (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0828.d010991 k sizes _root_.GD.N0232.N0719.N0864.d011079 omega
      ≤ (3 * Real.exp (1 / 16)) ^ (∑ i, sizes i) :=
  _root_.GD.N0232.N0719.N0864.d011077 k sizes _root_.GD.N0232.N0719.N0864.d011079 (by positivity)
    (fun x => _root_.GD.N0232.N0719.N0864.d011074 x) omega



theorem d011082 (g : _root_.GD.N0230.N0655.d000349) :
    Measurable (_root_.GD.N0232.N0719.N0828.d010991 k sizes g) := by
  unfold _root_.GD.N0232.N0719.N0828.d010991
  exact _root_.GD.N0232.N0719.N0932.d009220 k sizes _ _



theorem d011083 (g : _root_.GD.N0230.N0655.d000349) {C : ℝ}
    (hlik : ∀ omega, _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega ≤ C)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    ∫⁻ omega, ENNReal.ofReal
        ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal C *
          ∫⁻ omega, ENNReal.ofReal ((d omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
  have hF : Measurable fun omega => ENNReal.ofReal ((d omega) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hd.pow_const 2)
  have hinv : Measurable (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ)) :=
    _root_.GD.N0232.N0719.N0842.d010908 k sizes _ _
  have hw : Measurable fun omega =>
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0828.d010991 k sizes g omega) :=
    ENNReal.measurable_ofReal.comp (_root_.GD.N0232.N0719.N0864.d011082 k sizes g)
  calc ∫⁻ omega, ENNReal.ofReal
        ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      = ∫⁻ omega, ENNReal.ofReal ((d omega) ^ 2)
          ∂((_root_.GD.N0232.N0719.d009182 k sizes).map (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ))) :=
        (lintegral_map hF hinv).symm
    _ = ∫⁻ omega, ENNReal.ofReal (_root_.GD.N0232.N0719.N0828.d010991 k sizes g omega) *
          ENNReal.ofReal ((d omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
        rw [_root_.GD.N0232.N0719.N0828.d010998 k sizes g,
          lintegral_withDensity_eq_lintegral_mul _ hw hF]
        rfl
    _ ≤ ∫⁻ omega, ENNReal.ofReal C * ENNReal.ofReal ((d omega) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes) :=
        lintegral_mono fun omega =>
          mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hlik omega)) _
    _ = ENNReal.ofReal C *
          ∫⁻ omega, ENNReal.ofReal ((d omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) :=
        lintegral_const_mul _ hF


theorem d011084 (g : _root_.GD.N0230.N0655.d000349) {C : ℝ}
    (hlik : ∀ omega, _root_.GD.N0232.N0719.N0828.d010991 k sizes g omega ≤ C)
    (d d' : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) (hd' : Measurable d') :
    ∫⁻ omega, ENNReal.ofReal
        ((_root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 (g.2 : ℝ) d omega
          - _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 (g.2 : ℝ) d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal ((g.2 : ℝ) ^ 2 * C) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
  have hpt : ∀ omega, ENNReal.ofReal
      ((_root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 (g.2 : ℝ) d omega
        - _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 (g.2 : ℝ) d' omega) ^ 2)
      = ENNReal.ofReal ((g.2 : ℝ) ^ 2) *
          ENNReal.ofReal
            ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)
              - d' (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2) := by
    intro omega
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold _root_.GD.N0232.N0719.N0842.d010911
    ring
  simp_rw [hpt]
  have hmeas : Measurable fun omega => ENNReal.ofReal
      ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)
        - d' (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2) :=
    ENNReal.measurable_ofReal.comp (((hd.sub hd').comp
      (_root_.GD.N0232.N0719.N0842.d010908 k sizes _ _)).pow_const 2)
  rw [lintegral_const_mul _ hmeas]
  have h : ∫⁻ omega, ENNReal.ofReal
      ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)
        - d' (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal C *
          ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) :=
    _root_.GD.N0232.N0719.N0864.d011083 k sizes g hlik (fun ω => d ω - d' ω) (hd.sub hd')
  calc ENNReal.ofReal ((g.2 : ℝ) ^ 2) *
        ∫⁻ omega, ENNReal.ofReal
          ((d (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)
            - d' (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)) ^ 2)
            ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal ((g.2 : ℝ) ^ 2) *
          (ENNReal.ofReal C *
            ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes)) :=
        mul_le_mul_left' h _
    _ = ENNReal.ofReal ((g.2 : ℝ) ^ 2 * C) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]


theorem d011085
    (d d' : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) (hd' : Measurable d') :
    ∫⁻ omega, ENNReal.ofReal
        ((_root_.GD.N0232.N0719.N0842.d010911 k sizes 0 2 d omega - _root_.GD.N0232.N0719.N0842.d010911 k sizes 0 2 d' omega) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal (4 * 2 ^ (∑ i, sizes i)) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
  have h := _root_.GD.N0232.N0719.N0864.d011084 k sizes _root_.GD.N0232.N0719.N0864.d011078
    (_root_.GD.N0232.N0719.N0864.d011080 k sizes) d d' hd hd'
  have hc : ENNReal.ofReal ((_root_.GD.N0232.N0719.N0864.d011078.2 : ℝ) ^ 2 * 2 ^ (∑ i, sizes i))
      = ENNReal.ofReal (4 * 2 ^ (∑ i, sizes i)) := by
    norm_num [_root_.GD.N0232.N0719.N0864.d011078]
  rw [hc] at h
  exact h



theorem d011086
    (d d' : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) (hd' : Measurable d') :
    ∫⁻ omega, ENNReal.ofReal
        ((_root_.GD.N0232.N0719.N0842.d010911 k sizes 1 3 d omega - _root_.GD.N0232.N0719.N0842.d010911 k sizes 1 3 d' omega) ^ 2)
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      ≤ ENNReal.ofReal (9 * (3 * Real.exp (1 / 16)) ^ (∑ i, sizes i)) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - d' omega) ^ 2) ∂(_root_.GD.N0232.N0719.d009182 k sizes) := by
  have h := _root_.GD.N0232.N0719.N0864.d011084 k sizes _root_.GD.N0232.N0719.N0864.d011079
    (_root_.GD.N0232.N0719.N0864.d011081 k sizes) d d' hd hd'
  have hc : ENNReal.ofReal ((_root_.GD.N0232.N0719.N0864.d011079.2 : ℝ) ^ 2 *
        (3 * Real.exp (1 / 16)) ^ (∑ i, sizes i))
      = ENNReal.ofReal (9 * (3 * Real.exp (1 / 16)) ^ (∑ i, sizes i)) := by
    norm_num [_root_.GD.N0232.N0719.N0864.d011079]
  rw [hc] at h
  exact h






theorem d011087 (g : _root_.GD.N0230.N0655.d000349)
    (F : _root_.GD.N0232.N0719.d009173 k sizes → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ omega, F (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega) *
        (ENNReal.ofReal (_root_.GD.N0232.N0719.N0828.d010991 k sizes g
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega)))⁻¹
          ∂(_root_.GD.N0232.N0719.d009182 k sizes)
      = ∫⁻ omega, F omega ∂(_root_.GD.N0232.N0719.d009182 k sizes) :=
  _root_.GD.N0230.N0641.d001049 (_root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ))
    (_root_.GD.N0232.N0719.N0842.d010908 k sizes _ _)
    (fun omega => ENNReal.ofReal (_root_.GD.N0232.N0719.N0828.d010991 k sizes g omega))
    (ENNReal.measurable_ofReal.comp (_root_.GD.N0232.N0719.N0864.d011082 k sizes g))
    (_root_.GD.N0232.N0719.N0828.d010998 k sizes g)
    (Filter.Eventually.of_forall fun omega =>
      (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0719.N0864.d011076 k sizes g omega)).ne')
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
    F hF



#print axioms _root_.GD.N0232.N0719.N0864.d011072
#print axioms _root_.GD.N0232.N0719.N0864.d011073
#print axioms _root_.GD.N0232.N0719.N0864.d011074
#print axioms _root_.GD.N0232.N0719.N0864.d011080
#print axioms _root_.GD.N0232.N0719.N0864.d011081
#print axioms _root_.GD.N0232.N0719.N0864.d011083
#print axioms _root_.GD.N0232.N0719.N0864.d011085
#print axioms _root_.GD.N0232.N0719.N0864.d011086
#print axioms _root_.GD.N0232.N0719.N0864.d011087

end N0864
end N0719
end N0232
end GD
