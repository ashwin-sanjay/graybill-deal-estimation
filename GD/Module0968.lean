import GD.Module0967
import GD.Module0932
import GD.Module0105





















open MeasureTheory Filter
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1028

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1027
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0668
open _root_.GD.N0230.N0644
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229



section Abstract

variable {G Theta Rule : Type*} [Group G] [MulAction G Theta]



def d015319
    (crossTax : Theta → Rule → Rule → ℝ)
    (character : G → ℝ) (r s : Rule) : Prop :=
  ∀ (g : G) (theta : Theta),
    crossTax (g • theta) r s = character g * crossTax theta r s



def d015320
    (risk : Theta → Rule → ℝ) (crossTax : Theta → Rule → Rule → ℝ)
    (lambda : ℝ) (r s repair : Rule) : Prop :=
  ∀ theta,
    risk theta repair =
      (1 - lambda) * risk theta r + lambda * risk theta s -
        lambda * (1 - lambda) * crossTax theta r s



theorem d015321
    (risk : Theta → Rule → ℝ) (crossTax : Theta → Rule → Rule → ℝ)
    (character : G → ℝ) (lambda : ℝ) (r s repair : Rule)
    (hr : _root_.GD.N0232.N0720.N1027.d015301 risk character r)
    (hs : _root_.GD.N0232.N0720.N1027.d015301 risk character s)
    (htax : _root_.GD.N0232.N0720.N1028.d015319 crossTax character r s)
    (hidentity : _root_.GD.N0232.N0720.N1028.d015320
      risk crossTax lambda r s repair) :
    _root_.GD.N0232.N0720.N1027.d015301 risk character repair := by
  intro g theta
  rw [hidentity, hidentity, hr, hs, htax]
  ring





theorem d015322
    (risk : Theta → Rule → ℝ) (crossTax : Theta → Rule → Rule → ℝ)
    (character : G → ℝ) (lambda : ℝ) (r s repair : Rule)
    (hr : _root_.GD.N0232.N0720.N1027.d015301 risk character r)
    (hs : _root_.GD.N0232.N0720.N1027.d015301 risk character s)
    (hidentity : _root_.GD.N0232.N0720.N1028.d015320
      risk crossTax lambda r s repair)
    (hcoefficient : lambda * (1 - lambda) ≠ 0) :
    _root_.GD.N0232.N0720.N1028.d015319 crossTax character r s ↔
      _root_.GD.N0232.N0720.N1027.d015301 risk character repair := by
  constructor
  · intro htax
    exact _root_.GD.N0232.N0720.N1028.d015321
      risk crossTax character lambda r s repair hr hs htax hidentity
  · intro hrepair g theta
    have hrepairAt := hrepair g theta
    rw [hidentity, hidentity, hr, hs] at hrepairAt
    have hscaled :
        (lambda * (1 - lambda)) * crossTax (g • theta) r s =
          (lambda * (1 - lambda)) *
            (character g * crossTax theta r s) := by
      linear_combination -hrepairAt
    exact mul_left_cancel₀ hcoefficient hscaled

end Abstract




noncomputable def d015323
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  ∫⁻ omega, ENNReal.ofReal ((r omega - s omega) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta



def d015324
    (lambda : ℝ) (r s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ (1 - lambda) * r omega + lambda * s omega


theorem d015325
    (lambda : ℝ) {r s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hr : Measurable r) (hs : Measurable s) :
    Measurable (_root_.GD.N0232.N0720.N1028.d015324 (m := m) (n := n) lambda r s) := by
  unfold _root_.GD.N0232.N0720.N1028.d015324
  fun_prop




theorem d015326
    (lambda : ℝ) {r s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hr : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) r)
    (hs : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) s) :
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
      (_root_.GD.N0232.N0720.N1028.d015324 (m := m) (n := n) lambda r s) := by
  intro g omega
  unfold _root_.GD.N0232.N0720.N1028.d015324
  rw [hr g omega, hs g omega]
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
  ring





theorem d015327
    (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {r s : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hrMeasurable : Measurable r) (hsMeasurable : Measurable s)
    (hr : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) r)
    (hs : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) s) :
    _root_.GD.N0232.N0720.N1028.d015323 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) r s =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1028.d015323 m n theta r s := by
  have hmap := _root_.GD.N0232.N0720.N1215.d014282 m n g theta
  unfold _root_.GD.N0232.N0720.N1028.d015323
  rw [← hmap, lintegral_map]
  · calc
      (∫⁻ omega,
          ENNReal.ofReal
            ((r (_root_.GD.N0107.d009024
                m n g.shift g.d009239 g.d009239 omega) -
              s (_root_.GD.N0107.d009024
                m n g.shift g.d009239 g.d009239 omega)) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫⁻ omega,
          ENNReal.ofReal (g.d009239 ^ 2) *
            ENNReal.ofReal ((r omega - s omega) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
            apply lintegral_congr
            intro omega
            have hrOmega :
                r (_root_.GD.N0107.d009024
                  m n g.shift g.d009239 g.d009239 omega) = g • r omega := by
              simpa only [_root_.GD.N0232.N0720.N1214.d014259]
                using hr g omega
            have hsOmega :
                s (_root_.GD.N0107.d009024
                  m n g.shift g.d009239 g.d009239 omega) = g • s omega := by
              simpa only [_root_.GD.N0232.N0720.N1214.d014259]
                using hs g omega
            rw [hrOmega, hsOmega]
            simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
            have hreal :
                ((g.shift + g.d009239 * r omega) -
                  (g.shift + g.d009239 * s omega)) ^ 2 =
                  g.d009239 ^ 2 * (r omega - s omega) ^ 2 := by ring
            rw [hreal, ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
          ∫⁻ omega, ENNReal.ofReal ((r omega - s omega) ^ 2)
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
        rw [lintegral_const_mul]
        fun_prop
  · exact ENNReal.measurable_ofReal.comp
      ((hrMeasurable.sub hsMeasurable).pow_const 2)
  · exact _root_.GD.N0107.d009026
      m n g.shift g.d009239 g.d009239





noncomputable def d015328
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1028.d015323 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q)




theorem d015329
    (m n : ℕ) (lambda : ℝ)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0668.d001343 lambda p q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1028.d015324 (m := m) (n := n) lambda
        (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q) := by
  have href :
      _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0668.d001343 lambda p q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1028.d015324 (m := m) (n := n) lambda
          (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014265 m n q) := by
    filter_upwards [
      _root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0230.N0668.d001343 lambda p q),
      _root_.GD.N0232.N0720.N1214.d014267 m n p,
      _root_.GD.N0232.N0720.N1214.d014267 m n q,
      Lp.coeFn_add ((1 - lambda) • p) (lambda • q),
      Lp.coeFn_smul (1 - lambda) p,
      Lp.coeFn_smul lambda q] with
        omega hrepair hp hq hadd hsmulP hsmulQ
    rw [hrepair]
    unfold _root_.GD.N0230.N0668.d001343 _root_.GD.N0232.N0720.N1028.d015324
    simp only [hadd, hsmulP, hsmulQ, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hp, hq]
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq href



theorem d015330
    (m n : ℕ) (lambda : ℝ)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014652 m n q) :
    _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0230.N0668.d001343 lambda p q) := by
  obtain ⟨rp, hrpMeasurable, hrpClass, hrpEquivariant⟩ := hp
  obtain ⟨rq, hrqMeasurable, hrqClass, hrqEquivariant⟩ := hq
  refine ⟨_root_.GD.N0232.N0720.N1028.d015324 (m := m) (n := n) lambda rp rq,
    _root_.GD.N0232.N0720.N1028.d015325 (m := m) (n := n) lambda
      hrpMeasurable hrqMeasurable,
    ?_, _root_.GD.N0232.N0720.N1028.d015326 (m := m) (n := n) lambda
      hrpEquivariant hrqEquivariant⟩
  intro theta
  have hcanonical := _root_.GD.N0232.N0720.N1028.d015329
    m n lambda p q theta
  filter_upwards [hrpClass theta, hrqClass theta, hcanonical] with
      omega hpOmega hqOmega hcanonicalOmega
  unfold _root_.GD.N0232.N0720.N1028.d015324
  rw [hpOmega, hqOmega]
  exact hcanonicalOmega.symm



theorem d015331
    (m n : ℕ) (lambda : ℝ)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014652 m n q) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0230.N0668.d001343 lambda p q) := by
  exact _root_.GD.N0232.N0720.N1159.d014653
    m n (_root_.GD.N0230.N0668.d001343 lambda p q)
      (_root_.GD.N0232.N0720.N1028.d015330
        m n lambda p q hp hq)



theorem d015332
    (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014652 m n q) :
    _root_.GD.N0232.N0720.N1028.d015328 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p q =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1028.d015328 m n theta p q := by
  obtain ⟨rp, hrpMeasurable, hrpClass, hrpEquivariant⟩ := hp
  obtain ⟨rq, hrqMeasurable, hrqClass, hrqEquivariant⟩ := hq
  have htaxRaw := _root_.GD.N0232.N0720.N1028.d015327
    m n g theta hrpMeasurable hrqMeasurable hrpEquivariant hrqEquivariant
  have tax_eq_raw (eta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1028.d015328 m n eta p q =
        _root_.GD.N0232.N0720.N1028.d015323 m n eta rp rq := by
    unfold _root_.GD.N0232.N0720.N1028.d015328 _root_.GD.N0232.N0720.N1028.d015323
    apply lintegral_congr_ae
    filter_upwards [hrpClass eta, hrqClass eta] with omega hpOmega hqOmega
    rw [hpOmega, hqOmega]
  rw [tax_eq_raw (_root_.GD.N0232.N0720.N1215.d014272 g theta), tax_eq_raw theta]
  exact htaxRaw

end
end N1028
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1028.d015321
#print axioms _root_.GD.N0232.N0720.N1028.d015322
#print axioms _root_.GD.N0232.N0720.N1028.d015327
#print axioms _root_.GD.N0232.N0720.N1028.d015330
#print axioms _root_.GD.N0232.N0720.N1028.d015331
#print axioms _root_.GD.N0232.N0720.N1028.d015332
