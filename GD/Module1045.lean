import GD.Module1007
import GD.Module1044







































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1181

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1172
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1182
open _root_.GD.N0232.N0720.N1180
open _root_.GD.N0232.N0720.N1178
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229


abbrev d016656 := _root_.GD.N0232.N0720.N1172.d015905





def d016657 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1173.d015936 ≃ᵐ _root_.GD.N0232.N0720.N1173.d015936 where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x
  measurable_toFun := by
    change Measurable (fun x : _root_.GD.N0232.N0720.N1173.d015936 ↦ g • x)
    have h := _root_.GD.N0232.N0720.N1484.d015095 2 2 g⁻¹
    unfold _root_.GD.N0232.N0720.N1484.d015094 at h
    simpa only [inv_inv] using h
  measurable_invFun := by
    change Measurable (_root_.GD.N0232.N0720.N1484.d015094 2 2 g)
    exact _root_.GD.N0232.N0720.N1484.d015095 2 2 g

@[simp] theorem d016658
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1181.d016657 g x = g • x := rfl

@[simp] theorem d016659
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    (_root_.GD.N0232.N0720.N1181.d016657 g).symm x = g⁻¹ • x := rfl



theorem d016660
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1181.d016656) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1182.d016042 (_root_.GD.N0232.N0720.N1172.d015906 g theta) (g • x) =
      _root_.GD.N0232.N0720.N1180.d016652 g x *
        _root_.GD.N0232.N0720.N1182.d016042 theta x := by
  unfold _root_.GD.N0232.N0720.N1182.d016042 _root_.GD.N0232.N0720.N1173.d015937 _root_.GD.N0232.N0720.N1173.d015935
    _root_.GD.N0232.N0720.N1180.d016652
  rw [_root_.GD.N0232.N0720.N1172.d015916]
  rw [_root_.GD.N0232.N0720.N1124.d016500]
  rw [ENNReal.ofReal_mul]
  exact _root_.GD.N0232.N0720.N1499.d015003 2 2
    (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • x)

theorem d016661
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 < _root_.GD.N0232.N0720.N1180.d016652 g x := by
  exact ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0720.N1499.d015005 2 2
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • x))

theorem d016662
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1180.d016652 g x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem d016663
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1180.d016653 g x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem d016664 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (_root_.GD.N0232.N0720.N1180.d016653 g) := by
  exact
    (_root_.GD.N0232.N0720.N1499.d015002 2 2
      (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)).ennreal_ofReal


theorem d016665
    (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1080.d014169 x = 1 := by
  have h := _root_.GD.N0232.N0720.N1124.d016500
    (m := 2) (n := 2) (g := (1 : _root_.GD.N0232.N0719.N0946.d009229))
    _root_.GD.N0232.N0720.N1080.d014169 x
  simp only [_root_.GD.N0232.N0720.N1215.d014276, one_smul] at h
  have hpos := _root_.GD.N0232.N0720.N1499.d015005 2 2 _root_.GD.N0232.N0720.N1080.d014169 x
  nlinarith


theorem d016666
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1180.d016652 g x *
        _root_.GD.N0232.N0720.N1180.d016653 g x = 1 := by
  have hcocycle := _root_.GD.N0232.N0720.N1124.d016500
    (m := 2) (n := 2) g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) x
  rw [_root_.GD.N0232.N0720.N1215.d014279] at hcocycle
  unfold _root_.GD.N0232.N0720.N1180.d016652 _root_.GD.N0232.N0720.N1180.d016653
  rw [← ENNReal.ofReal_mul
    (_root_.GD.N0232.N0720.N1499.d015003 2 2
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • x))]
  rw [← hcocycle, _root_.GD.N0232.N0720.N1181.d016665]
  exact ENNReal.ofReal_one



theorem d016667 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    0 < _root_.GD.N0232.N0720.N1180.d016654 g := by
  exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos g.d009240)

theorem d016668 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1180.d016654 g ≠ 0 :=
  ne_of_gt (_root_.GD.N0232.N0720.N1181.d016667 g)

theorem d016669 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1180.d016654 g ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem d016670 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1180.d016654 g⁻¹ = (_root_.GD.N0232.N0720.N1180.d016654 g)⁻¹ := by
  unfold _root_.GD.N0232.N0720.N1180.d016654 _root_.GD.N0232.N0719.N0946.d009229.d009239
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009238, Real.exp_neg]
  rw [← ENNReal.ofReal_inv_of_pos
    (sq_pos_of_pos (Real.exp_pos g.logScale))]
  congr 1
  rw [inv_pow]




theorem d016671
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1182.d016043 rho (g • x) =
      (_root_.GD.N0232.N0720.N1180.d016654 g)⁻¹ *
        _root_.GD.N0232.N0720.N1180.d016652 g x *
          _root_.GD.N0232.N0720.N1182.d016043 rho x := by
  let pi4 : Measure _root_.GD.N0232.N0720.N1181.d016656 := _root_.GD.N0232.N0720.N1173.d015934 rho
  let F : _root_.GD.N0232.N0720.N1181.d016656 → ℝ≥0∞ := fun theta =>
    _root_.GD.N0232.N0720.N1182.d016042 (_root_.GD.N0232.N0720.N1172.d015906 g theta) (g • x)
  have hmap :
      pi4.map (_root_.GD.N0232.N0720.N1178.d016015 g).symm =
        _root_.GD.N0232.N0720.N1180.d016654 g⁻¹ • pi4 := by
    have hinverse :
        ((_root_.GD.N0232.N0720.N1178.d016015 g).symm : _root_.GD.N0232.N0720.N1181.d016656 → _root_.GD.N0232.N0720.N1181.d016656) =
          _root_.GD.N0232.N0720.N1172.d015906 g⁻¹ := by
      funext theta
      exact _root_.GD.N0232.N0720.N1178.d016018 g theta
    rw [hinverse]
    unfold pi4 _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1180.d016654
    exact _root_.GD.N0232.N0720.N1178.d016026 rho g⁻¹
  have hchange := congrArg
    (fun nu : Measure _root_.GD.N0232.N0720.N1181.d016656 => ∫⁻ theta, F theta ∂nu) hmap
  rw [MeasureTheory.lintegral_map_equiv,
    MeasureTheory.lintegral_smul_measure] at hchange
  have hleft :
      (∫⁻ theta, F ((_root_.GD.N0232.N0720.N1178.d016015 g).symm theta) ∂pi4) =
        _root_.GD.N0232.N0720.N1182.d016043 rho (g • x) := by
    apply lintegral_congr
    intro theta
    simp [F, _root_.GD.N0232.N0720.N1178.d016018]
  have hright :
      (∫⁻ theta, F theta ∂pi4) =
        _root_.GD.N0232.N0720.N1180.d016652 g x *
          _root_.GD.N0232.N0720.N1182.d016043 rho x := by
    calc
      (∫⁻ theta, F theta ∂pi4) =
          ∫⁻ theta, _root_.GD.N0232.N0720.N1180.d016652 g x *
            _root_.GD.N0232.N0720.N1182.d016042 theta x ∂pi4 := by
        apply lintegral_congr
        intro theta
        exact _root_.GD.N0232.N0720.N1181.d016660 g theta x
      _ = _root_.GD.N0232.N0720.N1180.d016652 g x *
          _root_.GD.N0232.N0720.N1182.d016043 rho x := by
        rw [lintegral_const_mul' _ _
          (_root_.GD.N0232.N0720.N1181.d016662 g x)]
        rfl
  rw [hleft, hright, _root_.GD.N0232.N0720.N1181.d016670] at hchange
  simpa only [smul_eq_mul, mul_assoc] using hchange




private theorem d016672
    (A C L₁ L₂ E : ℝ≥0∞)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) :
    (C * L₁) * (C * L₂) / (A⁻¹ * C * E) =
      A * C * (L₁ * L₂ / E) := by
  have hAinv0 : A⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hAtop
  have hAinvtop : A⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  calc
    (C * L₁) * (C * L₂) / (A⁻¹ * C * E) =
        C * (C * (L₁ * L₂)) / (C * (A⁻¹ * E)) := by
      congr 1 <;> ac_rfl
    _ = C * (L₁ * L₂) / (A⁻¹ * E) := by
      exact ENNReal.mul_div_mul_left _ _ hC0 hCtop
    _ = (A⁻¹ * (A * (C * (L₁ * L₂)))) / (A⁻¹ * E) := by
      congr 1
      exact (ENNReal.inv_mul_cancel_left hA0 hAtop).symm
    _ = A * (C * (L₁ * L₂)) / E := by
      exact ENNReal.mul_div_mul_left _ _ hAinv0 hAinvtop
    _ = A * C * (L₁ * L₂ / E) := by
      simp only [div_eq_mul_inv]
      ac_rfl



theorem d016673
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (z : _root_.GD.N0232.N0720.N1181.d016656 × _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
        (_root_.GD.N0232.N0720.N1180.d016651 g z) =
      _root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1180.d016652 g x *
        _root_.GD.N0232.N0720.N1182.d016045 rho x z := by
  unfold _root_.GD.N0232.N0720.N1182.d016045 _root_.GD.N0232.N0720.N1180.d016651
  rw [_root_.GD.N0232.N0720.N1181.d016660,
    _root_.GD.N0232.N0720.N1181.d016660,
    _root_.GD.N0232.N0720.N1181.d016671]
  exact _root_.GD.N0232.N0720.N1181.d016672
    (_root_.GD.N0232.N0720.N1180.d016654 g) (_root_.GD.N0232.N0720.N1180.d016652 g x)
    (_root_.GD.N0232.N0720.N1182.d016042 z.1 x) (_root_.GD.N0232.N0720.N1182.d016042 z.2 x)
    (_root_.GD.N0232.N0720.N1182.d016043 rho x)
    (_root_.GD.N0232.N0720.N1181.d016668 g) (_root_.GD.N0232.N0720.N1181.d016669 g)
    (ne_of_gt (_root_.GD.N0232.N0720.N1181.d016661 g x))
    (_root_.GD.N0232.N0720.N1181.d016662 g x)







theorem d016674
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (g : _root_.GD.N0232.N0719.N0946.d009229) (z : _root_.GD.N0232.N0720.N1181.d016656 × _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1182.d016048 rho (_root_.GD.N0232.N0720.N1180.d016651 g z) =
      ∫⁻ x,
        _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
            (_root_.GD.N0232.N0720.N1180.d016651 g z) *
          _root_.GD.N0232.N0720.N1180.d016653 g x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  let e := _root_.GD.N0232.N0720.N1181.d016657 g
  let F : _root_.GD.N0232.N0720.N1173.d015936 → ℝ≥0∞ := fun y =>
    _root_.GD.N0232.N0720.N1182.d016045 rho y
      (_root_.GD.N0232.N0720.N1180.d016651 g z)
  have hmap :
      (_root_.GD.N0232.N0720.N1080.d014172 2 2).map e.symm =
        (_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
          (_root_.GD.N0232.N0720.N1180.d016653 g) := by
    have hinverse :
        (e.symm : _root_.GD.N0232.N0720.N1173.d015936 → _root_.GD.N0232.N0720.N1173.d015936) =
          _root_.GD.N0232.N0720.N1484.d015094 2 2 g := by
      funext x
      rfl
    rw [hinverse]
    change
      (_root_.GD.N0232.N0720.N1080.d014172 2 2).map (_root_.GD.N0232.N0720.N1484.d015094 2 2 g) =
        (_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
          (fun x ↦ ENNReal.ofReal
            (_root_.GD.N0232.N0720.N1499.d015001 2 2
              (_root_.GD.N0232.N0720.N1484.d015099 g) x))
    exact _root_.GD.N0232.N0720.N1484.d015102
      (m := 2) (n := 2) g
  calc
    _root_.GD.N0232.N0720.N1182.d016048 rho (_root_.GD.N0232.N0720.N1180.d016651 g z) =
        ∫⁻ y, F y ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := rfl
    _ = ∫⁻ x, F (e x) ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2).map e.symm := by
      rw [MeasureTheory.lintegral_map_equiv]
      apply lintegral_congr
      intro x
      exact congrArg F ((e.apply_symm_apply x).symm)
    _ = ∫⁻ x, F (e x) ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
          (_root_.GD.N0232.N0720.N1180.d016653 g) := by rw [hmap]
    _ = ∫⁻ x, _root_.GD.N0232.N0720.N1180.d016653 g x * F (e x)
          ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable
        (_root_.GD.N0232.N0720.N1080.d014172 2 2) (_root_.GD.N0232.N0720.N1181.d016664 g)
        (ae_of_all _ fun x => (_root_.GD.N0232.N0720.N1181.d016663 g x).lt_top)
        _
    _ = ∫⁻ x,
        _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
            (_root_.GD.N0232.N0720.N1180.d016651 g z) *
          _root_.GD.N0232.N0720.N1180.d016653 g x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
      apply lintegral_congr
      intro x
      simp only [F, e, _root_.GD.N0232.N0720.N1181.d016658]
      ac_rfl






theorem d016675
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (g : _root_.GD.N0232.N0719.N0946.d009229) (z : _root_.GD.N0232.N0720.N1181.d016656 × _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1182.d016048 rho (_root_.GD.N0232.N0720.N1180.d016651 g z) =
      _root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1182.d016048 rho z := by
  rw [_root_.GD.N0232.N0720.N1181.d016674 rho g z]
  calc
    (∫⁻ x,
        _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
            (_root_.GD.N0232.N0720.N1180.d016651 g z) *
          _root_.GD.N0232.N0720.N1180.d016653 g x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫⁻ x, _root_.GD.N0232.N0720.N1180.d016654 g *
          _root_.GD.N0232.N0720.N1182.d016045 rho x z ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
      apply lintegral_congr
      intro x
      rw [_root_.GD.N0232.N0720.N1181.d016673]
      calc
        (_root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1180.d016652 g x *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z) *
            _root_.GD.N0232.N0720.N1180.d016653 g x =
            _root_.GD.N0232.N0720.N1180.d016654 g *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z *
                (_root_.GD.N0232.N0720.N1180.d016652 g x *
                  _root_.GD.N0232.N0720.N1180.d016653 g x) := by
              ac_rfl
        _ = _root_.GD.N0232.N0720.N1180.d016654 g *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z := by
          rw [_root_.GD.N0232.N0720.N1181.d016666,
            mul_one]
    _ = _root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1182.d016048 rho z := by
      rw [lintegral_const_mul' _ _ (_root_.GD.N0232.N0720.N1181.d016669 g)]
      rfl





def d016676 (theta : _root_.GD.N0232.N0720.N1181.d016656) : _root_.GD.N0232.N0719.N0946.d009229 where
  shift := theta.1
  logScale := Real.log (Real.sqrt (theta.2.1 : ℝ))

theorem d016677 (theta : _root_.GD.N0232.N0720.N1181.d016656) :
    (_root_.GD.N0232.N0720.N1181.d016676 theta).d009239 = Real.sqrt (theta.2.1 : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1181.d016676 _root_.GD.N0232.N0719.N0946.d009229.d009239
  rw [Real.exp_log (Real.sqrt_pos.2 theta.2.1.property)]


def d016678 (theta : _root_.GD.N0232.N0720.N1181.d016656) : _root_.GD.N0232.N0720.N1181.d016656 :=
  (0, (⟨1, by norm_num⟩, theta.2.2))


def d016679 (theta eta : _root_.GD.N0232.N0720.N1181.d016656) : _root_.GD.N0232.N0720.N1181.d016656 :=
  (_root_.GD.N0232.N0720.N1172.d015919 theta eta,
    (⟨_root_.GD.N0232.N0720.N1172.d015917 theta eta, _root_.GD.N0232.N0720.N1172.d015920 theta eta⟩,
      eta.2.2))

theorem d016680 (theta : _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1172.d015906 (_root_.GD.N0232.N0720.N1181.d016676 theta) (_root_.GD.N0232.N0720.N1181.d016678 theta) = theta := by
  apply Prod.ext
  · change theta.1 + (_root_.GD.N0232.N0720.N1181.d016676 theta).d009239 * 0 = theta.1
    ring
  · apply Prod.ext
    · apply Subtype.ext
      change (_root_.GD.N0232.N0720.N1181.d016676 theta).d009239 ^ 2 * 1 = (theta.2.1 : ℝ)
      rw [_root_.GD.N0232.N0720.N1181.d016677, Real.sq_sqrt theta.2.1.property.le, mul_one]
    · simp only [_root_.GD.N0232.N0720.N1172.d015909, _root_.GD.N0232.N0720.N1181.d016678]

theorem d016681
    (theta eta : _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1172.d015906 (_root_.GD.N0232.N0720.N1181.d016676 theta) (_root_.GD.N0232.N0720.N1181.d016679 theta eta) = eta := by
  apply Prod.ext
  · change theta.1 + (_root_.GD.N0232.N0720.N1181.d016676 theta).d009239 *
      _root_.GD.N0232.N0720.N1172.d015919 theta eta = eta.1
    rw [_root_.GD.N0232.N0720.N1181.d016677]
    exact _root_.GD.N0232.N0720.N1172.d015928 theta eta
  · apply Prod.ext
    · apply Subtype.ext
      simp only [_root_.GD.N0232.N0720.N1172.d015908, _root_.GD.N0232.N0720.N1181.d016677,
        _root_.GD.N0232.N0720.N1181.d016679]
      rw [Real.sq_sqrt theta.2.1.property.le]
      simpa [mul_comm] using _root_.GD.N0232.N0720.N1172.d015925 theta eta
    · simp only [_root_.GD.N0232.N0720.N1172.d015909, _root_.GD.N0232.N0720.N1181.d016679]

theorem d016682 (theta : _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1180.d016654 (_root_.GD.N0232.N0720.N1181.d016676 theta) =
      ENNReal.ofReal (theta.2.1 : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1180.d016654
  rw [_root_.GD.N0232.N0720.N1181.d016677, Real.sq_sqrt theta.2.1.property.le]




theorem d016683
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (theta eta : _root_.GD.N0232.N0720.N1181.d016656) :
    _root_.GD.N0232.N0720.N1182.d016048 rho (theta, eta) =
      ENNReal.ofReal (theta.2.1 : ℝ) *
        _root_.GD.N0232.N0720.N1182.d016048 rho
          (_root_.GD.N0232.N0720.N1181.d016678 theta, _root_.GD.N0232.N0720.N1181.d016679 theta eta) := by
  have h := _root_.GD.N0232.N0720.N1181.d016675 rho
    (_root_.GD.N0232.N0720.N1181.d016676 theta) (_root_.GD.N0232.N0720.N1181.d016678 theta, _root_.GD.N0232.N0720.N1181.d016679 theta eta)
  simpa [_root_.GD.N0232.N0720.N1180.d016651, _root_.GD.N0232.N0720.N1181.d016680,
    _root_.GD.N0232.N0720.N1181.d016681,
    _root_.GD.N0232.N0720.N1181.d016682] using h

end

end N1181
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1181.d016671
#print axioms _root_.GD.N0232.N0720.N1181.d016673
#print axioms _root_.GD.N0232.N0720.N1181.d016675
#print axioms _root_.GD.N0232.N0720.N1181.d016683
