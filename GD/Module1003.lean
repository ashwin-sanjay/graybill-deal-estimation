import GD.Module1002


































open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1174

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0230.N0589







theorem d015959
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (mass response : Omega → ℝ)
    (hmassNonneg : 0 ≤ᵐ[mu] mass)
    (hmass : Integrable mass mu)
    (hcurrent : Integrable (fun z ↦ mass z * response z) mu)
    (henergy : Integrable (fun z ↦ mass z * response z ^ 2) mu) :
    (∫ z, mass z * response z ∂mu) ^ 2 ≤
      (∫ z, mass z ∂mu) *
        ∫ z, mass z * response z ^ 2 ∂mu := by
  let M : ℝ := ∫ z, mass z ∂mu
  let C : ℝ := ∫ z, mass z * response z ∂mu
  let E : ℝ := ∫ z, mass z * response z ^ 2 ∂mu
  change C ^ 2 ≤ M * E
  have hMnonneg : 0 ≤ M := by
    exact integral_nonneg_of_ae hmassNonneg
  by_cases hMzero : M = 0
  · have hmassZero : mass =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hmassNonneg hmass).mp hMzero
    have hcurrentZero :
        (fun z ↦ mass z * response z) =ᵐ[mu] 0 := by
      filter_upwards [hmassZero] with z hz
      simp [hz]
    have hCzero : C = 0 := by
      dsimp [C]
      calc
        (∫ z, mass z * response z ∂mu) =
            ∫ _z : Omega, (0 : ℝ) ∂mu := integral_congr_ae hcurrentZero
        _ = 0 := by simp
    simp [hMzero, hCzero]
  · let a : ℝ := C / M
    have hpoint :
        (fun z ↦ mass z * (response z - a) ^ 2) =
          (fun z ↦
            mass z * response z ^ 2 -
              (2 * a) * (mass z * response z) +
                a ^ 2 * mass z) := by
      funext z
      ring
    have hcross : Integrable
        (fun z ↦ (2 * a) * (mass z * response z)) mu :=
      hcurrent.const_mul _
    have hconstant : Integrable
        (fun z ↦ a ^ 2 * mass z) mu :=
      hmass.const_mul _
    have hcenterNonneg :
        0 ≤ ∫ z, mass z * (response z - a) ^ 2 ∂mu := by
      apply integral_nonneg_of_ae
      filter_upwards [hmassNonneg] with z hz
      exact mul_nonneg hz (sq_nonneg _)
    have hcenterExpansion :
        (∫ z, mass z * (response z - a) ^ 2 ∂mu) =
          E - (2 * a) * C + a ^ 2 * M := by
      rw [hpoint]
      calc
        (∫ z,
            mass z * response z ^ 2 -
                (2 * a) * (mass z * response z) +
              a ^ 2 * mass z ∂mu) =
            (∫ z,
              mass z * response z ^ 2 -
                (2 * a) * (mass z * response z) ∂mu) +
              ∫ z, a ^ 2 * mass z ∂mu := by
                simpa only [Pi.add_apply, Pi.sub_apply] using
                  integral_add (henergy.sub hcross) hconstant
        _ = ((∫ z, mass z * response z ^ 2 ∂mu) -
              ∫ z, (2 * a) * (mass z * response z) ∂mu) +
              ∫ z, a ^ 2 * mass z ∂mu := by
                rw [integral_sub henergy hcross]
        _ = E - (2 * a) * C + a ^ 2 * M := by
              rw [integral_const_mul, integral_const_mul]
    rw [hcenterExpansion] at hcenterNonneg
    have hCM : C = a * M := by
      dsimp [a]
      field_simp [hMzero]
    have hscaled := mul_nonneg hMnonneg hcenterNonneg
    nlinarith




def d015960
    (_rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015937 z.1 x * _root_.GD.N0232.N0720.N1173.d015937 z.2 x



def d015961
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  (_root_.GD.N0232.N0720.N1173.d015938 z.1 - _root_.GD.N0232.N0720.N1173.d015938 z.2) *
    (weight z.1 - weight z.2)









def d015962
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    _root_.GD.N0232.N0720.N1174.d015960 rho x z *
      _root_.GD.N0232.N0720.N1174.d015961 weight z ^ 2 ∂
        (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)




def d015963
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ENNReal :=
  ∫⁻ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1174.d015960 rho x z *
        _root_.GD.N0232.N0720.N1174.d015961 weight z ^ 2) ∂
          (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)


def d015964
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015946 rho weight x ^ 2 /
    (4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
      _root_.GD.N0232.N0720.N1173.d015940 rho weight x)


def d015965
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1174.d015962 rho weight x /
    (4 * _root_.GD.N0232.N0720.N1173.d015940 rho weight x)


def d015966
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1174.d015965 rho weight x
    ∂_root_.GD.N0232.N0720.N1080.d014172 2 2

theorem d015967
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1174.d015962 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1174.d015962 _root_.GD.N0232.N0720.N1174.d015960
  apply integral_nonneg_of_ae
  filter_upwards [] with z
  exact mul_nonneg
    (mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.2) x))
    (sq_nonneg _)



theorem d015968
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (henergy : Integrable
      (fun z ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          _root_.GD.N0232.N0720.N1174.d015961 weight z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho))) :
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1174.d015962 rho weight x) =
      _root_.GD.N0232.N0720.N1174.d015963 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1174.d015962 _root_.GD.N0232.N0720.N1174.d015963
  exact ofReal_integral_eq_lintegral_ofReal henergy
    (Filter.Eventually.of_forall fun z ↦
      mul_nonneg
        (mul_nonneg
          (_root_.GD.N0232.N0720.N1499.d015003 2 2
            (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
          (_root_.GD.N0232.N0720.N1499.d015003 2 2
            (_root_.GD.N0232.N0720.N1173.d015935 z.2) x))
        (sq_nonneg _))





theorem d015969
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1174.d015962 rho (fun theta ↦ h theta ^ 2) x =
      ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          (_root_.GD.N0232.N0720.N1173.d015938 z.1 - _root_.GD.N0232.N0720.N1173.d015938 z.2) ^ 2 *
          (h z.1 - h z.2) ^ 2 * (h z.1 + h z.2) ^ 2 ∂
            (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
  unfold _root_.GD.N0232.N0720.N1174.d015962 _root_.GD.N0232.N0720.N1174.d015961
  apply integral_congr_ae
  filter_upwards [] with z
  ring



theorem d015970
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcurrent : Integrable
      (fun z ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          _root_.GD.N0232.N0720.N1174.d015961 weight z)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (henergy : Integrable
      (fun z ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          _root_.GD.N0232.N0720.N1174.d015961 weight z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho))) :
    _root_.GD.N0232.N0720.N1173.d015946 rho weight x ^ 2 ≤
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
        _root_.GD.N0232.N0720.N1174.d015962 rho weight x := by
  letI : SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  let pairMeasure :=
    (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)
  have hpairMass : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z) pairMeasure := by
    simpa [pairMeasure, _root_.GD.N0232.N0720.N1174.d015960] using
      hfull.mul_prod hfull
  have hpairMassNonneg :
      0 ≤ᵐ[pairMeasure]
        (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1174.d015960 rho x z) := by
    filter_upwards [] with z
    exact mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.2) x)
  have hcs := _root_.GD.N0232.N0720.N1174.d015959
    pairMeasure
    (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
      _root_.GD.N0232.N0720.N1174.d015960 rho x z)
    (_root_.GD.N0232.N0720.N1174.d015961 weight)
    hpairMassNonneg hpairMass hcurrent henergy
  have hmass :
      (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1174.d015960 rho x z ∂pairMeasure) =
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1174.d015960 pairMeasure
    rw [integral_prod_mul
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)]
    simp [_root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0232.N0720.N1173.d015939, pow_two]
  rw [hmass] at hcs
  simpa [_root_.GD.N0232.N0720.N1173.d015946, _root_.GD.N0232.N0720.N1174.d015962,
    _root_.GD.N0232.N0720.N1174.d015960, _root_.GD.N0232.N0720.N1174.d015961, pairMeasure,
    mul_assoc] using hcs




theorem d015971
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcurrent : Integrable
      (fun z ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          _root_.GD.N0232.N0720.N1174.d015961 weight z)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (henergy : Integrable
      (fun z ↦
        _root_.GD.N0232.N0720.N1174.d015960 rho x z *
          _root_.GD.N0232.N0720.N1174.d015961 weight z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0)
    (hcutoffEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho weight x) :
    _root_.GD.N0232.N0720.N1174.d015964 rho weight x ≤
      _root_.GD.N0232.N0720.N1174.d015965 rho weight x := by
  have hcs := _root_.GD.N0232.N0720.N1174.d015970
    rho weight x hfull hcurrent henergy
  have hden :
      0 < 4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
        _root_.GD.N0232.N0720.N1173.d015940 rho weight x :=
    mul_pos
      (mul_pos (by norm_num) (sq_pos_of_ne_zero hfullEvidence))
      hcutoffEvidence
  unfold _root_.GD.N0232.N0720.N1174.d015964 _root_.GD.N0232.N0720.N1174.d015965
  apply (div_le_iff₀ hden).2
  calc
    _root_.GD.N0232.N0720.N1173.d015946 rho weight x ^ 2 ≤
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
          _root_.GD.N0232.N0720.N1174.d015962 rho weight x := hcs
    _ =
        (_root_.GD.N0232.N0720.N1174.d015962 rho weight x /
            (4 * _root_.GD.N0232.N0720.N1173.d015940 rho weight x)) *
          (4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
            _root_.GD.N0232.N0720.N1173.d015940 rho weight x) := by
      field_simp [ne_of_gt hcutoffEvidence]











theorem d015972
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015944 rho)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2))).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho)
          (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2))
          (_root_.GD.N0232.N0720.N1173.d015944 rho)
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x ≠ 0)
    (hfullMoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1173.d015938 theta)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0)
    (hpair : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun z ↦
            _root_.GD.N0232.N0720.N1174.d015960 rho x z *
              _root_.GD.N0232.N0720.N1174.d015961 (fun theta ↦ h theta ^ 2) z)
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) ∧
      Integrable
          (fun z ↦
            _root_.GD.N0232.N0720.N1174.d015960 rho x z *
              _root_.GD.N0232.N0720.N1174.d015961 (fun theta ↦ h theta ^ 2) z ^ 2)
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hdeficitIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1174.d015964 rho (fun theta ↦ h theta ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hdirichletIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1174.d015965 rho (fun theta ↦ h theta ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1173.d015956 rho (fun theta ↦ h theta ^ 2) ≤
      _root_.GD.N0232.N0720.N1174.d015966 rho (fun theta ↦ h theta ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1173.d015958
    rho (fun theta ↦ h theta ^ 2)
      hfullJoint hcutJoint htax hmoments hfullMoments]
  change
    (∫ x,
      _root_.GD.N0232.N0720.N1174.d015964 rho (fun theta ↦ h theta ^ 2) x
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) ≤
      ∫ x,
        _root_.GD.N0232.N0720.N1174.d015965 rho (fun theta ↦ h theta ^ 2) x
          ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
  apply integral_mono_ae hdeficitIntegrable hdirichletIntegrable
  filter_upwards [hmoments, hfullMoments, hpair] with x hx hfullx hpairx
  have hcutoffEvidence :
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x :=
    lt_of_le_of_ne
      (_root_.GD.N0232.N0720.N1173.d015941 rho h x)
      (Ne.symm hx.2.2.2)
  exact _root_.GD.N0232.N0720.N1174.d015971
    rho (fun theta ↦ h theta ^ 2) x
      hfullx.1 hpairx.1 hpairx.2 hfullx.2.2 hcutoffEvidence

end

end N1174
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1174.d015959
#print axioms _root_.GD.N0232.N0720.N1174.d015968
#print axioms _root_.GD.N0232.N0720.N1174.d015970
#print axioms _root_.GD.N0232.N0720.N1174.d015971
#print axioms _root_.GD.N0232.N0720.N1174.d015972
