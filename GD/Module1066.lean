import GD.Module1065
import GD.Module0968



































open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1128

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0668
open _root_.GD.N0232.N0720.N1028
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214




private theorem d017094
    (m n : ℕ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun omega ↦ p omega - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hstrong : AEStronglyMeasurable
      (fun omega ↦ p omega - theta.location) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    (AEStronglyMeasurable.mono_ac
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      (Lp.aestronglyMeasurable p)).sub aestronglyMeasurable_const
  exact (memLp_two_iff_integrable_sq hstrong).2
    (_root_.GD.N0232.N0720.N1078.d016376 m n theta p (hp theta))



theorem d017095
    (m n : ℕ) (lambda : ℝ)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (fun omega ↦ _root_.GD.N0230.N0668.d001343 lambda r s omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      fun omega ↦ (1 - lambda) * r omega + lambda * s omega := by
  have href :
      (fun omega ↦ _root_.GD.N0230.N0668.d001343 lambda r s omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ (1 - lambda) * r omega + lambda * s omega := by
    filter_upwards [
      Lp.coeFn_add ((1 - lambda) • r) (lambda • s),
      Lp.coeFn_smul (1 - lambda) r,
      Lp.coeFn_smul lambda s] with omega hadd hr hs
    unfold _root_.GD.N0230.N0668.d001343
    simp only [hadd, hr, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq href




theorem d017096
    (m n : ℕ) (lambda : ℝ)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r)
    (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0230.N0668.d001343 lambda r s) := by
  intro theta
  have hrError := _root_.GD.N0232.N0720.N1128.d017094 m n r hr theta
  have hsError := _root_.GD.N0232.N0720.N1128.d017094 m n s hs theta
  have hcombo : MemLp
      (fun omega ↦
        (1 - lambda) * (r omega - theta.location) +
          lambda * (s omega - theta.location)) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    exact (hrError.const_mul (1 - lambda)).add
      (hsError.const_mul lambda)
  have hrepairError : MemLp
      (fun omega ↦
        _root_.GD.N0230.N0668.d001343 lambda r s omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply (memLp_congr_ae ?_).2 hcombo
    filter_upwards [_root_.GD.N0232.N0720.N1128.d017095
      m n lambda r s theta] with omega hrepair
    rw [hrepair]
    ring
  unfold _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
  rw [← ofReal_integral_eq_lintegral_ofReal
    hrepairError.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  exact ENNReal.ofReal_ne_top



theorem d017097
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal =
      ∫ omega, (p omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  have hint := _root_.GD.N0232.N0720.N1078.d016376 m n theta p hp
  unfold _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]




def d017098
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  (_root_.GD.N0232.N0720.N1028.d015328 m n theta r s).toReal

private theorem d017099
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r)
    (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    Integrable
      (fun omega ↦
        (_root_.GD.N0232.N0720.N1214.d014265 m n r omega - _root_.GD.N0232.N0720.N1214.d014265 m n s omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hrError := _root_.GD.N0232.N0720.N1128.d017094 m n r hr theta
  have hsError := _root_.GD.N0232.N0720.N1128.d017094 m n s hs theta
  have hrBorelError : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n r omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply MemLp.ae_eq _ hrError
    filter_upwards [
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
        (_root_.GD.N0232.N0720.N1214.d014267 m n r)] with omega hrOmega
    rw [hrOmega]
  have hsBorelError : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n s omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply MemLp.ae_eq _ hsError
    filter_upwards [
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
        (_root_.GD.N0232.N0720.N1214.d014267 m n s)] with omega hsOmega
    rw [hsOmega]
  have hdiff := (hrBorelError.sub hsBorelError).integrable_sq
  convert hdiff using 1
  funext omega
  simp only [Pi.sub_apply]
  ring



theorem d017100
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r)
    (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    _root_.GD.N0232.N0720.N1028.d015328 m n theta r s ≠ ⊤ := by
  have hint := _root_.GD.N0232.N0720.N1128.d017099 m n theta r s hr hs
  unfold _root_.GD.N0232.N0720.N1028.d015328 _root_.GD.N0232.N0720.N1028.d015323
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  exact ENNReal.ofReal_ne_top



theorem d017101
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r)
    (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    _root_.GD.N0232.N0720.N1128.d017098 m n theta r s =
      ∫ omega, (r omega - s omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  have hint := _root_.GD.N0232.N0720.N1128.d017099 m n theta r s hr hs
  unfold _root_.GD.N0232.N0720.N1128.d017098 _root_.GD.N0232.N0720.N1028.d015328
    _root_.GD.N0232.N0720.N1028.d015323
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]
  apply integral_congr_ae
  filter_upwards [
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
      (_root_.GD.N0232.N0720.N1214.d014267 m n r),
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
      (_root_.GD.N0232.N0720.N1214.d014267 m n s)] with omega hrOmega hsOmega
  rw [hrOmega, hsOmega]

theorem d017102
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1128.d017098 m n theta r s :=
  ENNReal.toReal_nonneg






theorem d017103
    (m n : ℕ) (lambda : ℝ)
    (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r)
    (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s).toReal =
      (1 - lambda) *
        (((_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal - (_root_.GD.N0232.N0720.N1080.d014182 m n theta s).toReal) -
          lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta r s) := by
  have hrepairFinite := _root_.GD.N0232.N0720.N1128.d017096
    m n lambda r s hr hs
  have hrInt := _root_.GD.N0232.N0720.N1078.d016376
    m n theta r (hr theta)
  have hsInt := _root_.GD.N0232.N0720.N1078.d016376
    m n theta s (hs theta)
  have hrepairInt := _root_.GD.N0232.N0720.N1078.d016376
    m n theta (_root_.GD.N0230.N0668.d001343 lambda r s) (hrepairFinite theta)
  have hcrossInt : Integrable
      (fun omega ↦ (r omega - s omega) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have hrError := _root_.GD.N0232.N0720.N1128.d017094 m n r hr theta
    have hsError := _root_.GD.N0232.N0720.N1128.d017094 m n s hs theta
    have hdiff := (hrError.sub hsError).integrable_sq
    convert hdiff using 1
    funext omega
    simp only [Pi.sub_apply]
    ring
  rw [_root_.GD.N0232.N0720.N1128.d017097 m n theta
      (_root_.GD.N0230.N0668.d001343 lambda r s) (hrepairFinite theta),
    _root_.GD.N0232.N0720.N1128.d017097 m n theta s (hs theta),
    _root_.GD.N0232.N0720.N1128.d017097 m n theta r (hr theta),
    _root_.GD.N0232.N0720.N1128.d017101
      m n theta r s hr hs]
  calc
    (∫ omega,
        (_root_.GD.N0230.N0668.d001343 lambda r s omega - theta.location) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) -
        ∫ omega, (s omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta =
      ∫ omega,
        ((_root_.GD.N0230.N0668.d001343 lambda r s omega - theta.location) ^ 2 -
          (s omega - theta.location) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
            rw [integral_sub hrepairInt hsInt]
    _ = ∫ omega,
        (1 - lambda) *
          (((r omega - theta.location) ^ 2 -
              (s omega - theta.location) ^ 2) -
            lambda * (r omega - s omega) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
          apply integral_congr_ae
          filter_upwards [_root_.GD.N0232.N0720.N1128.d017095
            m n lambda r s theta] with omega hrepair
          rw [hrepair]
          ring
    _ = (1 - lambda) *
        (((∫ omega, (r omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) -
            ∫ omega, (s omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) -
          lambda * ∫ omega, (r omega - s omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
          have hsub := integral_sub
            (hrInt.sub hsInt) (hcrossInt.const_mul lambda)
          have hdiff := integral_sub hrInt hsInt
          have hmul :
              (∫ omega, lambda * (r omega - s omega) ^ 2
                  ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
                lambda * ∫ omega, (r omega - s omega) ^ 2
                  ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
            rw [integral_const_mul]
          calc
            (∫ omega,
                (1 - lambda) *
                  (((r omega - theta.location) ^ 2 -
                      (s omega - theta.location) ^ 2) -
                    lambda * (r omega - s omega) ^ 2)
                ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
                (1 - lambda) *
                  ∫ omega,
                    ((r omega - theta.location) ^ 2 -
                        (s omega - theta.location) ^ 2) -
                      lambda * (r omega - s omega) ^ 2
                    ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
                      rw [integral_const_mul]
            _ = (1 - lambda) *
                ((∫ omega,
                    (r omega - theta.location) ^ 2 -
                      (s omega - theta.location) ^ 2
                    ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) -
                  ∫ omega, lambda * (r omega - s omega) ^ 2
                    ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
                      exact congrArg (fun z : ℝ ↦ (1 - lambda) * z)
                        (by
                          simpa only [Pi.sub_apply, Pi.mul_apply] using hsub)
            _ = _ := by rw [hdiff, hmul]





def d017104
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0230.N0668.d001343 lambda (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value




def d017105
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (lambda : ℝ) : Prop :=
  lambda ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal ≤
        lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value

theorem d017106
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) := by
  exact _root_.GD.N0232.N0720.N1126.d016428
    candidate.packet candidate.weight candidate.weight_nonneg


theorem d017107
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta
        (_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate)).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal =
      (1 - lambda) *
        (((_root_.GD.N0232.N0720.N1080.d014182 m n theta
              (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
            (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal) -
          lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta
            (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value) := by
  exact _root_.GD.N0232.N0720.N1128.d017103 m n lambda
    (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value
    (_root_.GD.N0232.N0720.N1128.d017106 m n candidate)
    s.finiteRisk theta




theorem d017108
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hcertificate : _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda) :
    _root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  intro theta
  have hrFinite := _root_.GD.N0232.N0720.N1128.d017106 m n candidate
  have hrepairFinite := _root_.GD.N0232.N0720.N1128.d017096 m n lambda
    (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value hrFinite s.finiteRisk
  have hidentity := _root_.GD.N0232.N0720.N1128.d017107
    m n lambda s candidate theta
  have hfactor :
      (1 - lambda) *
          (((_root_.GD.N0232.N0720.N1080.d014182 m n theta
                (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
              (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal) -
            lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta
              (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hcertificate.1.2)
      (sub_nonpos.mpr (hcertificate.2 theta))
  change _root_.GD.N0232.N0720.N1080.d014182 m n theta
      (_root_.GD.N0230.N0668.d001343 lambda (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value) ≤
    _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value
  apply (ENNReal.toReal_le_toReal
    (hrepairFinite theta) (s.finiteRisk theta)).1
  apply sub_nonpos.mp
  calc
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta
          (_root_.GD.N0230.N0668.d001343 lambda
            (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value)).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal =
      (1 - lambda) *
        (((_root_.GD.N0232.N0720.N1080.d014182 m n theta
              (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
            (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal) -
          lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta
            (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value) := hidentity
    _ ≤ 0 := hfactor





theorem d017109
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lambda : ℝ) (r s : H) :
    ‖_root_.GD.N0230.N0668.d001343 lambda r s - r‖ = |lambda| * ‖s - r‖ := by
  have hdiff : _root_.GD.N0230.N0668.d001343 lambda r s - r = lambda • (s - r) := by
    unfold _root_.GD.N0230.N0668.d001343
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs]



theorem d017110
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hlambda : 0 ≤ lambda) :
    ‖_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate -
        _root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ =
      lambda * ‖s.value - _root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ := by
  unfold _root_.GD.N0232.N0720.N1128.d017104
  simpa only [abs_of_nonneg hlambda] using
    _root_.GD.N0232.N0720.N1128.d017109 lambda
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value



theorem d017111
    (m n : ℕ) (lambda : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    ‖_root_.GD.N0232.N0720.N1128.d017104 m n lambda s candidate -
        _root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ≤
      ‖s.value - _root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ := by
  rw [_root_.GD.N0232.N0720.N1128.d017110
    m n lambda s candidate hlambda.1]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hlambda.2
      (norm_nonneg (s.value - _root_.GD.N0232.N0720.N1130.d017075 m n candidate))

end
end N1128
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1128.d017103
#print axioms _root_.GD.N0232.N0720.N1128.d017108
#print axioms _root_.GD.N0232.N0720.N1128.d017110
