import Mathlib
































open MeasureTheory
open scoped ENNReal

namespace GD
namespace N0230
namespace N0589

noncomputable section

variable {Theta X : Type*}
variable [MeasurableSpace Theta] [MeasurableSpace X]




def d000071
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) (theta : Theta) (x : X) : ℝ :=
  likelihood theta x * (action x - target theta) ^ 2



def d000072
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) (theta : Theta) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0230.N0589.d000071 likelihood target action theta x)



theorem d000073
    {likelihood : Theta → X → ℝ} {target : Theta → ℝ}
    {action : X → ℝ}
    (hlikelihood : Measurable likelihood.uncurry)
    (htarget : Measurable target) (haction : Measurable action) :
    Measurable (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry := by
  have htarget' : Measurable (fun z : Theta × X ↦ target z.1) :=
    htarget.comp measurable_fst
  have haction' : Measurable (fun z : Theta × X ↦ action z.2) :=
    haction.comp measurable_snd
  exact hlikelihood.mul ((haction'.sub htarget').pow_const 2)


theorem d000074
    {likelihood : Theta → X → ℝ} {target : Theta → ℝ}
    {action : X → ℝ}
    (hlikelihood : Measurable likelihood.uncurry)
    (htarget : Measurable target) (haction : Measurable action) :
    Measurable (_root_.GD.N0230.N0589.d000072 likelihood target action).uncurry :=
  (_root_.GD.N0230.N0589.d000073
    hlikelihood htarget haction).ennreal_ofReal


theorem d000075
    {likelihood : Theta → X → ℝ} {target : Theta → ℝ}
    {action : X → ℝ}
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (theta : Theta) (x : X) :
    0 ≤ _root_.GD.N0230.N0589.d000071 likelihood target action theta x := by
  exact mul_nonneg (hlikelihood theta x) (sq_nonneg _)




def d000076
    (prior : Measure Theta) (data : Measure X)
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ theta, ∫⁻ x,
    _root_.GD.N0230.N0589.d000072 likelihood target action theta x ∂data ∂prior


def d000077
    (prior : Measure Theta) (data : Measure X)
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ theta,
    _root_.GD.N0230.N0589.d000072 likelihood target action theta x ∂prior ∂data



theorem d000078
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ)
    (hjoint : AEMeasurable
      (_root_.GD.N0230.N0589.d000072 likelihood target action).uncurry
      (prior.prod data)) :
    _root_.GD.N0230.N0589.d000076 prior data likelihood target action =
      _root_.GD.N0230.N0589.d000077 prior data likelihood target action := by
  exact MeasureTheory.lintegral_lintegral_swap hjoint


theorem d000079
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ)
    (hlikelihood : Measurable likelihood.uncurry)
    (htarget : Measurable target) (haction : Measurable action) :
    _root_.GD.N0230.N0589.d000076 prior data likelihood target action =
      _root_.GD.N0230.N0589.d000077 prior data likelihood target action := by
  exact _root_.GD.N0230.N0589.d000078
    prior data likelihood target action
      (_root_.GD.N0230.N0589.d000074
        hlikelihood htarget haction).aemeasurable


def d000080
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (target : Theta → ℝ) (x : X) (action : ℝ) : ℝ≥0∞ :=
  ∫⁻ theta,
    ENNReal.ofReal
      (likelihood theta x * (action - target theta) ^ 2) ∂prior


def d000081
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ theta, ENNReal.ofReal (likelihood theta x) ∂prior


def d000082
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (action center : X → ℝ) (x : X) : ℝ≥0∞ :=
  _root_.GD.N0230.N0589.d000081 prior likelihood x *
    ENNReal.ofReal ((action x - center x) ^ 2)






theorem d000083
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hactionJoint : AEMeasurable
      (_root_.GD.N0230.N0589.d000072 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : AEMeasurable
      (_root_.GD.N0230.N0589.d000072 likelihood target center).uncurry
      (prior.prod data))
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000080 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000080 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000082 prior likelihood action center x) :
    _root_.GD.N0230.N0589.d000076 prior data likelihood target action =
      _root_.GD.N0230.N0589.d000076 prior data likelihood target center +
        ∫⁻ x, _root_.GD.N0230.N0589.d000082 prior likelihood action center x ∂data := by
  rw [_root_.GD.N0230.N0589.d000078
      prior data likelihood target action hactionJoint,
    _root_.GD.N0230.N0589.d000078
      prior data likelihood target center hcenterJoint]
  change
    (∫⁻ x,
      _root_.GD.N0230.N0589.d000080 prior likelihood target x (action x)
        ∂data) =
      (∫⁻ x,
        _root_.GD.N0230.N0589.d000080 prior likelihood target x (center x)
          ∂data) +
        ∫⁻ x, _root_.GD.N0230.N0589.d000082 prior likelihood action center x ∂data
  rw [lintegral_congr_ae hpointwise]
  have hcenterObjective : AEMeasurable
      (fun x ↦
        _root_.GD.N0230.N0589.d000080 prior likelihood target x (center x))
      data := by
    simpa [_root_.GD.N0230.N0589.d000080,
      _root_.GD.N0230.N0589.d000072, _root_.GD.N0230.N0589.d000071] using
        hcenterJoint.lintegral_prod_left'
  exact lintegral_add_left' hcenterObjective
    (_root_.GD.N0230.N0589.d000082 prior likelihood action center)




def d000084
    (prior : Measure Theta) (data : Measure X)
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) : ℝ :=
  ∫ theta, ∫ x,
    _root_.GD.N0230.N0589.d000071 likelihood target action theta x ∂data ∂prior


def d000085
    (prior : Measure Theta) (data : Measure X)
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ) : ℝ :=
  ∫ x, ∫ theta,
    _root_.GD.N0230.N0589.d000071 likelihood target action theta x ∂prior ∂data


theorem d000086
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action : X → ℝ)
    (hjoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data)) :
    _root_.GD.N0230.N0589.d000084 prior data likelihood target action =
      _root_.GD.N0230.N0589.d000085 prior data likelihood target action := by
  exact MeasureTheory.integral_integral_swap hjoint


def d000087
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (target : Theta → ℝ) (x : X) (action : ℝ) : ℝ :=
  ∫ theta, likelihood theta x * (action - target theta) ^ 2 ∂prior


def d000088
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (x : X) : ℝ :=
  ∫ theta, likelihood theta x ∂prior


def d000089
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (action center : X → ℝ) (x : X) : ℝ :=
  _root_.GD.N0230.N0589.d000088 prior likelihood x * (action x - center x) ^ 2


theorem d000090
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x) (x : X) :
    0 ≤ _root_.GD.N0230.N0589.d000088 prior likelihood x := by
  unfold _root_.GD.N0230.N0589.d000088
  exact integral_nonneg fun theta ↦ hlikelihood theta x


theorem d000091
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x) (x : X) :
    0 ≤ _root_.GD.N0230.N0589.d000089 prior likelihood action center x := by
  exact mul_nonneg (_root_.GD.N0230.N0589.d000090 prior likelihood hlikelihood x)
    (sq_nonneg _)







theorem d000092
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000089 prior likelihood action center x) :
    _root_.GD.N0230.N0589.d000084 prior data likelihood target action =
      _root_.GD.N0230.N0589.d000084 prior data likelihood target center +
        ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data := by
  rw [_root_.GD.N0230.N0589.d000086
      prior data likelihood target action hactionJoint,
    _root_.GD.N0230.N0589.d000086
      prior data likelihood target center hcenterJoint]
  change
    (∫ x,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x)
        ∂data) =
      (∫ x,
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x)
          ∂data) +
        ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data
  rw [integral_congr_ae hpointwise]
  have hcenterObjective : Integrable
      (fun x ↦ _root_.GD.N0230.N0589.d000087
        prior likelihood target x (center x)) data := by
    simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0230.N0589.d000071] using
      hcenterJoint.integral_prod_right
  exact integral_add hcenterObjective htax


theorem d000093
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000089 prior likelihood action center x) :
    _root_.GD.N0230.N0589.d000084 prior data likelihood target action -
        _root_.GD.N0230.N0589.d000084 prior data likelihood target center =
      ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data := by
  rw [_root_.GD.N0230.N0589.d000092
    prior data likelihood target action center
    hactionJoint hcenterJoint htax hpointwise]
  ring



theorem d000094
    (prior : Measure Theta) (data : Measure X)
    (likelihood : Theta → X → ℝ) (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x) :
    0 ≤ ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data := by
  exact integral_nonneg fun x ↦
    _root_.GD.N0230.N0589.d000091 prior likelihood action center hlikelihood x





def d000095
    (data : Measure X) (likelihood : Theta → X → ℝ)
    (target : Theta → ℝ) (action : X → ℝ) (theta : Theta) : ℝ :=
  ∫ x, _root_.GD.N0230.N0589.d000071 likelihood target action theta x ∂data






def d000096
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ) (theta : Theta) (x : X) : ℝ :=
  _root_.GD.N0230.N0589.d000071 likelihood target action theta x -
    _root_.GD.N0230.N0589.d000071 likelihood target center theta x




theorem d000097
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ) (theta : Theta) (x : X) :
    _root_.GD.N0230.N0589.d000096 likelihood target action center theta x =
      likelihood theta x * (action x - center x) *
        (action x + center x - 2 * target theta) := by
  unfold _root_.GD.N0230.N0589.d000096 _root_.GD.N0230.N0589.d000071
  ring


def d000098
    (data : Measure X) (likelihood : Theta → X → ℝ)
    (target : Theta → ℝ) (action center : X → ℝ)
    (theta : Theta) : ℝ :=
  ∫ x, _root_.GD.N0230.N0589.d000096 likelihood target action center theta x ∂data


def d000099
    (prior : Measure Theta) (likelihood : Theta → X → ℝ)
    (target : Theta → ℝ) (action center : X → ℝ)
    (x : X) : ℝ :=
  ∫ theta, _root_.GD.N0230.N0589.d000096 likelihood target action center theta x ∂prior



theorem d000100
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data)) :
    (∫ theta,
        _root_.GD.N0230.N0589.d000098 data likelihood target action center theta
      ∂prior) =
      ∫ x,
        _root_.GD.N0230.N0589.d000099 prior likelihood target action center x ∂data := by
  exact MeasureTheory.integral_integral_swap hdeficit



theorem d000101
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target center).uncurry
      (prior.prod data))
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000089 prior likelihood action center x) :
    Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data := by
  have hactionObjective : Integrable
      (fun x ↦ _root_.GD.N0230.N0589.d000087
        prior likelihood target x (action x)) data := by
    simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0230.N0589.d000071] using
      hactionJoint.integral_prod_right
  have hcenterObjective : Integrable
      (fun x ↦ _root_.GD.N0230.N0589.d000087
        prior likelihood target x (center x)) data := by
    simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0230.N0589.d000071] using
      hcenterJoint.integral_prod_right
  apply (hactionObjective.sub hcenterObjective).congr
  filter_upwards [hpointwise] with x hx
  change
    _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) -
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) =
      _root_.GD.N0230.N0589.d000089 prior likelihood action center x
  linarith













theorem d000102
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000089 prior likelihood action center x)
    (hdom : ∀ theta,
      _root_.GD.N0230.N0589.d000095 data likelihood target action theta ≤
        _root_.GD.N0230.N0589.d000095 data likelihood target center theta) :
    action =ᵐ[data] center := by
  have hactionParameter : Integrable
      (_root_.GD.N0230.N0589.d000095 data likelihood target action) prior := by
    change Integrable
      (fun theta ↦ ∫ x,
        likelihood theta x * (action x - target theta) ^ 2 ∂data) prior
    exact hactionJoint.integral_prod_left
  have hcenterParameter : Integrable
      (_root_.GD.N0230.N0589.d000095 data likelihood target center) prior := by
    change Integrable
      (fun theta ↦ ∫ x,
        likelihood theta x * (center x - target theta) ^ 2 ∂data) prior
    exact hcenterJoint.integral_prod_left
  have hBayesLe :
      _root_.GD.N0230.N0589.d000084 prior data likelihood target action ≤
        _root_.GD.N0230.N0589.d000084 prior data likelihood target center := by
    change
      (∫ theta, _root_.GD.N0230.N0589.d000095 data likelihood target action theta
          ∂prior) ≤
        ∫ theta, _root_.GD.N0230.N0589.d000095 data likelihood target center theta
          ∂prior
    exact integral_mono_ae hactionParameter hcenterParameter
      (Filter.Eventually.of_forall hdom)
  have hdecomp := _root_.GD.N0230.N0589.d000092
    prior data likelihood target action center
    hactionJoint hcenterJoint htax hpointwise
  have htaxNonneg : ∀ᵐ x ∂data,
      0 ≤ _root_.GD.N0230.N0589.d000089 prior likelihood action center x :=
    Filter.Eventually.of_forall fun x ↦
      _root_.GD.N0230.N0589.d000091 prior likelihood action center hlikelihood x
  have htaxIntegralZero :
      ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data = 0 := by
    have htaxIntegralNonneg := integral_nonneg_of_ae htaxNonneg
    rw [hdecomp] at hBayesLe
    linarith
  have htaxZero : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000089 prior likelihood action center x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae htaxNonneg htax).1 htaxIntegralZero
  filter_upwards [hmarginal, htaxZero] with x hmarginalx htaxx
  unfold _root_.GD.N0230.N0589.d000089 at htaxx
  have hsquare : (action x - center x) ^ 2 = 0 := by
    exact (mul_eq_zero.mp htaxx).resolve_left hmarginalx.ne'
  nlinarith




theorem d000103
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target action).uncurry
      (prior.prod data))
    (hcenterJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 likelihood target center).uncurry
      (prior.prod data))
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hpointwise : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000087 prior likelihood target x (action x) =
        _root_.GD.N0230.N0589.d000087 prior likelihood target x (center x) +
          _root_.GD.N0230.N0589.d000089 prior likelihood action center x)
    (hdom : ∀ theta,
      _root_.GD.N0230.N0589.d000095 data likelihood target action theta ≤
        _root_.GD.N0230.N0589.d000095 data likelihood target center theta) :
    action =ᵐ[data] center := by
  exact _root_.GD.N0230.N0589.d000102
    prior data likelihood target action center hlikelihood
    hactionJoint hcenterJoint
    (_root_.GD.N0230.N0589.d000101
      prior data likelihood target action center
      hactionJoint hcenterJoint hpointwise)
    hmarginal hpointwise hdom








theorem d000104
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hposteriorDeficit : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0) :
    action =ᵐ[data] center := by
  have hparameterIntegrable : Integrable
      (_root_.GD.N0230.N0589.d000098 data likelihood target action center) prior := by
    exact hdeficit.integral_prod_left
  have hdataIntegrable : Integrable
      (_root_.GD.N0230.N0589.d000099 prior likelihood target action center) data := by
    exact hdeficit.integral_prod_right
  have htax : Integrable
      (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data :=
    hdataIntegrable.congr hposteriorDeficit
  have hparameterIntegralNonpos :
      (∫ theta,
        _root_.GD.N0230.N0589.d000098 data likelihood target action center theta
          ∂prior) ≤ 0 :=
    integral_nonpos hnonpos
  have hswap :=
    _root_.GD.N0230.N0589.d000100
      prior data likelihood target action center hdeficit
  have hdataIntegralEqTax :
      (∫ x, _root_.GD.N0230.N0589.d000099 prior likelihood target action center x
          ∂data) =
        ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data :=
    integral_congr_ae hposteriorDeficit
  have htaxNonneg : ∀ᵐ x ∂data,
      0 ≤ _root_.GD.N0230.N0589.d000089 prior likelihood action center x :=
    Filter.Eventually.of_forall fun x ↦
      _root_.GD.N0230.N0589.d000091 prior likelihood action center hlikelihood x
  have htaxIntegralZero :
      ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data = 0 := by
    have htaxIntegralNonneg := integral_nonneg_of_ae htaxNonneg
    linarith
  have htaxZero : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000089 prior likelihood action center x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae htaxNonneg htax).1 htaxIntegralZero
  filter_upwards [hmarginal, htaxZero] with x hmarginalx htaxx
  unfold _root_.GD.N0230.N0589.d000089 at htaxx
  have hsquare : (action x - center x) ^ 2 = 0 := by
    exact (mul_eq_zero.mp htaxx).resolve_left hmarginalx.ne'
  nlinarith







theorem d000105
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0) :
    ∫ x, boundaryFlux x ∂data ≤
      -∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data := by
  have hparameterIntegralNonpos :
      (∫ theta,
        _root_.GD.N0230.N0589.d000098 data likelihood target action center theta
          ∂prior) ≤ 0 :=
    integral_nonpos hnonpos
  have hswap :=
    _root_.GD.N0230.N0589.d000100
      prior data likelihood target action center hdeficit
  have hbalanceIntegral :
      (∫ x, _root_.GD.N0230.N0589.d000099 prior likelihood target action center x
          ∂data) =
        (∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data) +
          ∫ x, boundaryFlux x ∂data := by
    calc
      (∫ x, _root_.GD.N0230.N0589.d000099 prior likelihood target action center x
          ∂data) =
          ∫ x,
            _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x
              ∂data := integral_congr_ae hbalance
      _ =
          (∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data) +
            ∫ x, boundaryFlux x ∂data := integral_add htax hboundary
  linarith




theorem d000106
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0)
    (hdistinct : ¬ action =ᵐ[data] center) :
    ∫ x, boundaryFlux x ∂data < 0 := by
  have htaxNonneg : ∀ᵐ x ∂data,
      0 ≤ _root_.GD.N0230.N0589.d000089 prior likelihood action center x :=
    Filter.Eventually.of_forall fun x ↦
      _root_.GD.N0230.N0589.d000091 prior likelihood action center hlikelihood x
  have htaxIntegralNonneg :
      0 ≤ ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data :=
    integral_nonneg_of_ae htaxNonneg
  have htaxIntegralNeZero :
      (∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data) ≠ 0 := by
    intro hzero
    have htaxZero : ∀ᵐ x ∂data,
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae htaxNonneg htax).1 hzero
    apply hdistinct
    filter_upwards [hmarginal, htaxZero] with x hmarginalx htaxx
    unfold _root_.GD.N0230.N0589.d000089 at htaxx
    have hsquare : (action x - center x) ^ 2 = 0 := by
      exact (mul_eq_zero.mp htaxx).resolve_left hmarginalx.ne'
    nlinarith
  have htaxIntegralPos :
      0 < ∫ x, _root_.GD.N0230.N0589.d000089 prior likelihood action center x ∂data :=
    lt_of_le_of_ne htaxIntegralNonneg (Ne.symm htaxIntegralNeZero)
  have hfluxLe := _root_.GD.N0230.N0589.d000105
    prior data likelihood target action center boundaryFlux
    hdeficit htax hboundary hbalance hnonpos
  linarith




theorem d000107
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center : X → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hposteriorDeficit : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0)
    (hdistinct : ¬ action =ᵐ[data] center) :
    ¬ Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data) := by
  intro hdeficit
  exact hdistinct
    (_root_.GD.N0230.N0589.d000104
      prior data likelihood target action center hlikelihood hdeficit
      hmarginal hposteriorDeficit hnonpos)

end

end N0589
end N0230
end GD

#print axioms _root_.GD.N0230.N0589.d000078
#print axioms _root_.GD.N0230.N0589.d000083
#print axioms _root_.GD.N0230.N0589.d000086
#print axioms _root_.GD.N0230.N0589.d000092
#print axioms _root_.GD.N0230.N0589.d000093
#print axioms _root_.GD.N0230.N0589.d000097
#print axioms _root_.GD.N0230.N0589.d000102
#print axioms _root_.GD.N0230.N0589.d000104
#print axioms _root_.GD.N0230.N0589.d000106
#print axioms _root_.GD.N0230.N0589.d000107
