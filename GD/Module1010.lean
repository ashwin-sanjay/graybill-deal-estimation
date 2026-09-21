import GD.Module1002
import GD.Module0946
























open Filter MeasureTheory
open scoped ENNReal

namespace GD.N0232.N0720.N1276

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1282
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0657




noncomputable local instance d016058 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016059 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨rfl⟩

abbrev d016060 := _root_.GD.N0232.N0720.N1080.d014170 2 2


def d016061 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := theta.location


def d016062
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 2 2 theta x


def d016063
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  _root_.GD.N0230.N0589.d000088 prior _root_.GD.N0232.N0720.N1276.d016062 x


def d016064
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  ∫ theta, _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x ∂prior



def d016065
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  _root_.GD.N0232.N0720.N1276.d016064 prior x / _root_.GD.N0232.N0720.N1276.d016063 prior x


def d016066
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  ∫ theta,
    (_root_.GD.N0232.N0720.N1276.d016061 theta - candidate x) * _root_.GD.N0232.N0720.N1276.d016062 theta x
      ∂prior



def d016067
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1276.d016066 prior candidate x ^ 2 /
      _root_.GD.N0232.N0720.N1276.d016063 prior x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2



def d016068
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ) : ℝ :=
  _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate -
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1276.d016065 prior)



structure d016069
    (N : ℝ) (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ) : Prop where
  finitePrior : IsFiniteMeasure prior
  evidence_eq :
    _root_.GD.N0232.N0720.N1276.d016063 prior =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1282.d014826 N
  current_eq :
    _root_.GD.N0232.N0720.N1276.d016066 prior candidate =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1282.d014827 N


theorem d016070
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016063 prior x =
      _root_.GD.N0230.N0657.d000366 prior (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) := by
  rfl


theorem d016071
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016065 prior x =
      _root_.GD.N0230.N0657.d000367 prior _root_.GD.N0232.N0720.N1276.d016061
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) := by
  rfl


theorem d016072
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (x : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior)
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
      prior) :
    _root_.GD.N0232.N0720.N1276.d016066 prior candidate x =
      _root_.GD.N0232.N0720.N1276.d016064 prior x -
        candidate x * _root_.GD.N0232.N0720.N1276.d016063 prior x := by
  unfold _root_.GD.N0232.N0720.N1276.d016066 _root_.GD.N0232.N0720.N1276.d016064
    _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
  let W := fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x
  have hconst : Integrable (fun theta ↦ candidate x * W theta) prior :=
    hw.const_mul _
  have hpoint :
      (fun theta ↦ (_root_.GD.N0232.N0720.N1276.d016061 theta - candidate x) * W theta) =
        (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta * W theta - candidate x * W theta) := by
    funext theta
    ring
  rw [hpoint, integral_sub htw hconst, integral_const_mul]


theorem d016073
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (x : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior)
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
      prior)
    (hmass : _root_.GD.N0232.N0720.N1276.d016063 prior x ≠ 0) :
    _root_.GD.N0232.N0720.N1276.d016065 prior x - candidate x =
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate x /
        _root_.GD.N0232.N0720.N1276.d016063 prior x := by
  rw [_root_.GD.N0232.N0720.N1276.d016072 prior candidate x hw htw]
  unfold _root_.GD.N0232.N0720.N1276.d016065
  field_simp [hmass]



theorem d016074
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (x : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior)
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
      prior)
    (hmass : _root_.GD.N0232.N0720.N1276.d016063 prior x ≠ 0) :
    _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
        (_root_.GD.N0232.N0720.N1276.d016065 prior) x =
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate x ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior x := by
  unfold _root_.GD.N0230.N0589.d000089
  change _root_.GD.N0232.N0720.N1276.d016063 prior x *
      (candidate x - _root_.GD.N0232.N0720.N1276.d016065 prior x) ^ 2 = _
  have hshift := _root_.GD.N0232.N0720.N1276.d016073
    prior candidate x hw htw hmass
  rw [show candidate x - _root_.GD.N0232.N0720.N1276.d016065 prior x =
      -(_root_.GD.N0232.N0720.N1276.d016065 prior x - candidate x) by ring, hshift]
  field_simp [hmass]


theorem d016075
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (x : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior)
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
      prior)
    (ht2w : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta x)
      prior)
    (hmass : _root_.GD.N0232.N0720.N1276.d016063 prior x ≠ 0) :
    _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
        (candidate x) =
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
          (_root_.GD.N0232.N0720.N1276.d016065 prior x) +
        _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
          (_root_.GD.N0232.N0720.N1276.d016065 prior) x := by
  have h := _root_.GD.N0232.N0720.N1173.d015949
    prior _root_.GD.N0232.N0720.N1276.d016061 (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x)
      (candidate x) hw htw ht2w
      (by simpa [_root_.GD.N0232.N0720.N1276.d016070] using hmass)
  simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0232.N0720.N1173.d015947,
    _root_.GD.N0232.N0720.N1276.d016071, _root_.GD.N0230.N0589.d000089,
    _root_.GD.N0232.N0720.N1276.d016063, _root_.GD.N0230.N0589.d000088, _root_.GD.N0230.N0657.d000366] using h



theorem d016076
    {N : ℝ} {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ}
    (hreal : _root_.GD.N0232.N0720.N1276.d016069 N prior candidate) :
    _root_.GD.N0232.N0720.N1276.d016067 prior candidate =
      _root_.GD.N0232.N0720.N1282.d014828 N := by
  unfold _root_.GD.N0232.N0720.N1276.d016067 _root_.GD.N0232.N0720.N1282.d014828
  apply integral_congr_ae
  filter_upwards [hreal.evidence_eq, hreal.current_eq] with x hE hJ
  rw [hE, hJ]



theorem d016077
    {N : ℝ} (hN : 3 ≤ N)
    {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ}
    (hreal : _root_.GD.N0232.N0720.N1276.d016069 N prior candidate) :
    _root_.GD.N0232.N0720.N1276.d016067 prior candidate ≤
      48 / N ^ 9 := by
  rw [_root_.GD.N0232.N0720.N1276.d016076 hreal]
  exact _root_.GD.N0232.N0720.N1282.d014838 hN




theorem d016078
    {N : ℝ} (hN : 3 ≤ N)
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hreal : _root_.GD.N0232.N0720.N1276.d016069 N prior candidate)
    (hcandidateJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hposteriorJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1276.d016065 prior)).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
        (_root_.GD.N0232.N0720.N1276.d016065 prior))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior ∧
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
        prior ∧
      Integrable
        (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta x)
        prior ∧
      _root_.GD.N0232.N0720.N1276.d016063 prior x ≠ 0) :
    _root_.GD.N0232.N0720.N1276.d016068 prior candidate ≤ 48 / N ^ 9 := by
  letI : IsFiniteMeasure prior := hreal.finitePrior
  letI : SigmaFinite prior := inferInstance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 2 2) := inferInstance
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
          (candidate x) =
        _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
            (_root_.GD.N0232.N0720.N1276.d016065 prior x) +
          _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
            (_root_.GD.N0232.N0720.N1276.d016065 prior) x := by
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1276.d016075 prior candidate x
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hdeficit : _root_.GD.N0232.N0720.N1276.d016068 prior candidate =
      ∫ x, _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
        (_root_.GD.N0232.N0720.N1276.d016065 prior) x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
    unfold _root_.GD.N0232.N0720.N1276.d016068
    exact _root_.GD.N0230.N0589.d000093
      prior (_root_.GD.N0232.N0720.N1080.d014172 2 2) _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
      candidate (_root_.GD.N0232.N0720.N1276.d016065 prior)
      hcandidateJoint hposteriorJoint htax hpointwise
  rw [hdeficit]
  have hperspective :
      (∫ x, _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
          (_root_.GD.N0232.N0720.N1276.d016065 prior) x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        _root_.GD.N0232.N0720.N1276.d016067 prior candidate := by
    unfold _root_.GD.N0232.N0720.N1276.d016067
    apply integral_congr_ae
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1276.d016074
      prior candidate x hx.1 hx.2.1 hx.2.2.2
  rw [hperspective]
  exact _root_.GD.N0232.N0720.N1276.d016077 hN hreal

#print axioms _root_.GD.N0232.N0720.N1276.d016076
#print axioms _root_.GD.N0232.N0720.N1276.d016077
#print axioms _root_.GD.N0232.N0720.N1276.d016078

end

end GD.N0232.N0720.N1276
