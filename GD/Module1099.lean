import GD.Module1093
import GD.Module1097
















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1192

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1183
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1188
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589

abbrev d017637 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017638 :=
  _root_.GD.N0232.N0720.N1173.d015936

private abbrev d017639 : Measure _root_.GD.N0232.N0720.N1192.d017637 :=
  _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104




theorem d017640
    (weight : _root_.GD.N0232.N0720.N1192.d017637 → ℝ)
    (hlegal : _root_.GD.N0232.N0720.N1183.d017557 weight)
    (ht118Integrable : Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (_root_.GD.N0232.N0720.N1183.d017550 weight)) :
    Integrable
      (_root_.GD.N0232.N0720.N1185.d017513 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 weight)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  letI : SigmaFinite _root_.GD.N0232.N0720.N1192.d017639 := by
    unfold _root_.GD.N0232.N0720.N1192.d017639 _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x) _root_.GD.N0232.N0720.N1192.d017639 ∧
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
        _root_.GD.N0232.N0720.N1173.d015939 weight theta x) _root_.GD.N0232.N0720.N1192.d017639 ∧
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
        _root_.GD.N0232.N0720.N1173.d015939 weight theta x) _root_.GD.N0232.N0720.N1192.d017639 ∧
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 weight x ≠ 0 :=
    hlegal.moments
  have hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
        (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight)).uncurry
      (_root_.GD.N0232.N0720.N1192.d017639.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :=
    hlegal.cutoffJoint
  have hcandJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)).uncurry
      (_root_.GD.N0232.N0720.N1192.d017639.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
    exact _root_.GD.N0232.N0720.N1183.d017564
      weight hlegal.measurable hlegal.nonneg
      _root_.GD.N0232.N0720.N1185.d017526 _root_.GD.N0232.N0720.N1185.d017528 ht118Integrable
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1173.d015939 weight)
          _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526 x) =
        _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) +
          _root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)
            (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight) x := by
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    simpa [_root_.GD.N0230.N0589.d000089, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1173.d015951
        _root_.GD.N0232.N0720.N1493.d016104 weight x
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526 x) hw htw ht2w hmass
  have htax : Integrable
      (_root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1173.d015939 weight)
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)
        (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    _root_.GD.N0230.N0589.d000101
      _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1080.d014172 2 2) (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
      (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)
      (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight)
      hcandJoint hcutJoint hpointwise
  have ht118AE : _root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1190.d017536 := by
    have hcoe : (fun x ↦ _root_.GD.N0232.N0720.N1185.d017526 x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
        _root_.GD.N0232.N0720.N1190.d017536 := by
      filter_upwards [_root_.GD.N0232.N0720.N1190.d017538] with x hx
      change _root_.GD.N0232.N0720.N1185.d017526 x = _root_.GD.N0232.N0720.N1190.d017536 x at hx
      exact hx
    exact (_root_.GD.N0232.N0720.N1214.d014267 2 2 _root_.GD.N0232.N0720.N1185.d017526).trans hcoe
  refine htax.congr ?_
  filter_upwards [hmoments, ht118AE] with x hx hcandidate
  calc
    _root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1192.d017639 (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)
          (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight) x =
        _root_.GD.N0232.N0720.N1185.d017513 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526) weight x :=
      _root_.GD.N0232.N0720.N1185.d017518
        _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526)
        weight x hx.1 hx.2.1 hx.2.2.2
    _ = _root_.GD.N0232.N0720.N1185.d017513 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 weight x :=
      _root_.GD.N0232.N0720.N1190.d017540
        _root_.GD.N0232.N0720.N1493.d016104 weight x hcandidate



theorem d017641
    (k : ℕ) (current : _root_.GD.N0232.N0720.N1192.d017638 → ℝ)
    (hcurrent : MemLp current 2 (_root_.GD.N0232.N0720.N1186.d017597 k)) :
    Integrable
      (fun x ↦ current x ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1166.d017432 k) x)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hsq : Integrable (fun x ↦ current x ^ 2)
      (_root_.GD.N0232.N0720.N1186.d017597 k) := hcurrent.integrable_sq
  change Integrable (fun x ↦ current x ^ 2)
    ((_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
      (_root_.GD.N0232.N0720.N1186.d017586
        (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1166.d017432 k)))) at hsq
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1186.d017587
      (_root_.GD.N0232.N0720.N1186.d017599 k))
    (_root_.GD.N0232.N0720.N1186.d017588
      (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k)))] at hsq
  refine hsq.congr ?_
  filter_upwards [_root_.GD.N0232.N0720.N1186.d017600 k] with x hx
  unfold _root_.GD.N0232.N0720.N1186.d017586
  rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  simp only [smul_eq_mul]
  field_simp [hx.ne']

end

end N1192
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1192.d017640
#print axioms _root_.GD.N0232.N0720.N1192.d017641
