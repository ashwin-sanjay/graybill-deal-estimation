import GD.Module1095
import GD.Module1089













open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1188

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1167
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

abbrev d017604 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017605 :=
  _root_.GD.N0232.N0720.N1173.d015936

private abbrev d017606 : Measure _root_.GD.N0232.N0720.N1188.d017604 :=
  _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104





theorem d017607
    (evidence current : _root_.GD.N0232.N0720.N1188.d017605 → ℝ)
    (hevidence : Measurable evidence)
    (hcurrent : AEStronglyMeasurable current (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hevidencePos : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2, 0 < evidence x)
    (hintegrable : Integrable
      (fun x ↦ current x ^ 2 / evidence x) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    MemLp current 2
      ((_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity
        (_root_.GD.N0232.N0720.N1186.d017586 evidence)) := by
  let weightedLaw : Measure _root_.GD.N0232.N0720.N1188.d017605 :=
    (_root_.GD.N0232.N0720.N1080.d014172 2 2).withDensity (_root_.GD.N0232.N0720.N1186.d017586 evidence)
  have hac : weightedLaw ≪ _root_.GD.N0232.N0720.N1080.d014172 2 2 :=
    withDensity_absolutelyContinuous _ _
  have hcurrentWeighted : AEStronglyMeasurable current weightedLaw :=
    hcurrent.mono_ac hac
  rw [memLp_two_iff_integrable_sq hcurrentWeighted]
  unfold weightedLaw
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1186.d017587 hevidence)
    (_root_.GD.N0232.N0720.N1186.d017588 evidence)]
  refine hintegrable.congr ?_
  filter_upwards [hevidencePos] with x hx
  unfold _root_.GD.N0232.N0720.N1186.d017586
  rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  simp only [smul_eq_mul]
  field_simp [hx.ne']





theorem d017608
    (k : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q) :
    Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry
      (_root_.GD.N0232.N0720.N1188.d017606.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have htarget : Measurable _root_.GD.N0232.N0720.N1173.d015938 := by
    unfold _root_.GD.N0232.N0720.N1173.d015938
    fun_prop
  have hjoint : Measurable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry :=
    _root_.GD.N0230.N0589.d000073
      (_root_.GD.N0232.N0720.N1166.d017448 k)
      htarget (_root_.GD.N0232.N0720.N1214.d014266 2 2 q)
  apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
  constructor
  · filter_upwards with theta
    have hbase := _root_.GD.N0232.N0720.N1126.d016429
      (_root_.GD.N0232.N0720.N1173.d015935 theta) q (hq (_root_.GD.N0232.N0720.N1173.d015935 theta))
    have hborel : Integrable
        (fun x ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x *
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
      refine hbase.congr ?_
      filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with x hx
      change
        _root_.GD.N0232.N0720.N1499.d015001 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x *
              (q x - (_root_.GD.N0232.N0720.N1173.d015935 theta).location) ^ 2 =
          _root_.GD.N0232.N0720.N1173.d015937 theta x *
              (_root_.GD.N0232.N0720.N1214.d014265 2 2 q x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2
      rw [hx]
      rfl
    have hscaled := hborel.const_mul (_root_.GD.N0232.N0720.N1166.d017432 k theta)
    refine hscaled.congr (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun x ↦ ?_)
    unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1173.d015939
    dsimp only [Function.uncurry_apply_pair]
    ring
  · have hprofilePrior :=
      _root_.GD.N0232.N0720.N1166.d017483 k q hq
    rw [_root_.GD.N0232.N0720.N1166.d017440] at hprofilePrior
    have hprofileWeighted : Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta *
          (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal) _root_.GD.N0232.N0720.N1188.d017606 := by
      have hconverted :=
        (integrable_withDensity_iff_integrable_smul'
          ((_root_.GD.N0232.N0720.N1166.d017436 k).pow_const 2
            |>.ennreal_ofReal)
          (ae_of_all _root_.GD.N0232.N0720.N1188.d017606 fun _ ↦ ENNReal.ofReal_lt_top)).1
          hprofilePrior
      refine hconverted.congr (ae_of_all _root_.GD.N0232.N0720.N1188.d017606 fun theta ↦ ?_)
      change
        (ENNReal.ofReal (_root_.GD.N0232.N0720.N1166.d017432 k theta ^ 2)).toReal •
            (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal =
          _root_.GD.N0232.N0720.N1166.d017432 k theta *
            (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
      simp only [smul_eq_mul]
      rw [_root_.GD.N0232.N0720.N1166.d017435]
    refine hprofileWeighted.congr
      (ae_of_all _root_.GD.N0232.N0720.N1188.d017606 fun theta ↦ ?_)
    change
      _root_.GD.N0232.N0720.N1166.d017432 k theta *
          (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal =
        ∫ x,
          ‖_root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
              (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta x‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
    rw [show
      (∫ x,
        ‖_root_.GD.N0230.N0589.d000071
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta x‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫ x,
          _root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
              (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
        apply integral_congr_ae
        filter_upwards with x
        exact Real.norm_of_nonneg (by
          apply _root_.GD.N0230.N0589.d000075
          intro eta y
          exact mul_nonneg
            (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 eta) y)
            (_root_.GD.N0232.N0720.N1166.d017437 k eta))]
    rw [show
      (∫ x,
        _root_.GD.N0230.N0589.d000071
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        _root_.GD.N0232.N0720.N1166.d017432 k theta *
          ∫ x, _root_.GD.N0232.N0720.N1173.d015937 theta x *
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1173.d015939
        ring]
    congr 1
    rw [_root_.GD.N0232.N0720.N1126.d016430
      (_root_.GD.N0232.N0720.N1173.d015935 theta) q (hq (_root_.GD.N0232.N0720.N1173.d015935 theta))]
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with x hx
    rw [hx]
    rfl





theorem d017609
    (k : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q) :
    MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) (_root_.GD.N0232.N0720.N1166.d017432 k)) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k) := by
  letI : SigmaFinite _root_.GD.N0232.N0720.N1188.d017606 := by
    unfold _root_.GD.N0232.N0720.N1188.d017606 _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hmoments := _root_.GD.N0232.N0720.N1167.d017493 k
  have hdata := _root_.GD.N0232.N0720.N1167.d017494 k
  have hcandidateJoint :=
    _root_.GD.N0232.N0720.N1188.d017608 k q hq
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1188.d017606
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938 x
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q x) =
        _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1188.d017606
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938 x
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
                (_root_.GD.N0232.N0720.N1166.d017432 k) x) +
          _root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1188.d017606
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k))
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)
            (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
              (_root_.GD.N0232.N0720.N1166.d017432 k)) x := by
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    simpa [_root_.GD.N0230.N0589.d000089, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1173.d015951
        _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k) x
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q x) hw htw ht2w hmass
  have htax : Integrable
      (_root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1188.d017606
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k))
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)
        (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1166.d017432 k))) (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    _root_.GD.N0230.N0589.d000101
      _root_.GD.N0232.N0720.N1188.d017606 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
      (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)
      (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k))
      hcandidateJoint hdata.cutoffJoint hpointwise
  have hperspective : Integrable
      (fun x ↦
        _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) (_root_.GD.N0232.N0720.N1166.d017432 k) x ^ 2 /
          _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
            (_root_.GD.N0232.N0720.N1166.d017432 k) x) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    refine htax.congr ?_
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1185.d017518
      _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)
      (_root_.GD.N0232.N0720.N1166.d017432 k) x hx.1 hx.2.1 hx.2.2.2
  have hcurrentEq :
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) (_root_.GD.N0232.N0720.N1166.d017432 k) =ᵐ[
            _root_.GD.N0232.N0720.N1080.d014172 2 2]
        fun x ↦
          _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1493.d016104
              (_root_.GD.N0232.N0720.N1166.d017432 k) x -
            _root_.GD.N0232.N0720.N1214.d014265 2 2 q x *
              _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
                (_root_.GD.N0232.N0720.N1166.d017432 k) x := by
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1185.d017516
      _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)
        (_root_.GD.N0232.N0720.N1166.d017432 k) x hx.1 hx.2.1
  have hcurrentMeas : AEStronglyMeasurable
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) (_root_.GD.N0232.N0720.N1166.d017432 k))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    apply ((_root_.GD.N0232.N0720.N1166.d017450 k).sub
      ((_root_.GD.N0232.N0720.N1214.d014266 2 2 q).mul
        (_root_.GD.N0232.N0720.N1166.d017449 k))).aestronglyMeasurable.congr
    exact hcurrentEq.symm
  exact _root_.GD.N0232.N0720.N1188.d017607
    (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k))
    (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) (_root_.GD.N0232.N0720.N1166.d017432 k))
    (_root_.GD.N0232.N0720.N1166.d017449 k) hcurrentMeas
    (_root_.GD.N0232.N0720.N1186.d017600 k) hperspective





theorem d017610 (k : ℕ) :
    MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k)) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k) := by
  have hborel :=
    _root_.GD.N0232.N0720.N1188.d017609
      k _root_.GD.N0232.N0720.N1185.d017526 _root_.GD.N0232.N0720.N1185.d017528
  have hcandidate : _root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1190.d017536 :=
    (_root_.GD.N0232.N0720.N1214.d014267 2 2 _root_.GD.N0232.N0720.N1185.d017526).trans
      _root_.GD.N0232.N0720.N1190.d017538
  have hcurrent :
      _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1185.d017526) (_root_.GD.N0232.N0720.N1166.d017432 k) =ᵐ[
            _root_.GD.N0232.N0720.N1080.d014172 2 2]
        _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) := by
    filter_upwards [hcandidate] with x hx
    exact _root_.GD.N0232.N0720.N1190.d017539
      _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k) x hx
  have hac : _root_.GD.N0232.N0720.N1186.d017597 k ≪ _root_.GD.N0232.N0720.N1080.d014172 2 2 :=
    withDensity_absolutelyContinuous _ _
  exact MemLp.ae_eq (hac.ae_le hcurrent) hborel




theorem d017611
    (k : ℕ) (reservoir : _root_.GD.N0232.N0720.N1188.d017604 → ℝ)
    (hreservoir : MemLp
      (_root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 reservoir) 2
      (_root_.GD.N0232.N0720.N1186.d017597 k)) :
    ‖_root_.GD.N0232.N0720.N1186.d017591 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir hreservoir -
        _root_.GD.N0232.N0720.N1186.d017593 _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) (_root_.GD.N0232.N0720.N1188.d017610 k)‖ ^ 2 =
      _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
        _root_.GD.N0232.N0720.N1190.d017536 (_root_.GD.N0232.N0720.N1166.d017432 k) reservoir := by
  exact _root_.GD.N0232.N0720.N1186.d017601 k reservoir
    (_root_.GD.N0232.N0720.N1188.d017610 k) hreservoir

#print axioms _root_.GD.N0232.N0720.N1188.d017607
#print axioms _root_.GD.N0232.N0720.N1188.d017608
#print axioms _root_.GD.N0232.N0720.N1188.d017609
#print axioms _root_.GD.N0232.N0720.N1188.d017610
#print axioms _root_.GD.N0232.N0720.N1188.d017611

end
end N1188
end N0720
end N0232
end GD
