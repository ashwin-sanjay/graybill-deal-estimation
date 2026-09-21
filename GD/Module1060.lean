import GD.Module1058
import GD.Module1057
import GD.Module0205
import GD.Module1040
import Mathlib.Tactic




















open Filter MeasureTheory Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1360

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1347
open _root_.GD.N0232.N0720.N1365
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602

noncomputable local instance d017006 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d017007 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩





theorem d017008
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0) :
    (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) =ᵐ[prior]
      (fun _ ↦ (0 : ℝ)) := by
  have hnonneg : ∀ theta, 0 ≤ _root_.GD.N0232.N0720.N1276.d016062 theta omega :=
    fun theta ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega
  apply (integral_eq_zero_iff_of_nonneg hnonneg hw).1
  simpa only [_root_.GD.N0232.N0720.N1276.d016063,
    _root_.GD.N0230.N0589.d000088] using hzero




theorem d017009
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0) :
    _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega = 0 := by
  unfold _root_.GD.N0232.N0720.N1276.d016066
  apply integral_eq_zero_of_ae
  filter_upwards
    [_root_.GD.N0232.N0720.N1360.d017008
      prior omega hw hzero] with theta htheta
  simp [htheta]


theorem d017010
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1276.d016060) (a : ℝ)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0) :
    _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega a = 0 := by
  unfold _root_.GD.N0230.N0589.d000087
  apply integral_eq_zero_of_ae
  filter_upwards
    [_root_.GD.N0232.N0720.N1360.d017008
      prior omega hw hzero] with theta htheta
  simp [htheta]






theorem d017011
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (htw : Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (ht2w : Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (hmass : _root_.GD.N0232.N0720.N1276.d016063 prior omega ≠ 0) :
    _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
          (candidate omega) -
        _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega ≤
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
        (action omega) := by
  have hc := _root_.GD.N0232.N0720.N1276.d016075 prior candidate omega
    hw htw ht2w hmass
  have ha := _root_.GD.N0232.N0720.N1276.d016075 prior action omega
    hw htw ht2w hmass
  have htax := _root_.GD.N0232.N0720.N1276.d016074
    prior candidate omega hw htw hmass
  have hnonneg : 0 ≤ _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 action
      (_root_.GD.N0232.N0720.N1276.d016065 prior) omega :=
    _root_.GD.N0230.N0589.d000091 prior _root_.GD.N0232.N0720.N1276.d016062 action
      (_root_.GD.N0232.N0720.N1276.d016065 prior)
      (fun theta x ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta x) omega
  rw [htax] at hc
  linarith


theorem d017012
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0) :
    _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
          (candidate omega) -
        _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega ≤
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
        (action omega) := by
  rw [_root_.GD.N0232.N0720.N1360.d017010
      prior omega (candidate omega) hw hzero,
    _root_.GD.N0232.N0720.N1360.d017010
      prior omega (action omega) hw hzero,
    _root_.GD.N0232.N0720.N1360.d017009
      prior candidate omega hw hzero,
    hzero]
  norm_num



theorem d017013
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hw : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (htw : Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (ht2w : Integrable (fun theta ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior) :
    _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
          (candidate omega) -
        _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega ≤
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
        (action omega) := by
  by_cases hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0
  · exact _root_.GD.N0232.N0720.N1360.d017012
      prior candidate action omega hw hzero
  · exact _root_.GD.N0232.N0720.N1360.d017011
      prior candidate action omega hw htw ht2w hzero







theorem d017014
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q) :
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) =
      ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
  unfold _root_.GD.N0230.N0589.d000084
  apply integral_congr_ae
  filter_upwards with theta
  rw [_root_.GD.N0232.N0720.N1126.d016430 theta q (hq theta)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
  simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]



theorem d017015
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : ∀ᵐ theta ∂prior, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ≠ ⊤)
    (hqIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior) :
    Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hjoint : Measurable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry :=
    _root_.GD.N0230.N0589.d000073
      _root_.GD.N0232.N0720.N1365.d016976
      _root_.GD.N0232.N0720.N1499.d014998.measurable
      (_root_.GD.N0232.N0720.N1214.d014266 2 2 q)
  apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
  constructor
  · filter_upwards [hq] with theta htheta
    have hbase := _root_.GD.N0232.N0720.N1126.d016429
      theta q htheta
    refine hbase.congr ?_
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
    simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]
  · refine hqIntegrable.congr ?_
    filter_upwards [hq] with theta htheta
    change (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal =
      ∫ omega,
        ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
    rw [show
      (∫ omega,
        ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫ omega,
          _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
      apply integral_congr_ae
      filter_upwards with omega
      exact Real.norm_of_nonneg
        (_root_.GD.N0230.N0589.d000075
          (fun eta x ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x)
          theta omega)]
    rw [_root_.GD.N0232.N0720.N1126.d016430 theta q htheta]
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
    simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]



theorem d017016
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hqIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior) :
    Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hjoint : Measurable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry :=
    _root_.GD.N0230.N0589.d000073
      _root_.GD.N0232.N0720.N1365.d016976
      _root_.GD.N0232.N0720.N1499.d014998.measurable
      (_root_.GD.N0232.N0720.N1214.d014266 2 2 q)
  apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
  constructor
  · filter_upwards with theta
    have hbase := _root_.GD.N0232.N0720.N1126.d016429
      theta q (hq theta)
    refine hbase.congr ?_
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
    simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]
  · refine hqIntegrable.congr (ae_of_all prior fun theta ↦ ?_)
    change (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal =
      ∫ omega,
        ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
    rw [show
      (∫ omega,
        ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫ omega,
          _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
      apply integral_congr_ae
      filter_upwards with omega
      exact Real.norm_of_nonneg
        (_root_.GD.N0230.N0589.d000075
          (fun eta x ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x)
          theta omega)]
    rw [_root_.GD.N0232.N0720.N1126.d016430 theta q (hq theta)]
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
    simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]





theorem d017017
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hjoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2))) :
    Integrable (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hright : Integrable (fun theta ↦
      ∫ omega,
        _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) prior :=
    hjoint.integral_prod_left
  refine hright.congr (ae_of_all prior fun theta ↦ ?_)
  change (∫ omega,
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) theta omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal
  rw [_root_.GD.N0232.N0720.N1126.d016430 theta q (hq theta)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
  simp [_root_.GD.N0230.N0589.d000071, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]



theorem d017018
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure prior] :
    Integrable _root_.GD.N0232.N0720.N1276.d016062.uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  apply (integrable_prod_iff
    _root_.GD.N0232.N0720.N1365.d016976.aestronglyMeasurable).2
  constructor
  · filter_upwards with theta
    change Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016062 theta omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
    simpa only [_root_.GD.N0232.N0720.N1276.d016062] using
      _root_.GD.N0232.N0720.N1484.d015103 2 2 theta
  · refine (integrable_const (1 : ℝ)).congr
      (ae_of_all prior fun theta ↦ ?_)
    change (1 : ℝ) =
      ∫ omega, ‖_root_.GD.N0232.N0720.N1276.d016062 theta omega‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
    symm
    rw [show (∫ omega, ‖_root_.GD.N0232.N0720.N1276.d016062 theta omega‖
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
      ∫ omega, _root_.GD.N0232.N0720.N1276.d016062 theta omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
      apply integral_congr_ae
      filter_upwards with omega
      exact Real.norm_of_nonneg
        (_root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega)]
    exact _root_.GD.N0232.N0720.N1484.d015104 2 2 theta









theorem d017019
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : ∀ᵐ theta ∂prior, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ≠ ⊤)
    (hqIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) ∧
      _root_.GD.N0232.N0720.N1276.d016067 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) ≤
        ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let response : _root_.GD.N0232.N0720.N1080.d014168 → _root_.GD.N0232.N0720.N1276.d016060 → ℝ := fun theta omega ↦
    _root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1214.d014265 2 2 q omega
  have hweight := _root_.GD.N0232.N0720.N1360.d017018 prior
  have hjoint := _root_.GD.N0232.N0720.N1360.d017015
    prior q hq hqIntegrable
  have hresponseMeasurable : Measurable response.uncurry := by
    exact (_root_.GD.N0232.N0720.N1499.d014998.measurable.comp measurable_fst).sub
      ((_root_.GD.N0232.N0720.N1214.d014266 2 2 q).comp measurable_snd)
  have hcurrentMeasurable : AEStronglyMeasurable
      (fun z : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2 * response z.1 z.2)
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :=
    (_root_.GD.N0232.N0720.N1365.d016976.mul
      hresponseMeasurable).aestronglyMeasurable
  have henergy : Integrable (fun z : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2 * response z.1 z.2 ^ 2)
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
    refine hjoint.congr (ae_of_all _ fun z ↦ ?_)
    change _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2 *
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 q z.2 - _root_.GD.N0232.N0720.N1276.d016061 z.1) ^ 2 =
      _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2 *
        (_root_.GD.N0232.N0720.N1276.d016061 z.1 - _root_.GD.N0232.N0720.N1214.d014265 2 2 q z.2) ^ 2
    ring
  have hsafe :=
    _root_.GD.N0232.N0720.N1347.d002846
      prior (_root_.GD.N0232.N0720.N1080.d014172 2 2) _root_.GD.N0232.N0720.N1276.d016062 response
      (fun theta omega ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega)
      hweight hcurrentMeasurable henergy
  have hcurrentEq (omega : _root_.GD.N0232.N0720.N1276.d016060) :
      (∫ theta, _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ∂prior) =
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega := by
    unfold _root_.GD.N0232.N0720.N1276.d016066 response
    apply integral_congr_ae
    filter_upwards with theta
    ring
  have hsafeEq :
      (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦ _root_.GD.N0232.N0720.N1347.d002831
        (∫ theta, _root_.GD.N0232.N0720.N1276.d016062 theta omega ∂prior)
        (∫ theta, _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ∂prior))
        =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      (fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) := by
    filter_upwards [hweight.prod_left_ae] with omega hw
    rw [hcurrentEq omega]
    change _root_.GD.N0232.N0720.N1347.d002831 (_root_.GD.N0232.N0720.N1276.d016063 prior omega)
        (_root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega) = _
    by_cases hzero : _root_.GD.N0232.N0720.N1276.d016063 prior omega = 0
    · rw [_root_.GD.N0232.N0720.N1360.d017009
        prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega hw hzero, hzero]
      simp
    · exact _root_.GD.N0232.N0720.N1347.d002833 hzero
  have hperspective : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    hsafe.1.congr hsafeEq
  have henergyRisk :
      (∫ omega, ∫ theta,
          _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ^ 2
            ∂prior ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
    calc
      (∫ omega, ∫ theta,
          _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ^ 2
            ∂prior ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
          ∫ theta, ∫ omega,
            _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 ∂prior :=
        (integral_integral_swap henergy).symm
      _ = ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
        apply integral_congr_ae
        filter_upwards [hq] with theta htheta
        rw [_root_.GD.N0232.N0720.N1126.d016430 theta q htheta]
        apply integral_congr_ae
        filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 2 2 q] with omega homega
        simp only [response, _root_.GD.N0232.N0720.N1276.d016062, _root_.GD.N0232.N0720.N1276.d016061, homega]
        ring
  refine ⟨hperspective, ?_⟩
  unfold _root_.GD.N0232.N0720.N1276.d016067
  calc
    (∫ omega,
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        _root_.GD.N0232.N0720.N1347.d002837 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
          (fun omega ↦ ∫ theta, _root_.GD.N0232.N0720.N1276.d016062 theta omega ∂prior)
          (fun omega ↦ ∫ theta,
            _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ∂prior) := by
      unfold _root_.GD.N0232.N0720.N1347.d002837
      exact integral_congr_ae hsafeEq.symm
    _ ≤ ∫ omega, ∫ theta,
          _root_.GD.N0232.N0720.N1276.d016062 theta omega * response theta omega ^ 2
            ∂prior ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := hsafe.2
    _ = ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := henergyRisk




theorem d017020
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hqIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) ∧
      _root_.GD.N0232.N0720.N1276.d016067 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) ≤
        ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
  exact
    _root_.GD.N0232.N0720.N1360.d017019
      prior q (ae_of_all prior hq) hqIntegrable









theorem d017021
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hrisk : (∫⁻ theta, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ∂prior) ≠ ⊤) :
    (∀ᵐ theta ∂prior, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ≠ ⊤) ∧
      Integrable (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior ∧
      Integrable
        (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 q)).uncurry
        (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) ∧
      Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) ∧
      _root_.GD.N0232.N0720.N1276.d016067 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) ≤
        (∫⁻ theta, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ∂prior).toReal := by
  have hriskMeasurable : Measurable
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q) :=
    (_root_.GD.N0232.N0720.N1499.d015008 2 2 q).measurable
  have hriskLtTop : ∀ᵐ theta ∂prior, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q < ⊤ :=
    ae_lt_top hriskMeasurable hrisk
  have hriskFinite : ∀ᵐ theta ∂prior, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ≠ ⊤ :=
    hriskLtTop.mono fun _ htheta ↦ ne_of_lt htheta
  have hriskIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior :=
    integrable_toReal_of_lintegral_ne_top
      hriskMeasurable.aemeasurable hrisk
  have hjoint := _root_.GD.N0232.N0720.N1360.d017015
    prior q hriskFinite hriskIntegrable
  have hperspective :=
    _root_.GD.N0232.N0720.N1360.d017019
      prior q hriskFinite hriskIntegrable
  have hriskIntegral :
      (∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior) =
        (∫⁻ theta, _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ∂prior).toReal :=
    integral_toReal hriskMeasurable.aemeasurable hriskLtTop
  refine ⟨hriskFinite, hriskIntegrable, hjoint, hperspective.1, ?_⟩
  rw [← hriskIntegral]
  exact hperspective.2






theorem d017022
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior]
    (candidate action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hcandidateJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hperspective : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior) :
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate -
      _root_.GD.N0232.N0720.N1276.d016067 prior candidate ≤
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  rw [_root_.GD.N0230.N0589.d000086 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate hcandidateJoint,
    _root_.GD.N0230.N0589.d000086 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action hactionJoint]
  unfold _root_.GD.N0230.N0589.d000085 _root_.GD.N0232.N0720.N1276.d016067
  change
    (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
        _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
          omega (candidate omega) ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) -
      (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
        _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) ≤
    ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        omega (action omega) ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
  have hcObj : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
        (candidate omega)) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0230.N0589.d000071] using
      hcandidateJoint.integral_prod_right
  have haObj : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 omega
        (action omega)) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0230.N0589.d000071] using
      hactionJoint.integral_prod_right
  rw [← integral_sub hcObj hperspective]
  apply integral_mono_ae (hcObj.sub hperspective) haObj
  filter_upwards [hmoments] with omega hx
  exact _root_.GD.N0232.N0720.N1360.d017013
    prior candidate action omega hx.1 hx.2.1 hx.2.2



theorem d017023
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior]
    (candidate action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hcandidateJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hactionJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hperspective : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      _root_.GD.N0232.N0720.N1276.d016063 prior omega ≠ 0) :
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate -
      _root_.GD.N0232.N0720.N1276.d016067 prior candidate ≤
    _root_.GD.N0230.N0589.d000084 prior (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action := by
  apply _root_.GD.N0232.N0720.N1360.d017022
    prior candidate action hcandidateJoint hactionJoint hperspective
  filter_upwards [hmoments] with omega hx
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

end

end GD.N0232.N0720.N1360

#print axioms _root_.GD.N0232.N0720.N1360.d017008
#print axioms _root_.GD.N0232.N0720.N1360.d017013
#print axioms _root_.GD.N0232.N0720.N1360.d017014
#print axioms _root_.GD.N0232.N0720.N1360.d017016
#print axioms _root_.GD.N0232.N0720.N1360.d017017
#print axioms _root_.GD.N0232.N0720.N1360.d017020
#print axioms _root_.GD.N0232.N0720.N1360.d017021
#print axioms _root_.GD.N0232.N0720.N1360.d017022
