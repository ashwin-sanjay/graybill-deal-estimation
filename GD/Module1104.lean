import GD.Module1103
import GD.Module1060
import GD.Module1040
import Mathlib.Tactic










open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1349

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1275
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1347
open _root_.GD.N0232.N0720.N1365
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1361
open _root_.GD.N0232.N0720.N1362
open _root_.GD.N0232.N0720.N1360
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602

attribute [local instance]
  _root_.GD.N0232.N0720.N1361.d016928
  _root_.GD.N0232.N0720.N1361.d016929

private local instance d017734 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance








theorem d017735
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure prior]
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hqFinite : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hqIntegrable : Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal) prior) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) ∧
      _root_.GD.N0232.N0720.N1276.d016067 prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) ≤
        ∫ theta, (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal ∂prior := by
  exact _root_.GD.N0232.N0720.N1360.d017020
    prior q hqFinite hqIntegrable



private theorem d017736 :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      _root_.GD.N0232.N0720.N1111.d016605
        (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942
          (_root_.GD.N0232.N0720.N1362.d017692 k) (select k)) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (nhds 0) :=
  _root_.GD.N0232.N0720.N1362.d017731


noncomputable def d017737 : ℕ → ℕ :=
  Classical.choose _root_.GD.N0232.N0720.N1349.d017736


noncomputable def d017738 (k : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1275.d016918 (_root_.GD.N0232.N0720.N1349.d017737 k)



def d017739 (k : ℕ) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1361.d016942 (_root_.GD.N0232.N0720.N1362.d017692 k) (_root_.GD.N0232.N0720.N1349.d017737 k)

theorem d017740 (k : ℕ) :
    k ≤ _root_.GD.N0232.N0720.N1349.d017737 k :=
  (Classical.choose_spec _root_.GD.N0232.N0720.N1349.d017736).1 k

theorem d017741 :
    Tendsto _root_.GD.N0232.N0720.N1349.d017737 atTop atTop :=
  tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall _root_.GD.N0232.N0720.N1349.d017740) tendsto_id

theorem d017742 :
    Tendsto _root_.GD.N0232.N0720.N1349.d017738 atTop atTop := by
  exact _root_.GD.N0232.N0720.N1275.d016921.comp _root_.GD.N0232.N0720.N1349.d017741

theorem d017743 (k : ℕ) :
    3 ≤ _root_.GD.N0232.N0720.N1349.d017738 k :=
  _root_.GD.N0232.N0720.N1275.d016919 (_root_.GD.N0232.N0720.N1349.d017737 k)

theorem d017744 (k : ℕ) :
    _root_.GD.N0232.N0720.N1349.d017739 k =
      _root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1349.d017738 k) (_root_.GD.N0232.N0720.N1349.d017743 k) +
        _root_.GD.N0232.N0720.N1362.d017692 k := by
  rfl

theorem d017745 :
    _root_.GD.N0232.N0720.N1111.d016605 _root_.GD.N0232.N0720.N1349.d017739 := by
  intro theta U hU
  obtain ⟨a, ha, N, hN⟩ :=
    (Classical.choose_spec _root_.GD.N0232.N0720.N1349.d017736).2.1 theta U hU
  refine ⟨a, ha, N, fun k hk ↦ ?_⟩
  simpa only [_root_.GD.N0232.N0720.N1349.d017739, _root_.GD.N0232.N0720.N1349.d017737] using hN k hk

theorem d017746 :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1349.d017739 k) _root_.GD.N0232.N0720.N1405.d016086)
      atTop (nhds 0) := by
  simpa only [_root_.GD.N0232.N0720.N1349.d017739, _root_.GD.N0232.N0720.N1349.d017737] using
    (Classical.choose_spec _root_.GD.N0232.N0720.N1349.d017736).2.2

noncomputable instance d017747 (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1349.d017739 k) := by
  unfold _root_.GD.N0232.N0720.N1349.d017739
  infer_instance

theorem d017748 (k : ℕ) :
    _root_.GD.N0232.N0720.N1349.d017739 k ≠ 0 := by
  intro hzero
  have hpos := _root_.GD.N0232.N0720.N1362.d017732
    k (_root_.GD.N0232.N0720.N1349.d017737 k)
  rw [← _root_.GD.N0232.N0720.N1349.d017739, hzero] at hpos
  simp at hpos



theorem d017749 (k : ℕ) :
    Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal)
      (_root_.GD.N0232.N0720.N1349.d017739 k) := by
  simpa [_root_.GD.N0232.N0720.N1349.d017739] using
    (_root_.GD.N0232.N0720.N1362.d017729
      k (_root_.GD.N0232.N0720.N1349.d017737 k))





def d017750 (k : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1111.d016604 2 2 id _root_.GD.N0232.N0720.N1349.d017739 k
      _root_.GD.N0232.N0720.N1362.d017715 -
    _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1349.d017739 k) _root_.GD.N0232.N0720.N1405.d016086

private theorem d017751 :
    _root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1405.d016086 :=
  (_root_.GD.N0232.N0720.N1214.d014267 2 2 _root_.GD.N0232.N0720.N1362.d017715).trans
    _root_.GD.N0232.N0720.N1362.d017716



theorem d017752
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1276.d016067 prior
        (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715) =
      _root_.GD.N0232.N0720.N1276.d016067 prior
        _root_.GD.N0232.N0720.N1405.d016086 := by
  unfold _root_.GD.N0232.N0720.N1276.d016067
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1349.d017751] with omega homega
  have hcurrent : _root_.GD.N0232.N0720.N1276.d016066 prior
      (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715) omega =
        _root_.GD.N0232.N0720.N1276.d016066 prior _root_.GD.N0232.N0720.N1405.d016086 omega := by
    unfold _root_.GD.N0232.N0720.N1276.d016066
    simp only [homega]
  rw [hcurrent]



theorem d017753 :
    _root_.GD.N0232.N0720.N1111.d016610 2 2 id _root_.GD.N0232.N0720.N1349.d017739
      _root_.GD.N0232.N0720.N1349.d017750 := by
  intro k q hqFinite hqIntegrable
  let prior := _root_.GD.N0232.N0720.N1349.d017739 k
  letI : IsFiniteMeasure prior := _root_.GD.N0232.N0720.N1349.d017747 k
  have hcJoint := _root_.GD.N0232.N0720.N1360.d017016
    prior _root_.GD.N0232.N0720.N1362.d017715 _root_.GD.N0232.N0720.N1362.d017718
      (by simpa [prior] using
        _root_.GD.N0232.N0720.N1349.d017749 k)
  have hqJoint := _root_.GD.N0232.N0720.N1360.d017016
    prior q hqFinite (by simpa [prior] using hqIntegrable)
  have hpRaw := _root_.GD.N0232.N0720.N1362.d017730
    k (_root_.GD.N0232.N0720.N1349.d017737 k)
  have hpRawPrior : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 prior _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    simpa only [prior, _root_.GD.N0232.N0720.N1349.d017739] using hpRaw
  have hpBorel : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 prior
          (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715) omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    refine hpRawPrior.congr ?_
    filter_upwards [_root_.GD.N0232.N0720.N1349.d017751] with omega homega
    have hcurrent : _root_.GD.N0232.N0720.N1276.d016066 prior
        _root_.GD.N0232.N0720.N1405.d016086 omega =
          _root_.GD.N0232.N0720.N1276.d016066 prior
            (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715) omega := by
      unfold _root_.GD.N0232.N0720.N1276.d016066
      simp only [homega]
    rw [hcurrent]
  have hmoments : ∀ᵐ omega ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2),
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable (fun theta ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior := by
    filter_upwards with omega
    have hm := _root_.GD.N0232.N0720.N1362.d017728
      k (_root_.GD.N0232.N0720.N1349.d017737 k) omega
    simpa [prior, _root_.GD.N0232.N0720.N1349.d017739] using ⟨hm.1, hm.2.1, hm.2.2.1⟩
  have hlower := _root_.GD.N0232.N0720.N1360.d017022
    prior (_root_.GD.N0232.N0720.N1214.d014265 2 2 _root_.GD.N0232.N0720.N1362.d017715)
      (_root_.GD.N0232.N0720.N1214.d014265 2 2 q) hcJoint hqJoint hpBorel hmoments
  rw [_root_.GD.N0232.N0720.N1360.d017014
      prior _root_.GD.N0232.N0720.N1362.d017715
        _root_.GD.N0232.N0720.N1362.d017718,
    _root_.GD.N0232.N0720.N1360.d017014
      prior q hqFinite,
    _root_.GD.N0232.N0720.N1349.d017752 prior]
    at hlower
  simpa [_root_.GD.N0232.N0720.N1349.d017750, _root_.GD.N0232.N0720.N1111.d016604,
    prior, Function.id_def] using hlower



theorem d017754 :
    _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1362.d017715 := by
  apply _root_.GD.N0232.N0720.N1111.d016611
    2 2 id continuous_id Function.surjective_id _root_.GD.N0232.N0720.N1349.d017739
      (fun k ↦ _root_.GD.N0232.N0720.N1349.d017747 k)
      _root_.GD.N0232.N0720.N1349.d017745
      _root_.GD.N0232.N0720.N1362.d017715 _root_.GD.N0232.N0720.N1362.d017718
      _root_.GD.N0232.N0720.N1349.d017749
      _root_.GD.N0232.N0720.N1349.d017750
      _root_.GD.N0232.N0720.N1349.d017753
  have haction := _root_.GD.N0232.N0720.N1349.d017746
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 haction) epsilon hepsilon
  refine ⟨N, fun k hk ↦ ?_⟩
  have hkAction := hN k hk
  have hkAbs : |_root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1349.d017739 k) _root_.GD.N0232.N0720.N1405.d016086| < epsilon := by
    simpa only [Real.dist_eq, sub_zero] using hkAction
  have hdeficit :
      _root_.GD.N0232.N0720.N1111.d016604 2 2 id _root_.GD.N0232.N0720.N1349.d017739 k
          _root_.GD.N0232.N0720.N1362.d017715 - _root_.GD.N0232.N0720.N1349.d017750 k =
        _root_.GD.N0232.N0720.N1276.d016067
          (_root_.GD.N0232.N0720.N1349.d017739 k) _root_.GD.N0232.N0720.N1405.d016086 := by
    unfold _root_.GD.N0232.N0720.N1349.d017750
    ring
  change |_root_.GD.N0232.N0720.N1111.d016604 2 2 id _root_.GD.N0232.N0720.N1349.d017739 k
    _root_.GD.N0232.N0720.N1362.d017715 - _root_.GD.N0232.N0720.N1349.d017750 k| < epsilon
  rw [hdeficit]
  exact hkAbs

end

end GD.N0232.N0720.N1349

#print axioms _root_.GD.N0232.N0720.N1349.d017735
#print axioms _root_.GD.N0232.N0720.N1349.d017753
#print axioms _root_.GD.N0232.N0720.N1349.d017754
