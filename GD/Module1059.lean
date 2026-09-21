import GD.Module1057
import GD.Module0205
import GD.Module1058
import Mathlib.Tactic













open Filter MeasureTheory Topology

namespace GD.N0232.N0720.N1348

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0232.N0720.N1275
open _root_.GD.N0232.N0720.N1361
open _root_.GD.N0232.N0720.N1347
open _root_.GD.N0232.N0720.N1365
open _root_.GD.N0232.N0720.N1088
open _root_.GD.N0232.N0720.N1111

noncomputable local instance d016998 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016999 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩



theorem d017000
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite rho] :
    Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086) := by
  unfold _root_.GD.N0232.N0720.N1276.d016066
  have hjoint : Measurable (fun z : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 ↦
      (_root_.GD.N0232.N0720.N1276.d016061 z.1 - _root_.GD.N0232.N0720.N1405.d016086 z.2) *
        _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2) := by
    exact ((_root_.GD.N0232.N0720.N1499.d014998.measurable.comp measurable_fst).sub
      (_root_.GD.N0232.N0720.N1365.d016969.comp measurable_snd)).mul
        _root_.GD.N0232.N0720.N1365.d016976
  exact hjoint.stronglyMeasurable.integral_prod_left'.measurable


def d017001
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ) : ℝ :=
  ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
    _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
      (_root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega +
        _root_.GD.N0232.N0720.N1276.d016063 rho omega) ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)



theorem d017002
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hevidenceMeas : Measurable (_root_.GD.N0232.N0720.N1276.d016063 rho))
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hevidencePos : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1276.d016063 rho omega)
    (hintrinsic : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 rho omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Tendsto (_root_.GD.N0232.N0720.N1348.d017001 rho) atTop (𝓝 0) := by
  apply _root_.GD.N0232.N0720.N1347.d002847
  · intro n
    exact ((hcurrentMeas.pow_const 2).div
      ((_root_.GD.N0232.N0720.N1361.d016941
          (_root_.GD.N0232.N0720.N1275.d016919 n)).add hevidenceMeas)).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun omega ↦
      (_root_.GD.N0232.N0720.N1361.d016939
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega).trans' zero_le_one
  · exact hevidencePos
  · exact ae_of_all _
      _root_.GD.N0232.N0720.N1275.d016926
  · exact hintrinsic

theorem d017003
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ)
    (hevidenceMeas : Measurable (_root_.GD.N0232.N0720.N1276.d016063 rho))
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hevidencePos : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1276.d016063 rho omega)
    (hintrinsic : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 rho omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        (_root_.GD.N0232.N0720.N1276.d016063
            (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega +
          _root_.GD.N0232.N0720.N1276.d016063 rho omega)) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  apply hintrinsic.mono_nonneg
  · exact ((hcurrentMeas.pow_const 2).div
      ((_root_.GD.N0232.N0720.N1361.d016941
          (_root_.GD.N0232.N0720.N1275.d016919 n)).add hevidenceMeas)).aestronglyMeasurable
  · filter_upwards [hevidencePos] with omega hrho
    have hcentral : 0 ≤ _root_.GD.N0232.N0720.N1276.d016063
        (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega :=
      zero_le_one.trans (_root_.GD.N0232.N0720.N1361.d016939
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
    exact div_nonneg (sq_nonneg _) (add_pos_of_nonneg_of_pos hcentral hrho).le
  · filter_upwards [hevidencePos] with omega hrho
    have hcentral : 0 ≤ _root_.GD.N0232.N0720.N1276.d016063
        (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega :=
      zero_le_one.trans (_root_.GD.N0232.N0720.N1361.d016939
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
    exact div_le_div_of_nonneg_left (sq_nonneg _) hrho
      (le_add_of_nonneg_left hcentral)


theorem d017004
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ)
    (hlikelihood : ∀ omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho)
    (hcentered : ∀ omega, Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho)
    (hevidenceMeas : Measurable (_root_.GD.N0232.N0720.N1276.d016063 rho))
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hevidencePos : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1276.d016063 rho omega)
    (hintrinsic : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 rho omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1276.d016067 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
        _root_.GD.N0232.N0720.N1405.d016086 ≤
      2 * _root_.GD.N0232.N0720.N1276.d016067
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n))
          _root_.GD.N0232.N0720.N1405.d016086 +
        2 * _root_.GD.N0232.N0720.N1348.d017001 rho n := by
  let central := _root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)
  have hE : _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1361.d016942 rho n) =
      fun omega ↦ _root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega := by
    funext omega
    exact _root_.GD.N0232.N0720.N1361.d016936 central rho omega
      (_root_.GD.N0232.N0720.N1361.d016934
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega) (hlikelihood omega)
  have hJ : _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
      _root_.GD.N0232.N0720.N1405.d016086 = fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086 omega +
          _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega := by
    funext omega
    exact _root_.GD.N0232.N0720.N1361.d016937 central rho
      _root_.GD.N0232.N0720.N1405.d016086 omega
      (_root_.GD.N0232.N0720.N1361.d016935
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega) (hcentered omega)
  have hmixed : AEStronglyMeasurable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086 omega +
          _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega) ^ 2 /
        (_root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    letI : IsFiniteMeasure central :=
      _root_.GD.N0232.N0720.N1367.d016869 (_root_.GD.N0232.N0720.N1275.d016919 n)
    have hmeas : Measurable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086 omega +
            _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega) ^ 2 /
          (_root_.GD.N0232.N0720.N1276.d016063 central omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega)) :=
      (((_root_.GD.N0232.N0720.N1348.d017000 central).add
        hcurrentMeas).pow_const 2).div
          ((_root_.GD.N0232.N0720.N1361.d016941
            (_root_.GD.N0232.N0720.N1275.d016919 n)).add hevidenceMeas)
    exact hmeas.aestronglyMeasurable
  have hbound :=
    _root_.GD.N0232.N0720.N1347.d002850
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1276.d016063 central) (_root_.GD.N0232.N0720.N1276.d016063 rho)
      (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086)
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086)
      (ae_of_all _ fun omega ↦
        (_root_.GD.N0232.N0720.N1361.d016939
          (_root_.GD.N0232.N0720.N1275.d016919 n) omega).trans_lt' zero_lt_one)
      (ae_of_all _ (_root_.GD.N0232.N0720.N1361.d016938 rho))
      (_root_.GD.N0232.N0720.N1361.d016933
        (_root_.GD.N0232.N0720.N1275.d016919 n))
      (_root_.GD.N0232.N0720.N1348.d017003 rho n
        hevidenceMeas hcurrentMeas hevidencePos hintrinsic)
      hmixed
  change _root_.GD.N0232.N0720.d002827 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1361.d016942 rho n))
      (_root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
        _root_.GD.N0232.N0720.N1405.d016086) ≤
    2 * _root_.GD.N0232.N0720.d002827 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1276.d016063 central)
      (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086) +
    2 * _root_.GD.N0232.N0720.N1348.d017001 rho n
  rw [hE, hJ]
  exact hbound



theorem d017005
    (rho : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hrhoFinite : ∀ k, IsFiniteMeasure (rho k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 rho)
    (hlikelihood : ∀ k omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hcentered : ∀ k omega, Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hevidenceMeas : ∀ k, Measurable (_root_.GD.N0232.N0720.N1276.d016063 (rho k)))
    (hcurrentMeas : ∀ k, Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086))
    (hevidencePos : ∀ k, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1276.d016063 (rho k) omega)
    (hintrinsic : ∀ k, Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 (rho k) omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      _root_.GD.N0232.N0720.N1111.d016605
        (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k)) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (𝓝 0) := by
  let centralAction : ℕ → ℝ := fun n ↦
    _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n))
      _root_.GD.N0232.N0720.N1405.d016086
  let shield : ℕ → ℕ → ℝ := fun k n ↦
    _root_.GD.N0232.N0720.N1348.d017001 (rho k) n
  let combined : ℕ → ℕ → ℝ := fun k n ↦
    _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1361.d016942 (rho k) n) _root_.GD.N0232.N0720.N1405.d016086
  obtain ⟨select, hcofinal, hlimit⟩ := _root_.GD.N0232.N0720.d002830
    centralAction shield combined
    _root_.GD.N0232.N0720.N1275.d016927
    (fun k ↦ _root_.GD.N0232.N0720.N1348.d017002
      (rho k) (hevidenceMeas k) (hcurrentMeas k)
      (hevidencePos k) (hintrinsic k))
    (fun k n ↦ _root_.GD.N0232.N0720.N1361.d016946 (rho k) n
      (hlikelihood k))
    (fun k n ↦ _root_.GD.N0232.N0720.N1348.d017004 (rho k) n
      (hlikelihood k) (hcentered k) (hevidenceMeas k)
      (hcurrentMeas k) (hevidencePos k) (hintrinsic k))
  exact ⟨select, hcofinal,
    _root_.GD.N0232.N0720.N1361.d016950
      rho hrhoFinite hretain select,
    hlimit⟩

end

end GD.N0232.N0720.N1348

#print axioms _root_.GD.N0232.N0720.N1348.d017002
#print axioms _root_.GD.N0232.N0720.N1348.d017004
#print axioms _root_.GD.N0232.N0720.N1348.d017005
