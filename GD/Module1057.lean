import GD.Module0204
import GD.Module1056
import GD.Module1055
import GD.Module1054
import Mathlib.Tactic















open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1361

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1280 _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1282
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1366
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0232.N0720.N1278
open _root_.GD.N0232.N0720.N1275
open _root_.GD.N0232.N0720.N1088
open _root_.GD.N0232.N0720.N1111

noncomputable local instance d016928 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016929 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩






theorem d016930
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) ↦
        _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z)
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let major : (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun z ↦
    (2 / _root_.GD.N0232.N0720.N1285.d002684 N) *
      (_root_.GD.N0232.N0720.N1280.d003888 N z.1 *
          (_root_.GD.N0232.N0720.N1280.d003884 e z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2) +
        _root_.GD.N0232.N0720.N1280.d003889 N z.1 *
          (_root_.GD.N0232.N0720.N1280.d003885 N z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2))
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith : 0 < N)).le
  have he9 : e ≤ 1 / 9 := _root_.GD.N0232.N0720.N1285.d002687 hN
  have hProdN : Integrable
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) ↦
        _root_.GD.N0232.N0720.N1280.d003888 N z.1 *
          (_root_.GD.N0232.N0720.N1280.d003884 e z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2))
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) :=
    (_root_.GD.N0232.N0720.N1280.d003896 hN).mul_prod
      (_root_.GD.N0232.N0720.N1280.d003927 he0 he9)
  have hProdB : Integrable
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) ↦
        _root_.GD.N0232.N0720.N1280.d003889 N z.1 *
          (_root_.GD.N0232.N0720.N1280.d003885 N z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2))
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) :=
    (_root_.GD.N0232.N0720.N1280.d003897 hN).mul_prod
      (_root_.GD.N0232.N0720.N1280.d003932 hN)
  have hMajor : Integrable major
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
    dsimp [major]
    exact (hProdN.add hProdB).const_mul _
  apply hMajor.mono_nonneg
      (_root_.GD.N0232.N0720.N1280.d003951 N)
  · exact Filter.Eventually.of_forall fun z ↦
      div_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1282.d014833 hN z).le
  · apply Filter.Eventually.of_forall
    intro z
    have hpoint := _root_.GD.N0232.N0720.N1278.d002662
      (x := z.1) (p := _root_.GD.N0232.N0720.N1280.d003886 z.1)
      (h := _root_.GD.N0232.N0720.N1280.d003887 N z.1) (k := _root_.GD.N0232.N0720.N1280.d003882 e z.2)
      (L := _root_.GD.N0232.N0720.N1280.d003884 e z.2)
      (C := _root_.GD.N0232.N0720.N1280.d003885 N z.2)
      (theta := _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) (gamma := _root_.GD.N0232.N0720.N1285.d002684 N)
      (D := _root_.GD.N0232.N0720.N1280.d003939 N z)
      (_root_.GD.N0232.N0720.N1280.d003942 hN)
      (_root_.GD.N0232.N0720.N1280.d003925 (by linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]) z.2)
      (_root_.GD.N0232.N0720.N1280.d003894 hN z.1)
      (_root_.GD.N0232.N0720.N1280.d003948 hN z)
    simpa [major, e, _root_.GD.N0232.N0720.N1280.d003940,
      _root_.GD.N0232.N0720.N1280.d003888, _root_.GD.N0232.N0720.N1280.d003889,
      mul_assoc, mul_left_comm, mul_comm] using hpoint



theorem d016931
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1282.d014825 N)
      ((gaussianReal 0 (1 / 4 : ℝ≥0)).prod
        _root_.GD.N0232.N0720.N1397.d014799) := by
  rw [_root_.GD.N0232.N0720.N1282.d014832]
  have hdensity : Measurable
      (fun z : _root_.GD.N0232.N0720.N1282.d014822 ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 z.1)) :=
    (_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hdensity
    (ae_of_all (volume.prod _root_.GD.N0232.N0720.N1280.d003880)
      fun _ ↦ ENNReal.ofReal_lt_top)]
  refine (_root_.GD.N0232.N0720.N1361.d016930 hN).congr
    (ae_of_all (volume.prod _root_.GD.N0232.N0720.N1280.d003880) fun z ↦ ?_)
  change _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z =
    (ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 z.1)).toReal *
      _root_.GD.N0232.N0720.N1282.d014825 N z
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1280.d003893 z.1).le]
  exact (_root_.GD.N0232.N0720.N1282.d014835 hN z).symm



theorem d016932
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (fun omega : _root_.GD.N0232.N0720.N1282.d014821 ↦
        _root_.GD.N0232.N0720.N1282.d014827 N omega ^ 2 / _root_.GD.N0232.N0720.N1282.d014826 N omega)
      (_root_.GD.N0107.d009030 2 2 0 1 1) := by
  have hprod := _root_.GD.N0232.N0720.N1361.d016931 hN
  rw [← _root_.GD.N0232.N0720.N1397.d014820] at hprod
  have hpull := (integrable_map_measure
    (_root_.GD.N0232.N0720.N1282.d014834 N).aestronglyMeasurable
    _root_.GD.N0232.N0720.N1397.d014816.aemeasurable).1 hprod
  simpa [Function.comp_def, _root_.GD.N0232.N0720.N1282.d014825,
    _root_.GD.N0232.N0720.N1282.d014827, _root_.GD.N0232.N0720.N1282.d014826] using hpull



theorem d016933
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
        _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1367.d016868 N hN)
              _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  refine (_root_.GD.N0232.N0720.N1361.d016932 hN).congr
    (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega ↦ ?_)
  dsimp only
  rw [_root_.GD.N0232.N0720.N1366.d016915 hN,
    _root_.GD.N0232.N0720.N1367.d016882 hN]
  ring



theorem d016934
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have href : Integrable
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) := integrable_dirac (by simp)
  exact (href.add_measure
    (_root_.GD.N0232.N0720.N1367.d016880 hN omega)).add_measure
    (_root_.GD.N0232.N0720.N1367.d016881 hN omega)

theorem d016935
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have href : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
    integrable_dirac (by simp [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1080.d014169])
  have htarget : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) :=
    (href.add_measure
      (_root_.GD.N0232.N0720.N1366.d016910 hN omega)).add_measure
      (_root_.GD.N0232.N0720.N1366.d016911 hN omega)
  have hlike := _root_.GD.N0232.N0720.N1361.d016934 hN omega
  refine (htarget.sub (hlike.const_mul
    (_root_.GD.N0232.N0720.N1405.d016086 omega))).congr
      (ae_of_all (_root_.GD.N0232.N0720.N1367.d016868 N hN) fun theta ↦ ?_)
  simp only [Pi.sub_apply]
  ring



theorem d016936
    (pi rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hpi : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) pi)
    (hrho : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho) :
    _root_.GD.N0232.N0720.N1276.d016063 (pi + rho) omega =
      _root_.GD.N0232.N0720.N1276.d016063 pi omega + _root_.GD.N0232.N0720.N1276.d016063 rho omega := by
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
  exact integral_add_measure hpi hrho



theorem d016937
    (pi rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hpi : Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - candidate omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) pi)
    (hrho : Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - candidate omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho) :
    _root_.GD.N0232.N0720.N1276.d016066 (pi + rho) candidate omega =
      _root_.GD.N0232.N0720.N1276.d016066 pi candidate omega +
        _root_.GD.N0232.N0720.N1276.d016066 rho candidate omega := by
  unfold _root_.GD.N0232.N0720.N1276.d016066
  exact integral_add_measure hpi hrho

theorem d016938 (rho : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    0 ≤ _root_.GD.N0232.N0720.N1276.d016063 rho omega := by
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
  apply integral_nonneg
  intro theta
  exact _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega



theorem d016939
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    1 ≤ _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega := by
  have href : Integrable
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) := integrable_dirac (by simp)
  have hfirst := _root_.GD.N0232.N0720.N1367.d016880 hN omega
  have hsecond := _root_.GD.N0232.N0720.N1367.d016881 hN omega
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
    _root_.GD.N0232.N0720.N1367.d016868
  rw [integral_add_measure (href.add_measure hfirst) hsecond,
    integral_add_measure href hfirst, integral_dirac]
  rw [show _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1080.d014169 omega = 1 by
    exact _root_.GD.N0232.N0720.N1181.d016665 omega]
  have h1 : 0 ≤ ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1276.d016062 theta omega
      ∂((_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN)) :=
    integral_nonneg fun theta ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega
  have h2 : 0 ≤ ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1276.d016062 theta omega
      ∂((_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)) :=
    integral_nonneg fun theta ↦ _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega
  linarith

theorem d016940 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1282.d014826 N) := by
  unfold _root_.GD.N0232.N0720.N1282.d014826 _root_.GD.N0232.N0720.N1282.d014823
  exact ((_root_.GD.N0232.N0720.N1280.d003950 N).comp
      _root_.GD.N0232.N0720.N1397.d014816).div
    ((_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst).comp
      _root_.GD.N0232.N0720.N1397.d014816)

theorem d016941
    {N : ℝ} (hN : 3 ≤ N) :
    Measurable (_root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN)) := by
  rw [show _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) = _root_.GD.N0232.N0720.N1282.d014826 N by
    funext omega
    exact _root_.GD.N0232.N0720.N1367.d016882 hN omega]
  exact _root_.GD.N0232.N0720.N1361.d016940 N



def d016942
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n) + rho



theorem d016943
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hcurrentSq : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Tendsto (fun n ↦ ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega
        ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)) atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.d002828
  · intro n
    exact ((hcurrentMeas.pow_const 2).div
      (_root_.GD.N0232.N0720.N1361.d016941
        (_root_.GD.N0232.N0720.N1275.d016919 n))).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (_root_.GD.N0232.N0720.N1361.d016939
      (_root_.GD.N0232.N0720.N1275.d016919 n))
  · exact ae_of_all _
      _root_.GD.N0232.N0720.N1275.d016926
  · exact hcurrentSq

theorem d016944
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ)
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hcurrentSq : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  apply hcurrentSq.mono_nonneg
  · exact ((hcurrentMeas.pow_const 2).div
      (_root_.GD.N0232.N0720.N1361.d016941
        (_root_.GD.N0232.N0720.N1275.d016919 n))).aestronglyMeasurable
  · apply ae_of_all
    intro omega
    have hden : 0 ≤ _root_.GD.N0232.N0720.N1276.d016063
        (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega :=
      zero_le_one.trans (_root_.GD.N0232.N0720.N1361.d016939
        (_root_.GD.N0232.N0720.N1275.d016919 n) omega)
    exact div_nonneg (sq_nonneg _) hden
  · apply ae_of_all
    intro omega
    have hfloor := _root_.GD.N0232.N0720.N1361.d016939
      (_root_.GD.N0232.N0720.N1275.d016919 n) omega
    exact div_le_self (sq_nonneg _) hfloor

theorem d016945
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ)
    (hlikelihood : ∀ omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho)
    (hcentered : ∀ omega, Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho)
    (hcurrentMeas : Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086))
    (hcurrentSq : Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1276.d016067 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
        _root_.GD.N0232.N0720.N1405.d016086 ≤
      2 * _root_.GD.N0232.N0720.N1276.d016067
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n))
          _root_.GD.N0232.N0720.N1405.d016086 +
        2 * ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
          _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
            _root_.GD.N0232.N0720.N1276.d016063
              (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega
            ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
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
  have hbound := _root_.GD.N0232.N0720.d002829
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
    (_root_.GD.N0232.N0720.N1361.d016944 rho n hcurrentMeas hcurrentSq)
  change _root_.GD.N0232.N0720.d002827 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1361.d016942 rho n))
      (_root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
        _root_.GD.N0232.N0720.N1405.d016086) ≤
    2 * _root_.GD.N0232.N0720.d002827 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (_root_.GD.N0232.N0720.N1276.d016063 central)
      (_root_.GD.N0232.N0720.N1276.d016066 central _root_.GD.N0232.N0720.N1405.d016086) +
    2 * ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      _root_.GD.N0232.N0720.N1276.d016066 rho _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063 central omega ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)
  rw [hE, hJ]
  exact hbound

theorem d016946
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) (n : ℕ)
    (hlikelihood : ∀ omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) rho) :
    0 ≤ _root_.GD.N0232.N0720.N1276.d016067 (_root_.GD.N0232.N0720.N1361.d016942 rho n)
      _root_.GD.N0232.N0720.N1405.d016086 := by
  unfold _root_.GD.N0232.N0720.N1276.d016067
  apply integral_nonneg
  intro omega
  apply div_nonneg (sq_nonneg _)
  change 0 ≤ _root_.GD.N0232.N0720.N1276.d016063
    (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n) + rho) omega
  rw [_root_.GD.N0232.N0720.N1361.d016936 _ _ _
    (_root_.GD.N0232.N0720.N1361.d016934
      (_root_.GD.N0232.N0720.N1275.d016919 n) omega) (hlikelihood omega)]
  exact add_nonneg
    (zero_le_one.trans (_root_.GD.N0232.N0720.N1361.d016939
      (_root_.GD.N0232.N0720.N1275.d016919 n) omega))
    (_root_.GD.N0232.N0720.N1361.d016938 rho omega)




theorem d016947
    (rho : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hlikelihood : ∀ k omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hcentered : ∀ k omega, Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hcurrentMeas : ∀ k, Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086))
    (hcurrentSq : ∀ k, Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (nhds 0) := by
  let centralAction : ℕ → ℝ := fun n ↦
    _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n))
      _root_.GD.N0232.N0720.N1405.d016086
  let shield : ℕ → ℕ → ℝ := fun k n ↦
    ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      _root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2 /
        _root_.GD.N0232.N0720.N1276.d016063
          (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega
      ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)
  let combined : ℕ → ℕ → ℝ := fun k n ↦
    _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1361.d016942 (rho k) n) _root_.GD.N0232.N0720.N1405.d016086
  obtain ⟨select, hcofinal, hlimit⟩ := _root_.GD.N0232.N0720.d002830
    centralAction shield combined
    _root_.GD.N0232.N0720.N1275.d016927
    (fun k ↦ _root_.GD.N0232.N0720.N1361.d016943
      (rho k) (hcurrentMeas k) (hcurrentSq k))
    (fun k n ↦ _root_.GD.N0232.N0720.N1361.d016946 (rho k) n
      (hlikelihood k))
    (fun k n ↦ _root_.GD.N0232.N0720.N1361.d016945 (rho k) n
      (hlikelihood k) (hcentered k) (hcurrentMeas k) (hcurrentSq k))
  exact ⟨select, hcofinal, hlimit⟩





theorem d016948
    {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
    [OpensMeasurableSpace Xi]
    (rho pi : ℕ → Measure Xi)
    (hrhoFinite : ∀ k, IsFiniteMeasure (rho k))
    (hpiFinite : ∀ k, IsFiniteMeasure (pi k))
    (hle : ∀ k, rho k ≤ pi k)
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 rho) :
    _root_.GD.N0232.N0720.N1111.d016605 pi := by
  intro xi U hU
  obtain ⟨a, ha, N, hN⟩ := hretain xi U hU
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (rho k) := hrhoFinite k
  letI : IsFiniteMeasure (pi k) := hpiFinite k
  exact (hN k hk).trans ((ENNReal.toReal_le_toReal
    (measure_ne_top (rho k) U) (measure_ne_top (pi k) U)).2 (hle k U))





theorem d016949
    {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
    [OpensMeasurableSpace Xi]
    (rho : ℕ → Measure Xi) (point : ℕ → Xi) (weight : ℕ → NNReal)
    (hrhoFinite : ∀ k, IsFiniteMeasure (rho k))
    (hweight : ∀ i, 0 < weight i)
    (hhit : ∀ xi U, U ∈ nhds xi → ∃ i, point i ∈ U)
    (hpersist : ∀ i, ∃ N, ∀ k, N ≤ k →
      weight i • Measure.dirac (point i) ≤ rho k) :
    _root_.GD.N0232.N0720.N1111.d016605 rho := by
  intro xi U hU
  obtain ⟨V, hVU, hVopen, hxiV⟩ := mem_nhds_iff.mp hU
  obtain ⟨i, hiV⟩ := hhit xi V (hVopen.mem_nhds hxiV)
  obtain ⟨N, hN⟩ := hpersist i
  refine ⟨(weight i : ℝ), by exact_mod_cast hweight i, N, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (rho k) := hrhoFinite k
  have hatomV : (weight i • Measure.dirac (point i)) V = (weight i : ENNReal) := by
    rw [Measure.coe_nnreal_smul_apply,
      Measure.dirac_apply' _ hVopen.measurableSet]
    simp [hiV]
  have hENN : (weight i : ENNReal) ≤ rho k U := by
    calc
      (weight i : ENNReal) = (weight i • Measure.dirac (point i)) V :=
        hatomV.symm
      _ ≤ rho k V := hN k hk V
      _ ≤ rho k U := measure_mono hVU
  have hreal := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
    (measure_ne_top (rho k) U)).2 hENN
  simpa using hreal



theorem d016950
    (rho : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hrhoFinite : ∀ k, IsFiniteMeasure (rho k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 rho)
    (select : ℕ → ℕ) :
    _root_.GD.N0232.N0720.N1111.d016605
      (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k)) := by
  apply _root_.GD.N0232.N0720.N1361.d016948 rho
    (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k))
      hrhoFinite
  · intro k
    letI : IsFiniteMeasure (rho k) := hrhoFinite k
    letI : IsFiniteMeasure
        (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 (select k))
          (_root_.GD.N0232.N0720.N1275.d016919 (select k))) :=
      _root_.GD.N0232.N0720.N1367.d016869 (_root_.GD.N0232.N0720.N1275.d016919 (select k))
    unfold _root_.GD.N0232.N0720.N1361.d016942
    infer_instance
  · intro k
    unfold _root_.GD.N0232.N0720.N1361.d016942
    exact Measure.le_add_left le_rfl
  · exact hretain





theorem d016951
    (rho : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hrhoFinite : ∀ k, IsFiniteMeasure (rho k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 rho)
    (hlikelihood : ∀ k omega, Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hcentered : ∀ k omega, Integrable (fun theta ↦
      (_root_.GD.N0232.N0720.N1276.d016061 theta - _root_.GD.N0232.N0720.N1405.d016086 omega) *
        _root_.GD.N0232.N0720.N1276.d016062 theta omega) (rho k))
    (hcurrentMeas : ∀ k, Measurable
      (_root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086))
    (hcurrentSq : ∀ k, Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 ↦
      _root_.GD.N0232.N0720.N1276.d016066 (rho k) _root_.GD.N0232.N0720.N1405.d016086 omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      _root_.GD.N0232.N0720.N1111.d016605
        (fun k ↦ _root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k)) ∧
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067
        (_root_.GD.N0232.N0720.N1361.d016942 (rho k) (select k))
        _root_.GD.N0232.N0720.N1405.d016086) atTop (nhds 0) := by
  obtain ⟨select, hselect, hlimit⟩ := _root_.GD.N0232.N0720.N1361.d016947
    rho hlikelihood hcentered hcurrentMeas hcurrentSq
  exact ⟨select, hselect,
    _root_.GD.N0232.N0720.N1361.d016950
      rho hrhoFinite hretain select,
    hlimit⟩

end

end GD.N0232.N0720.N1361

#print axioms _root_.GD.N0232.N0720.N1361.d016930
#print axioms _root_.GD.N0232.N0720.N1361.d016933
#print axioms _root_.GD.N0232.N0720.N1361.d016943
#print axioms _root_.GD.N0232.N0720.N1361.d016947
#print axioms _root_.GD.N0232.N0720.N1361.d016949
#print axioms _root_.GD.N0232.N0720.N1361.d016951
