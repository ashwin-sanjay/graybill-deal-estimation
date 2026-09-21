import GD.Module1053
import GD.Module1052
import GD.Module1011
import Mathlib.Tactic










open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1366

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1280 _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1282
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1277
open _root_.GD.N0232.N0720.N1279
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1405

noncomputable local instance d016902 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016903 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩



theorem d016904
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ ↦ mu *
      (_root_.GD.N0232.N0720.N1279.d003964 N mu *
        _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003958 N)
          (x - mu))) := by
  have hU := _root_.GD.N0232.N0720.N1277.d002642
    (x := x)
    (_root_.GD.N0232.N0720.N1279.d003971 hN)
    (_root_.GD.N0232.N0720.N1279.d003966 hN)
  have hw := _root_.GD.N0232.N0720.N1277.d002642
    (x := x)
    (_root_.GD.N0232.N0720.N1279.d003968 hN)
    (_root_.GD.N0232.N0720.N1279.d003966 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003964
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1285.d002682 N)).sub
    (hw.const_mul 2)).congr (ae_of_all volume fun mu ↦ ?_)
  change
    _root_.GD.N0232.N0720.N1285.d002682 N *
          (mu * (_root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003962 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003958 N)
              (x - mu))) -
        2 * (mu * (_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003960 N) mu *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003958 N)
            (x - mu))) =
      mu *
        ((_root_.GD.N0232.N0720.N1285.d002682 N * _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003962 N) mu -
          2 * _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003960 N) mu) *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003958 N)
            (x - mu))
  ring

theorem d016905
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ ↦ mu *
      (_root_.GD.N0232.N0720.N1279.d003965 N mu *
        _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003959 N)
          (x - mu))) := by
  have hU := _root_.GD.N0232.N0720.N1277.d002642
    (x := x)
    (_root_.GD.N0232.N0720.N1279.d003973 hN)
    (_root_.GD.N0232.N0720.N1279.d003967 hN)
  have hw := _root_.GD.N0232.N0720.N1277.d002642
    (x := x)
    (_root_.GD.N0232.N0720.N1279.d003969 hN)
    (_root_.GD.N0232.N0720.N1279.d003967 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003965
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1280.d003936 N)).add hw).congr
    (ae_of_all volume fun mu ↦ ?_)
  change
    _root_.GD.N0232.N0720.N1280.d003936 N *
          (mu * (_root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003963 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003959 N)
              (x - mu))) +
        mu * (_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003961 N) mu *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003959 N)
            (x - mu)) =
      mu *
        ((_root_.GD.N0232.N0720.N1280.d003936 N * _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003963 N) mu +
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003961 N) mu) *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003959 N)
            (x - mu))
  ring

theorem d016906
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016860 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016862 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hbase :=
    (_root_.GD.N0232.N0720.N1366.d016904 hN
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu ↦ ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu *
          (_root_.GD.N0232.N0720.N1279.d003964 N mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003958 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) =
      (ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1279.d003964 N mu)).toReal *
        (_root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) *
          _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega)
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1279.d003978 hN mu)]
  rw [_root_.GD.N0232.N0720.N1367.d016870 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016856
  simp only [_root_.GD.N0232.N0720.N1289.d016780]
  ring

theorem d016907
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016861 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016863 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hbase :=
    (_root_.GD.N0232.N0720.N1366.d016905 hN
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu ↦ ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu *
          (_root_.GD.N0232.N0720.N1279.d003965 N mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003959 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) =
      (ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1279.d003965 N mu)).toReal *
        (_root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) *
          _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega)
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1279.d003979 hN mu)]
  rw [_root_.GD.N0232.N0720.N1367.d016871 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016857
  simp only [_root_.GD.N0232.N0720.N1289.d016780]
  ring



theorem d016908
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ mu : ℝ,
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega
        ∂(_root_.GD.N0232.N0720.N1367.d016860 N)) =
      (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 *
        (_root_.GD.N0232.N0720.N1285.d002682 N *
            (1 - _root_.GD.N0232.N0720.N1285.d002681 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
              _root_.GD.N0232.N0720.N1280.d003887 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 -
          2 * _root_.GD.N0232.N0720.N1285.d002679 N *
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)) := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1367.d016862 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1279.d003978 hN _),
    smul_eq_mul, _root_.GD.N0232.N0720.N1367.d016870 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016856
  simp only [_root_.GD.N0232.N0720.N1289.d016780]
  rw [show (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1279.d003964 N mu *
        (mu *
          ((_root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003958 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
            _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2))) =
      (fun mu : ℝ ↦
        (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu *
          (_root_.GD.N0232.N0720.N1279.d003964 N mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003958 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu)))) by
      funext mu; ring]
  rw [integral_const_mul,
    _root_.GD.N0232.N0720.N1279.d003986 hN]
  have hV : _root_.GD.N0232.N0720.N1280.d003879 N ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003892 hN).ne'
  have hv0 : _root_.GD.N0232.N0720.N1280.d003878 ≠ 0 := _root_.GD.N0232.N0720.N1280.d003890.ne'
  unfold _root_.GD.N0232.N0720.N1279.d003962
    _root_.GD.N0232.N0720.N1279.d003958
    _root_.GD.N0232.N0720.N1279.d003960
  field_simp [hV, hv0]

theorem d016909
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ mu : ℝ,
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega
        ∂(_root_.GD.N0232.N0720.N1367.d016861 N)) =
      (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 *
        (_root_.GD.N0232.N0720.N1280.d003936 N *
            (1 - (1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N) * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
              _root_.GD.N0232.N0720.N1280.d003887 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 +
          2 * _root_.GD.N0232.N0720.N1285.d002679 N *
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)) := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1367.d016863 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1279.d003979 hN _),
    smul_eq_mul, _root_.GD.N0232.N0720.N1367.d016871 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016857
  simp only [_root_.GD.N0232.N0720.N1289.d016780]
  rw [show (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1279.d003965 N mu *
        (mu *
          ((_root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003959 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
            _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2))) =
      (fun mu : ℝ ↦
        (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu *
          (_root_.GD.N0232.N0720.N1279.d003965 N mu *
            _root_.GD.N0232.N0720.N1277.d002621
              (_root_.GD.N0232.N0720.N1279.d003959 N)
              ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu)))) by
      funext mu; ring]
  rw [integral_const_mul,
    _root_.GD.N0232.N0720.N1279.d003987 hN]
  have hV : _root_.GD.N0232.N0720.N1280.d003879 N ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003892 hN).ne'
  have hv0 : _root_.GD.N0232.N0720.N1280.d003878 ≠ 0 := _root_.GD.N0232.N0720.N1280.d003890.ne'
  unfold _root_.GD.N0232.N0720.N1279.d003963
    _root_.GD.N0232.N0720.N1279.d003959
    _root_.GD.N0232.N0720.N1279.d003961
  field_simp [hV, hv0]

theorem d016910
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016860 N).map
        (_root_.GD.N0232.N0720.N1367.d016856 N hN)) := by
  exact (integrable_map_measure
    ((_root_.GD.N0232.N0720.N1499.d014998.mul
      (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)
    (_root_.GD.N0232.N0720.N1367.d016858 N hN).aemeasurable).2
      (_root_.GD.N0232.N0720.N1366.d016906 hN omega)

theorem d016911
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016861 N).map
        (_root_.GD.N0232.N0720.N1367.d016857 N hN)) := by
  exact (integrable_map_measure
    ((_root_.GD.N0232.N0720.N1499.d014998.mul
      (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)
    (_root_.GD.N0232.N0720.N1367.d016859 N hN).aemeasurable).2
      (_root_.GD.N0232.N0720.N1366.d016907 hN omega)

theorem d016912
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega
        ∂((_root_.GD.N0232.N0720.N1367.d016860 N).map
          (_root_.GD.N0232.N0720.N1367.d016856 N hN))) =
      (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 *
        (_root_.GD.N0232.N0720.N1285.d002682 N *
            (1 - _root_.GD.N0232.N0720.N1285.d002681 N * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
              _root_.GD.N0232.N0720.N1280.d003887 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 -
          2 * _root_.GD.N0232.N0720.N1285.d002679 N *
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)) := by
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1276.d016062
  rw [integral_map
    (μ := _root_.GD.N0232.N0720.N1367.d016860 N)
    (φ := _root_.GD.N0232.N0720.N1367.d016856 N hN)
    (f := fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      theta.location * _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega)
    (_root_.GD.N0232.N0720.N1367.d016858 N hN).aemeasurable
    ((_root_.GD.N0232.N0720.N1499.d014998.mul
      (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)]
  simpa [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1276.d016062] using
    _root_.GD.N0232.N0720.N1366.d016908 hN omega

theorem d016913
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega
        ∂((_root_.GD.N0232.N0720.N1367.d016861 N).map
          (_root_.GD.N0232.N0720.N1367.d016857 N hN))) =
      (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 *
        (_root_.GD.N0232.N0720.N1280.d003936 N *
            (1 - (1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N) * _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) *
              _root_.GD.N0232.N0720.N1280.d003887 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 +
          2 * _root_.GD.N0232.N0720.N1285.d002679 N *
            _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)) := by
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1276.d016062
  rw [integral_map
    (μ := _root_.GD.N0232.N0720.N1367.d016861 N)
    (φ := _root_.GD.N0232.N0720.N1367.d016857 N hN)
    (f := fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      theta.location * _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega)
    (_root_.GD.N0232.N0720.N1367.d016859 N hN).aemeasurable
    ((_root_.GD.N0232.N0720.N1499.d014998.mul
      (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)]
  simpa [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1276.d016062] using
    _root_.GD.N0232.N0720.N1366.d016909 hN omega



theorem d016914
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016064 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega =
      _root_.GD.N0232.N0720.N1364.d016841 N
          (_root_.GD.N0232.N0720.N1397.d014815 omega) /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1 := by
  have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
    integrable_dirac (by simp [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1080.d014169])
  have hone := _root_.GD.N0232.N0720.N1366.d016910 hN omega
  have htwo := _root_.GD.N0232.N0720.N1366.d016911 hN omega
  unfold _root_.GD.N0232.N0720.N1276.d016064 _root_.GD.N0232.N0720.N1367.d016868
  rw [integral_add_measure (hzero.add_measure hone) htwo,
    integral_add_measure hzero hone, integral_dirac,
    _root_.GD.N0232.N0720.N1366.d016912 hN,
    _root_.GD.N0232.N0720.N1366.d016913 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1080.d014169
  simp only [zero_mul, zero_add]
  unfold _root_.GD.N0232.N0720.N1364.d016841
    _root_.GD.N0232.N0720.N1364.d016790 _root_.GD.N0232.N0720.N1364.d016794
    _root_.GD.N0232.N0720.N1364.d016795 _root_.GD.N0232.N0720.N1364.d016792
    _root_.GD.N0232.N0720.N1364.d016793
  simp only [_root_.GD.N0232.N0720.N1364.d016790]
  unfold _root_.GD.N0232.N0720.N1285.d002681
  have hp : _root_.GD.N0232.N0720.N1280.d003886
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1280.d003893 _).ne'
  field_simp [hp]




theorem d016915
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016066 (_root_.GD.N0232.N0720.N1367.d016868 N hN)
        _root_.GD.N0232.N0720.N1405.d016086 omega =
      -_root_.GD.N0232.N0720.N1282.d014827 N omega := by
  have hlikelihood : Integrable
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
    have hzero : Integrable
        (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
        (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) := integrable_dirac (by simp)
    exact (hzero.add_measure
      (_root_.GD.N0232.N0720.N1367.d016880 hN omega)).add_measure
      (_root_.GD.N0232.N0720.N1367.d016881 hN omega)
  have hmoment : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
    have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
        _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
        (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
      integrable_dirac (by simp [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1080.d014169])
    exact (hzero.add_measure
      (_root_.GD.N0232.N0720.N1366.d016910 hN omega)).add_measure
      (_root_.GD.N0232.N0720.N1366.d016911 hN omega)
  rw [_root_.GD.N0232.N0720.N1276.d016072 _ _ _ hlikelihood hmoment,
    _root_.GD.N0232.N0720.N1366.d016914 hN,
    _root_.GD.N0232.N0720.N1367.d016882 hN]
  unfold _root_.GD.N0232.N0720.N1405.d016086 _root_.GD.N0232.N0720.N1282.d014826
    _root_.GD.N0232.N0720.N1282.d014823 _root_.GD.N0232.N0720.N1282.d014827 _root_.GD.N0232.N0720.N1282.d014824
  rw [_root_.GD.N0232.N0720.N1364.d016843
    hN]
  have hp : _root_.GD.N0232.N0720.N1280.d003886
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1280.d003893 _).ne'
  field_simp [hp]
  ring



theorem d016916
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1405.d016081 N (_root_.GD.N0232.N0720.N1367.d016868 N hN)
      _root_.GD.N0232.N0720.N1405.d016086 (-1) := by
  apply _root_.GD.N0232.N0720.N1405.d016085 (_root_.GD.N0232.N0720.N1367.d016869 hN)
  · exact ae_of_all _ (_root_.GD.N0232.N0720.N1367.d016882 hN)
  · exact ae_of_all _ (_root_.GD.N0232.N0720.N1366.d016915 hN)



theorem d016917
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1276.d016067 (_root_.GD.N0232.N0720.N1367.d016868 N hN)
        _root_.GD.N0232.N0720.N1405.d016086 ≤ 48 / N ^ 9 := by
  exact _root_.GD.N0232.N0720.N1405.d016083 hN
    (_root_.GD.N0232.N0720.N1366.d016916 hN)

end

end GD.N0232.N0720.N1366

#print axioms _root_.GD.N0232.N0720.N1366.d016914
#print axioms _root_.GD.N0232.N0720.N1366.d016915
#print axioms _root_.GD.N0232.N0720.N1366.d016916
#print axioms _root_.GD.N0232.N0720.N1366.d016917
