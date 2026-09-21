import GD.Module0270
import GD.Module1051
import GD.Module1010
import GD.Module1045
import Mathlib.Tactic








open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1367

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1280 _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1281
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1279
open _root_.GD.N0232.N0720.N1289
open _root_.GD.N0232.N0719.N0932

noncomputable local instance d016848 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016849 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩

def d016850 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1281.d016761 (_root_.GD.N0232.N0720.N1285.d002679 N)

def d016851 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1281.d016761 (2 * _root_.GD.N0232.N0720.N1285.d002679 N)

theorem d016852 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1367.d016850 N := by
  apply _root_.GD.N0232.N0720.N1281.d016763
  linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]

theorem d016853 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1367.d016851 N := by
  apply _root_.GD.N0232.N0720.N1281.d016763
  linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]

theorem d016854 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1367.d016850 N ^ 2 / 4 = _root_.GD.N0232.N0720.N1279.d003958 N := by
  have he : _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  rw [show _root_.GD.N0232.N0720.N1367.d016850 N ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 (_root_.GD.N0232.N0720.N1285.d002679 N) by
    exact _root_.GD.N0232.N0720.N1281.d016764 he]
  unfold _root_.GD.N0232.N0720.N1279.d003958 _root_.GD.N0232.N0720.N1285.d002681
    _root_.GD.N0232.N0720.N1280.d003878 _root_.GD.N0232.N0720.N1283.d003854
  ring

theorem d016855 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1367.d016851 N ^ 2 / 4 = _root_.GD.N0232.N0720.N1279.d003959 N := by
  have he : 2 * _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  rw [show _root_.GD.N0232.N0720.N1367.d016851 N ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 (2 * _root_.GD.N0232.N0720.N1285.d002679 N) by
    exact _root_.GD.N0232.N0720.N1281.d016764 he]
  unfold _root_.GD.N0232.N0720.N1279.d003959 _root_.GD.N0232.N0720.N1280.d003878
    _root_.GD.N0232.N0720.N1283.d003854
  ring

def d016856 (N : ℝ) (hN : 3 ≤ N) : ℝ → _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1289.d016779 (_root_.GD.N0232.N0720.N1367.d016850 N) (_root_.GD.N0232.N0720.N1367.d016852 hN)

def d016857 (N : ℝ) (hN : 3 ≤ N) : ℝ → _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1289.d016779 (_root_.GD.N0232.N0720.N1367.d016851 N) (_root_.GD.N0232.N0720.N1367.d016853 hN)

@[fun_prop] theorem d016858
    (N : ℝ) (hN : 3 ≤ N) : Measurable (_root_.GD.N0232.N0720.N1367.d016856 N hN) := by
  exact (_root_.GD.N0232.N0720.N1289.d016783 _ _).measurable

@[fun_prop] theorem d016859
    (N : ℝ) (hN : 3 ≤ N) : Measurable (_root_.GD.N0232.N0720.N1367.d016857 N hN) := by
  exact (_root_.GD.N0232.N0720.N1289.d016783 _ _).measurable

def d016860 (N : ℝ) : Measure ℝ :=
  volume.withDensity (fun mu ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003964 N mu))

def d016861 (N : ℝ) : Measure ℝ :=
  volume.withDensity (fun mu ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003965 N mu))

theorem d016862 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1279.d003964 N) := by
  unfold _root_.GD.N0232.N0720.N1279.d003964 _root_.GD.N0232.N0720.N1277.d002621
  fun_prop

theorem d016863 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1279.d003965 N) := by
  unfold _root_.GD.N0232.N0720.N1279.d003965 _root_.GD.N0232.N0720.N1277.d002621
  fun_prop

theorem d016864 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1367.d016860 N Set.univ =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1285.d002682 N - 2) := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0232.N0720.N1279.d003980 hN)
    (ae_of_all volume (_root_.GD.N0232.N0720.N1279.d003978 hN))]
  rw [_root_.GD.N0232.N0720.N1279.d003982 hN]

theorem d016865 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1367.d016861 N Set.univ =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003936 N + 1) := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0232.N0720.N1279.d003981 hN)
    (ae_of_all volume (_root_.GD.N0232.N0720.N1279.d003979 hN))]
  rw [_root_.GD.N0232.N0720.N1279.d003983 hN]

theorem d016866 {N : ℝ} (hN : 3 ≤ N) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016860 N) where
  measure_univ_lt_top := by
    rw [_root_.GD.N0232.N0720.N1367.d016864 hN]
    exact ENNReal.ofReal_lt_top

theorem d016867 {N : ℝ} (hN : 3 ≤ N) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016861 N) where
  measure_univ_lt_top := by
    rw [_root_.GD.N0232.N0720.N1367.d016865 hN]
    exact ENNReal.ofReal_lt_top



def d016868 (N : ℝ) (hN : 3 ≤ N) : Measure _root_.GD.N0232.N0720.N1080.d014168 :=
  Measure.dirac _root_.GD.N0232.N0720.N1080.d014169 +
    (_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN) +
    (_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)

theorem d016869 {N : ℝ} (hN : 3 ≤ N) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016860 N) := _root_.GD.N0232.N0720.N1367.d016866 hN
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016861 N) := _root_.GD.N0232.N0720.N1367.d016867 hN
  unfold _root_.GD.N0232.N0720.N1367.d016868
  infer_instance



theorem d016870
    {N : ℝ} (hN : 3 ≤ N) (mu : ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega =
      (_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003958 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 := by
  have he : _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1367.d016856
  rw [_root_.GD.N0232.N0720.N1289.d016786]
  rw [show
      _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016850 N)
            (_root_.GD.N0232.N0720.N1397.d014815 omega).2.1 *
          (_root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016850 N)
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.1 *
            _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016850 N)
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.2) =
        _root_.GD.N0232.N0720.N1281.d016767 (_root_.GD.N0232.N0720.N1285.d002679 N)
          (_root_.GD.N0232.N0720.N1397.d014815 omega).2 by rfl]
  rw [_root_.GD.N0232.N0720.N1281.d016768 he]
  rw [_root_.GD.N0232.N0720.N1289.d016787 _ _ _ (_root_.GD.N0232.N0720.N1367.d016852 hN),
    _root_.GD.N0232.N0720.N1367.d016854 hN]
  rfl

theorem d016871
    {N : ℝ} (hN : 3 ≤ N) (mu : ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega =
      (_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003959 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 := by
  have he : 2 * _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1367.d016857
  rw [_root_.GD.N0232.N0720.N1289.d016786]
  rw [show
      _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016851 N)
            (_root_.GD.N0232.N0720.N1397.d014815 omega).2.1 *
          (_root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016851 N)
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.1 *
            _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1367.d016851 N)
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.2) =
        _root_.GD.N0232.N0720.N1281.d016767 (2 * _root_.GD.N0232.N0720.N1285.d002679 N)
          (_root_.GD.N0232.N0720.N1397.d014815 omega).2 by rfl]
  rw [_root_.GD.N0232.N0720.N1281.d016768 he]
  rw [_root_.GD.N0232.N0720.N1289.d016787 _ _ _ (_root_.GD.N0232.N0720.N1367.d016853 hN),
    _root_.GD.N0232.N0720.N1367.d016855 hN]
  rfl



theorem d016872
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ mu : ℝ, _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega
        ∂(_root_.GD.N0232.N0720.N1367.d016860 N)) =
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 *
        _root_.GD.N0232.N0720.N1280.d003937 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1 := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1367.d016862 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003978 hN _), smul_eq_mul,
    _root_.GD.N0232.N0720.N1367.d016870 hN]
  rw [show (fun mu : ℝ ↦ _root_.GD.N0232.N0720.N1279.d003964 N mu *
      ((_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003958 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
       _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2)) =
      (fun mu : ℝ ↦
        (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (_root_.GD.N0232.N0720.N1279.d003964 N mu *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003958 N)
            ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) by
      funext mu; ring]
  rw [integral_const_mul, _root_.GD.N0232.N0720.N1279.d003984 hN]
  ring

theorem d016873
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ mu : ℝ, _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega
        ∂(_root_.GD.N0232.N0720.N1367.d016861 N)) =
      _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 *
        _root_.GD.N0232.N0720.N1280.d003938 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1 := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1367.d016863 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003979 hN _), smul_eq_mul,
    _root_.GD.N0232.N0720.N1367.d016871 hN]
  rw [show (fun mu : ℝ ↦ _root_.GD.N0232.N0720.N1279.d003965 N mu *
      ((_root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003959 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
       _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2)) =
      (fun mu : ℝ ↦
        (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (_root_.GD.N0232.N0720.N1279.d003965 N mu *
          _root_.GD.N0232.N0720.N1277.d002621
            (_root_.GD.N0232.N0720.N1279.d003959 N)
            ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) by
      funext mu; ring]
  rw [integral_const_mul, _root_.GD.N0232.N0720.N1279.d003985 hN]
  ring



theorem d016874
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ ↦ _root_.GD.N0232.N0720.N1279.d003964 N mu *
      _root_.GD.N0232.N0720.N1277.d002621
        (_root_.GD.N0232.N0720.N1279.d003958 N) (x - mu)) := by
  have hU := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) (_root_.GD.N0232.N0720.N1279.d003971 hN) (_root_.GD.N0232.N0720.N1279.d003966 hN)
  have hw := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) (_root_.GD.N0232.N0720.N1279.d003968 hN) (_root_.GD.N0232.N0720.N1279.d003966 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003964
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1285.d002682 N)).sub
    (hw.const_mul 2)).congr (ae_of_all volume fun mu ↦ ?_)
  simp only [Pi.sub_apply]
  ring

theorem d016875
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ ↦ _root_.GD.N0232.N0720.N1279.d003965 N mu *
      _root_.GD.N0232.N0720.N1277.d002621
        (_root_.GD.N0232.N0720.N1279.d003959 N) (x - mu)) := by
  have hU := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) (_root_.GD.N0232.N0720.N1279.d003973 hN) (_root_.GD.N0232.N0720.N1279.d003967 hN)
  have hw := _root_.GD.N0232.N0720.N1277.d002639
    (x := x) (_root_.GD.N0232.N0720.N1279.d003969 hN) (_root_.GD.N0232.N0720.N1279.d003967 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003965
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1280.d003936 N)).add hw).congr
    (ae_of_all volume fun mu ↦ ?_)
  simp only [Pi.add_apply]
  ring

theorem d016876
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016860 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016862 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hbase := (_root_.GD.N0232.N0720.N1367.d016874 hN
    (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu ↦ ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      (_root_.GD.N0232.N0720.N1279.d003964 N mu *
        _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003958 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu)) =
      (ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003964 N mu)).toReal *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003978 hN mu)]
  rw [_root_.GD.N0232.N0720.N1367.d016870 hN]
  ring

theorem d016877
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ ↦
      _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016861 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016863 N).ennreal_ofReal
    (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)]
  have hbase := (_root_.GD.N0232.N0720.N1367.d016875 hN
    (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu ↦ ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
      (_root_.GD.N0232.N0720.N1279.d003965 N mu *
        _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1279.d003959 N)
          ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu)) =
      (ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003965 N mu)).toReal *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003979 hN mu)]
  rw [_root_.GD.N0232.N0720.N1367.d016871 hN]
  ring

theorem d016878
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1276.d016062 theta omega
        ∂((_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN))) =
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 *
        _root_.GD.N0232.N0720.N1280.d003937 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1 := by
  unfold _root_.GD.N0232.N0720.N1276.d016062
  rw [integral_map (_root_.GD.N0232.N0720.N1367.d016858 N hN).aemeasurable
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega).aestronglyMeasurable]
  exact _root_.GD.N0232.N0720.N1367.d016872 hN omega

theorem d016879
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    (∫ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1276.d016062 theta omega
        ∂((_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN))) =
      _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 *
        _root_.GD.N0232.N0720.N1280.d003938 N (_root_.GD.N0232.N0720.N1397.d014815 omega).1 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1 := by
  unfold _root_.GD.N0232.N0720.N1276.d016062
  rw [integral_map (_root_.GD.N0232.N0720.N1367.d016859 N hN).aemeasurable
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega).aestronglyMeasurable]
  exact _root_.GD.N0232.N0720.N1367.d016873 hN omega

theorem d016880
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN)) := by
  exact (integrable_map_measure
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega).aestronglyMeasurable
    (_root_.GD.N0232.N0720.N1367.d016858 N hN).aemeasurable).2
      (_root_.GD.N0232.N0720.N1367.d016876 hN omega)

theorem d016881
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)) := by
  exact (integrable_map_measure
    (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega).aestronglyMeasurable
    (_root_.GD.N0232.N0720.N1367.d016859 N hN).aemeasurable).2
      (_root_.GD.N0232.N0720.N1367.d016877 hN omega)




theorem d016882
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega =
      _root_.GD.N0232.N0720.N1282.d014826 N omega := by
  have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) := integrable_dirac (by simp)
  have hone := _root_.GD.N0232.N0720.N1367.d016880 hN omega
  have htwo := _root_.GD.N0232.N0720.N1367.d016881 hN omega
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
    _root_.GD.N0232.N0720.N1367.d016868
  rw [integral_add_measure (hzero.add_measure hone) htwo,
    integral_add_measure hzero hone, integral_dirac]
  rw [show _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1080.d014169 omega = 1 by
    exact _root_.GD.N0232.N0720.N1181.d016665 omega]
  rw [_root_.GD.N0232.N0720.N1367.d016878 hN, _root_.GD.N0232.N0720.N1367.d016879 hN]
  unfold _root_.GD.N0232.N0720.N1282.d014826
    _root_.GD.N0232.N0720.N1282.d014823
    _root_.GD.N0232.N0720.N1280.d003939
  have hp := _root_.GD.N0232.N0720.N1280.d003893
    (_root_.GD.N0232.N0720.N1397.d014815 omega).1
  field_simp [hp.ne']

end


end GD.N0232.N0720.N1367

#print axioms _root_.GD.N0232.N0720.N1367.d016869
#print axioms _root_.GD.N0232.N0720.N1367.d016872
#print axioms _root_.GD.N0232.N0720.N1367.d016873
#print axioms _root_.GD.N0232.N0720.N1367.d016882

