import GD.Module1055
import Mathlib.Tactic










open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1365

noncomputable section

set_option maxHeartbeats 800000

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1280 _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1283 _root_.GD.N0232.N0720.N1278
open _root_.GD.N0232.N0720.N1282 _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1277 _root_.GD.N0232.N0720.N1279
open _root_.GD.N0232.N0720.N1367 _root_.GD.N0232.N0720.N1366
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0591
open _root_.GD.N0232.N0719.N0932

noncomputable local instance d016952 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016953 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩





theorem d016954
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (fun z : _root_.GD.N0232.N0720.N1282.d014822 =>
        _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z)
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let perspective : _root_.GD.N0232.N0720.N1282.d014822 → ℝ := fun z =>
    _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z
  let major : _root_.GD.N0232.N0720.N1282.d014822 → ℝ := fun z =>
    (2 / _root_.GD.N0232.N0720.N1285.d002684 N) *
      ((z.1 ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 z.1 ^ 2 /
          _root_.GD.N0232.N0720.N1280.d003887 N z.1) *
        (_root_.GD.N0232.N0720.N1280.d003884 e z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2) +
       ((_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * z.1 ^ 2 *
          _root_.GD.N0232.N0720.N1280.d003887 N z.1) *
        (_root_.GD.N0232.N0720.N1280.d003885 N z.2 ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e z.2))
  have he0 : 0 ≤ e := (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he9 : e ≤ 1 / 9 := _root_.GD.N0232.N0720.N1285.d002687 hN
  have hlocN : Integrable (fun x : ℝ =>
      x ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 x ^ 2 / _root_.GD.N0232.N0720.N1280.d003887 N x)
      volume := _root_.GD.N0232.N0720.N1280.d003896 hN
  have hlocB : Integrable (fun x : ℝ =>
      (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 * _root_.GD.N0232.N0720.N1280.d003887 N x)
      volume := _root_.GD.N0232.N0720.N1280.d003897 hN
  have hancN : Integrable (fun r =>
      _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)
      _root_.GD.N0232.N0720.N1280.d003880 :=
    _root_.GD.N0232.N0720.N1280.d003927 he0 he9
  have hancB : Integrable (fun r =>
      _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)
      _root_.GD.N0232.N0720.N1280.d003880 :=
    _root_.GD.N0232.N0720.N1280.d003932 hN
  have hmajor : Integrable major
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
    dsimp [major]
    exact ((hlocN.mul_prod hancN).add (hlocB.mul_prod hancB)).const_mul _
  have hpmeas : AEStronglyMeasurable perspective
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
    simpa [perspective] using _root_.GD.N0232.N0720.N1280.d003951 N
  apply hmajor.mono_nonneg hpmeas
  · filter_upwards with z
    dsimp [perspective]
    exact div_nonneg (sq_nonneg _)
      (_root_.GD.N0232.N0720.N1282.d014833 hN z).le
  · filter_upwards with z
    dsimp [perspective, major]
    have hpoint := _root_.GD.N0232.N0720.N1278.d002662
      (x := z.1)
      (p := _root_.GD.N0232.N0720.N1280.d003886 z.1)
      (h := _root_.GD.N0232.N0720.N1280.d003887 N z.1)
      (k := _root_.GD.N0232.N0720.N1280.d003882 e z.2)
      (L := _root_.GD.N0232.N0720.N1280.d003884 e z.2)
      (C := _root_.GD.N0232.N0720.N1280.d003885 N z.2)
      (theta := _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N)
      (gamma := _root_.GD.N0232.N0720.N1285.d002684 N)
      (D := _root_.GD.N0232.N0720.N1280.d003939 N z)
      (_root_.GD.N0232.N0720.N1280.d003942 hN)
      (_root_.GD.N0232.N0720.N1280.d003925 (show e < 1 by linarith) z.2)
      (_root_.GD.N0232.N0720.N1280.d003894 hN z.1)
      (_root_.GD.N0232.N0720.N1280.d003948 hN z)
    simpa [_root_.GD.N0232.N0720.N1280.d003940, e, mul_assoc, mul_left_comm, mul_comm] using hpoint



theorem d016955
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1282.d014825 N)
      ((gaussianReal 0 (1 / 4 : ℝ≥0)).prod
        _root_.GD.N0232.N0720.N1397.d014799) := by
  rw [_root_.GD.N0232.N0720.N1282.d014832]
  let density : _root_.GD.N0232.N0720.N1282.d014822 → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 z.1)
  have hdensity : Measurable density := by
    exact (_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hdensity
    (ae_of_all (volume.prod _root_.GD.N0232.N0720.N1280.d003880)
      fun _ => ENNReal.ofReal_lt_top)]
  refine (_root_.GD.N0232.N0720.N1365.d016954 hN).congr
    (ae_of_all (volume.prod _root_.GD.N0232.N0720.N1280.d003880)
      fun z => ?_)
  change _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z =
    (density z).toReal • _root_.GD.N0232.N0720.N1282.d014825 N z
  rw [show (density z).toReal = _root_.GD.N0232.N0720.N1280.d003886 z.1 by
    simp [density, (_root_.GD.N0232.N0720.N1280.d003893 z.1).le]]
  simp only [smul_eq_mul]
  exact (_root_.GD.N0232.N0720.N1282.d014835 hN z).symm



theorem d016956
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
        _root_.GD.N0232.N0720.N1282.d014827 N omega ^ 2 / _root_.GD.N0232.N0720.N1282.d014826 N omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hproduct := _root_.GD.N0232.N0720.N1365.d016955 hN
  rw [← _root_.GD.N0232.N0720.N1397.d014820] at hproduct
  have hmap := (integrable_map_measure
    (_root_.GD.N0232.N0720.N1282.d014834 N).aestronglyMeasurable
    _root_.GD.N0232.N0720.N1397.d014816.aemeasurable).1 hproduct
  change Integrable (_root_.GD.N0232.N0720.N1282.d014825 N ∘
    _root_.GD.N0232.N0720.N1397.d014815) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
  exact hmap



theorem d016957
    (t m : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => y ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 t (y - m)) := by
  have hsq := (_root_.GD.N0232.N0720.N1280.d003895 ht).comp_sub_right m
  have hlin := (_root_.GD.N0232.N0720.N1277.d002640 t ht).comp_sub_right m
  have hmass := (_root_.GD.N0232.N0720.N1277.d002625 t).comp_sub_right m
  have hsum := (hsq.add (hlin.const_mul (2 * m))).add
    (hmass.const_mul (m ^ 2))
  refine hsum.congr (ae_of_all volume fun y => ?_)
  change
    (y - m) ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 t (y - m) +
        (2 * m) * ((y - m) * _root_.GD.N0232.N0720.N1277.d002621 t (y - m)) +
        m ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 t (y - m) =
      y ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 t (y - m)
  ring

theorem d016958
    {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ => y ^ 2 *
      (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y))) := by
  have ht : 0 < _root_.GD.N0232.N0720.N1277.d002628 a b := _root_.GD.N0232.N0720.N1277.d002630 ha hb
  have hs := _root_.GD.N0232.N0720.N1365.d016957
    (_root_.GD.N0232.N0720.N1277.d002628 a b) (_root_.GD.N0232.N0720.N1277.d002629 a b x) ht
  have hscaled := hs.const_mul (_root_.GD.N0232.N0720.N1277.d002621 (a + b) x)
  refine hscaled.congr (ae_of_all volume fun y => ?_)
  change _root_.GD.N0232.N0720.N1277.d002621 (a + b) x *
      (y ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1277.d002628 a b)
        (y - _root_.GD.N0232.N0720.N1277.d002629 a b x)) =
    y ^ 2 * (_root_.GD.N0232.N0720.N1277.d002621 a y * _root_.GD.N0232.N0720.N1277.d002621 b (x - y))
  rw [_root_.GD.N0232.N0720.N1277.d002634 ha hb]
  ring

theorem d016959
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ => mu ^ 2 *
      (_root_.GD.N0232.N0720.N1279.d003964 N mu *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - mu))) := by
  have hU := _root_.GD.N0232.N0720.N1365.d016958
    (x := x) (_root_.GD.N0232.N0720.N1279.d003971 hN) (_root_.GD.N0232.N0720.N1279.d003966 hN)
  have hw := _root_.GD.N0232.N0720.N1365.d016958
    (x := x) (_root_.GD.N0232.N0720.N1279.d003968 hN) (_root_.GD.N0232.N0720.N1279.d003966 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003964
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1285.d002682 N)).sub
    (hw.const_mul 2)).congr (ae_of_all volume fun mu => ?_)
  change
    _root_.GD.N0232.N0720.N1285.d002682 N *
          (mu ^ 2 * (_root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003962 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - mu))) -
        2 * (mu ^ 2 *
          (_root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003960 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - mu))) =
      mu ^ 2 *
        ((_root_.GD.N0232.N0720.N1285.d002682 N *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003962 N) mu -
          2 * _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003960 N) mu) *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N) (x - mu))
  ring

theorem d016960
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    Integrable (fun mu : ℝ => mu ^ 2 *
      (_root_.GD.N0232.N0720.N1279.d003965 N mu *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - mu))) := by
  have hU := _root_.GD.N0232.N0720.N1365.d016958
    (x := x) (_root_.GD.N0232.N0720.N1279.d003973 hN) (_root_.GD.N0232.N0720.N1279.d003967 hN)
  have hw := _root_.GD.N0232.N0720.N1365.d016958
    (x := x) (_root_.GD.N0232.N0720.N1279.d003969 hN) (_root_.GD.N0232.N0720.N1279.d003967 hN)
  unfold _root_.GD.N0232.N0720.N1279.d003965
  refine ((hU.const_mul (_root_.GD.N0232.N0720.N1280.d003936 N)).add hw).congr
    (ae_of_all volume fun mu => ?_)
  change
    _root_.GD.N0232.N0720.N1280.d003936 N *
          (mu ^ 2 * (_root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003963 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - mu))) +
        mu ^ 2 *
          (_root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003961 N) mu *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - mu)) =
      mu ^ 2 *
        ((_root_.GD.N0232.N0720.N1280.d003936 N *
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003963 N) mu +
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003961 N) mu) *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N) (x - mu))
  ring

theorem d016961
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ =>
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) ^ 2 *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016860 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016860
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016862 N).ennreal_ofReal
    (ae_of_all volume fun _ => ENNReal.ofReal_lt_top)]
  have hbase :=
    (_root_.GD.N0232.N0720.N1365.d016959 hN
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu => ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu ^ 2 * (_root_.GD.N0232.N0720.N1279.d003964 N mu *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003958 N)
            ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) =
      (ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003964 N mu)).toReal *
        (_root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) ^ 2 *
          _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016856 N hN mu) omega)
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003978 hN mu),
    _root_.GD.N0232.N0720.N1367.d016870 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016856
  simp only [_root_.GD.N0232.N0720.N1289.d016780,
    smul_eq_mul]
  ring

theorem d016962
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun mu : ℝ =>
      _root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) ^ 2 *
        _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega)
      (_root_.GD.N0232.N0720.N1367.d016861 N) := by
  unfold _root_.GD.N0232.N0720.N1367.d016861
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1367.d016863 N).ennreal_ofReal
    (ae_of_all volume fun _ => ENNReal.ofReal_lt_top)]
  have hbase :=
    (_root_.GD.N0232.N0720.N1365.d016960 hN
      (_root_.GD.N0232.N0720.N1397.d014815 omega).1).const_mul
      (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
        _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1)
  refine hbase.congr (ae_of_all volume fun mu => ?_)
  change
    (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) (_root_.GD.N0232.N0720.N1397.d014815 omega).2 /
          _root_.GD.N0232.N0720.N1280.d003886 (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (mu ^ 2 * (_root_.GD.N0232.N0720.N1279.d003965 N mu *
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1279.d003959 N)
            ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu))) =
      (ENNReal.ofReal (_root_.GD.N0232.N0720.N1279.d003965 N mu)).toReal *
        (_root_.GD.N0232.N0720.N1276.d016061 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) ^ 2 *
          _root_.GD.N0232.N0720.N1276.d016062 (_root_.GD.N0232.N0720.N1367.d016857 N hN mu) omega)
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1279.d003979 hN mu),
    _root_.GD.N0232.N0720.N1367.d016871 hN]
  unfold _root_.GD.N0232.N0720.N1276.d016061 _root_.GD.N0232.N0720.N1367.d016857
  simp only [_root_.GD.N0232.N0720.N1289.d016780,
    smul_eq_mul]
  ring

theorem d016963
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
    integrable_dirac (by simp [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1080.d014169])
  have hone : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN)) := by
    exact (integrable_map_measure
      ((_root_.GD.N0232.N0720.N1499.d014998.pow 2 |>.mul
        (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)
      (_root_.GD.N0232.N0720.N1367.d016858 N hN).aemeasurable).2
        (_root_.GD.N0232.N0720.N1365.d016961 hN omega)
  have htwo : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      ((_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)) := by
    exact (integrable_map_measure
      ((_root_.GD.N0232.N0720.N1499.d014998.pow 2 |>.mul
        (_root_.GD.N0232.N0720.N1499.d015007 2 2 omega)).aestronglyMeasurable)
      (_root_.GD.N0232.N0720.N1367.d016859 N hN).aemeasurable).2
        (_root_.GD.N0232.N0720.N1365.d016962 hN omega)
  exact (hzero.add_measure hone).add_measure htwo

theorem d016964
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 => _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016062 theta omega) (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
    integrable_dirac (by simp)
  exact (hzero.add_measure
    (_root_.GD.N0232.N0720.N1367.d016880 hN omega)).add_measure
    (_root_.GD.N0232.N0720.N1367.d016881 hN omega)

theorem d016965
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  have hzero : Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      (Measure.dirac _root_.GD.N0232.N0720.N1080.d014169) :=
    integrable_dirac (by simp [_root_.GD.N0232.N0720.N1276.d016061, _root_.GD.N0232.N0720.N1080.d014169])
  exact (hzero.add_measure
    (_root_.GD.N0232.N0720.N1366.d016910 hN omega)).add_measure
    (_root_.GD.N0232.N0720.N1366.d016911 hN omega)

theorem d016966
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    0 < _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega := by
  rw [_root_.GD.N0232.N0720.N1367.d016882 hN]
  unfold _root_.GD.N0232.N0720.N1282.d014826 _root_.GD.N0232.N0720.N1282.d014823
  exact div_pos (_root_.GD.N0232.N0720.N1282.d014833 hN _)
    (_root_.GD.N0232.N0720.N1280.d003893 _)



theorem d016967
    {N : ℝ} (hN : 3 ≤ N) :
    ∀ omega : _root_.GD.N0232.N0720.N1276.d016060,
      Integrable (fun theta => _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1367.d016868 N hN) ∧
      Integrable (fun theta =>
          _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1367.d016868 N hN) ∧
      Integrable (fun theta =>
          _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
          (_root_.GD.N0232.N0720.N1367.d016868 N hN) ∧
      _root_.GD.N0232.N0720.N1276.d016063 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega ≠ 0 := by
  intro omega
  exact ⟨_root_.GD.N0232.N0720.N1365.d016964 hN omega,
    _root_.GD.N0232.N0720.N1365.d016965 hN omega,
    _root_.GD.N0232.N0720.N1365.d016963 hN omega,
    (_root_.GD.N0232.N0720.N1365.d016966 hN omega).ne'⟩



theorem d016968
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (_root_.GD.N0230.N0589.d000089 (_root_.GD.N0232.N0720.N1367.d016868 N hN) _root_.GD.N0232.N0720.N1276.d016062
        _root_.GD.N0232.N0720.N1405.d016086
        (_root_.GD.N0232.N0720.N1276.d016065 (_root_.GD.N0232.N0720.N1367.d016868 N hN)))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  refine (_root_.GD.N0232.N0720.N1365.d016956 hN).congr
    (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega => ?_)
  have hm := _root_.GD.N0232.N0720.N1365.d016967 hN omega
  rw [_root_.GD.N0232.N0720.N1276.d016074
    (_root_.GD.N0232.N0720.N1367.d016868 N hN) _root_.GD.N0232.N0720.N1405.d016086 omega
    hm.1 hm.2.1 hm.2.2.2,
    _root_.GD.N0232.N0720.N1366.d016915 hN,
    _root_.GD.N0232.N0720.N1367.d016882 hN]
  ring



@[fun_prop] theorem d016969 :
    Measurable _root_.GD.N0232.N0720.N1405.d016086 := by
  unfold _root_.GD.N0232.N0720.N1405.d016086
  exact measurable_fst.comp _root_.GD.N0232.N0720.N1397.d014816

@[fun_prop] theorem d016970 :
    Measurable (_root_.GD.N0232.N0719.N0932.d009193 : ℝ → ℝ≥0) := by
  have heq : (_root_.GD.N0232.N0719.N0932.d009193 : ℝ → ℝ≥0) =
      fun s => Real.toNNReal (s ^ 2) := by
    funext s
    apply NNReal.eq
    change s ^ 2 = (Real.toNNReal (s ^ 2) : ℝ)
    rw [Real.coe_toNNReal _ (sq_nonneg s)]
  rw [heq]
  exact (measurable_id.pow_const 2).real_toNNReal

@[fun_prop] theorem d016971 :
    Measurable (_root_.GD.N0232.N0720.N1080.d014168.location : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) :=
  _root_.GD.N0232.N0720.N1499.d014998.measurable

@[fun_prop] theorem d016972 :
    Measurable (_root_.GD.N0232.N0720.N1080.d014168.scale₁ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) :=
  _root_.GD.N0232.N0720.N1499.d014999.measurable

@[fun_prop] theorem d016973 :
    Measurable (_root_.GD.N0232.N0720.N1080.d014168.scale₂ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) :=
  _root_.GD.N0232.N0720.N1499.d015000.measurable

theorem d016974 (location scale x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 location scale x =
      gaussianPDFReal location (_root_.GD.N0232.N0719.N0932.d009193 scale) x /
        gaussianPDFReal 0 1 x := by
  unfold _root_.GD.N0232.N0719.N0932.d009204 _root_.GD.N0232.N0719.N0932.d009197 gaussianPDF
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal
      (gaussianPDFReal_nonneg location (_root_.GD.N0232.N0719.N0932.d009193 scale) x),
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]

@[fun_prop] theorem d016975
    (s : ℝ) :
    Measurable (fun z : ℝ × ℝ => _root_.GD.N0232.N0719.N0932.d009204 z.1 s z.2) := by
  simp_rw [_root_.GD.N0232.N0720.N1365.d016974]
  fun_prop

theorem d016976 :
    Measurable _root_.GD.N0232.N0720.N1276.d016062.uncurry := by
  unfold _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1499.d015001
    _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp_rw [_root_.GD.N0232.N0720.N1365.d016974]
  fun_prop

theorem d016977 :
    Measurable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry := by
  exact _root_.GD.N0230.N0589.d000073
    _root_.GD.N0232.N0720.N1365.d016976 _root_.GD.N0232.N0720.N1499.d014998.measurable
    _root_.GD.N0232.N0720.N1365.d016969

theorem d016978
    (action : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action theta omega‖ =
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 action theta omega := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact _root_.GD.N0230.N0589.d000075
    (fun eta x => _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x) theta omega

theorem d016979 (mu : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x - mu) ^ 2) (gaussianReal mu v) := by
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal mu v) := by
    simpa only [Function.id_def] using (memLp_id_gaussianReal' (μ := mu) (v := v)
      2 (by norm_num))
  have hconst : MemLp (fun _ : ℝ => mu) 2 (gaussianReal mu v) :=
    memLp_const mu
  simpa only [Pi.sub_apply] using (hid.sub hconst).integrable_sq

theorem d016980 (mu : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (x - mu) ^ 2 ∂(gaussianReal mu v)) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := mu) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal] using h

theorem d016981
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
      (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)) := by
  let ancillaryS : Measure (ℝ × (ℝ × ℝ)) :=
    (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
      ((gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
        (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)))
  have hloc : Integrable (fun x : ℝ => (x - mu) ^ 2)
      (gaussianReal mu (_root_.GD.N0232.N0719.N0932.d009193 (s / 2))) :=
    _root_.GD.N0232.N0720.N1365.d016979 mu _
  have hprod : Integrable (fun z : _root_.GD.N0232.N0720.N1282.d014822 => (z.1 - mu) ^ 2)
      (_root_.GD.N0232.N0720.N1397.d014809 mu s) := by
    unfold _root_.GD.N0232.N0720.N1397.d014809
    exact hloc.comp_fst ancillaryS
  have hmap :
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)).map
          _root_.GD.N0232.N0720.N1397.d014815 = _root_.GD.N0232.N0720.N1397.d014809 mu s := by
    change (_root_.GD.N0107.d009030 2 2 mu s s).map
      _root_.GD.N0232.N0720.N1397.d014815 = _root_.GD.N0232.N0720.N1397.d014809 mu s
    exact _root_.GD.N0232.N0720.N1397.d014819 mu s hs.ne'
  rw [← hmap] at hprod
  have hpull := (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable
      (fun z : _root_.GD.N0232.N0720.N1282.d014822 => (z.1 - mu) ^ 2)
      ((_root_.GD.N0232.N0720.N1080.d014171 2 2
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)).map
          _root_.GD.N0232.N0720.N1397.d014815))
    _root_.GD.N0232.N0720.N1397.d014816.aemeasurable).1 hprod
  simpa [Function.comp_def, _root_.GD.N0232.N0720.N1405.d016086] using hpull

theorem d016982
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2
      ∂(_root_.GD.N0232.N0720.N1080.d014171 2 2
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu))) =
      (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ) := by
  let ancillaryS : Measure (ℝ × (ℝ × ℝ)) :=
    (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
      ((gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
        (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)))
  have hmap :
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)).map
          _root_.GD.N0232.N0720.N1397.d014815 = _root_.GD.N0232.N0720.N1397.d014809 mu s := by
    change (_root_.GD.N0107.d009030 2 2 mu s s).map
      _root_.GD.N0232.N0720.N1397.d014815 = _root_.GD.N0232.N0720.N1397.d014809 mu s
    exact _root_.GD.N0232.N0720.N1397.d014819 mu s hs.ne'
  calc
    (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2
      ∂(_root_.GD.N0232.N0720.N1080.d014171 2 2
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu))) =
        ∫ z : _root_.GD.N0232.N0720.N1282.d014822, (z.1 - mu) ^ 2
          ∂(_root_.GD.N0232.N0720.N1397.d014809 mu s) := by
      rw [← hmap, integral_map
        _root_.GD.N0232.N0720.N1397.d014816.aemeasurable
        (by fun_prop : AEStronglyMeasurable
          (fun z : _root_.GD.N0232.N0720.N1282.d014822 => (z.1 - mu) ^ 2)
          ((_root_.GD.N0232.N0720.N1080.d014171 2 2
            (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)).map
              _root_.GD.N0232.N0720.N1397.d014815))]
      rfl
    _ = ∫ x : ℝ, (x - mu) ^ 2 ∂(gaussianReal mu
          (_root_.GD.N0232.N0719.N0932.d009193 (s / 2))) := by
      letI : IsProbabilityMeasure ancillaryS := by
        dsimp [ancillaryS]
        infer_instance
      simpa [_root_.GD.N0232.N0720.N1397.d014809, ancillaryS] using
        (integral_fun_fst
          (μ := gaussianReal mu (_root_.GD.N0232.N0719.N0932.d009193 (s / 2)))
          (ν := ancillaryS) (fun x : ℝ => (x - mu) ^ 2))
    _ = (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ) := by
      rw [_root_.GD.N0232.N0720.N1365.d016980]

theorem d016983
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    Integrable (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hactual := _root_.GD.N0232.N0720.N1365.d016981 s hs mu
  rw [_root_.GD.N0232.N0720.N1499.d015006 2 2
      (_root_.GD.N0232.N0720.N1289.d016779 s hs mu),
    integrable_withDensity_iff_integrable_smul'
      (_root_.GD.N0232.N0720.N1499.d015002 2 2
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)).ennreal_ofReal
      (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun _ => ENNReal.ofReal_lt_top)] at hactual
  refine hactual.congr (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega => ?_)
  change
    (ENNReal.ofReal (_root_.GD.N0232.N0720.N1499.d015001 2 2
      (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)
      omega)).toReal *
        (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2 =
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu) omega
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 2 2
    (_root_.GD.N0232.N0720.N1289.d016779 s hs mu) omega)]
  unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
  simp only [_root_.GD.N0232.N0720.N1289.d016780]

theorem d016984
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086
        (_root_.GD.N0232.N0720.N1289.d016779 s hs mu) omega‖
      ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)) = (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ) := by
  let theta := _root_.GD.N0232.N0720.N1289.d016779 s hs mu
  have hchange := _root_.GD.N0230.N0591.d000135
    (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta)
    (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
      (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2)
    (_root_.GD.N0232.N0720.N1499.d015006 2 2 theta)
    (_root_.GD.N0232.N0720.N1499.d015002 2 2 theta)
    (_root_.GD.N0232.N0720.N1499.d015003 2 2 theta)
  calc
    (∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
      ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086 theta omega‖ ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2)) =
        ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
          _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega *
            (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2
          ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · rfl
      · exact _root_.GD.N0230.N0589.d000075
          (fun eta x => _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x) theta omega
    _ = ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
          (_root_.GD.N0232.N0720.N1405.d016086 omega - mu) ^ 2
          ∂(_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
      simpa [_root_.GD.N0230.N0591.d000133, theta] using hchange.symm
    _ = (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ) := by
      simpa [theta] using _root_.GD.N0232.N0720.N1365.d016982 s hs mu



def d016985
    (s : ℝ) (hs : 0 < s) (z : ℝ × _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  (_root_.GD.N0232.N0719.N0932.d009204 (2 * z.1) s
      (2 * (_root_.GD.N0232.N0720.N1397.d014815 z.2).1) *
    (_root_.GD.N0232.N0719.N0932.d009204 0 s
        (_root_.GD.N0232.N0720.N1397.d014815 z.2).2.1 *
      (_root_.GD.N0232.N0719.N0932.d009204 0 s
          (_root_.GD.N0232.N0720.N1397.d014815 z.2).2.2.1 *
        _root_.GD.N0232.N0719.N0932.d009204 0 s
          (_root_.GD.N0232.N0720.N1397.d014815 z.2).2.2.2))) *
    (_root_.GD.N0232.N0720.N1405.d016086 z.2 - z.1) ^ 2

theorem d016986
    (s : ℝ) (hs : 0 < s) (z : ℝ × _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1365.d016985 s hs z =
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086
        (_root_.GD.N0232.N0720.N1289.d016779 s hs z.1) z.2 := by
  unfold _root_.GD.N0232.N0720.N1365.d016985 _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062
    _root_.GD.N0232.N0720.N1276.d016061
  rw [_root_.GD.N0232.N0720.N1289.d016786]
  simp only [_root_.GD.N0232.N0720.N1289.d016780]

set_option maxHeartbeats 1600000 in
theorem d016987
    (s : ℝ) (hs : 0 < s) :
    Measurable (_root_.GD.N0232.N0720.N1365.d016985 s hs) := by
  let parameterMap :=
    _root_.GD.N0232.N0720.N1289.d016779 s hs
  let liftMap : ℝ × _root_.GD.N0232.N0720.N1276.d016060 → _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 :=
    Prod.map parameterMap id
  have hpmeas : Measurable parameterMap :=
    (_root_.GD.N0232.N0720.N1289.d016783 s hs).measurable
  have hlift : Measurable liftMap := by
    exact hpmeas.comp measurable_fst |>.prodMk measurable_snd
  have heq : _root_.GD.N0232.N0720.N1365.d016985 s hs =
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry ∘ liftMap := by
    funext z
    change _root_.GD.N0232.N0720.N1365.d016985 s hs z =
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086 (parameterMap z.1) z.2
    exact _root_.GD.N0232.N0720.N1365.d016986 s hs z
  rw [heq]
  exact _root_.GD.N0232.N0720.N1365.d016977.comp hlift

theorem d016988
    (locationMeasure : Measure ℝ) [IsFiniteMeasure locationMeasure]
    (s : ℝ) (hs : 0 < s) :
    Integrable (_root_.GD.N0232.N0720.N1365.d016985 s hs)
      (locationMeasure.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  apply (integrable_prod_iff
    (_root_.GD.N0232.N0720.N1365.d016987 s hs).aestronglyMeasurable).2
  constructor
  · exact ae_of_all locationMeasure fun mu => by
      refine (_root_.GD.N0232.N0720.N1365.d016983 s hs mu).congr
        (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega => ?_)
      exact (_root_.GD.N0232.N0720.N1365.d016986 s hs (mu, omega)).symm
  · refine (integrable_const (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ)
      (μ := locationMeasure)).congr (ae_of_all locationMeasure fun mu => ?_)
    calc
      (_root_.GD.N0232.N0719.N0932.d009193 (s / 2) : ℝ) =
          ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
            ‖_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
              _root_.GD.N0232.N0720.N1405.d016086
              (_root_.GD.N0232.N0720.N1289.d016779 s hs mu)
              omega‖ ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
        (_root_.GD.N0232.N0720.N1365.d016984 s hs mu).symm
      _ = ∫ omega : _root_.GD.N0232.N0720.N1276.d016060,
          ‖_root_.GD.N0232.N0720.N1365.d016985 s hs (mu, omega)‖
          ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
        apply integral_congr_ae
        filter_upwards with omega
        rw [_root_.GD.N0232.N0720.N1365.d016986]

theorem d016989
    (locationMeasure : Measure ℝ) [IsFiniteMeasure locationMeasure]
    (s : ℝ) (hs : 0 < s) :
    Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry
      ((locationMeasure.map
          (_root_.GD.N0232.N0720.N1289.d016779 s hs)).prod
        (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let parameterMap := _root_.GD.N0232.N0720.N1289.d016779 s hs
  let liftMap : ℝ × _root_.GD.N0232.N0720.N1276.d016060 → _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 :=
    Prod.map parameterMap id
  have hpmeas : Measurable parameterMap :=
    (_root_.GD.N0232.N0720.N1289.d016783 s hs).measurable
  have hlift : Measurable liftMap := by
    exact hpmeas.comp measurable_fst |>.prodMk measurable_snd
  have hmeasure :
      (locationMeasure.map parameterMap).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        (locationMeasure.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)).map liftMap := by
    simpa [parameterMap, liftMap] using
      (Measure.map_prod_map locationMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        hpmeas measurable_id)
  rw [hmeasure]
  apply (integrable_map_measure
    _root_.GD.N0232.N0720.N1365.d016977.aestronglyMeasurable
    hlift.aemeasurable).2
  refine (_root_.GD.N0232.N0720.N1365.d016988
    locationMeasure s hs).congr
      (ae_of_all (locationMeasure.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) fun z => ?_)
  change _root_.GD.N0232.N0720.N1365.d016985 s hs z =
    _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
      _root_.GD.N0232.N0720.N1405.d016086
      (_root_.GD.N0232.N0720.N1289.d016779 s hs z.1) z.2
  exact _root_.GD.N0232.N0720.N1365.d016986 s hs z



theorem d016990
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry
      ((_root_.GD.N0232.N0720.N1367.d016868 N hN).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016860 N) :=
    _root_.GD.N0232.N0720.N1367.d016866 hN
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1367.d016861 N) :=
    _root_.GD.N0232.N0720.N1367.d016867 hN
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hzeroMapped :=
    _root_.GD.N0232.N0720.N1365.d016989
      (Measure.dirac (0 : ℝ)) 1 (by norm_num : (0 : ℝ) < 1)
  have hzero : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry
      ((Measure.dirac _root_.GD.N0232.N0720.N1080.d014169).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
    simpa [Measure.map_dirac,
      _root_.GD.N0232.N0720.N1289.d016779,
      _root_.GD.N0232.N0720.N1080.d014169] using hzeroMapped
  have hone : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry
      (((_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN)).prod
        (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
    simpa [_root_.GD.N0232.N0720.N1367.d016856] using
      (_root_.GD.N0232.N0720.N1365.d016989
        (_root_.GD.N0232.N0720.N1367.d016860 N) (_root_.GD.N0232.N0720.N1367.d016850 N)
          (_root_.GD.N0232.N0720.N1367.d016852 hN))
  have htwo : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        _root_.GD.N0232.N0720.N1405.d016086).uncurry
      (((_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)).prod
        (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
    simpa [_root_.GD.N0232.N0720.N1367.d016857] using
      (_root_.GD.N0232.N0720.N1365.d016989
        (_root_.GD.N0232.N0720.N1367.d016861 N) (_root_.GD.N0232.N0720.N1367.d016851 N)
          (_root_.GD.N0232.N0720.N1367.d016853 hN))
  unfold _root_.GD.N0232.N0720.N1367.d016868
  rw [Measure.add_prod, Measure.add_prod]
  exact (hzero.add_measure hone).add_measure htwo



theorem d016991
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior] :
    Measurable (_root_.GD.N0232.N0720.N1276.d016063 prior) := by
  unfold _root_.GD.N0232.N0720.N1276.d016063 _root_.GD.N0230.N0589.d000088
  exact _root_.GD.N0232.N0720.N1365.d016976.stronglyMeasurable
    |>.integral_prod_left.measurable

theorem d016992
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior] :
    Measurable (_root_.GD.N0232.N0720.N1276.d016064 prior) := by
  unfold _root_.GD.N0232.N0720.N1276.d016064
  have hjoint : Measurable (fun z : _root_.GD.N0232.N0720.N1080.d014168 × _root_.GD.N0232.N0720.N1276.d016060 =>
      _root_.GD.N0232.N0720.N1276.d016061 z.1 * _root_.GD.N0232.N0720.N1276.d016062 z.1 z.2) :=
    (_root_.GD.N0232.N0720.N1499.d014998.measurable.comp measurable_fst).mul
      (_root_.GD.N0232.N0720.N1365.d016976)
  exact hjoint.stronglyMeasurable.integral_prod_left'.measurable

theorem d016993
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior] :
    Measurable (_root_.GD.N0232.N0720.N1276.d016065 prior) := by
  unfold _root_.GD.N0232.N0720.N1276.d016065
  exact (_root_.GD.N0232.N0720.N1365.d016992 prior).div
    (_root_.GD.N0232.N0720.N1365.d016991 prior)

theorem d016994
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168) [SFinite prior] :
    Measurable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1276.d016065 prior)).uncurry := by
  exact _root_.GD.N0230.N0589.d000073
    _root_.GD.N0232.N0720.N1365.d016976 _root_.GD.N0232.N0720.N1499.d014998.measurable
    (_root_.GD.N0232.N0720.N1365.d016993 prior)

theorem d016995
    {N : ℝ} (hN : 3 ≤ N) (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1276.d016065 (_root_.GD.N0232.N0720.N1367.d016868 N hN)) theta omega)
      (_root_.GD.N0232.N0720.N1367.d016868 N hN) := by
  let a := _root_.GD.N0232.N0720.N1276.d016065 (_root_.GD.N0232.N0720.N1367.d016868 N hN) omega
  have hm := _root_.GD.N0232.N0720.N1365.d016967 hN omega
  have h0 := hm.1.const_mul (a ^ 2)
  have h1 := hm.2.1.const_mul (2 * a)
  have h2 := hm.2.2.1
  refine ((h0.sub h1).add h2).congr
    (ae_of_all (_root_.GD.N0232.N0720.N1367.d016868 N hN) fun theta => ?_)
  unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016061
  dsimp [a]
  ring

theorem d016996
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1276.d016065 (_root_.GD.N0232.N0720.N1367.d016868 N hN))).uncurry
      ((_root_.GD.N0232.N0720.N1367.d016868 N hN).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  let prior := _root_.GD.N0232.N0720.N1367.d016868 N hN
  letI : IsFiniteMeasure prior := _root_.GD.N0232.N0720.N1367.d016869 hN
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let postJoint :=
    (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
      (_root_.GD.N0232.N0720.N1276.d016065 prior)).uncurry
  let candJoint :=
    (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
      _root_.GD.N0232.N0720.N1405.d016086).uncurry
  have hpostMeas : Measurable postJoint := by
    exact _root_.GD.N0232.N0720.N1365.d016994 prior
  have hcand := _root_.GD.N0232.N0720.N1365.d016990 hN
  have hcandOuter : Integrable
      (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
        ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖candJoint (theta, omega)‖ ∂prior)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    have hbase := hcand.integral_prod_right
    refine hbase.congr (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega => ?_)
    apply integral_congr_ae
    filter_upwards with theta
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact _root_.GD.N0230.N0589.d000075
      (fun eta x => _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x) theta omega
  have hpostOuterMeas : AEStronglyMeasurable
      (fun omega : _root_.GD.N0232.N0720.N1276.d016060 =>
        ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖postJoint (theta, omega)‖ ∂prior)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    hpostMeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hpostOuterNonneg : ∀ᵐ omega ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2),
      0 ≤ ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖postJoint (theta, omega)‖ ∂prior :=
    ae_of_all _ fun omega => integral_nonneg fun theta => norm_nonneg _
  have hpostOuterLe : ∀ᵐ omega ∂(_root_.GD.N0232.N0720.N1080.d014172 2 2),
      (∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖postJoint (theta, omega)‖ ∂prior) ≤
        ∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖candJoint (theta, omega)‖ ∂prior := by
    filter_upwards with omega
    have hm := _root_.GD.N0232.N0720.N1365.d016967 hN omega
    have hsquare := _root_.GD.N0232.N0720.N1276.d016075 prior
      _root_.GD.N0232.N0720.N1405.d016086 omega hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
    have htaxNonneg : 0 ≤ _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062
        _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1276.d016065 prior) omega :=
      _root_.GD.N0230.N0589.d000091 prior _root_.GD.N0232.N0720.N1276.d016062
        _root_.GD.N0232.N0720.N1405.d016086 (_root_.GD.N0232.N0720.N1276.d016065 prior)
        (fun eta x => _root_.GD.N0232.N0720.N1499.d015003 2 2 eta x) omega
    have hpostNorm :
        (∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖postJoint (theta, omega)‖ ∂prior) =
          _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
            omega (_root_.GD.N0232.N0720.N1276.d016065 prior omega) := by
      unfold _root_.GD.N0230.N0589.d000087 postJoint
      apply integral_congr_ae
      filter_upwards with theta
      exact _root_.GD.N0232.N0720.N1365.d016978
        (_root_.GD.N0232.N0720.N1276.d016065 prior) theta omega
    have hcandNorm :
        (∫ theta : _root_.GD.N0232.N0720.N1080.d014168, ‖candJoint (theta, omega)‖ ∂prior) =
          _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
            omega (_root_.GD.N0232.N0720.N1405.d016086 omega) := by
      unfold _root_.GD.N0230.N0589.d000087 candJoint
      apply integral_congr_ae
      filter_upwards with theta
      exact _root_.GD.N0232.N0720.N1365.d016978
        _root_.GD.N0232.N0720.N1405.d016086 theta omega
    rw [hpostNorm, hcandNorm]
    linarith
  apply (integrable_prod_iff' hpostMeas.aestronglyMeasurable).2
  constructor
  · exact ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun omega => by
      simpa [prior, postJoint] using
        _root_.GD.N0232.N0720.N1365.d016995 hN omega
  · exact hcandOuter.mono_nonneg hpostOuterMeas
      hpostOuterNonneg hpostOuterLe







theorem d016997
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1276.d016068 (_root_.GD.N0232.N0720.N1367.d016868 N hN)
        _root_.GD.N0232.N0720.N1405.d016086 ≤ 48 / N ^ 9 := by
  exact _root_.GD.N0232.N0720.N1405.d016088 hN
    (_root_.GD.N0232.N0720.N1367.d016868 N hN) _root_.GD.N0232.N0720.N1405.d016086
    (_root_.GD.N0232.N0720.N1366.d016916 hN)
    (_root_.GD.N0232.N0720.N1365.d016990 hN)
    (_root_.GD.N0232.N0720.N1365.d016996 hN)
    (_root_.GD.N0232.N0720.N1365.d016968 hN)
    (ae_of_all _ (_root_.GD.N0232.N0720.N1365.d016967 hN))

end

end GD.N0232.N0720.N1365

#print axioms _root_.GD.N0232.N0720.N1365.d016990
#print axioms _root_.GD.N0232.N0720.N1365.d016996
#print axioms _root_.GD.N0232.N0720.N1365.d016968
#print axioms _root_.GD.N0232.N0720.N1365.d016997
