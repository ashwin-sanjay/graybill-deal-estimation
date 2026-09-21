import GD.Module0193
import GD.Module0268
import GD.Module0215
import GD.Module0194
import GD.Module0195
import GD.Module0196
import Mathlib













open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real

namespace GD.N0232.N0720.N1280

noncomputable section


def d003878 : ℝ := 1 / 4


def d003879 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002683 N / 4


def d003880 : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842).prod
    ((gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842).prod
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842))

instance d003881 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1280.d003880 := by
  unfold _root_.GD.N0232.N0720.N1280.d003880
  infer_instance


def d003882 (e : ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2


def d003883 (e : ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0720.N1283.d003859 (2 * e) r.1 r.2.1 r.2.2


def d003884 (e : ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  1 - 2 * (1 - e) * _root_.GD.N0232.N0720.N1280.d003882 e r + (1 - 2 * e) * _root_.GD.N0232.N0720.N1280.d003883 e r


def d003885 (N : ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  (_root_.GD.N0232.N0720.N1285.d002680 N + 1 -
      _root_.GD.N0232.N0720.N1285.d002679 N) *
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r +
    _root_.GD.N0232.N0720.N1285.d002679 N *
      _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) r



def d003886 (x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x

def d003887 (N x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x

def d003888 (N x : ℝ) : ℝ :=
  x ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 x ^ 2 / _root_.GD.N0232.N0720.N1280.d003887 N x

def d003889 (N x : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 * _root_.GD.N0232.N0720.N1280.d003887 N x

theorem d003890 : 0 < _root_.GD.N0232.N0720.N1280.d003878 := by
  unfold _root_.GD.N0232.N0720.N1280.d003878
  norm_num

theorem d003891 {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1280.d003878 < _root_.GD.N0232.N0720.N1280.d003879 N := by
  have he := _root_.GD.N0232.N0720.N1285.d002686
    (show 0 < N by linarith)
  have hc := _root_.GD.N0232.N0720.N1285.d002692 hN
  have hgain : 1 <
      _root_.GD.N0232.N0720.N1285.d002682 N ^ 2 / 4 := by
    nlinarith [sq_nonneg
      (_root_.GD.N0232.N0720.N1285.d002682 N - 4)]
  unfold _root_.GD.N0232.N0720.N1280.d003879 _root_.GD.N0232.N0720.N1280.d003878
  unfold _root_.GD.N0232.N0720.N1285.d002683
    _root_.GD.N0232.N0720.N1285.d002681
  nlinarith

theorem d003892 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1280.d003879 N :=
  _root_.GD.N0232.N0720.N1280.d003890.trans (_root_.GD.N0232.N0720.N1280.d003891 hN)

theorem d003893 (x : ℝ) :
    0 < _root_.GD.N0232.N0720.N1280.d003886 x := by
  exact _root_.GD.N0232.N0720.N1277.d002624 _root_.GD.N0232.N0720.N1280.d003890

theorem d003894 {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    0 < _root_.GD.N0232.N0720.N1280.d003887 N x := by
  exact _root_.GD.N0232.N0720.N1277.d002624
    (_root_.GD.N0232.N0720.N1280.d003892 hN)

theorem d003895
    {v : ℝ} (hv : 0 < v) :
    Integrable (fun x : ℝ =>
      x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 v x) := by
  have hb : 0 < (2 * v)⁻¹ := by positivity
  have hbase : Integrable (fun x : ℝ =>
      x ^ 2 * Real.exp (-(2 * v)⁻¹ * x ^ 2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb
        (show (-1 : ℝ) < 2 by norm_num))
  have hscaled := hbase.const_mul
    (_root_.GD.N0232.N0720.N1277.d002622 v)
  refine hscaled.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    change _root_.GD.N0232.N0720.N1277.d002622 v *
        (x ^ 2 * Real.exp (-(2 * v)⁻¹ * x ^ 2)) =
      x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 v x
    rw [_root_.GD.N0232.N0720.N1277.d002623 hv]
    have hexp : -(2 * v)⁻¹ * x ^ 2 = -(x ^ 2) / (2 * v) := by
      field_simp
    rw [hexp]
    ring

theorem d003896
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1280.d003888 N) := by
  have hv := _root_.GD.N0232.N0720.N1280.d003890
  have hV := _root_.GD.N0232.N0720.N1280.d003891 hN
  have ht := _root_.GD.N0232.N0720.N1277.d002649 hv hV
  have hbase := _root_.GD.N0232.N0720.N1280.d003895 ht
  have hscaled := hbase.const_mul
    (_root_.GD.N0232.N0720.N1277.d002647 _root_.GD.N0232.N0720.N1280.d003878 (_root_.GD.N0232.N0720.N1280.d003879 N))
  refine hscaled.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold _root_.GD.N0232.N0720.N1280.d003888 _root_.GD.N0232.N0720.N1280.d003886
      _root_.GD.N0232.N0720.N1280.d003887
    change _root_.GD.N0232.N0720.N1277.d002647 _root_.GD.N0232.N0720.N1280.d003878 (_root_.GD.N0232.N0720.N1280.d003879 N) *
        (x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1277.d002646 _root_.GD.N0232.N0720.N1280.d003878 (_root_.GD.N0232.N0720.N1280.d003879 N)) x) =
      x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x ^ 2 /
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x
    rw [show x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x ^ 2 /
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x =
        x ^ 2 *
          (_root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x ^ 2 /
            _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x) by
      ring]
    rw [_root_.GD.N0232.N0720.N1277.d002653
      hv hV]
    ring

theorem d003897
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (_root_.GD.N0232.N0720.N1280.d003889 N) := by
  have hbase := _root_.GD.N0232.N0720.N1280.d003895
    (_root_.GD.N0232.N0720.N1280.d003892 hN)
  unfold _root_.GD.N0232.N0720.N1280.d003889 _root_.GD.N0232.N0720.N1280.d003887
  convert hbase.const_mul ((_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2) using 1 <;>
    funext x <;> ring

theorem d003898
    {N : ℝ} (hN : 3 ≤ N) :
    (∫ x : ℝ, _root_.GD.N0232.N0720.N1280.d003889 N x) =
      1 / (4 * _root_.GD.N0232.N0720.N1285.d002683 N) := by
  unfold _root_.GD.N0232.N0720.N1280.d003889 _root_.GD.N0232.N0720.N1280.d003887
  rw [show (fun x : ℝ =>
      (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 *
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x) =
      (fun x : ℝ => (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 *
        (x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621
          (_root_.GD.N0232.N0720.N1280.d003879 N) x)) by
    funext x
    ring,
    integral_const_mul,
    _root_.GD.N0232.N0720.N1277.d002627
      (_root_.GD.N0232.N0720.N1280.d003892 hN)]
  have hB : 0 < _root_.GD.N0232.N0720.N1285.d002683 N :=
    lt_of_lt_of_le zero_lt_one
      (_root_.GD.N0232.N0720.N1285.d002695 hN)
  unfold _root_.GD.N0232.N0720.N1280.d003878 _root_.GD.N0232.N0720.N1280.d003879
  field_simp [hB.ne']

theorem d003899
    {N : ℝ} (hN : 3 ≤ N) :
    (∫ x : ℝ, _root_.GD.N0232.N0720.N1280.d003888 N x) =
      _root_.GD.N0232.N0720.N1285.d002685 N := by
  have hv := _root_.GD.N0232.N0720.N1280.d003890
  have hV := _root_.GD.N0232.N0720.N1280.d003891 hN
  unfold _root_.GD.N0232.N0720.N1280.d003888 _root_.GD.N0232.N0720.N1280.d003886
    _root_.GD.N0232.N0720.N1280.d003887
  rw [show (fun x : ℝ =>
      x ^ 2 * _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x ^ 2 /
        _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x) =
      (fun x : ℝ => x ^ 2 *
        (_root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878 x ^ 2 /
          _root_.GD.N0232.N0720.N1277.d002621 (_root_.GD.N0232.N0720.N1280.d003879 N) x)) by
    funext x
    ring,
    _root_.GD.N0232.N0720.N1277.d002655
      hv hV]
  let B := _root_.GD.N0232.N0720.N1285.d002683 N
  have hB : 1 ≤ B := _root_.GD.N0232.N0720.N1285.d002695 hN
  have hD : 0 < 2 * B - 1 := by linarith
  have hsqrtQuarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
  have hsqrtD : Real.sqrt ((2 * B - 1) / 4) =
      Real.sqrt (2 * B - 1) / 2 := by
    rw [Real.sqrt_div hD.le]
    norm_num
  have hsqrtSq : Real.sqrt (2 * B - 1) ^ 2 = 2 * B - 1 :=
    Real.sq_sqrt hD.le
  have hsqrtNe : Real.sqrt (2 * B - 1) ≠ 0 :=
    (Real.sqrt_pos.2 hD).ne'
  unfold _root_.GD.N0232.N0720.N1285.d002685
  change Real.sqrt (1 / 4 : ℝ) * (B / 4) ^ 2 /
      (_root_.GD.N0232.N0720.N1277.d002645 (1 / 4) (B / 4) *
        Real.sqrt (_root_.GD.N0232.N0720.N1277.d002645
          (1 / 4) (B / 4))) =
    B ^ 2 / (4 * Real.sqrt (2 * B - 1) ^ 3)
  unfold _root_.GD.N0232.N0720.N1277.d002645
  rw [show 2 * (B / 4) - 1 / 4 = (2 * B - 1) / 4 by ring,
    hsqrtQuarter, hsqrtD]
  field_simp [hsqrtNe]
  nlinarith



theorem d003900
    {a : ℝ}
    (hprecision : 0 <
      _root_.GD.N0232.N0719.N0887.d003554
        _root_.GD.N0232.N0720.N1283.d003842 a) :
    Integrable (fun x : ℝ => Real.exp (-a * x ^ 2))
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  rw [gaussianReal_of_var_ne_zero 0
    _root_.GD.N0232.N0720.N1283.d003843,
    integrable_withDensity_iff
      (measurable_gaussianPDF 0
        _root_.GD.N0232.N0720.N1283.d003842)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)]
  simp only [gaussianPDF, ENNReal.toReal_ofReal
    (gaussianPDFReal_nonneg 0
      _root_.GD.N0232.N0720.N1283.d003842 _)]
  have hbase :=
    (integrable_gaussianPDFReal
      (_root_.GD.N0232.N0719.N0887.d003557
        _root_.GD.N0232.N0720.N1283.d003842 a 0)
      (_root_.GD.N0232.N0719.N0887.d003556
        _root_.GD.N0232.N0720.N1283.d003842 a)).const_mul
      (_root_.GD.N0232.N0719.N0887.d003558
        _root_.GD.N0232.N0720.N1283.d003842 a 0)
  refine hbase.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    have htilt :=
      _root_.GD.N0232.N0719.N0887.d003566
        (v := _root_.GD.N0232.N0720.N1283.d003842)
        (a := a) (b := 0) (x := x)
        _root_.GD.N0232.N0720.N1283.d003843 hprecision
    simpa using htilt.symm

theorem d003901
    {a : ℝ} (ha : 0 < 1 + a) :
    Integrable (_root_.GD.N0232.N0720.N1283.d003851 a)
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  have hp : 0 <
      _root_.GD.N0232.N0719.N0887.d003554
        _root_.GD.N0232.N0720.N1283.d003842 (a / 2) := by
    unfold _root_.GD.N0232.N0719.N0887.d003554
    change 0 < 1 + 2 * (a / 2) * (1 : ℝ)
    linarith
  have h := _root_.GD.N0232.N0720.N1280.d003900 hp
  refine h.congr ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold _root_.GD.N0232.N0720.N1283.d003851
    congr 1
    ring

def d003902 (f : ℝ → ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  f r.1 * (f r.2.1 * f r.2.2)

theorem d003903
    {f : ℝ → ℝ}
    (hf : Integrable f
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842)) :
    Integrable (_root_.GD.N0232.N0720.N1280.d003902 f) _root_.GD.N0232.N0720.N1280.d003880 := by
  exact hf.mul_prod (hf.mul_prod hf)

theorem d003904
    {f : ℝ → ℝ}
    (hf : Integrable f
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842)) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003902 f r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f x * f y * f z
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
  have hpair := hf.mul_prod hf
  have hwhole := hf.mul_prod hpair
  unfold _root_.GD.N0232.N0720.N1280.d003880 _root_.GD.N0232.N0720.N1280.d003902
  rw [integral_prod _ hwhole]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : Integrable (fun yz : ℝ × ℝ =>
      f x * (f yz.1 * f yz.2))
      ((gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842).prod
        (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842)) :=
    hpair.const_mul (f x)
  rw [integral_prod _ hx]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with z
  ring

private theorem d003905
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    0 < _root_.GD.N0232.N0720.N1283.d003854 e ∧
    0 < _root_.GD.N0232.N0720.N1283.d003855 e ∧
    0 < _root_.GD.N0232.N0720.N1283.d003856 e := by
  unfold _root_.GD.N0232.N0720.N1283.d003854
    _root_.GD.N0232.N0720.N1283.d003855
    _root_.GD.N0232.N0720.N1283.d003856
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [sq_nonneg (e - 1 / 2)]

private theorem d003906
    {e x : ℝ}
    (hs1 : _root_.GD.N0232.N0720.N1283.d003854 e ≠ 0) :
    _root_.GD.N0232.N0720.N1283.d003844 e x =
      _root_.GD.N0232.N0720.N1283.d003851
        (-e / _root_.GD.N0232.N0720.N1283.d003854 e) x := by
  unfold _root_.GD.N0232.N0720.N1283.d003844
    _root_.GD.N0232.N0720.N1283.d003851
  unfold _root_.GD.N0232.N0720.N1283.d003854 at hs1 ⊢
  congr 1
  field_simp [hs1]

theorem d003907
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable
      (_root_.GD.N0232.N0720.N1283.d003844 e)
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  obtain ⟨hs1, hs2, _⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  have ha : 0 < 1 +
      (-e / _root_.GD.N0232.N0720.N1283.d003854 e) := by
    unfold _root_.GD.N0232.N0720.N1283.d003854 at hs1 ⊢
    unfold _root_.GD.N0232.N0720.N1283.d003855 at hs2
    rw [show 1 + -e / (1 - e) = (1 - 2 * e) / (1 - e) by
      field_simp [hs1.ne']
      ring]
    exact div_pos hs2 hs1
  have h := _root_.GD.N0232.N0720.N1280.d003901 ha
  refine h.congr ?_
  exact Filter.Eventually.of_forall fun x =>
    (_root_.GD.N0232.N0720.N1280.d003906 hs1.ne').symm

theorem d003908
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable
      (_root_.GD.N0232.N0720.N1283.d003851
        (e / _root_.GD.N0232.N0720.N1283.d003854 e))
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  obtain ⟨hs1, _, _⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  apply _root_.GD.N0232.N0720.N1280.d003901
  unfold _root_.GD.N0232.N0720.N1283.d003854 at hs1 ⊢
  rw [show 1 + e / (1 - e) = 1 / (1 - e) by
    field_simp [hs1.ne']
    ring]
  positivity

theorem d003909
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable
      (_root_.GD.N0232.N0720.N1283.d003851
        (2 * e / _root_.GD.N0232.N0720.N1283.d003855 e))
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  obtain ⟨_, hs2, _⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  apply _root_.GD.N0232.N0720.N1280.d003901
  unfold _root_.GD.N0232.N0720.N1283.d003855 at hs2 ⊢
  rw [show 1 + 2 * e / (1 - 2 * e) = 1 / (1 - 2 * e) by
    field_simp [hs2.ne']
    ring]
  positivity

theorem d003910
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable
      (_root_.GD.N0232.N0720.N1283.d003851
        (e / (_root_.GD.N0232.N0720.N1283.d003854 e *
          _root_.GD.N0232.N0720.N1283.d003855 e)))
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  obtain ⟨hs1, hs2, _⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  apply _root_.GD.N0232.N0720.N1280.d003901
  have hprod : 0 < _root_.GD.N0232.N0720.N1283.d003854 e *
      _root_.GD.N0232.N0720.N1283.d003855 e := mul_pos hs1 hs2
  positivity

theorem d003911
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable
      (_root_.GD.N0232.N0720.N1283.d003851
        (1 / (_root_.GD.N0232.N0720.N1283.d003854 e *
          _root_.GD.N0232.N0720.N1283.d003855 e) - 1))
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) := by
  obtain ⟨hs1, hs2, _⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  apply _root_.GD.N0232.N0720.N1280.d003901
  have hprod : 0 < _root_.GD.N0232.N0720.N1283.d003854 e *
      _root_.GD.N0232.N0720.N1283.d003855 e := mul_pos hs1 hs2
  rw [show 1 + (1 /
      (_root_.GD.N0232.N0720.N1283.d003854 e *
        _root_.GD.N0232.N0720.N1283.d003855 e) - 1) =
      1 / (_root_.GD.N0232.N0720.N1283.d003854 e *
        _root_.GD.N0232.N0720.N1283.d003855 e) by ring]
  exact one_div_pos.mpr hprod

theorem d003912
    {F : ℝ × (ℝ × ℝ) → ℝ}
    (hF : Integrable F _root_.GD.N0232.N0720.N1280.d003880) :
    (∫ r, F r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, F (x, (y, z))
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842
        ∂gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842 := by
  unfold _root_.GD.N0232.N0720.N1280.d003880 at hF ⊢
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with x hx
  rw [integral_prod _ hx]

theorem d003913
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    Integrable
      (fun r : ℝ × (ℝ × ℝ) =>
        _root_.GD.N0232.N0720.N1283.d003859
          d r.1 r.2.1 r.2.2)
      _root_.GD.N0232.N0720.N1280.d003880 := by
  have hs : 0 < _root_.GD.N0232.N0720.N1283.d003854 d := by
    unfold _root_.GD.N0232.N0720.N1283.d003854
    linarith
  have ha : 0 < 1 + d / _root_.GD.N0232.N0720.N1283.d003854 d := by
    unfold _root_.GD.N0232.N0720.N1283.d003854 at hs ⊢
    rw [show 1 + d / (1 - d) = 1 / (1 - d) by
      field_simp [hs.ne']
      ring]
    positivity
  have hf := _root_.GD.N0232.N0720.N1280.d003901 ha
  have ht := _root_.GD.N0232.N0720.N1280.d003903 hf
  have hc := ht.const_mul
    (((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 d))⁻¹) ^ 3)
  refine hc.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    unfold _root_.GD.N0232.N0720.N1283.d003859 _root_.GD.N0232.N0720.N1280.d003902
    ring

theorem d003914
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    (∫ r : ℝ × (ℝ × ℝ),
      _root_.GD.N0232.N0720.N1283.d003859
        d r.1 r.2.1 r.2.2 ∂_root_.GD.N0232.N0720.N1280.d003880) = 1 := by
  have hs : 0 < _root_.GD.N0232.N0720.N1283.d003854 d := by
    unfold _root_.GD.N0232.N0720.N1283.d003854
    linarith
  have ha : 0 < 1 + d / _root_.GD.N0232.N0720.N1283.d003854 d := by
    unfold _root_.GD.N0232.N0720.N1283.d003854 at hs ⊢
    rw [show 1 + d / (1 - d) = 1 / (1 - d) by
      field_simp [hs.ne']
      ring]
    positivity
  let f : ℝ → ℝ := _root_.GD.N0232.N0720.N1283.d003851
    (d / _root_.GD.N0232.N0720.N1283.d003854 d)
  have hf : Integrable f
      (gaussianReal 0 _root_.GD.N0232.N0720.N1283.d003842) :=
    _root_.GD.N0232.N0720.N1280.d003901 ha
  have ht := _root_.GD.N0232.N0720.N1280.d003903 hf
  have hpoint (r : ℝ × (ℝ × ℝ)) :
      _root_.GD.N0232.N0720.N1283.d003859
          d r.1 r.2.1 r.2.2 =
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 d))⁻¹) ^ 3 *
          _root_.GD.N0232.N0720.N1280.d003902 f r := by
    unfold _root_.GD.N0232.N0720.N1283.d003859 _root_.GD.N0232.N0720.N1280.d003902 f
    ring
  rw [show (fun r : ℝ × (ℝ × ℝ) =>
      _root_.GD.N0232.N0720.N1283.d003859 d r.1 r.2.1 r.2.2) =
      (fun r =>
        ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 d))⁻¹) ^ 3 *
          _root_.GD.N0232.N0720.N1280.d003902 f r) by
    funext r
    exact hpoint r,
    integral_const_mul,
    _root_.GD.N0232.N0720.N1280.d003904 hf,
    _root_.GD.N0232.N0720.N1283.d003853 ha]
  have hfrac : 1 + d / _root_.GD.N0232.N0720.N1283.d003854 d =
      1 / _root_.GD.N0232.N0720.N1283.d003854 d := by
    unfold _root_.GD.N0232.N0720.N1283.d003854 at hs ⊢
    field_simp [hs.ne']
    ring
  rw [hfrac, one_div, Real.sqrt_inv, inv_inv]
  have hsqrt : Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 d) ≠ 0 :=
    (Real.sqrt_pos.2 hs).ne'
  field_simp [hsqrt]

theorem d003915
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (_root_.GD.N0232.N0720.N1280.d003882 e) _root_.GD.N0232.N0720.N1280.d003880 := by
  change Integrable (fun r : ℝ × (ℝ × ℝ) =>
    _root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2)
    _root_.GD.N0232.N0720.N1280.d003880
  exact _root_.GD.N0232.N0720.N1280.d003913 he0
    (show e < 1 by linarith)

theorem d003916
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (_root_.GD.N0232.N0720.N1280.d003883 e) _root_.GD.N0232.N0720.N1280.d003880 := by
  change Integrable (fun r : ℝ × (ℝ × ℝ) =>
    _root_.GD.N0232.N0720.N1283.d003859
      (2 * e) r.1 r.2.1 r.2.2) _root_.GD.N0232.N0720.N1280.d003880
  exact _root_.GD.N0232.N0720.N1280.d003913
    (show 0 ≤ 2 * e by positivity)
    (show 2 * e < 1 by linarith)

theorem d003917
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) = 1 := by
  change (∫ r : ℝ × (ℝ × ℝ),
    _root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2
      ∂_root_.GD.N0232.N0720.N1280.d003880) = 1
  exact _root_.GD.N0232.N0720.N1280.d003914 he0
    (show e < 1 by linarith)

theorem d003918
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ∂_root_.GD.N0232.N0720.N1280.d003880) = 1 := by
  change (∫ r : ℝ × (ℝ × ℝ),
    _root_.GD.N0232.N0720.N1283.d003859
      (2 * e) r.1 r.2.1 r.2.2 ∂_root_.GD.N0232.N0720.N1280.d003880) = 1
  exact _root_.GD.N0232.N0720.N1280.d003914
    (show 0 ≤ 2 * e by positivity)
    (show 2 * e < 1 by linarith)

theorem d003919
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (fun r => 1 / _root_.GD.N0232.N0720.N1280.d003882 e r) _root_.GD.N0232.N0720.N1280.d003880 := by
  have heHalf : e < 1 / 2 := by linarith
  have hf := _root_.GD.N0232.N0720.N1280.d003907 he0 he9
  have ht := _root_.GD.N0232.N0720.N1280.d003903 hf
  have hs1 : 0 < _root_.GD.N0232.N0720.N1283.d003854 e :=
    (_root_.GD.N0232.N0720.N1280.d003905 he0 he9).1
  have hc := ht.const_mul (Real.sqrt
    (_root_.GD.N0232.N0720.N1283.d003854 e) ^ 3)
  refine hc.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    unfold _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1280.d003902
    change Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e) ^ 3 *
        (_root_.GD.N0232.N0720.N1283.d003844 e r.1 *
          (_root_.GD.N0232.N0720.N1283.d003844 e r.2.1 *
            _root_.GD.N0232.N0720.N1283.d003844 e r.2.2)) =
      1 / _root_.GD.N0232.N0720.N1283.d003859
        e r.1 r.2.1 r.2.2
    rw [_root_.GD.N0232.N0720.N1283.d003864
      heHalf]
    ring

theorem d003920
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (fun r => _root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r) _root_.GD.N0232.N0720.N1280.d003880 := by
  have heHalf : e < 1 / 2 := by linarith
  have hf := _root_.GD.N0232.N0720.N1280.d003910 he0 he9
  have ht := _root_.GD.N0232.N0720.N1280.d003903 hf
  have hs := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  have hc := ht.const_mul
    ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e) /
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e)) ^ 3)
  refine hc.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    unfold _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1280.d003883 _root_.GD.N0232.N0720.N1280.d003902
    change (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e) /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e)) ^ 3 *
        (_root_.GD.N0232.N0720.N1283.d003851
            (e / (_root_.GD.N0232.N0720.N1283.d003854 e *
              _root_.GD.N0232.N0720.N1283.d003855 e)) r.1 *
          (_root_.GD.N0232.N0720.N1283.d003851
              (e / (_root_.GD.N0232.N0720.N1283.d003854 e *
                _root_.GD.N0232.N0720.N1283.d003855 e)) r.2.1 *
            _root_.GD.N0232.N0720.N1283.d003851
              (e / (_root_.GD.N0232.N0720.N1283.d003854 e *
                _root_.GD.N0232.N0720.N1283.d003855 e)) r.2.2)) =
      _root_.GD.N0232.N0720.N1283.d003859
          (2 * e) r.1 r.2.1 r.2.2 /
        _root_.GD.N0232.N0720.N1283.d003859
          e r.1 r.2.1 r.2.2
    rw [_root_.GD.N0232.N0720.N1283.d003865
      heHalf]
    ring

theorem d003921
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (fun r => _root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) _root_.GD.N0232.N0720.N1280.d003880 := by
  have heHalf : e < 1 / 2 := by linarith
  have hf := _root_.GD.N0232.N0720.N1280.d003911 he0 he9
  have ht := _root_.GD.N0232.N0720.N1280.d003903 hf
  have hc := ht.const_mul
    ((Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e) /
      _root_.GD.N0232.N0720.N1283.d003855 e) ^ 3)
  refine hc.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    unfold _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1280.d003883 _root_.GD.N0232.N0720.N1280.d003902
    change (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e) /
        _root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 *
        (_root_.GD.N0232.N0720.N1283.d003851
            (1 / (_root_.GD.N0232.N0720.N1283.d003854 e *
              _root_.GD.N0232.N0720.N1283.d003855 e) - 1) r.1 *
          (_root_.GD.N0232.N0720.N1283.d003851
              (1 / (_root_.GD.N0232.N0720.N1283.d003854 e *
                _root_.GD.N0232.N0720.N1283.d003855 e) - 1) r.2.1 *
            _root_.GD.N0232.N0720.N1283.d003851
              (1 / (_root_.GD.N0232.N0720.N1283.d003854 e *
                _root_.GD.N0232.N0720.N1283.d003855 e) - 1) r.2.2)) =
      _root_.GD.N0232.N0720.N1283.d003859
          (2 * e) r.1 r.2.1 r.2.2 ^ 2 /
        _root_.GD.N0232.N0720.N1283.d003859
          e r.1 r.2.1 r.2.2
    rw [_root_.GD.N0232.N0720.N1283.d003866
      heHalf]
    ring

theorem d003922
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, 1 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 := by
  have hi := _root_.GD.N0232.N0720.N1280.d003919 he0 he9
  rw [_root_.GD.N0232.N0720.N1280.d003912 hi]
  simpa [_root_.GD.N0232.N0720.N1280.d003882] using
    _root_.GD.N0232.N0720.N1283.d003868
      he0 (show e < 1 / 2 by linarith)

theorem d003923
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 3 := by
  have hi := _root_.GD.N0232.N0720.N1280.d003920 he0 he9
  rw [_root_.GD.N0232.N0720.N1280.d003912 hi]
  simpa [_root_.GD.N0232.N0720.N1280.d003882, _root_.GD.N0232.N0720.N1280.d003883] using
    _root_.GD.N0232.N0720.N1283.d003869
      he0 (show e < 1 / 2 by linarith)

theorem d003924
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 := by
  have hi := _root_.GD.N0232.N0720.N1280.d003921 he0 he9
  rw [_root_.GD.N0232.N0720.N1280.d003912 hi]
  simpa [_root_.GD.N0232.N0720.N1280.d003882, _root_.GD.N0232.N0720.N1280.d003883] using
    _root_.GD.N0232.N0720.N1283.d003870
      he0 (show e < 1 / 2 by linarith)



theorem d003925
    {e : ℝ} (he1 : e < 1) (r : ℝ × (ℝ × ℝ)) :
    0 < _root_.GD.N0232.N0720.N1280.d003882 e r := by
  unfold _root_.GD.N0232.N0720.N1280.d003882
  exact _root_.GD.N0232.N0720.N1283.d003860
    he1 r.1 r.2.1 r.2.2

theorem d003926
    {e : ℝ} (he1 : e < 1) (r : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r =
      1 / _root_.GD.N0232.N0720.N1280.d003882 e r +
        4 * (1 - e) ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r +
        (1 - 2 * e) ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) -
        4 * (1 - e) +
        2 * (1 - 2 * e) * (_root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r) -
        4 * (1 - e) * (1 - 2 * e) * _root_.GD.N0232.N0720.N1280.d003883 e r := by
  have hk : _root_.GD.N0232.N0720.N1280.d003882 e r ≠ 0 := (_root_.GD.N0232.N0720.N1280.d003925 he1 r).ne'
  unfold _root_.GD.N0232.N0720.N1280.d003884
  field_simp [hk]
  ring

theorem d003927
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    Integrable (fun r => _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)
      _root_.GD.N0232.N0720.N1280.d003880 := by
  have h0 := _root_.GD.N0232.N0720.N1280.d003919 he0 he9
  have h1 := (_root_.GD.N0232.N0720.N1280.d003915 he0 he9).const_mul (4 * (1 - e) ^ 2)
  have h2 := (_root_.GD.N0232.N0720.N1280.d003921 he0 he9).const_mul
    ((1 - 2 * e) ^ 2)
  have h3 : Integrable (fun _r : ℝ × (ℝ × ℝ) => 4 * (1 - e))
      _root_.GD.N0232.N0720.N1280.d003880 := integrable_const _
  have h4 := (_root_.GD.N0232.N0720.N1280.d003920 he0 he9).const_mul
    (2 * (1 - 2 * e))
  have h5 := (_root_.GD.N0232.N0720.N1280.d003916 he0 he9).const_mul
    (4 * (1 - e) * (1 - 2 * e))
  have hexp := ((((h0.add h1).add h2).sub h3).add h4).sub h5
  refine hexp.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    change (1 / _root_.GD.N0232.N0720.N1280.d003882 e r + 4 * (1 - e) ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r +
          (1 - 2 * e) ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) -
          4 * (1 - e) +
          2 * (1 - 2 * e) * (_root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r) -
          4 * (1 - e) * (1 - 2 * e) * _root_.GD.N0232.N0720.N1280.d003883 e r) =
      _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
    exact (_root_.GD.N0232.N0720.N1280.d003926
      (show e < 1 by linarith) r).symm

private theorem d003928
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 +
        4 * (1 - e) ^ 2 +
        (1 - 2 * e) ^ 2 *
          (_root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3) -
        4 * (1 - e) +
        2 * (1 - 2 * e) *
          (_root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 3) -
        4 * (1 - e) * (1 - 2 * e) =
      _root_.GD.N0232.N0720.N1410.d002966 e := by
  obtain ⟨_, hs2, hm⟩ := _root_.GD.N0232.N0720.N1280.d003905 he0 he9
  have hs2sq : Real.sqrt
      (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 2 =
      _root_.GD.N0232.N0720.N1283.d003855 e := Real.sq_sqrt hs2.le
  have hmsq : Real.sqrt
      (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 2 =
      _root_.GD.N0232.N0720.N1283.d003856 e := Real.sq_sqrt hm.le
  have hs2cube : Real.sqrt
      (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 =
      _root_.GD.N0232.N0720.N1283.d003855 e *
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) := by
    calc
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 =
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 2 *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) := by ring
      _ = _ := by rw [hs2sq]
  have hmcube : Real.sqrt
      (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 3 =
      _root_.GD.N0232.N0720.N1283.d003856 e *
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) := by
    calc
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 3 =
          Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) ^ 2 *
            Real.sqrt (_root_.GD.N0232.N0720.N1283.d003856 e) := by ring
      _ = _ := by rw [hmsq]
  unfold _root_.GD.N0232.N0720.N1283.d003855 at hs2sq hs2cube
  unfold _root_.GD.N0232.N0720.N1283.d003856 at hmsq hmcube
  unfold _root_.GD.N0232.N0720.N1410.d002966
    _root_.GD.N0232.N0720.N1410.d002963
    _root_.GD.N0232.N0720.N1410.d002964
    _root_.GD.N0232.N0720.N1410.d002965
    _root_.GD.N0232.N0720.N1410.d002957 _root_.GD.N0232.N0720.N1410.d002958
    _root_.GD.N0232.N0720.N1410.d002959
    _root_.GD.N0232.N0720.N1283.d003854
    _root_.GD.N0232.N0720.N1283.d003855
    _root_.GD.N0232.N0720.N1283.d003856
  rw [hs2cube, hmcube]
  have hsqrt2 : Real.sqrt (1 - 2 * e) ≠ 0 :=
    (Real.sqrt_pos.2 (by linarith : 0 < 1 - 2 * e)).ne'
  have hsqrtm : Real.sqrt (1 - 2 * e + 2 * e ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by nlinarith [sq_nonneg (e - 1 / 2)] :
      0 < 1 - 2 * e + 2 * e ^ 2)).ne'
  have hs2ne : 1 - 2 * e ≠ 0 := by linarith
  have htermB :
      (1 - 2 * e) ^ 2 *
          ((1 - e) ^ 3 /
            ((1 - 2 * e) * Real.sqrt (1 - 2 * e))) =
        (1 - e) ^ 3 * Real.sqrt (1 - 2 * e) := by
    field_simp [hsqrt2, hs2ne]
    rw [hs2sq]
    ring
  rw [htermB]
  ring

theorem d003929
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
      _root_.GD.N0232.N0720.N1410.d002966 e := by
  have h0 := _root_.GD.N0232.N0720.N1280.d003919 he0 he9
  have h1 := (_root_.GD.N0232.N0720.N1280.d003915 he0 he9).const_mul (4 * (1 - e) ^ 2)
  have h2 := (_root_.GD.N0232.N0720.N1280.d003921 he0 he9).const_mul
    ((1 - 2 * e) ^ 2)
  have h3 : Integrable (fun _r : ℝ × (ℝ × ℝ) => 4 * (1 - e))
      _root_.GD.N0232.N0720.N1280.d003880 := integrable_const _
  have h4 := (_root_.GD.N0232.N0720.N1280.d003920 he0 he9).const_mul
    (2 * (1 - 2 * e))
  have h5 := (_root_.GD.N0232.N0720.N1280.d003916 he0 he9).const_mul
    (4 * (1 - e) * (1 - 2 * e))
  calc
    (∫ r, _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
        ∫ r,
          ((((1 / _root_.GD.N0232.N0720.N1280.d003882 e r + 4 * (1 - e) ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r) +
              (1 - 2 * e) ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)) -
              4 * (1 - e)) +
              2 * (1 - 2 * e) * (_root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r)) -
              4 * (1 - e) * (1 - 2 * e) * _root_.GD.N0232.N0720.N1280.d003883 e r
          ∂_root_.GD.N0232.N0720.N1280.d003880 := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun r =>
              _root_.GD.N0232.N0720.N1280.d003926
                (show e < 1 by linarith) r
    _ = (∫ r, 1 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) +
          4 * (1 - e) ^ 2 * (∫ r, _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) +
          (1 - 2 * e) ^ 2 *
            (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) -
          4 * (1 - e) +
          2 * (1 - 2 * e) *
            (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) -
          4 * (1 - e) * (1 - 2 * e) *
            (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ∂_root_.GD.N0232.N0720.N1280.d003880) := by
            let f0 : ℝ × (ℝ × ℝ) → ℝ := fun r => 1 / _root_.GD.N0232.N0720.N1280.d003882 e r
            let f1 : ℝ × (ℝ × ℝ) → ℝ :=
              fun r => 4 * (1 - e) ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r
            let f2 : ℝ × (ℝ × ℝ) → ℝ :=
              fun r => (1 - 2 * e) ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)
            let f3 : ℝ × (ℝ × ℝ) → ℝ := fun _ => 4 * (1 - e)
            let f4 : ℝ × (ℝ × ℝ) → ℝ :=
              fun r => 2 * (1 - 2 * e) * (_root_.GD.N0232.N0720.N1280.d003883 e r / _root_.GD.N0232.N0720.N1280.d003882 e r)
            let f5 : ℝ × (ℝ × ℝ) → ℝ :=
              fun r => 4 * (1 - e) * (1 - 2 * e) * _root_.GD.N0232.N0720.N1280.d003883 e r
            have hf0 : Integrable f0 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f0] using h0
            have hf1 : Integrable f1 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f1] using h1
            have hf2 : Integrable f2 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f2] using h2
            have hf3 : Integrable f3 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f3] using h3
            have hf4 : Integrable f4 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f4] using h4
            have hf5 : Integrable f5 _root_.GD.N0232.N0720.N1280.d003880 := by simpa [f5] using h5
            change (∫ r, (((((f0 + f1) + f2) - f3) + f4) - f5) r
              ∂_root_.GD.N0232.N0720.N1280.d003880) = _
            calc
              (∫ r, (((((f0 + f1) + f2) - f3) + f4) - f5) r
                  ∂_root_.GD.N0232.N0720.N1280.d003880) =
                  (∫ r, ((((f0 + f1) + f2) - f3) + f4) r ∂_root_.GD.N0232.N0720.N1280.d003880) -
                    ∫ r, f5 r ∂_root_.GD.N0232.N0720.N1280.d003880 :=
                integral_sub ((((hf0.add hf1).add hf2).sub hf3).add hf4) hf5
              _ = _ := by
                have h01 :
                    (∫ r, (f0 + f1) r ∂_root_.GD.N0232.N0720.N1280.d003880) =
                      (∫ r, f0 r ∂_root_.GD.N0232.N0720.N1280.d003880) + ∫ r, f1 r ∂_root_.GD.N0232.N0720.N1280.d003880 := by
                  simpa only [Pi.add_apply] using integral_add hf0 hf1
                have h012 :
                    (∫ r, ((f0 + f1) + f2) r ∂_root_.GD.N0232.N0720.N1280.d003880) =
                      (∫ r, (f0 + f1) r ∂_root_.GD.N0232.N0720.N1280.d003880) +
                        ∫ r, f2 r ∂_root_.GD.N0232.N0720.N1280.d003880 := by
                  simpa only [Pi.add_apply] using
                    integral_add (hf0.add hf1) hf2
                have h012m3 :
                    (∫ r, (((f0 + f1) + f2) - f3) r ∂_root_.GD.N0232.N0720.N1280.d003880) =
                      (∫ r, ((f0 + f1) + f2) r ∂_root_.GD.N0232.N0720.N1280.d003880) -
                        ∫ r, f3 r ∂_root_.GD.N0232.N0720.N1280.d003880 := by
                  simpa only [Pi.sub_apply] using
                    integral_sub ((hf0.add hf1).add hf2) hf3
                have h012m3a4 :
                    (∫ r, ((((f0 + f1) + f2) - f3) + f4) r
                      ∂_root_.GD.N0232.N0720.N1280.d003880) =
                      (∫ r, (((f0 + f1) + f2) - f3) r ∂_root_.GD.N0232.N0720.N1280.d003880) +
                        ∫ r, f4 r ∂_root_.GD.N0232.N0720.N1280.d003880 := by
                  simpa only [Pi.add_apply] using
                    integral_add (((hf0.add hf1).add hf2).sub hf3) hf4
                rw [h012m3a4, h012m3, h012, h01]
                dsimp [f0, f1, f2, f3, f4, f5]
                simp only [integral_const_mul, integral_const]
                simp [_root_.GD.N0232.N0720.N1280.d003880]
    _ = _root_.GD.N0232.N0720.N1410.d002966 e := by
          rw [_root_.GD.N0232.N0720.N1280.d003922 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003917 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003924 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003923 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003918 he0 he9]
          simpa using _root_.GD.N0232.N0720.N1280.d003928 he0 he9

def d003930 (N : ℝ) : ℝ :=
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let alpha := _root_.GD.N0232.N0720.N1285.d002680 N + 1 - e
  alpha ^ 2 + 2 * alpha * e + e ^ 2 *
    (_root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3)

theorem d003931
    {N : ℝ} (hN : 3 ≤ N) (r : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 /
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r =
      (_root_.GD.N0232.N0720.N1285.d002680 N + 1 -
          _root_.GD.N0232.N0720.N1285.d002679 N) ^ 2 *
          _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r +
        2 * (_root_.GD.N0232.N0720.N1285.d002680 N + 1 -
          _root_.GD.N0232.N0720.N1285.d002679 N) *
          _root_.GD.N0232.N0720.N1285.d002679 N *
          _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) r +
        _root_.GD.N0232.N0720.N1285.d002679 N ^ 2 *
          (_root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) r ^ 2 /
            _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r) := by
  have he : _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  have hk := (_root_.GD.N0232.N0720.N1280.d003925 he r).ne'
  unfold _root_.GD.N0232.N0720.N1280.d003885
  field_simp [hk]
  ring

theorem d003932
    {N : ℝ} (hN : 3 ≤ N) :
    Integrable (fun r => _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 /
      _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r) _root_.GD.N0232.N0720.N1280.d003880 := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let alpha := _root_.GD.N0232.N0720.N1285.d002680 N + 1 - e
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he9 : e ≤ 1 / 9 :=
    _root_.GD.N0232.N0720.N1285.d002687 hN
  have h1 := (_root_.GD.N0232.N0720.N1280.d003915 he0 he9).const_mul (alpha ^ 2)
  have h2 := (_root_.GD.N0232.N0720.N1280.d003916 he0 he9).const_mul (2 * alpha * e)
  have h3 := (_root_.GD.N0232.N0720.N1280.d003921 he0 he9).const_mul (e ^ 2)
  have hexp := (h1.add h2).add h3
  refine hexp.congr ?_
  exact Filter.Eventually.of_forall fun r => by
    change alpha ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r + 2 * alpha * e * _root_.GD.N0232.N0720.N1280.d003883 e r +
        e ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) =
      _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
    dsimp [e, alpha]
    exact (_root_.GD.N0232.N0720.N1280.d003931 hN r).symm

theorem d003933
    {N : ℝ} (hN : 3 ≤ N) :
    (∫ r, _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 /
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) r
      ∂_root_.GD.N0232.N0720.N1280.d003880) = _root_.GD.N0232.N0720.N1280.d003930 N := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let alpha := _root_.GD.N0232.N0720.N1285.d002680 N + 1 - e
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he9 : e ≤ 1 / 9 :=
    _root_.GD.N0232.N0720.N1285.d002687 hN
  have h1 := (_root_.GD.N0232.N0720.N1280.d003915 he0 he9).const_mul (alpha ^ 2)
  have h2 := (_root_.GD.N0232.N0720.N1280.d003916 he0 he9).const_mul (2 * alpha * e)
  have h3 := (_root_.GD.N0232.N0720.N1280.d003921 he0 he9).const_mul (e ^ 2)
  calc
    (∫ r, _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) =
        ∫ r, alpha ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r +
          2 * alpha * e * _root_.GD.N0232.N0720.N1280.d003883 e r +
          e ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) ∂_root_.GD.N0232.N0720.N1280.d003880 := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun r => by
              dsimp [e, alpha]
              exact _root_.GD.N0232.N0720.N1280.d003931 hN r
    _ = alpha ^ 2 * (∫ r, _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) +
          2 * alpha * e * (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ∂_root_.GD.N0232.N0720.N1280.d003880) +
          e ^ 2 * (∫ r, _root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r ∂_root_.GD.N0232.N0720.N1280.d003880) := by
            calc
              (∫ r, alpha ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r +
                  2 * alpha * e * _root_.GD.N0232.N0720.N1280.d003883 e r +
                  e ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r) ∂_root_.GD.N0232.N0720.N1280.d003880) =
                  (∫ r, alpha ^ 2 * _root_.GD.N0232.N0720.N1280.d003882 e r +
                    2 * alpha * e * _root_.GD.N0232.N0720.N1280.d003883 e r ∂_root_.GD.N0232.N0720.N1280.d003880) +
                    ∫ r, e ^ 2 * (_root_.GD.N0232.N0720.N1280.d003883 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r)
                      ∂_root_.GD.N0232.N0720.N1280.d003880 := integral_add (h1.add h2) h3
              _ = _ := by
                rw [integral_add h1 h2]
                simp only [integral_const_mul]
    _ = _root_.GD.N0232.N0720.N1280.d003930 N := by
          rw [_root_.GD.N0232.N0720.N1280.d003917 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003918 he0 he9,
            _root_.GD.N0232.N0720.N1280.d003924 he0 he9]
          simp only [mul_one]
          rfl

private theorem d003934
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1283.d003854
          (_root_.GD.N0232.N0720.N1285.d002679 N) ^ 3 /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855
          (_root_.GD.N0232.N0720.N1285.d002679 N)) ^ 3 ≤ 2 := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he9 : e ≤ 1 / 9 :=
    _root_.GD.N0232.N0720.N1285.d002687 hN
  have hs1 : 0 ≤ _root_.GD.N0232.N0720.N1283.d003854 e :=
    (_root_.GD.N0232.N0720.N1280.d003905 he0 he9).1.le
  have hs1le : _root_.GD.N0232.N0720.N1283.d003854 e ≤ 1 := by
    unfold _root_.GD.N0232.N0720.N1283.d003854
    linarith
  have hs2 : 0 < _root_.GD.N0232.N0720.N1283.d003855 e :=
    (_root_.GD.N0232.N0720.N1280.d003905 he0 he9).2.1
  have hs2lower : (16 / 25 : ℝ) ≤
      _root_.GD.N0232.N0720.N1283.d003855 e := by
    unfold _root_.GD.N0232.N0720.N1283.d003855
    linarith
  have hsqrt : (4 / 5 : ℝ) ≤
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hs2.le]
    norm_num at hs2lower ⊢
    exact hs2lower
  have hcubes : (64 / 125 : ℝ) ≤
      Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5) hsqrt 3]
  have hnum : _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 ≤ 1 := by
    nlinarith [pow_le_pow_left₀ hs1 hs1le 3]
  have hden : 0 < Real.sqrt
      (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

theorem d003935
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1280.d003930 N ≤
      2 * _root_.GD.N0232.N0720.N1285.d002680 N ^ 2 := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let M := _root_.GD.N0232.N0720.N1285.d002680 N
  let alpha := M + 1 - e
  have hM3 : 3 ≤ M := by
    unfold M _root_.GD.N0232.N0720.N1285.d002680
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hN 11
    norm_num at hp
    linarith
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he1 : e ≤ 1 :=
    (_root_.GD.N0232.N0720.N1285.d002687 hN).trans (by norm_num)
  apply _root_.GD.N0232.N0720.N1284.d002677
    (M := M) (epsilon := e) (alpha := alpha) (beta := e)
    (reciprocal :=
      _root_.GD.N0232.N0720.N1283.d003854 e ^ 3 /
        Real.sqrt (_root_.GD.N0232.N0720.N1283.d003855 e) ^ 3)
  · exact hM3
  · exact he0
  · exact he1
  · rfl
  · rfl
  · simpa [e] using _root_.GD.N0232.N0720.N1280.d003934 hN
  · rfl

def d003936 (N : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002679 N /
    (1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N)

def d003937 (N x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1285.d002682 N *
      _root_.GD.N0232.N0720.N1280.d003887 N x -
    2 * _root_.GD.N0232.N0720.N1280.d003886 x

def d003938 (N x : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003936 N * _root_.GD.N0232.N0720.N1280.d003887 N x +
    _root_.GD.N0232.N0720.N1280.d003886 x

def d003939
    (N : ℝ) (z : ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003886 z.1 +
    _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
      _root_.GD.N0232.N0720.N1280.d003937 N z.1 +
    _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
      _root_.GD.N0232.N0720.N1280.d003938 N z.1

def d003940
    (N : ℝ) (z : ℝ × (ℝ × (ℝ × ℝ))) : ℝ :=
  z.1 *
    (_root_.GD.N0232.N0720.N1280.d003884
          (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
        _root_.GD.N0232.N0720.N1280.d003886 z.1 +
      (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) * _root_.GD.N0232.N0720.N1280.d003885 N z.2 *
        _root_.GD.N0232.N0720.N1280.d003887 N z.1)

def d003941 (N : ℝ) : ℝ :=
  ∫ z : ℝ × (ℝ × (ℝ × ℝ)),
    _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z
      ∂(volume.prod _root_.GD.N0232.N0720.N1280.d003880)

theorem d003942 {N : ℝ} (hN : 3 ≤ N) :
    0 < _root_.GD.N0232.N0720.N1285.d002684 N := by
  have hc := _root_.GD.N0232.N0720.N1285.d002692 hN
  have hg := _root_.GD.N0232.N0720.N1285.d002694 hN
  linarith

theorem d003943 {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ _root_.GD.N0232.N0720.N1280.d003936 N := by
  have he := _root_.GD.N0232.N0720.N1285.d002686
    (show 0 < N by linarith)
  have hs2 : 0 < 1 - 2 * _root_.GD.N0232.N0720.N1285.d002679 N := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1280.d003936
  positivity

theorem d003944
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    _root_.GD.N0232.N0720.N1280.d003886 x ≤
      Real.sqrt (_root_.GD.N0232.N0720.N1285.d002683 N) *
        _root_.GD.N0232.N0720.N1280.d003887 N x := by
  let B := _root_.GD.N0232.N0720.N1285.d002683 N
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one
    (_root_.GD.N0232.N0720.N1285.d002695 hN)
  have hV : _root_.GD.N0232.N0720.N1280.d003878 ≤ _root_.GD.N0232.N0720.N1280.d003879 N := (_root_.GD.N0232.N0720.N1280.d003891 hN).le
  have hsqrtV : Real.sqrt (_root_.GD.N0232.N0720.N1280.d003879 N) = Real.sqrt B / 2 := by
    unfold _root_.GD.N0232.N0720.N1280.d003879
    change Real.sqrt (B / 4) = Real.sqrt B / 2
    rw [Real.sqrt_div hB.le]
    norm_num
  have hsqrtv0 : Real.sqrt _root_.GD.N0232.N0720.N1280.d003878 = 1 / 2 := by
    unfold _root_.GD.N0232.N0720.N1280.d003878
    norm_num
  have hpeak : 1 * Real.sqrt (_root_.GD.N0232.N0720.N1280.d003879 N) ≤
      Real.sqrt B * Real.sqrt _root_.GD.N0232.N0720.N1280.d003878 := by
    rw [hsqrtV, hsqrtv0]
    simpa [div_eq_mul_inv] using
      (le_refl (Real.sqrt B * (1 / 2 : ℝ)))
  have hdom := _root_.GD.N0232.N0720.N1277.d002660
    (w := _root_.GD.N0232.N0720.N1280.d003878) (U := _root_.GD.N0232.N0720.N1280.d003879 N)
    (c := Real.sqrt B) (d := 1) (x := x) _root_.GD.N0232.N0720.N1280.d003890 hV
    (Real.sqrt_nonneg _) hpeak
  simpa [_root_.GD.N0232.N0720.N1280.d003886, _root_.GD.N0232.N0720.N1280.d003887, B] using hdom

theorem d003945
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    _root_.GD.N0232.N0720.N1285.d002684 N *
        _root_.GD.N0232.N0720.N1280.d003887 N x ≤
      _root_.GD.N0232.N0720.N1280.d003937 N x := by
  have hp := _root_.GD.N0232.N0720.N1280.d003944 hN x
  unfold _root_.GD.N0232.N0720.N1280.d003937 _root_.GD.N0232.N0720.N1285.d002684
  nlinarith [mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)]

theorem d003946
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1280.d003937 N x := by
  have hf := _root_.GD.N0232.N0720.N1280.d003945 hN x
  have hg := _root_.GD.N0232.N0720.N1280.d003942 hN
  have hh := _root_.GD.N0232.N0720.N1280.d003894 hN x
  exact (mul_nonneg hg.le hh.le).trans hf

theorem d003947
    {N : ℝ} (hN : 3 ≤ N) (x : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1280.d003938 N x := by
  unfold _root_.GD.N0232.N0720.N1280.d003938
  exact add_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1280.d003943 hN)
      (_root_.GD.N0232.N0720.N1280.d003894 hN x).le)
    (_root_.GD.N0232.N0720.N1280.d003893 x).le

theorem d003948
    {N : ℝ} (hN : 3 ≤ N) (z : ℝ × (ℝ × (ℝ × ℝ))) :
    _root_.GD.N0232.N0720.N1285.d002684 N *
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
        _root_.GD.N0232.N0720.N1280.d003887 N z.1 ≤
      _root_.GD.N0232.N0720.N1280.d003939 N z := by
  have he1 : _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  have he2 : 2 * _root_.GD.N0232.N0720.N1285.d002679 N < 1 := by
    linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]
  unfold _root_.GD.N0232.N0720.N1280.d003939
  exact _root_.GD.N0232.N0720.N1284.d002675
    (_root_.GD.N0232.N0720.N1280.d003893 z.1).le
    (_root_.GD.N0232.N0720.N1280.d003925 he1 z.2).le
    (show 0 ≤ _root_.GD.N0232.N0720.N1280.d003883 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 by
      unfold _root_.GD.N0232.N0720.N1280.d003883
      exact (_root_.GD.N0232.N0720.N1283.d003860
        he2 z.2.1 z.2.2.1 z.2.2.2).le)
    (_root_.GD.N0232.N0720.N1280.d003945 hN z.1)
    (_root_.GD.N0232.N0720.N1280.d003947 hN z.1)

theorem d003949 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1280.d003940 N) := by
  unfold _root_.GD.N0232.N0720.N1280.d003940 _root_.GD.N0232.N0720.N1280.d003884 _root_.GD.N0232.N0720.N1280.d003885
    _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1280.d003883 _root_.GD.N0232.N0720.N1280.d003886 _root_.GD.N0232.N0720.N1280.d003887
    _root_.GD.N0232.N0720.N1277.d002621
    _root_.GD.N0232.N0720.N1283.d003859
    _root_.GD.N0232.N0720.N1283.d003851
  fun_prop

theorem d003950 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1280.d003939 N) := by
  unfold _root_.GD.N0232.N0720.N1280.d003939 _root_.GD.N0232.N0720.N1280.d003937 _root_.GD.N0232.N0720.N1280.d003938
    _root_.GD.N0232.N0720.N1280.d003936 _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1280.d003883 _root_.GD.N0232.N0720.N1280.d003886 _root_.GD.N0232.N0720.N1280.d003887
    _root_.GD.N0232.N0720.N1277.d002621
    _root_.GD.N0232.N0720.N1283.d003859
    _root_.GD.N0232.N0720.N1283.d003851
  fun_prop

theorem d003951 (N : ℝ) :
    AEStronglyMeasurable
      (fun z : ℝ × (ℝ × (ℝ × ℝ)) =>
        _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z)
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880) := by
  exact (((_root_.GD.N0232.N0720.N1280.d003949 N).pow_const 2).div
    (_root_.GD.N0232.N0720.N1280.d003950 N)).aestronglyMeasurable

theorem d003952
    {e : ℝ} (he0 : 0 ≤ e) (he9 : e ≤ 1 / 9) :
    0 ≤ _root_.GD.N0232.N0720.N1410.d002966 e := by
  rw [← _root_.GD.N0232.N0720.N1280.d003929 he0 he9]
  apply integral_nonneg
  intro r
  exact div_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1280.d003925 (by linarith) r).le

theorem d003953
    {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ _root_.GD.N0232.N0720.N1285.d002685 N := by
  rw [← _root_.GD.N0232.N0720.N1280.d003899 hN]
  apply integral_nonneg
  intro x
  unfold _root_.GD.N0232.N0720.N1280.d003888
  exact div_nonneg
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (_root_.GD.N0232.N0720.N1280.d003894 hN x).le

theorem d003954
    {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ _root_.GD.N0232.N0720.N1280.d003930 N := by
  rw [← _root_.GD.N0232.N0720.N1280.d003933 hN]
  apply integral_nonneg
  intro r
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1280.d003925 (show _root_.GD.N0232.N0720.N1285.d002679 N < 1 by
      linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]) r).le

theorem d003955
    {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ 1 /
      (4 * _root_.GD.N0232.N0720.N1285.d002683 N) := by
  have hB : 0 < _root_.GD.N0232.N0720.N1285.d002683 N :=
    lt_of_lt_of_le zero_lt_one
      (_root_.GD.N0232.N0720.N1285.d002695 hN)
  positivity



theorem d003956
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1280.d003941 N ≤
      (2 / _root_.GD.N0232.N0720.N1285.d002684 N) *
        (_root_.GD.N0232.N0720.N1285.d002685 N *
            _root_.GD.N0232.N0720.N1410.d002966
              (_root_.GD.N0232.N0720.N1285.d002679 N) +
          (1 / (4 * _root_.GD.N0232.N0720.N1285.d002683 N)) *
            _root_.GD.N0232.N0720.N1280.d003930 N) := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 (by linarith)).le
  have he9 : e ≤ 1 / 9 :=
    _root_.GD.N0232.N0720.N1285.d002687 hN
  have hraw :=
    _root_.GD.N0232.N0720.N1278.d002665
      (X := ℝ) (R := ℝ × (ℝ × ℝ))
      (μ := volume) (ν := _root_.GD.N0232.N0720.N1280.d003880)
      (coord := fun x : ℝ => x)
      (p := _root_.GD.N0232.N0720.N1280.d003886)
      (h := _root_.GD.N0232.N0720.N1280.d003887 N)
      (k := _root_.GD.N0232.N0720.N1280.d003882 e)
      (L := _root_.GD.N0232.N0720.N1280.d003884 e)
      (C := _root_.GD.N0232.N0720.N1280.d003885 N)
      (D := _root_.GD.N0232.N0720.N1280.d003939 N)
      (theta := _root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N)
      (gamma := _root_.GD.N0232.N0720.N1285.d002684 N)
      (_root_.GD.N0232.N0720.N1280.d003942 hN)
      (fun r => _root_.GD.N0232.N0720.N1280.d003925 (show e < 1 by linarith) r)
      (_root_.GD.N0232.N0720.N1280.d003894 hN)
      (_root_.GD.N0232.N0720.N1280.d003948 hN)
      (by
        simpa [_root_.GD.N0232.N0720.N1280.d003940, e] using
          _root_.GD.N0232.N0720.N1280.d003951 N)
      (by
        change Integrable (_root_.GD.N0232.N0720.N1280.d003888 N) volume
        exact _root_.GD.N0232.N0720.N1280.d003896 hN)
      (by
        change Integrable (_root_.GD.N0232.N0720.N1280.d003889 N) volume
        exact _root_.GD.N0232.N0720.N1280.d003897 hN)
      (_root_.GD.N0232.N0720.N1280.d003927 he0 he9)
      (_root_.GD.N0232.N0720.N1280.d003932 hN)
  have henergy : _root_.GD.N0232.N0720.N1280.d003941 N ≤
      (2 / _root_.GD.N0232.N0720.N1285.d002684 N) *
        ((∫ x : ℝ, x ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 x ^ 2 /
              _root_.GD.N0232.N0720.N1280.d003887 N x) *
            (∫ r, _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
              ∂_root_.GD.N0232.N0720.N1280.d003880) +
          (∫ x : ℝ, (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 *
              _root_.GD.N0232.N0720.N1280.d003887 N x) *
            (∫ r, _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
              ∂_root_.GD.N0232.N0720.N1280.d003880)) := by
    simpa [_root_.GD.N0232.N0720.N1280.d003941, _root_.GD.N0232.N0720.N1280.d003940, e] using hraw
  calc
    _root_.GD.N0232.N0720.N1280.d003941 N ≤
        (2 / _root_.GD.N0232.N0720.N1285.d002684 N) *
          ((∫ x : ℝ, x ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 x ^ 2 /
                _root_.GD.N0232.N0720.N1280.d003887 N x) *
              (∫ r, _root_.GD.N0232.N0720.N1280.d003884 e r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
                ∂_root_.GD.N0232.N0720.N1280.d003880) +
            (∫ x : ℝ, (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 *
                _root_.GD.N0232.N0720.N1280.d003887 N x) *
              (∫ r, _root_.GD.N0232.N0720.N1280.d003885 N r ^ 2 / _root_.GD.N0232.N0720.N1280.d003882 e r
                ∂_root_.GD.N0232.N0720.N1280.d003880)) := henergy
    _ = _ := by
      rw [show (fun x : ℝ => x ^ 2 * _root_.GD.N0232.N0720.N1280.d003886 x ^ 2 /
            _root_.GD.N0232.N0720.N1280.d003887 N x) = _root_.GD.N0232.N0720.N1280.d003888 N by rfl,
        _root_.GD.N0232.N0720.N1280.d003899 hN,
        _root_.GD.N0232.N0720.N1280.d003929 he0 he9,
        show (fun x : ℝ => (_root_.GD.N0232.N0720.N1280.d003878 / _root_.GD.N0232.N0720.N1280.d003879 N) ^ 2 * x ^ 2 *
            _root_.GD.N0232.N0720.N1280.d003887 N x) = _root_.GD.N0232.N0720.N1280.d003889 N by rfl,
        _root_.GD.N0232.N0720.N1280.d003898 hN,
        _root_.GD.N0232.N0720.N1280.d003933 hN]



theorem d003957
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1280.d003941 N ≤ 48 / N ^ 9 := by
  let e := _root_.GD.N0232.N0720.N1285.d002679 N
  let M := _root_.GD.N0232.N0720.N1285.d002680 N
  let c := _root_.GD.N0232.N0720.N1285.d002682 N
  let gamma := _root_.GD.N0232.N0720.N1285.d002684 N
  let H := _root_.GD.N0232.N0720.N1410.d002966 e
  let I := _root_.GD.N0232.N0720.N1285.d002685 N
  let K := _root_.GD.N0232.N0720.N1280.d003930 N
  let R := 1 / (4 * _root_.GD.N0232.N0720.N1285.d002683 N)
  have hN0 : 0 < N := by linarith
  have he0 : 0 ≤ e :=
    (_root_.GD.N0232.N0720.N1285.d002686 hN0).le
  have he9 : e ≤ 1 / 9 :=
    _root_.GD.N0232.N0720.N1285.d002687 hN
  have hpkg := _root_.GD.N0232.N0720.N1285.d002700 hN
  apply _root_.GD.N0232.N0720.N1284.d002678
    (N := N) (M := M) (epsilon := e) (c := c) (gamma := gamma)
    (H := H) (I := I) (K := K) (varianceRatio := R)
    (Phi := _root_.GD.N0232.N0720.N1280.d003941 N)
  · exact hN0
  · exact _root_.GD.N0232.N0720.N1285.d002690 hN
  · exact _root_.GD.N0232.N0720.N1285.d002686 hN0
  · exact hpkg.1
  · exact hpkg.2.1
  · exact _root_.GD.N0232.N0720.N1280.d003952 he0 he9
  · exact _root_.GD.N0232.N0720.N1280.d003953 hN
  · exact _root_.GD.N0232.N0720.N1280.d003954 hN
  · exact _root_.GD.N0232.N0720.N1280.d003955 hN
  · calc
      H ≤ 18 * e ^ 4 :=
        _root_.GD.N0232.N0720.N1410.d002976 he0 he9
      _ = 18 / N ^ 8 := by
        dsimp [e]
        unfold _root_.GD.N0232.N0720.N1285.d002679
        field_simp [hN0.ne']
  · exact hpkg.2.2.1
  · exact _root_.GD.N0232.N0720.N1280.d003935 hN
  · exact hpkg.2.2.2
  · rfl
  · rfl
  · simpa [H, I, K, R, e, mul_comm] using
      _root_.GD.N0232.N0720.N1280.d003956 hN

#print axioms _root_.GD.N0232.N0720.N1280.d003957

end

end GD.N0232.N0720.N1280
