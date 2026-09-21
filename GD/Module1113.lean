import GD.Module0998
import GD.Module0924
import GD.Module1028
import GD.Module0275




















open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1503

noncomputable section

open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0235
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1194
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1443
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499

private noncomputable local instance d017873 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance





def d017874 : _root_.GD.N0232.N0719.N0946.d009229 :=
  ⟨-(4 / 3), Real.log 2⟩



def d017875 : _root_.GD.N0232.N0719.N0946.d009229 :=
  ⟨4 / 3, Real.log 2⟩

def d017876 : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1484.d015099 _root_.GD.N0232.N0720.N1503.d017874

def d017877 : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1484.d015099 _root_.GD.N0232.N0720.N1503.d017875

def d017878 : ℝ := 2 / 3

def d017879 : ℝ := 3 / 32

def d017880 : ℝ := 101 / 288


def d017881 : ℝ :=
  16 * Real.exp (32 / 27)


def d017882 : ℝ :=
  4 * _root_.GD.N0232.N0720.N1503.d017881


def d017883 : ℝ :=
  101 / (8192 * Real.exp (32 / 27))


def d017884 : ℝ :=
  10201 / (2359296 * Real.exp (32 / 27))

@[simp] theorem d017885 :
    _root_.GD.N0232.N0720.N1503.d017874.d009239 = 2 := by
  simp [_root_.GD.N0232.N0720.N1503.d017874, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

@[simp] theorem d017886 :
    _root_.GD.N0232.N0720.N1503.d017875.d009239 = 2 := by
  simp [_root_.GD.N0232.N0720.N1503.d017875, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

@[simp] theorem d017887 :
    _root_.GD.N0232.N0720.N1503.d017876.location = _root_.GD.N0232.N0720.N1503.d017878 := by
  change -(Real.exp (-Real.log 2) * (-(4 / 3))) +
      Real.exp (-Real.log 2) * 0 = 2 / 3
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp] theorem d017888 :
    _root_.GD.N0232.N0720.N1503.d017877.location = -_root_.GD.N0232.N0720.N1503.d017878 := by
  change -(Real.exp (-Real.log 2) * (4 / 3)) +
      Real.exp (-Real.log 2) * 0 = -(2 / 3)
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp] theorem d017889 :
    _root_.GD.N0232.N0720.N1503.d017876.scale₁ = 1 / 2 := by
  change Real.exp (-Real.log 2) * 1 = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp] theorem d017890 :
    _root_.GD.N0232.N0720.N1503.d017876.scale₂ = 1 / 2 := by
  change Real.exp (-Real.log 2) * 1 = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp] theorem d017891 :
    _root_.GD.N0232.N0720.N1503.d017877.scale₁ = 1 / 2 := by
  change Real.exp (-Real.log 2) * 1 = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp] theorem d017892 :
    _root_.GD.N0232.N0720.N1503.d017877.scale₂ = 1 / 2 := by
  change Real.exp (-Real.log 2) * 1 = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem d017893 : 0 < _root_.GD.N0232.N0720.N1503.d017881 := by
  unfold _root_.GD.N0232.N0720.N1503.d017881
  positivity

theorem d017894 : 0 < _root_.GD.N0232.N0720.N1503.d017883 := by
  unfold _root_.GD.N0232.N0720.N1503.d017883
  positivity

theorem d017895 : 0 < _root_.GD.N0232.N0720.N1503.d017884 := by
  unfold _root_.GD.N0232.N0720.N1503.d017884
  positivity



theorem d017896 :
    _root_.GD.N0232.N0720.N1503.d017883 =
      _root_.GD.N0232.N0720.N1503.d017880 /
        (_root_.GD.N0232.N0720.N1503.d017878 ^ 2 * _root_.GD.N0232.N0720.N1503.d017882) := by
  unfold _root_.GD.N0232.N0720.N1503.d017883 _root_.GD.N0232.N0720.N1503.d017880 _root_.GD.N0232.N0720.N1503.d017878
    _root_.GD.N0232.N0720.N1503.d017882 _root_.GD.N0232.N0720.N1503.d017881
  field_simp [Real.exp_ne_zero]
  ring


theorem d017897 :
    _root_.GD.N0232.N0720.N1503.d017884 = _root_.GD.N0232.N0720.N1503.d017883 * _root_.GD.N0232.N0720.N1503.d017880 := by
  unfold _root_.GD.N0232.N0720.N1503.d017884 _root_.GD.N0232.N0720.N1503.d017883 _root_.GD.N0232.N0720.N1503.d017880
  field_simp [Real.exp_ne_zero]
  ring

theorem d017898 :
    _root_.GD.N0232.N0720.N1146.d015200 2 2 _root_.GD.N0232.N0720.N1503.d017874 =
      _root_.GD.N0232.N0720.N1503.d017881 := by
  rw [_root_.GD.N0232.N0720.N1146.d015207]
  simp only [_root_.GD.N0232.N0720.N1503.d017885]
  change (2 : ℝ) ^ 4 *
      Real.exp (4 * ((-(4 / 3 : ℝ)) ^ 2 / (2 * (2 ^ 2 - 1)))) =
        16 * Real.exp (32 / 27)
  norm_num

theorem d017899 :
    _root_.GD.N0232.N0720.N1146.d015200 2 2 _root_.GD.N0232.N0720.N1503.d017875 =
      _root_.GD.N0232.N0720.N1503.d017881 := by
  rw [_root_.GD.N0232.N0720.N1146.d015207]
  simp only [_root_.GD.N0232.N0720.N1503.d017886]
  change (2 : ℝ) ^ 4 *
      Real.exp (4 * ((4 / 3 : ℝ) ^ 2 / (2 * (2 ^ 2 - 1)))) =
        16 * Real.exp (32 / 27)
  norm_num

theorem d017900 (omega : _root_.GD.N0232.N0720.N1080.d014170 2 2) :
    _root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017876 omega ≤
      _root_.GD.N0232.N0720.N1503.d017881 := by
  unfold _root_.GD.N0232.N0720.N1503.d017876
  rw [← _root_.GD.N0232.N0720.N1503.d017898]
  exact _root_.GD.N0232.N0720.N1146.d015206 2 2
    _root_.GD.N0232.N0720.N1503.d017874 (by simp) omega

theorem d017901 (omega : _root_.GD.N0232.N0720.N1080.d014170 2 2) :
    _root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017877 omega ≤
      _root_.GD.N0232.N0720.N1503.d017881 := by
  unfold _root_.GD.N0232.N0720.N1503.d017877
  rw [← _root_.GD.N0232.N0720.N1503.d017899]
  exact _root_.GD.N0232.N0720.N1146.d015206 2 2
    _root_.GD.N0232.N0720.N1503.d017875 (by simp) omega

theorem d017902 :
    MemLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017876) 2
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  apply memLp_of_bounded (a := (0 : ℝ)) (b := _root_.GD.N0232.N0720.N1503.d017881)
  · filter_upwards [] with omega
    exact ⟨_root_.GD.N0232.N0720.N1499.d015003 2 2 _ omega,
      _root_.GD.N0232.N0720.N1503.d017900 omega⟩
  · exact (_root_.GD.N0232.N0720.N1499.d015002 2 2 _).aestronglyMeasurable

theorem d017903 :
    MemLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017877) 2
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  apply memLp_of_bounded (a := (0 : ℝ)) (b := _root_.GD.N0232.N0720.N1503.d017881)
  · filter_upwards [] with omega
    exact ⟨_root_.GD.N0232.N0720.N1499.d015003 2 2 _ omega,
      _root_.GD.N0232.N0720.N1503.d017901 omega⟩
  · exact (_root_.GD.N0232.N0720.N1499.d015002 2 2 _).aestronglyMeasurable

def d017904 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017876)
    _root_.GD.N0232.N0720.N1503.d017902

def d017905 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 _root_.GD.N0232.N0720.N1503.d017877)
    _root_.GD.N0232.N0720.N1503.d017903

def d017906 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1503.d017904 - _root_.GD.N0232.N0720.N1503.d017905



private theorem d017907
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (M : ℝ)
    (hbound : ∀ omega, _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega ≤ M)
    (hmem : MemLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) 2
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    ‖MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) hmem‖ ^ 2 ≤ M := by
  let likelihood := _root_.GD.N0232.N0720.N1499.d015001 2 2 theta
  have hsqInt : Integrable (fun omega ↦ likelihood omega ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := hmem.integrable_sq
  have hlinInt : Integrable likelihood (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
    _root_.GD.N0232.N0720.N1484.d015103 2 2 theta
  have hmulInt : Integrable (fun omega ↦ M * likelihood omega)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := hlinInt.const_mul M
  have hpoint : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      likelihood omega ^ 2 ≤ M * likelihood omega := by
    filter_upwards [] with omega
    have hnonneg := _root_.GD.N0232.N0720.N1499.d015003 2 2 theta omega
    have hle := hbound omega
    nlinarith
  calc
    ‖MemLp.toLp likelihood hmem‖ ^ 2 =
        ∫ omega, likelihood omega ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with omega homega
      have homega' :
          MemLp.toLp likelihood hmem omega = likelihood omega := by
        simpa only [likelihood] using homega
      simp only [RCLike.inner_apply, conj_trivial, homega', pow_two]
    _ ≤ ∫ omega, M * likelihood omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 :=
      integral_mono_ae hsqInt hmulInt hpoint
    _ = M := by
      rw [integral_const_mul,
        _root_.GD.N0232.N0720.N1484.d015104 2 2 theta, mul_one]

theorem d017908 :
    ‖_root_.GD.N0232.N0720.N1503.d017904‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1503.d017881 := by
  exact _root_.GD.N0232.N0720.N1503.d017907
    _root_.GD.N0232.N0720.N1503.d017876 _root_.GD.N0232.N0720.N1503.d017881
    _root_.GD.N0232.N0720.N1503.d017900
    _root_.GD.N0232.N0720.N1503.d017902

theorem d017909 :
    ‖_root_.GD.N0232.N0720.N1503.d017905‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1503.d017881 := by
  exact _root_.GD.N0232.N0720.N1503.d017907
    _root_.GD.N0232.N0720.N1503.d017877 _root_.GD.N0232.N0720.N1503.d017881
    _root_.GD.N0232.N0720.N1503.d017901
    _root_.GD.N0232.N0720.N1503.d017903

theorem d017910 :
    ‖_root_.GD.N0232.N0720.N1503.d017906‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1503.d017882 := by
  have htriangle : ‖_root_.GD.N0232.N0720.N1503.d017906‖ ≤
      ‖_root_.GD.N0232.N0720.N1503.d017904‖ +
        ‖_root_.GD.N0232.N0720.N1503.d017905‖ := by
    simpa only [_root_.GD.N0232.N0720.N1503.d017906] using
      norm_sub_le _root_.GD.N0232.N0720.N1503.d017904 _root_.GD.N0232.N0720.N1503.d017905
  have hsquare :
      ‖_root_.GD.N0232.N0720.N1503.d017906‖ ^ 2 ≤
        (‖_root_.GD.N0232.N0720.N1503.d017904‖ +
          ‖_root_.GD.N0232.N0720.N1503.d017905‖) ^ 2 := by
    nlinarith [norm_nonneg _root_.GD.N0232.N0720.N1503.d017906,
      norm_nonneg _root_.GD.N0232.N0720.N1503.d017904,
      norm_nonneg _root_.GD.N0232.N0720.N1503.d017905]
  have hsum :
      (‖_root_.GD.N0232.N0720.N1503.d017904‖ +
          ‖_root_.GD.N0232.N0720.N1503.d017905‖) ^ 2 ≤
        2 * ‖_root_.GD.N0232.N0720.N1503.d017904‖ ^ 2 +
          2 * ‖_root_.GD.N0232.N0720.N1503.d017905‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖_root_.GD.N0232.N0720.N1503.d017904‖ -
        ‖_root_.GD.N0232.N0720.N1503.d017905‖)]
  unfold _root_.GD.N0232.N0720.N1503.d017882
  nlinarith [_root_.GD.N0232.N0720.N1503.d017908,
    _root_.GD.N0232.N0720.N1503.d017909]



private theorem d017911 :
    _root_.GD.N0232.N0720.N1091.d012790 (1 / 2) (1 / 2) (1 / 2) = 1 / 8 := by
  let mu := betaMeasure (1 / 2) (1 / 2)
  letI : IsProbabilityMeasure mu :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  let monomial : ℝ → ℝ := fun u ↦ u ^ 1 * (1 - u) ^ 1
  have hmonoMeas : AEStronglyMeasurable monomial mu := by
    dsimp only [monomial]
    fun_prop
  have hmonoBound : ∀ᵐ u ∂mu, ‖monomial u‖ ≤ (1 : ℝ) := by
    have hsupport := _root_.GD.N0232.N0720.N1092.d013031 (1 / 2) (1 / 2)
    filter_upwards [hsupport] with u hu
    have hnonneg : 0 ≤ u * (1 - u) :=
      mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)
    have hle : u * (1 - u) ≤ 1 := by
      nlinarith [sq_nonneg (u - 1 / 2)]
    simpa only [monomial, pow_one, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hle
  have hmonoInt : Integrable monomial mu :=
    (integrable_const (1 : ℝ)).mono' hmonoMeas hmonoBound
  have hpoint (u : ℝ) :
      (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) (1 / 2)) u -
          1 / 2) ^ 2 = 1 / 4 - monomial u := by
    dsimp only [monomial]
    norm_num [_root_.GD.N0232.N0720.N1091.d012762, _root_.GD.N0232.N0720.N1091.d012763]
    ring
  unfold _root_.GD.N0232.N0720.N1091.d012790
  change (∫ u, _ ∂mu) = _
  simp_rw [hpoint]
  rw [integral_sub (integrable_const (1 / 4 : ℝ)) hmonoInt,
    integral_const]
  rw [probReal_univ, one_smul]
  change 1 / 4 -
      (∫ u, u ^ 1 * (1 - u) ^ 1 ∂betaMeasure (1 / 2) (1 / 2)) =
        1 / 8
  rw [_root_.GD.N0232.N0720.N1443.d004058 (g := (1 / 2 : ℝ)) (by norm_num)]
  norm_num

theorem d017912 :
    (_root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1080.d014169).toReal =
      3 / 8 := by
  rw [_root_.GD.N0232.N0720.N1071.d014427]
  change _root_.GD.N0107.d009045 2 2 1 1 *
      _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 2) (_root_.GD.N0232.N0720.N1433.d014025 2)
        (_root_.GD.N0232.N0720.N1067.d014408 2 2 _root_.GD.N0232.N0720.N1080.d014169) = 3 / 8
  have hSigma :
      _root_.GD.N0107.d009045 2 2 1 1 = 1 := by
    norm_num [_root_.GD.N0107.d009045,
      _root_.GD.N0107.d009043,
      _root_.GD.N0107.d009044]
  have hp : _root_.GD.N0232.N0720.N1067.d014408 2 2 _root_.GD.N0232.N0720.N1080.d014169 = 1 / 2 := by
    norm_num [_root_.GD.N0232.N0720.N1067.d014408, _root_.GD.N0232.N0720.N1080.d014169,
      _root_.GD.N0107.d009046,
      _root_.GD.N0107.d009045,
      _root_.GD.N0107.d009043,
      _root_.GD.N0107.d009044]
  rw [hSigma, hp]
  norm_num [_root_.GD.N0232.N0720.N1442.d013867, _root_.GD.N0232.N0720.N1442.d013866,
    _root_.GD.N0232.N0720.N1433.d014024, _root_.GD.N0232.N0720.N1433.d014025, _root_.GD.N0232.N0720.N1503.d017911]

theorem d017913 :
    _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1080.d014169 =
      ENNReal.ofReal (3 / 8) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (_root_.GD.N0232.N0720.N1066.d014323 2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1080.d014169)
    ENNReal.ofReal_ne_top).mp
  rw [_root_.GD.N0232.N0720.N1503.d017912]
  norm_num





theorem d017914
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hfinite : _root_.GD.N0232.N0720.N1080.d014182 2 2 theta q ≠ ⊤)
    (hlikelihood : MemLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) 2
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    theta.location ^ 2 -
        2 * theta.location *
          ⟪MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) hlikelihood,
            q⟫_ℝ ≤
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have herrorInt := _root_.GD.N0232.N0720.N1078.d016376 2 2 theta q hfinite
  have herrorStrong : AEStronglyMeasurable
      (fun omega ↦ (q omega - theta.location)) (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) :=
    (AEStronglyMeasurable.mono_ac
      (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta)
      (Lp.aestronglyMeasurable q)).sub
        aestronglyMeasurable_const
  have herrorLp : MemLp (fun omega ↦ q omega - theta.location) 2
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) :=
    (memLp_two_iff_integrable_sq herrorStrong).2 herrorInt
  have hqLp : MemLp (fun omega ↦ q omega) 2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    have hsum := herrorLp.add (memLp_const theta.location)
    convert hsum using 1
    funext omega
    simp only [Pi.add_apply]
    ring
  have hqInt : Integrable (fun omega ↦ q omega) (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) :=
    hqLp.integrable (by norm_num)
  have hleftInt : Integrable
      (fun omega ↦ theta.location ^ 2 -
        2 * theta.location * q omega) (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) :=
    (integrable_const (theta.location ^ 2)).sub
      (hqInt.const_mul (2 * theta.location))
  have hpoint : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta,
      theta.location ^ 2 - 2 * theta.location * q omega ≤
        (q omega - theta.location) ^ 2 := by
    filter_upwards [] with omega
    nlinarith [sq_nonneg (q omega)]
  have hintegral :
      theta.location ^ 2 -
          2 * theta.location * (∫ omega, q omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) ≤
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta := by
    have hmono := integral_mono_ae hleftInt herrorInt hpoint
    rw [integral_sub (integrable_const (theta.location ^ 2))
        (hqInt.const_mul (2 * theta.location)),
      integral_const, probReal_univ, one_smul,
      integral_const_mul] at hmono
    exact hmono
  have hmean :
      (∫ omega, q omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) =
        ⟪MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) hlikelihood,
          q⟫_ℝ := by
    calc
      (∫ omega, q omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) =
          ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 2 2 theta omega * q omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
        simpa [_root_.GD.N0230.N0591.d000133] using
          (_root_.GD.N0230.N0591.d000135
            (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) (fun omega ↦ q omega)
            (_root_.GD.N0232.N0720.N1499.d015006 2 2 theta)
            (_root_.GD.N0232.N0720.N1499.d015002 2 2 theta)
            (_root_.GD.N0232.N0720.N1499.d015003 2 2 theta))
      _ = ⟪MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) hlikelihood,
          q⟫_ℝ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hlikelihood.coeFn_toLp] with omega homega
        simp only [RCLike.inner_apply, conj_trivial, homega]
        ring
  have hriskReal :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal =
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta := by
    unfold _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
    rw [← ofReal_integral_eq_lintegral_ofReal herrorInt
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]
  calc
    theta.location ^ 2 -
          2 * theta.location *
            ⟪MemLp.toLp (_root_.GD.N0232.N0720.N1499.d015001 2 2 theta) hlikelihood,
              q⟫_ℝ =
        theta.location ^ 2 -
          2 * theta.location * (∫ omega, q omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
      rw [hmean]
    _ ≤ ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta :=
      hintegral
    _ = (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal := hriskReal.symm


theorem d017915
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hplusFinite : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≠ ⊤)
    (hminusFinite : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≠ ⊤)
    (hplusCap : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≤
      ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879)
    (hminusCap : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≤
      ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879) :
    _root_.GD.N0232.N0720.N1503.d017880 ≤ _root_.GD.N0232.N0720.N1503.d017878 *
      ⟪_root_.GD.N0232.N0720.N1503.d017906, q⟫_ℝ := by
  have hplusLinear :=
    _root_.GD.N0232.N0720.N1503.d017914
      _root_.GD.N0232.N0720.N1503.d017876 q hplusFinite
      _root_.GD.N0232.N0720.N1503.d017902
  have hminusLinear :=
    _root_.GD.N0232.N0720.N1503.d017914
      _root_.GD.N0232.N0720.N1503.d017877 q hminusFinite
      _root_.GD.N0232.N0720.N1503.d017903
  have hplusReal :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q).toReal ≤ _root_.GD.N0232.N0720.N1503.d017879 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hplusCap
    change (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q).toReal ≤
      (ENNReal.ofReal (3 / 32 : ℝ)).toReal at h
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 32 : ℝ))] at h
    simpa only [_root_.GD.N0232.N0720.N1503.d017879] using h
  have hminusReal :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q).toReal ≤ _root_.GD.N0232.N0720.N1503.d017879 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hminusCap
    change (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q).toReal ≤
      (ENNReal.ofReal (3 / 32 : ℝ)).toReal at h
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 32 : ℝ))] at h
    simpa only [_root_.GD.N0232.N0720.N1503.d017879] using h
  simp only [_root_.GD.N0232.N0720.N1503.d017887,
    _root_.GD.N0232.N0720.N1503.d017888] at hplusLinear hminusLinear
  change _root_.GD.N0232.N0720.N1503.d017880 ≤ _root_.GD.N0232.N0720.N1503.d017878 *
    ⟪_root_.GD.N0232.N0720.N1503.d017904 - _root_.GD.N0232.N0720.N1503.d017905,
      q⟫_ℝ
  rw [inner_sub_left]
  simp only [_root_.GD.N0232.N0720.N1503.d017904,
    _root_.GD.N0232.N0720.N1503.d017905] at hplusLinear hminusLinear ⊢
  norm_num [_root_.GD.N0232.N0720.N1503.d017880, _root_.GD.N0232.N0720.N1503.d017878, _root_.GD.N0232.N0720.N1503.d017879] at hplusLinear hminusLinear hplusReal hminusReal ⊢
  linarith



theorem d017916
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1200.d015250 2 2 (by omega) (by omega) s) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 s.value ≤
        ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879 ∧
      _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 s.value ≤
        ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879 := by
  have hbaseline (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014182 2 2 theta s.value ≤ _root_.GD.N0232.N0720.N1080.d014182 2 2 theta
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) :=
    (hstrict theta).le
  have hcap (g : _root_.GD.N0232.N0719.N0946.d009229)
      (hg : g.d009239 = 2) :
      _root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1484.d015099 g)
          (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) =
        ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879 := by
    change _root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) = _
    rw [_root_.GD.N0232.N0720.N1215.d014293]
    change ENNReal.ofReal (g⁻¹.d009239 ^ 2) *
      _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1080.d014169 = _
    rw [_root_.GD.N0232.N0720.N1503.d017913]
    have hginv : g⁻¹.d009239 = 1 / 2 := by
      rw [_root_.GD.N0232.N0720.N1146.d015204, hg]
      norm_num
    rw [hginv]
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ ((1 / 2 : ℝ) ^ 2))]
    congr 1
    norm_num [_root_.GD.N0232.N0720.N1503.d017879]
  constructor
  · have heq : _root_.GD.N0232.N0720.N1503.d017876 =
        _root_.GD.N0232.N0720.N1484.d015099 _root_.GD.N0232.N0720.N1503.d017874 := rfl
    exact (hbaseline _root_.GD.N0232.N0720.N1503.d017876).trans_eq
      (heq.symm ▸ hcap _root_.GD.N0232.N0720.N1503.d017874
        _root_.GD.N0232.N0720.N1503.d017885)
  · have heq : _root_.GD.N0232.N0720.N1503.d017877 =
        _root_.GD.N0232.N0720.N1484.d015099 _root_.GD.N0232.N0720.N1503.d017875 := rfl
    exact (hbaseline _root_.GD.N0232.N0720.N1503.d017877).trans_eq
      (heq.symm ▸ hcap _root_.GD.N0232.N0720.N1503.d017875
        _root_.GD.N0232.N0720.N1503.d017886)




theorem d017917
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1200.d015250 2 2 (by omega) (by omega) s)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 2 2 s.value) :
    _root_.GD.N0232.N0720.N1503.d017884 ≤ ‖q‖ ^ 2 := by
  have hseedCap := _root_.GD.N0232.N0720.N1503.d017916 s hstrict
  have hplusCap : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≤
      ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879 :=
    (hq _root_.GD.N0232.N0720.N1503.d017876).trans hseedCap.1
  have hminusCap : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≤
      ENNReal.ofReal _root_.GD.N0232.N0720.N1503.d017879 :=
    (hq _root_.GD.N0232.N0720.N1503.d017877).trans hseedCap.2
  have hfinite := _root_.GD.N0232.N0720.N1159.d014644 2 2 s q hq
  have hplusFinite : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≠ ⊤ :=
    hfinite _root_.GD.N0232.N0720.N1503.d017876
  have hminusFinite : _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≠ ⊤ :=
    hfinite _root_.GD.N0232.N0720.N1503.d017877
  have hmoment := _root_.GD.N0232.N0720.N1503.d017915 q hplusFinite hminusFinite
    hplusCap hminusCap
  have hcauchy :
      ⟪_root_.GD.N0232.N0720.N1503.d017906, q⟫_ℝ ≤
        ‖_root_.GD.N0232.N0720.N1503.d017906‖ * ‖q‖ :=
    real_inner_le_norm _root_.GD.N0232.N0720.N1503.d017906 q
  have hmarginPos : 0 < _root_.GD.N0232.N0720.N1503.d017880 := by
    norm_num [_root_.GD.N0232.N0720.N1503.d017880]
  have hlocationPos : 0 < _root_.GD.N0232.N0720.N1503.d017878 := by
    norm_num [_root_.GD.N0232.N0720.N1503.d017878]
  have hinnerNonneg : 0 ≤ ⟪_root_.GD.N0232.N0720.N1503.d017906, q⟫_ℝ := by
    nlinarith
  have hsquare :
      _root_.GD.N0232.N0720.N1503.d017880 ^ 2 ≤
        _root_.GD.N0232.N0720.N1503.d017878 ^ 2 *
          ‖_root_.GD.N0232.N0720.N1503.d017906‖ ^ 2 * ‖q‖ ^ 2 := by
    have hprodNonneg : 0 ≤
        ‖_root_.GD.N0232.N0720.N1503.d017906‖ * ‖q‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hinnerSq :
        ⟪_root_.GD.N0232.N0720.N1503.d017906, q⟫_ℝ ^ 2 ≤
          (‖_root_.GD.N0232.N0720.N1503.d017906‖ * ‖q‖) ^ 2 := by
      nlinarith
    nlinarith
  have hceiling :
      _root_.GD.N0232.N0720.N1503.d017878 ^ 2 * ‖_root_.GD.N0232.N0720.N1503.d017906‖ ^ 2 * ‖q‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1503.d017878 ^ 2 * _root_.GD.N0232.N0720.N1503.d017882 * ‖q‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left _root_.GD.N0232.N0720.N1503.d017910
        (sq_nonneg _root_.GD.N0232.N0720.N1503.d017878))
      (sq_nonneg ‖q‖)
  have hcombined :
      _root_.GD.N0232.N0720.N1503.d017880 ^ 2 ≤
        _root_.GD.N0232.N0720.N1503.d017878 ^ 2 * _root_.GD.N0232.N0720.N1503.d017882 * ‖q‖ ^ 2 :=
    hsquare.trans hceiling
  have hdenPos : 0 <
      _root_.GD.N0232.N0720.N1503.d017878 ^ 2 * _root_.GD.N0232.N0720.N1503.d017882 := by
    unfold _root_.GD.N0232.N0720.N1503.d017878 _root_.GD.N0232.N0720.N1503.d017882 _root_.GD.N0232.N0720.N1503.d017881
    positivity
  have hratio :
      _root_.GD.N0232.N0720.N1503.d017880 ^ 2 /
          (_root_.GD.N0232.N0720.N1503.d017878 ^ 2 * _root_.GD.N0232.N0720.N1503.d017882) ≤
        ‖q‖ ^ 2 := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcombined
  convert hratio using 1
  unfold _root_.GD.N0232.N0720.N1503.d017880 _root_.GD.N0232.N0720.N1503.d017878 _root_.GD.N0232.N0720.N1503.d017882
    _root_.GD.N0232.N0720.N1503.d017881 _root_.GD.N0232.N0720.N1503.d017884
  field_simp [Real.exp_ne_zero]
  ring



theorem d017918
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1200.d015250 2 2 (by omega) (by omega) s) :
    _root_.GD.N0232.N0720.N1194.d015813 2 2 s _root_.GD.N0232.N0720.N1503.d017884 := by
  intro q hq
  exact _root_.GD.N0232.N0720.N1503.d017917 s hstrict q hq



theorem d017919
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1200.d015250 2 2 (by omega) (by omega) s) :
    _root_.GD.N0232.N0720.N1503.d017884 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 2 2 s.value‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1194.d015814 2 2 s
    (_root_.GD.N0232.N0720.N1503.d017918 s hstrict)

end
end N1503
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1503.d017910
#print axioms _root_.GD.N0232.N0720.N1503.d017913
#print axioms _root_.GD.N0232.N0720.N1503.d017915
#print axioms _root_.GD.N0232.N0720.N1503.d017916
#print axioms _root_.GD.N0232.N0720.N1503.d017917
#print axioms _root_.GD.N0232.N0720.N1503.d017918
#print axioms _root_.GD.N0232.N0720.N1503.d017919
