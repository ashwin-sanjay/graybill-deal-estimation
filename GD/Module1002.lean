import GD.Module0011
import GD.Module0032
import GD.Module0088
import GD.Module1000




























open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1173

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0657
open _root_.GD.N0230.N0706


abbrev d015933 := _root_.GD.N0232.N0720.N1486.d015856


def d015934
    (ρ : Measure (Set.Ioo (0 : ℝ) 1)) : Measure _root_.GD.N0232.N0720.N1173.d015933 :=
  _root_.GD.N0232.N0720.N1486.d015870 ρ


def d015935 (θ : _root_.GD.N0232.N0720.N1173.d015933) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1486.d015873 2 2 (by norm_num) (by norm_num) θ


abbrev d015936 := _root_.GD.N0232.N0720.N1080.d014170 2 2


def d015937
    (θ : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 2 2 (_root_.GD.N0232.N0720.N1173.d015935 θ) x


def d015938 (θ : _root_.GD.N0232.N0720.N1173.d015933) : ℝ := θ.1


def d015939
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (θ : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015937 θ x * weight θ


def d015940
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0230.N0589.d000088
    (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight) x



theorem d015941
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015940 ρ (fun θ ↦ h θ ^ 2) x := by
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939 _root_.GD.N0232.N0720.N1173.d015937
  apply integral_nonneg_of_ae
  filter_upwards [] with θ
  exact mul_nonneg
    (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 θ) x)
    (sq_nonneg (h θ))


def d015942
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  ∫ θ,
    _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x
      ∂_root_.GD.N0232.N0720.N1173.d015934 ρ


def d015943
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015942 ρ weight x / _root_.GD.N0232.N0720.N1173.d015940 ρ weight x


def d015944
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015943 ρ (fun _ ↦ 1) x



def d015945
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  ∫ θ,
    (_root_.GD.N0232.N0720.N1173.d015938 θ - _root_.GD.N0232.N0720.N1173.d015944 ρ x) *
      _root_.GD.N0232.N0720.N1173.d015939 weight θ x
        ∂_root_.GD.N0232.N0720.N1173.d015934 ρ






def d015946
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    _root_.GD.N0232.N0720.N1173.d015937 z.1 x * _root_.GD.N0232.N0720.N1173.d015937 z.2 x *
      (_root_.GD.N0232.N0720.N1173.d015938 z.1 - _root_.GD.N0232.N0720.N1173.d015938 z.2) *
      (weight z.1 - weight z.2) ∂
        (_root_.GD.N0232.N0720.N1173.d015934 ρ).prod (_root_.GD.N0232.N0720.N1173.d015934 ρ)



def d015947
    {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (target weight : Θ → ℝ) (a : ℝ) : ℝ :=
  ∫ θ, weight θ * (a - target θ) ^ 2 ∂μ

theorem d015948
    {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (target weight : Θ → ℝ) (a : ℝ)
    (hw : Integrable weight μ)
    (htw : Integrable (fun θ ↦ target θ * weight θ) μ)
    (ht2w : Integrable (fun θ ↦ target θ ^ 2 * weight θ) μ) :
    _root_.GD.N0232.N0720.N1173.d015947 μ target weight a =
      a ^ 2 * _root_.GD.N0230.N0657.d000366 μ weight -
        2 * a * (∫ θ, target θ * weight θ ∂μ) +
          ∫ θ, target θ ^ 2 * weight θ ∂μ := by
  unfold _root_.GD.N0232.N0720.N1173.d015947 _root_.GD.N0230.N0657.d000366
  have hpoint :
      (fun θ ↦ weight θ * (a - target θ) ^ 2) =
        (fun θ ↦
          a ^ 2 * weight θ -
            (2 * a) * (target θ * weight θ) +
              target θ ^ 2 * weight θ) := by
    funext θ
    ring
  rw [hpoint]
  have hfirst : Integrable (fun θ ↦ a ^ 2 * weight θ) μ :=
    hw.const_mul _
  have hcross : Integrable
      (fun θ ↦ (2 * a) * (target θ * weight θ)) μ :=
    htw.const_mul _
  have hsub :
      (∫ θ, a ^ 2 * weight θ -
        (2 * a) * (target θ * weight θ) ∂μ) =
      (∫ θ, a ^ 2 * weight θ ∂μ) -
        ∫ θ, (2 * a) * (target θ * weight θ) ∂μ :=
    integral_sub hfirst hcross
  have hadd :
      (∫ θ, (a ^ 2 * weight θ -
        (2 * a) * (target θ * weight θ)) +
          target θ ^ 2 * weight θ ∂μ) =
      (∫ θ, a ^ 2 * weight θ -
        (2 * a) * (target θ * weight θ) ∂μ) +
        ∫ θ, target θ ^ 2 * weight θ ∂μ :=
    integral_add (hfirst.sub hcross) ht2w
  rw [hadd, hsub, integral_const_mul, integral_const_mul]



theorem d015949
    {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (target weight : Θ → ℝ) (a : ℝ)
    (hw : Integrable weight μ)
    (htw : Integrable (fun θ ↦ target θ * weight θ) μ)
    (ht2w : Integrable (fun θ ↦ target θ ^ 2 * weight θ) μ)
    (hmass : _root_.GD.N0230.N0657.d000366 μ weight ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015947 μ target weight a =
      _root_.GD.N0232.N0720.N1173.d015947 μ target weight
          (_root_.GD.N0230.N0657.d000367 μ target weight) +
        _root_.GD.N0230.N0657.d000366 μ weight *
          (a - _root_.GD.N0230.N0657.d000367 μ target weight) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1173.d015948 μ target weight a hw htw ht2w,
    _root_.GD.N0232.N0720.N1173.d015948 μ target weight
      (_root_.GD.N0230.N0657.d000367 μ target weight) hw htw ht2w]
  unfold _root_.GD.N0230.N0657.d000367
  field_simp [hmass]
  ring

theorem d015950
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1173.d015943 ρ weight x =
      _root_.GD.N0230.N0657.d000367
        (_root_.GD.N0232.N0720.N1173.d015934 ρ) _root_.GD.N0232.N0720.N1173.d015938
          (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x) := by
  rfl



theorem d015951
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) (a : ℝ)
    (hw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (htw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (ht2w : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hmass : _root_.GD.N0232.N0720.N1173.d015940 ρ weight x ≠ 0) :
    _root_.GD.N0230.N0589.d000087
        (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          _root_.GD.N0232.N0720.N1173.d015938 x a =
      _root_.GD.N0230.N0589.d000087
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015943 ρ weight x) +
        _root_.GD.N0232.N0720.N1173.d015940 ρ weight x *
          (a - _root_.GD.N0232.N0720.N1173.d015943 ρ weight x) ^ 2 := by
  have h := _root_.GD.N0232.N0720.N1173.d015949
    (_root_.GD.N0232.N0720.N1173.d015934 ρ) _root_.GD.N0232.N0720.N1173.d015938
    (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x) a
    hw htw ht2w
    (by
      simpa [_root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0230.N0657.d000366] using hmass)
  simpa [_root_.GD.N0230.N0589.d000087, _root_.GD.N0232.N0720.N1173.d015947, _root_.GD.N0230.N0657.d000366,
    _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0232.N0720.N1173.d015950] using h



theorem d015952
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (htw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ)) :
    _root_.GD.N0232.N0720.N1173.d015945 ρ weight x =
      _root_.GD.N0232.N0720.N1173.d015942 ρ weight x -
        _root_.GD.N0232.N0720.N1173.d015944 ρ x * _root_.GD.N0232.N0720.N1173.d015940 ρ weight x := by
  unfold _root_.GD.N0232.N0720.N1173.d015945 _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
  let W := fun θ : _root_.GD.N0232.N0720.N1173.d015933 ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x
  have hconst : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015944 ρ x * W θ)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) := hw.const_mul _
  have hpoint :
      (fun θ ↦
        (_root_.GD.N0232.N0720.N1173.d015938 θ - _root_.GD.N0232.N0720.N1173.d015944 ρ x) * W θ) =
      (fun θ ↦
        _root_.GD.N0232.N0720.N1173.d015938 θ * W θ - _root_.GD.N0232.N0720.N1173.d015944 ρ x * W θ) := by
    funext θ
    ring
  rw [hpoint, integral_sub htw hconst, integral_const_mul]





theorem d015953
    (ρ : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite ρ]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hfullMoment : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x * _root_.GD.N0232.N0720.N1173.d015938 θ)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hcutoff : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x * weight θ)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hcutoffMoment : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x *
        (_root_.GD.N0232.N0720.N1173.d015938 θ * weight θ))
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015945 ρ weight x =
      _root_.GD.N0232.N0720.N1173.d015946 ρ weight x /
        (2 * _root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x) := by
  letI : SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  have hpair := _root_.GD.N0230.N0706.d001169
    (_root_.GD.N0232.N0720.N1173.d015934 ρ)
    (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x) _root_.GD.N0232.N0720.N1173.d015938 weight
    hfull hfullMoment hcutoff hcutoffMoment
  have hE₀ :
      (∫ θ, _root_.GD.N0232.N0720.N1173.d015937 θ x ∂_root_.GD.N0232.N0720.N1173.d015934 ρ) =
        _root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x := by
    simp [_root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0232.N0720.N1173.d015939]
  have hEw :
      (∫ θ, _root_.GD.N0232.N0720.N1173.d015937 θ x * weight θ
          ∂_root_.GD.N0232.N0720.N1173.d015934 ρ) =
        _root_.GD.N0232.N0720.N1173.d015940 ρ weight x := by
    rfl
  have hM₀ :
      (∫ θ, _root_.GD.N0232.N0720.N1173.d015937 θ x * _root_.GD.N0232.N0720.N1173.d015938 θ
          ∂_root_.GD.N0232.N0720.N1173.d015934 ρ) =
        _root_.GD.N0232.N0720.N1173.d015942 ρ (fun _ ↦ 1) x := by
    unfold _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015939
    apply integral_congr_ae
    filter_upwards with θ
    ring
  have hMw :
      (∫ θ, _root_.GD.N0232.N0720.N1173.d015937 θ x *
          (_root_.GD.N0232.N0720.N1173.d015938 θ * weight θ)
          ∂_root_.GD.N0232.N0720.N1173.d015934 ρ) =
        _root_.GD.N0232.N0720.N1173.d015942 ρ weight x := by
    unfold _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015939
    apply integral_congr_ae
    filter_upwards with θ
    ring
  have hpair' :
      _root_.GD.N0232.N0720.N1173.d015946 ρ weight x =
        2 *
          (_root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x *
              _root_.GD.N0232.N0720.N1173.d015942 ρ weight x -
            _root_.GD.N0232.N0720.N1173.d015942 ρ (fun _ ↦ 1) x *
              _root_.GD.N0232.N0720.N1173.d015940 ρ weight x) := by
    change _root_.GD.N0232.N0720.N1173.d015946 ρ weight x = _ at hpair
    rw [hE₀, hMw, hM₀, hEw] at hpair
    exact hpair
  have hw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939] using hcutoff
  have htw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc, mul_left_comm, mul_comm] using
      hcutoffMoment
  rw [_root_.GD.N0232.N0720.N1173.d015952 ρ weight x hw htw, hpair']
  unfold _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1173.d015943
  field_simp [hfullEvidence]

theorem d015954
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (htw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hmass : _root_.GD.N0232.N0720.N1173.d015940 ρ weight x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015943 ρ weight x - _root_.GD.N0232.N0720.N1173.d015944 ρ x =
      _root_.GD.N0232.N0720.N1173.d015945 ρ weight x /
        _root_.GD.N0232.N0720.N1173.d015940 ρ weight x := by
  rw [_root_.GD.N0232.N0720.N1173.d015952 ρ weight x hw htw]
  unfold _root_.GD.N0232.N0720.N1173.d015943
  field_simp [hmass]

theorem d015955
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (htw : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ))
    (hmass : _root_.GD.N0232.N0720.N1173.d015940 ρ weight x ≠ 0) :
    _root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1173.d015944 ρ) (_root_.GD.N0232.N0720.N1173.d015943 ρ weight) x =
      _root_.GD.N0232.N0720.N1173.d015945 ρ weight x ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 ρ weight x := by
  unfold _root_.GD.N0230.N0589.d000089
  change
    _root_.GD.N0232.N0720.N1173.d015940 ρ weight x *
        (_root_.GD.N0232.N0720.N1173.d015944 ρ x - _root_.GD.N0232.N0720.N1173.d015943 ρ weight x) ^ 2 = _
  have hshift :=
    _root_.GD.N0232.N0720.N1173.d015954 ρ weight x hw htw hmass
  rw [show _root_.GD.N0232.N0720.N1173.d015944 ρ x - _root_.GD.N0232.N0720.N1173.d015943 ρ weight x =
      -(_root_.GD.N0232.N0720.N1173.d015943 ρ weight x - _root_.GD.N0232.N0720.N1173.d015944 ρ x) by ring,
    hshift]
  field_simp [hmass]





def d015956
    (ρ : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ :=
  _root_.GD.N0230.N0589.d000084
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015944 ρ) -
    _root_.GD.N0230.N0589.d000084
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015943 ρ weight)







theorem d015957
    (ρ : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite ρ]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015944 ρ)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 ρ).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 ρ weight)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 ρ).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1173.d015944 ρ) (_root_.GD.N0232.N0720.N1173.d015943 ρ weight))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      Integrable
          (fun θ ↦
            _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      Integrable
          (fun θ ↦
            _root_.GD.N0232.N0720.N1173.d015938 θ ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      _root_.GD.N0232.N0720.N1173.d015940 ρ weight x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015956 ρ weight =
      ∫ x,
        _root_.GD.N0232.N0720.N1173.d015945 ρ weight x ^ 2 /
          _root_.GD.N0232.N0720.N1173.d015940 ρ weight x
            ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  letI : SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 2 2) := inferInstance
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015944 ρ x) =
        _root_.GD.N0230.N0589.d000087
            (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
              _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015943 ρ weight x) +
          _root_.GD.N0230.N0589.d000089
            (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
              (_root_.GD.N0232.N0720.N1173.d015944 ρ) (_root_.GD.N0232.N0720.N1173.d015943 ρ weight) x := by
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    simpa [_root_.GD.N0230.N0589.d000089, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1173.d015951
        ρ weight x (_root_.GD.N0232.N0720.N1173.d015944 ρ x) hw htw ht2w hmass
  unfold _root_.GD.N0232.N0720.N1173.d015956
  rw [_root_.GD.N0230.N0589.d000093
    (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
    (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
    (_root_.GD.N0232.N0720.N1173.d015944 ρ) (_root_.GD.N0232.N0720.N1173.d015943 ρ weight)
    hfullJoint hcutJoint htax hpointwise]
  apply integral_congr_ae
  filter_upwards [hmoments] with x hx
  exact _root_.GD.N0232.N0720.N1173.d015955
    ρ weight x hx.1 hx.2.1 hx.2.2.2







theorem d015958
    (ρ : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite ρ]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015944 ρ)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 ρ).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 ρ weight)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 ρ).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 ρ) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          (_root_.GD.N0232.N0720.N1173.d015944 ρ) (_root_.GD.N0232.N0720.N1173.d015943 ρ weight))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      Integrable
          (fun θ ↦
            _root_.GD.N0232.N0720.N1173.d015938 θ * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      Integrable
          (fun θ ↦
            _root_.GD.N0232.N0720.N1173.d015938 θ ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      _root_.GD.N0232.N0720.N1173.d015940 ρ weight x ≠ 0)
    (hfullMoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      Integrable
          (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x * _root_.GD.N0232.N0720.N1173.d015938 θ)
          (_root_.GD.N0232.N0720.N1173.d015934 ρ) ∧
      _root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015956 ρ weight =
      ∫ x,
        _root_.GD.N0232.N0720.N1173.d015946 ρ weight x ^ 2 /
          (4 * _root_.GD.N0232.N0720.N1173.d015940 ρ (fun _ ↦ 1) x ^ 2 *
            _root_.GD.N0232.N0720.N1173.d015940 ρ weight x)
              ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  rw [_root_.GD.N0232.N0720.N1173.d015957
    ρ weight hfullJoint hcutJoint htax hmoments]
  apply integral_congr_ae
  filter_upwards [hmoments, hfullMoments] with x hx hfullx
  have hcutoff : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x * weight θ)
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939] using hx.1
  have hcutoffMoment : Integrable
      (fun θ ↦ _root_.GD.N0232.N0720.N1173.d015937 θ x *
        (_root_.GD.N0232.N0720.N1173.d015938 θ * weight θ))
      (_root_.GD.N0232.N0720.N1173.d015934 ρ) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc, mul_left_comm, mul_comm] using
      hx.2.1
  rw [_root_.GD.N0232.N0720.N1173.d015953
    ρ weight x hfullx.1 hfullx.2.1 hcutoff hcutoffMoment
      hfullx.2.2]
  field_simp [hx.2.2.2, hfullx.2.2]
  ring

end

end N1173
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1173.d015949
#print axioms _root_.GD.N0232.N0720.N1173.d015951
#print axioms _root_.GD.N0232.N0720.N1173.d015957
#print axioms _root_.GD.N0232.N0720.N1173.d015953
#print axioms _root_.GD.N0232.N0720.N1173.d015958
