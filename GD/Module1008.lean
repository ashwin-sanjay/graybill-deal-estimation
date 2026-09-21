import GD.Module0034
import GD.Module1002

































open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1179

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0658

noncomputable local instance d016027
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho] :
    SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
  unfold _root_.GD.N0232.N0720.N1173.d015934
  infer_instance


def d016028
    (_rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015937 z.1 x * _root_.GD.N0232.N0720.N1173.d015937 z.2 x


def d016029
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  (_root_.GD.N0232.N0720.N1173.d015938 z.1 - _root_.GD.N0232.N0720.N1173.d015938 z.2) * (h z.1 - h z.2)


def d016030
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  h z.1 + h z.2



def d016031
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016029 h z ^ 2 ∂
      (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)


def d016032
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1179.d016031 rho h x /
    _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x


def d016033
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1179.d016032 rho h x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2



def d016034
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015946 rho weight x ^ 2 /
    (4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
      _root_.GD.N0232.N0720.N1173.d015940 rho weight x)

theorem d016035
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1179.d016031 rho h x := by
  unfold _root_.GD.N0232.N0720.N1179.d016031 _root_.GD.N0232.N0720.N1179.d016028
  apply integral_nonneg_of_ae
  filter_upwards [] with z
  exact mul_nonneg
    (mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.2) x))
    (sq_nonneg _)



theorem d016036
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1173.d015946 rho (fun theta ↦ h theta ^ 2) x =
      ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1179.d016028 rho x z *
          (_root_.GD.N0232.N0720.N1179.d016029 h z * _root_.GD.N0232.N0720.N1179.d016030 h z) ∂
            (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
  unfold _root_.GD.N0232.N0720.N1173.d015946 _root_.GD.N0232.N0720.N1179.d016028
    _root_.GD.N0232.N0720.N1179.d016029 _root_.GD.N0232.N0720.N1179.d016030 _root_.GD.N0232.N0720.N1173.d015938
  apply integral_congr_ae
  filter_upwards [] with z
  ring



theorem d016037
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hlinear : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hsquare : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2 ∂
          (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) =
      2 * (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x ∂_root_.GD.N0232.N0720.N1173.d015934 rho) *
          (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2
            ∂_root_.GD.N0232.N0720.N1173.d015934 rho) +
        2 * (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 rho) ^ 2 := by
  let e : _root_.GD.N0232.N0720.N1173.d015933 → ℝ := fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x
  let eh : _root_.GD.N0232.N0720.N1173.d015933 → ℝ := fun theta ↦ e theta * h theta
  let ehSq : _root_.GD.N0232.N0720.N1173.d015933 → ℝ := fun theta ↦ e theta * h theta ^ 2
  let mu := _root_.GD.N0232.N0720.N1173.d015934 rho
  have h11 : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦ ehSq z.1 * e z.2)
      (mu.prod mu) := hsquare.mul_prod hfull
  have h12 : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        2 * (eh z.1 * eh z.2)) (mu.prod mu) :=
    (hlinear.mul_prod hlinear).const_mul 2
  have h22 : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦ e z.1 * ehSq z.2)
      (mu.prod mu) := hfull.mul_prod hsquare
  have hexpand :
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2) =
      (fun z ↦
        ehSq z.1 * e z.2 + 2 * (eh z.1 * eh z.2) +
          e z.1 * ehSq z.2) := by
    funext z
    simp only [_root_.GD.N0232.N0720.N1179.d016028, _root_.GD.N0232.N0720.N1179.d016030, e, eh, ehSq]
    ring
  rw [hexpand]
  calc
    (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        ehSq z.1 * e z.2 + 2 * (eh z.1 * eh z.2) +
          e z.1 * ehSq z.2 ∂mu.prod mu) =
      (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        ehSq z.1 * e z.2 + 2 * (eh z.1 * eh z.2) ∂mu.prod mu) +
        ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
          e z.1 * ehSq z.2 ∂mu.prod mu := by
      simpa only [Pi.add_apply] using integral_add (h11.add h12) h22
    _ = ((∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
          ehSq z.1 * e z.2 ∂mu.prod mu) +
        ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
          2 * (eh z.1 * eh z.2) ∂mu.prod mu) +
        ∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
          e z.1 * ehSq z.2 ∂mu.prod mu := by
      rw [integral_add h11 h12]
    _ = 2 * (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x
          ∂_root_.GD.N0232.N0720.N1173.d015934 rho) *
          (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2
            ∂_root_.GD.N0232.N0720.N1173.d015934 rho) +
        2 * (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 rho) ^ 2 := by
      rw [integral_const_mul, integral_prod_mul ehSq e,
        integral_prod_mul eh eh, integral_prod_mul e ehSq]
      simp only [e, eh, ehSq, mu]
      ring




theorem d016038
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hlinear : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hsquare : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2 ∂
          (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) ≤
      4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x *
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x := by
  have hnonneg :
      0 ≤ᵐ[_root_.GD.N0232.N0720.N1173.d015934 rho]
        (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x) := by
    filter_upwards [] with theta
    exact _root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x
  have hunitSq : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * (1 : ℝ) ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := by simpa using hfull
  have hunitMul : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * ((1 : ℝ) * h theta))
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := by simpa using hlinear
  have hcs := _root_.GD.N0230.N0658.d000405
    (_root_.GD.N0232.N0720.N1173.d015934 rho)
    (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x) (fun _ ↦ (1 : ℝ)) h
    hnonneg hunitSq hunitMul hsquare
  have hcs' :
      (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 rho) ^ 2 ≤
        (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x ∂_root_.GD.N0232.N0720.N1173.d015934 rho) *
          ∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2
            ∂_root_.GD.N0232.N0720.N1173.d015934 rho := by
    simpa only [one_mul, mul_one, one_pow] using hcs
  have hsum := _root_.GD.N0232.N0720.N1179.d016037
    rho h x hfull hlinear hsquare
  have hE₀ :
      (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x ∂_root_.GD.N0232.N0720.N1173.d015934 rho) =
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x := by
    simp [_root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0232.N0720.N1173.d015939]
  have hEhSq :
      (∫ theta, _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2
          ∂_root_.GD.N0232.N0720.N1173.d015934 rho) =
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x := by
    rfl
  rw [hsum, hE₀, hEhSq]
  rw [hE₀, hEhSq] at hcs'
  nlinarith



theorem d016039
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hlinear : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hsquare : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcurrent : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z *
          (_root_.GD.N0232.N0720.N1179.d016029 h z * _root_.GD.N0232.N0720.N1179.d016030 h z))
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hroot : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016029 h z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho))) :
    _root_.GD.N0232.N0720.N1173.d015946 rho (fun theta ↦ h theta ^ 2) x ^ 2 ≤
      4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x *
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x *
          _root_.GD.N0232.N0720.N1179.d016031 rho h x := by
  let mu := _root_.GD.N0232.N0720.N1173.d015934 rho
  let pairMeasure := mu.prod mu
  have hsum : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2)
      pairMeasure := by
    have h11 : Integrable
        (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
          (_root_.GD.N0232.N0720.N1173.d015937 z.1 x * h z.1 ^ 2) * _root_.GD.N0232.N0720.N1173.d015937 z.2 x)
        pairMeasure := hsquare.mul_prod hfull
    have h12 : Integrable
        (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
          2 * ((_root_.GD.N0232.N0720.N1173.d015937 z.1 x * h z.1) *
            (_root_.GD.N0232.N0720.N1173.d015937 z.2 x * h z.2))) pairMeasure :=
      (hlinear.mul_prod hlinear).const_mul 2
    have h22 : Integrable
        (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1173.d015937 z.1 x *
            (_root_.GD.N0232.N0720.N1173.d015937 z.2 x * h z.2 ^ 2)) pairMeasure :=
      hfull.mul_prod hsquare
    exact ((h11.add h12).add h22).congr
      (Filter.Eventually.of_forall fun z ↦ by
        simp only [Pi.add_apply, _root_.GD.N0232.N0720.N1179.d016028, _root_.GD.N0232.N0720.N1179.d016030]
        ring)
  have hmassNonneg :
      0 ≤ᵐ[pairMeasure]
        (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1179.d016028 rho x z) := by
    filter_upwards [] with z
    exact mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.1) x)
      (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 z.2) x)
  have hcross := _root_.GD.N0230.N0658.d000405
    pairMeasure
    (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
      _root_.GD.N0232.N0720.N1179.d016028 rho x z)
    (_root_.GD.N0232.N0720.N1179.d016029 h) (_root_.GD.N0232.N0720.N1179.d016030 h)
    hmassNonneg hroot hcurrent hsum
  rw [← _root_.GD.N0232.N0720.N1179.d016036
    rho h x] at hcross
  change
    _root_.GD.N0232.N0720.N1173.d015946 rho (fun theta ↦ h theta ^ 2) x ^ 2 ≤
      _root_.GD.N0232.N0720.N1179.d016031 rho h x *
        (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
          _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2 ∂
            (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) at hcross
  have hsumBound := _root_.GD.N0232.N0720.N1179.d016038
    rho h x hfull hlinear hsquare
  have hrootNonneg := _root_.GD.N0232.N0720.N1179.d016035 rho h x
  calc
    _root_.GD.N0232.N0720.N1173.d015946 rho (fun theta ↦ h theta ^ 2) x ^ 2 ≤
        _root_.GD.N0232.N0720.N1179.d016031 rho h x *
          (∫ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
            _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016030 h z ^ 2 ∂
              (_root_.GD.N0232.N0720.N1173.d015934 rho).prod
                (_root_.GD.N0232.N0720.N1173.d015934 rho)) := hcross
    _ ≤ _root_.GD.N0232.N0720.N1179.d016031 rho h x *
        (4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x *
          _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x) :=
      mul_le_mul_of_nonneg_left hsumBound hrootNonneg
    _ = 4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x *
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x *
          _root_.GD.N0232.N0720.N1179.d016031 rho h x := by ring



theorem d016040
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hlinear : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hsquare : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hcurrent : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z *
          (_root_.GD.N0232.N0720.N1179.d016029 h z * _root_.GD.N0232.N0720.N1179.d016030 h z))
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hroot : Integrable
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1179.d016028 rho x z * _root_.GD.N0232.N0720.N1179.d016029 h z ^ 2)
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hfullEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x)
    (hcutoffEvidence :
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x) :
    _root_.GD.N0232.N0720.N1179.d016034 rho (fun theta ↦ h theta ^ 2) x ≤
      _root_.GD.N0232.N0720.N1179.d016032 rho h x := by
  have hcs :=
    _root_.GD.N0232.N0720.N1179.d016039
      rho h x hfull hlinear hsquare hcurrent hroot
  have hden :
      0 < 4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
        _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x :=
    mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos hfullEvidence))
      hcutoffEvidence
  unfold _root_.GD.N0232.N0720.N1179.d016034 _root_.GD.N0232.N0720.N1179.d016032
  apply (div_le_iff₀ hden).2
  calc
    _root_.GD.N0232.N0720.N1173.d015946 rho (fun theta ↦ h theta ^ 2) x ^ 2 ≤
        4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x *
          _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x *
            _root_.GD.N0232.N0720.N1179.d016031 rho h x := hcs
    _ = (_root_.GD.N0232.N0720.N1179.d016031 rho h x /
          _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x) *
        (4 * _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ^ 2 *
          _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x) := by
      field_simp [ne_of_gt hfullEvidence]










theorem d016041
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015944 rho)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2))).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho)
          (_root_.GD.N0232.N0720.N1173.d015939 (fun theta ↦ h theta ^ 2))
          (_root_.GD.N0232.N0720.N1173.d015944 rho)
          (_root_.GD.N0232.N0720.N1173.d015943 rho (fun theta ↦ h theta ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
            _root_.GD.N0232.N0720.N1173.d015939 (fun eta ↦ h eta ^ 2) theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x ≠ 0)
    (hfullMoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1173.d015938 theta)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0)
    (hrootData : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
            _root_.GD.N0232.N0720.N1179.d016028 rho x z *
              (_root_.GD.N0232.N0720.N1179.d016029 h z * _root_.GD.N0232.N0720.N1179.d016030 h z))
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)) ∧
      Integrable
          (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933 ↦
            _root_.GD.N0232.N0720.N1179.d016028 rho x z *
              _root_.GD.N0232.N0720.N1179.d016029 h z ^ 2)
          ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))
    (hdeficitIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1179.d016034 rho (fun theta ↦ h theta ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hrootIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1179.d016032 rho h) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1173.d015956 rho (fun theta ↦ h theta ^ 2) ≤
      _root_.GD.N0232.N0720.N1179.d016033 rho h := by
  rw [_root_.GD.N0232.N0720.N1173.d015958
    rho (fun theta ↦ h theta ^ 2)
      hfullJoint hcutJoint htax hmoments hfullMoments]
  change
    (∫ x,
      _root_.GD.N0232.N0720.N1179.d016034 rho (fun theta ↦ h theta ^ 2) x
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) ≤
      ∫ x, _root_.GD.N0232.N0720.N1179.d016032 rho h x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
  apply integral_mono_ae hdeficitIntegrable hrootIntegrable
  filter_upwards [hmoments, hfullMoments, hrootData] with x hx hfullx hrootx
  have hsquare : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x * h theta ^ 2)
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    simpa only [_root_.GD.N0232.N0720.N1173.d015939] using hx.1
  have hfullEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x :=
    lt_of_le_of_ne
      (by simpa using
        (_root_.GD.N0232.N0720.N1173.d015941 rho (fun _ : _root_.GD.N0232.N0720.N1173.d015933 ↦ 1) x))
      (Ne.symm hfullx.2.2)
  have hcutoffEvidence :
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ h theta ^ 2) x :=
    lt_of_le_of_ne (_root_.GD.N0232.N0720.N1173.d015941 rho h x)
      (Ne.symm hx.2.2.2)
  exact _root_.GD.N0232.N0720.N1179.d016040
    rho h x hfullx.1 hrootx.1 hsquare hrootx.2.1 hrootx.2.2
      hfullEvidence hcutoffEvidence

end

end N1179
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1179.d016036
#print axioms _root_.GD.N0232.N0720.N1179.d016040
#print axioms _root_.GD.N0232.N0720.N1179.d016041
