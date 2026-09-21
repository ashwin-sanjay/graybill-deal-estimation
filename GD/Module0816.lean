import GD.Module0674
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


























open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1034

noncomputable section




@[ext]
structure d012402 where
  location : ℝ
  radius : ℝ
  fraction : ℝ


def d012403 (shift dilation : ℝ)
    (x : _root_.GD.N0232.N0720.N1034.d012402) : _root_.GD.N0232.N0720.N1034.d012402 where
  location := shift + dilation * x.location
  radius := dilation * x.radius
  fraction := x.fraction

@[simp] theorem d012404
    (shift dilation : ℝ) (x : _root_.GD.N0232.N0720.N1034.d012402) :
    (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x).location =
      shift + dilation * x.location := rfl

@[simp] theorem d012405
    (shift dilation : ℝ) (x : _root_.GD.N0232.N0720.N1034.d012402) :
    (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x).radius = dilation * x.radius := rfl

@[simp] theorem d012406
    (shift dilation : ℝ) (x : _root_.GD.N0232.N0720.N1034.d012402) :
    (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x).fraction = x.fraction := rfl


theorem d012407
    (a b c d : ℝ) (x : _root_.GD.N0232.N0720.N1034.d012402) :
    _root_.GD.N0232.N0720.N1034.d012403 a b (_root_.GD.N0232.N0720.N1034.d012403 c d x) =
      _root_.GD.N0232.N0720.N1034.d012403 (a + b * c) (b * d) x := by
  ext <;> simp [_root_.GD.N0232.N0720.N1034.d012403] <;> ring


def d012408 (dilation : ℝ) : ℝ := dilation ^ 2


theorem d012409 (b d : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012408 (b * d) =
      _root_.GD.N0232.N0720.N1034.d012408 b * _root_.GD.N0232.N0720.N1034.d012408 d := by
  unfold _root_.GD.N0232.N0720.N1034.d012408
  ring










def d012410 (m n : ℝ) (r z : ℝ) : ℝ :=
  r * Real.sqrt (m * n) / (2 * Real.sqrt (z * (1 - z)))



theorem d012411
    (m n r z b : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012410 m n (b * r) z =
      b * _root_.GD.N0232.N0720.N1034.d012410 m n r z := by
  unfold _root_.GD.N0232.N0720.N1034.d012410
  ring



theorem d012412
    (m n r z b : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012410 m n (b * r) z *
        _root_.GD.N0232.N0720.N1034.d012408 b =
      b ^ 3 * _root_.GD.N0232.N0720.N1034.d012410 m n r z := by
  rw [_root_.GD.N0232.N0720.N1034.d012411]
  unfold _root_.GD.N0232.N0720.N1034.d012408
  ring


def d012413 (m r z : ℝ) : ℝ :=
  m * r ^ 2 * (1 - z)

def d012414 (n r z : ℝ) : ℝ :=
  n * r ^ 2 * z






theorem d012415
    (m n r z : ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hr : r ≠ 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    r⁻¹ * (_root_.GD.N0232.N0720.N1034.d012413 m r z)⁻¹ *
        (_root_.GD.N0232.N0720.N1034.d012414 n r z)⁻¹ =
      (m * n)⁻¹ * (r ^ 5 * (z * (1 - z)))⁻¹ := by
  have hzbar : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  unfold _root_.GD.N0232.N0720.N1034.d012413 _root_.GD.N0232.N0720.N1034.d012414
  field_simp [hm, hn, hr, hz0, hzbar]





def d012416 (z xbar ybar : ℝ) : ℝ :=
  z * xbar + (1 - z) * ybar



def d012417 (z : ℝ) : Fin 2 → ℝ := ![z, 1 - z]

def d012418 (xbar ybar : ℝ) : Fin 2 → ℝ := ![xbar, ybar]



theorem d012419
    (z xbar ybar : ℝ) :
    _root_.GD.N0232.N0719.N0928.d009405
        (_root_.GD.N0232.N0720.N1034.d012417 z) (_root_.GD.N0232.N0720.N1034.d012418 xbar ybar) =
      _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
    _root_.GD.N0232.N0720.N1034.d012417 _root_.GD.N0232.N0720.N1034.d012418 _root_.GD.N0232.N0720.N1034.d012416
  rw [Fin.sum_univ_two]
  simp




def d012420
    (m n z xbar ybar sse₁ sse₂ : ℝ) : ℝ :=
  (xbar - ybar) ^ 2 +
    sse₁ / (m * (1 - z)) + sse₂ / (n * z)


theorem d012421
    (z xbar ybar shift dilation : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012416 z
        (shift + dilation * xbar) (shift + dilation * ybar) =
      shift + dilation * _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar := by
  unfold _root_.GD.N0232.N0720.N1034.d012416
  ring



theorem d012422
    (z mu xbar ybar : ℝ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (mu - xbar) ^ 2 / (1 - z) + (mu - ybar) ^ 2 / z =
      (mu - _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar) ^ 2 / (z * (1 - z)) +
        (xbar - ybar) ^ 2 := by
  have honeSub : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  unfold _root_.GD.N0232.N0720.N1034.d012416
  field_simp [hz0, honeSub]
  ring



theorem d012423
    (m n z xbar ybar sse₁ sse₂ shift dilation : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012420 m n z
        (shift + dilation * xbar) (shift + dilation * ybar)
        (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂) =
      dilation ^ 2 *
        _root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂ := by
  unfold _root_.GD.N0232.N0720.N1034.d012420
  ring



def d012424 (r z : ℝ) : ℝ := r ^ 2 * z * (1 - z)




theorem d012425
    (r z : ℝ) (hr : r ≠ 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    z / _root_.GD.N0232.N0720.N1034.d012424 r z = 1 / (r ^ 2 * (1 - z)) := by
  unfold _root_.GD.N0232.N0720.N1034.d012424
  have hzbar : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  field_simp [hr, hz0, hzbar]

theorem d012426
    (r z : ℝ) (hr : r ≠ 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (1 - z) / _root_.GD.N0232.N0720.N1034.d012424 r z = 1 / (r ^ 2 * z) := by
  unfold _root_.GD.N0232.N0720.N1034.d012424
  have hzbar : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  field_simp [hr, hz0, hzbar]




theorem d012427
    (m n z xbar ybar t₁ t₂ : ℝ)
    (hm : m ≠ 0) (hn : n ≠ 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (1 / 2 : ℝ) * z * (1 - z) * (xbar - ybar) ^ 2 +
        ((m - 1) / 2) * z * t₁ +
        ((n - 1) / 2) * (1 - z) * t₂ =
      z * (1 - z) / 2 *
        _root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar
          ((m - 1) * m * t₁) ((n - 1) * n * t₂) := by
  unfold _root_.GD.N0232.N0720.N1034.d012420
  have hzbar : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  field_simp [hm, hn, hz0, hzbar]





def d012428 (kappa : ℝ) : ℝ := (kappa + 1) / 2


def d012429 (m n kappa : ℝ) : ℝ :=
  (m + n + kappa - 2) / 2


def d012430 (m n : ℕ) : Fin 2 → ℕ := ![m, n]



theorem d012431
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (kappa : ℝ) :
    _root_.GD.N0232.N0719.N0928.d009415
        (_root_.GD.N0232.N0719.N0954.d009355
          (_root_.GD.N0232.N0720.N1034.d012430 m n))
        (_root_.GD.N0232.N0720.N1034.d012428 kappa) =
      _root_.GD.N0232.N0720.N1034.d012429 m n kappa := by
  unfold _root_.GD.N0232.N0719.N0928.d009415
  rw [_root_.GD.N0232.N0719.N0928.d009418
    (_root_.GD.N0232.N0720.N1034.d012430 m n) (by
      intro i
      fin_cases i
      · simpa [_root_.GD.N0232.N0720.N1034.d012430] using hm
      · simpa [_root_.GD.N0232.N0720.N1034.d012430] using hn)]
  rw [Fin.sum_univ_two]
  change (m : ℝ) / 2 + (n : ℝ) / 2 +
      _root_.GD.N0232.N0720.N1034.d012428 kappa - 3 / 2 =
    _root_.GD.N0232.N0720.N1034.d012429 (m : ℝ) (n : ℝ) kappa
  unfold _root_.GD.N0232.N0720.N1034.d012428 _root_.GD.N0232.N0720.N1034.d012429
  ring

theorem d012432
    (m n kappa : ℝ) :
    (m + n) / 2 + _root_.GD.N0232.N0720.N1034.d012428 kappa - 3 / 2 =
      _root_.GD.N0232.N0720.N1034.d012429 m n kappa := by
  unfold _root_.GD.N0232.N0720.N1034.d012428 _root_.GD.N0232.N0720.N1034.d012429
  ring



theorem d012433
    (kappa : ℝ) :
    _root_.GD.N0232.N0719.N0907.d009855
        (_root_.GD.N0232.N0720.N1034.d012428 kappa) = 4 - kappa := by
  unfold _root_.GD.N0232.N0720.N1034.d012428
    _root_.GD.N0232.N0719.N0907.d009855
  ring



theorem d012434
    (kappa : ℝ) :
    _root_.GD.N0232.N0719.N0907.d009855
        (_root_.GD.N0232.N0720.N1034.d012428 kappa) = 0 ↔ kappa = 4 := by
  rw [_root_.GD.N0232.N0720.N1034.d012433]
  constructor <;> intro h <;> linarith





theorem d012435
    (kappa r z : ℝ) (hr : 0 < r) (hz : 0 < z * (1 - z)) :
    _root_.GD.N0232.N0720.N1034.d012424 r z ^ (-_root_.GD.N0232.N0720.N1034.d012428 kappa) *
        (2 * r * (z * (1 - z))) =
      2 * r ^ (-kappa) *
        (z * (1 - z)) ^ ((1 - kappa) / 2) := by
  unfold _root_.GD.N0232.N0720.N1034.d012424 _root_.GD.N0232.N0720.N1034.d012428
  rw [show r ^ 2 * z * (1 - z) = r ^ 2 * (z * (1 - z)) by ring]
  let Z : ℝ := z * (1 - z)
  change (r ^ 2 * Z) ^ (-((kappa + 1) / 2)) * (2 * r * Z) =
    2 * r ^ (-kappa) * Z ^ ((1 - kappa) / 2)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hZ : 0 < Z := by simpa [Z] using hz
  rw [Real.mul_rpow hr2.le hZ.le]
  rw [show r ^ 2 = r ^ (2 : ℝ) by simp [Real.rpow_two]]
  rw [← Real.rpow_mul hr.le]
  calc
    r ^ ((2 : ℝ) * (-((kappa + 1) / 2))) *
          Z ^ (-((kappa + 1) / 2)) *
          (2 * r * Z) =
        r ^ ((2 : ℝ) * (-((kappa + 1) / 2))) *
          Z ^ (-((kappa + 1) / 2)) *
          (2 * r ^ (1 : ℝ) * Z ^ (1 : ℝ)) := by
      rw [Real.rpow_one, Real.rpow_one]
    _ = 2 *
          (r ^ ((2 : ℝ) * (-((kappa + 1) / 2))) * r ^ (1 : ℝ)) *
          (Z ^ (-((kappa + 1) / 2)) * Z ^ (1 : ℝ)) := by ring
    _ = 2 *
          r ^ ((2 : ℝ) * (-((kappa + 1) / 2)) + 1) *
          Z ^ (-((kappa + 1) / 2) + 1) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hZ]
    _ = 2 * r ^ (-kappa) * Z ^ ((1 - kappa) / 2) := by
      congr 1 <;> ring




theorem d012436
    (r z : ℝ) (hr : 0 < r) (hz : 0 < z * (1 - z)) :
    _root_.GD.N0232.N0720.N1034.d012424 r z ^ (-(5 / 2 : ℝ)) *
        (2 * r * (z * (1 - z))) =
      2 * r ^ (-(4 : ℝ)) *
        (z * (1 - z)) ^ (-(3 / 2 : ℝ)) := by
  convert _root_.GD.N0232.N0720.N1034.d012435 (4 : ℝ) r z hr hz using 1 <;>
    norm_num [_root_.GD.N0232.N0720.N1034.d012428]



def d012437
    (m n kappa z energy : ℝ) : ℝ :=
  (1 - z) ^ (-(m - 1) / 2) *
    z ^ (-(n - 1) / 2) *
    energy ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa)





theorem d012438
    (m n kappa z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    z ^ (m / 2) * (1 - z) ^ (n / 2) *
        (z * (1 - z)) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
        (z * (1 - z)) ^ ((kappa - 1) / 2) =
      (1 - z) ^ (-(m - 1) / 2) *
        z ^ (-(n - 1) / 2) := by
  have h1z : 0 < 1 - z := sub_pos.mpr hz1
  rw [Real.mul_rpow hz0.le h1z.le,
    Real.mul_rpow hz0.le h1z.le]
  calc
    z ^ (m / 2) * (1 - z) ^ (n / 2) *
          (z ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
            (1 - z) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa)) *
          (z ^ ((kappa - 1) / 2) *
            (1 - z) ^ ((kappa - 1) / 2)) =
        (z ^ (m / 2) * z ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
            z ^ ((kappa - 1) / 2)) *
          ((1 - z) ^ (n / 2) *
            (1 - z) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
            (1 - z) ^ ((kappa - 1) / 2)) := by ring
    _ = z ^ (m / 2 - _root_.GD.N0232.N0720.N1034.d012429 m n kappa +
            (kappa - 1) / 2) *
          (1 - z) ^ (n / 2 - _root_.GD.N0232.N0720.N1034.d012429 m n kappa +
            (kappa - 1) / 2) := by
      rw [← Real.rpow_add hz0, ← Real.rpow_add hz0,
        ← Real.rpow_add h1z, ← Real.rpow_add h1z]
      congr 1 <;> ring
    _ = (1 - z) ^ (-(m - 1) / 2) *
          z ^ (-(n - 1) / 2) := by
      have hzExponent :
          m / 2 - _root_.GD.N0232.N0720.N1034.d012429 m n kappa + (kappa - 1) / 2 =
            -(n - 1) / 2 := by
        unfold _root_.GD.N0232.N0720.N1034.d012429
        ring
      have hOneSubExponent :
          n / 2 - _root_.GD.N0232.N0720.N1034.d012429 m n kappa + (kappa - 1) / 2 =
            -(m - 1) / 2 := by
        unfold _root_.GD.N0232.N0720.N1034.d012429
        ring
      rw [hzExponent, hOneSubExponent]
      ring




theorem d012439
    (m n kappa z energy : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    z ^ (m / 2) * (1 - z) ^ (n / 2) *
        (z * (1 - z)) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
        (z * (1 - z)) ^ ((kappa - 1) / 2) *
        energy ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) =
      _root_.GD.N0232.N0720.N1034.d012437 m n kappa z energy := by
  rw [_root_.GD.N0232.N0720.N1034.d012438 m n kappa z hz0 hz1]
  unfold _root_.GD.N0232.N0720.N1034.d012437
  ring



theorem d012440
    (m n kappa z energy : ℝ) {dilation : ℝ}
    (hdilation : 0 < dilation) (henergy : 0 ≤ energy) :
    _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
        (dilation ^ 2 * energy) =
      (dilation ^ 2) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa) *
        _root_.GD.N0232.N0720.N1034.d012437 m n kappa z energy := by
  unfold _root_.GD.N0232.N0720.N1034.d012437
  rw [Real.mul_rpow (sq_nonneg dilation) henergy]
  ring



theorem d012441
    (m n kappa : ℝ) :
    0 < _root_.GD.N0232.N0720.N1034.d012429 m n kappa ↔ 2 < m + n + kappa := by
  unfold _root_.GD.N0232.N0720.N1034.d012429
  constructor <;> intro h <;> linarith






def d012442
    (rho : Measure ℝ) (m n kappa xbar ybar sse₁ sse₂ : ℝ) : ℝ :=
  ∫ z,
    _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
      (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂) ∂rho


def d012443
    (rho : Measure ℝ) (m n kappa xbar ybar sse₁ sse₂ : ℝ) : ℝ :=
  ∫ z,
    _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
        (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂) *
      _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar ∂rho



def d012444
    (rho : Measure ℝ) (m n kappa xbar ybar sse₁ sse₂ : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1034.d012443 rho m n kappa xbar ybar sse₁ sse₂ /
    _root_.GD.N0232.N0720.N1034.d012442 rho m n kappa xbar ybar sse₁ sse₂






theorem d012445
    (rho : Measure ℝ) (m n kappa xbar ybar sse₁ sse₂ shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (henergy : ∀ᵐ z ∂rho,
      0 ≤ _root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂)
    (hweight : Integrable
      (fun z ↦ _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
        (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂)) rho)
    (hweightedCenter : Integrable
      (fun z ↦ _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
          (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂) *
        _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar) rho)
    (hevidence : _root_.GD.N0232.N0720.N1034.d012442 rho m n kappa
      xbar ybar sse₁ sse₂ ≠ 0) :
    _root_.GD.N0232.N0720.N1034.d012444 rho m n kappa
        (shift + dilation * xbar) (shift + dilation * ybar)
        (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂) =
      shift + dilation *
        _root_.GD.N0232.N0720.N1034.d012444 rho m n kappa xbar ybar sse₁ sse₂ := by
  let A : ℝ :=
    (dilation ^ 2) ^ (-_root_.GD.N0232.N0720.N1034.d012429 m n kappa)
  let E : ℝ → ℝ := fun z ↦
    _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
      (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂)
  let M : ℝ → ℝ := fun z ↦ _root_.GD.N0232.N0720.N1034.d012416 z xbar ybar
  have hA : A ≠ 0 := by
    unfold A
    exact (Real.rpow_pos_of_pos (sq_pos_of_pos hdilation) _).ne'
  have hEvidenceTransform :
      _root_.GD.N0232.N0720.N1034.d012442 rho m n kappa
          (shift + dilation * xbar) (shift + dilation * ybar)
          (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂) =
        A * _root_.GD.N0232.N0720.N1034.d012442 rho m n kappa
          xbar ybar sse₁ sse₂ := by
    unfold _root_.GD.N0232.N0720.N1034.d012442
    calc
      (∫ z, _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
          (_root_.GD.N0232.N0720.N1034.d012420 m n z
            (shift + dilation * xbar) (shift + dilation * ybar)
            (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂)) ∂rho) =
          ∫ z, A * E z ∂rho := by
        apply integral_congr_ae
        filter_upwards [henergy] with z hz
        rw [_root_.GD.N0232.N0720.N1034.d012423,
          _root_.GD.N0232.N0720.N1034.d012440
            m n kappa z
              (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂)
              hdilation hz]
      _ = A * ∫ z, E z ∂rho := by rw [integral_const_mul]
      _ = _ := rfl
  have hNumeratorTransform :
      _root_.GD.N0232.N0720.N1034.d012443 rho m n kappa
          (shift + dilation * xbar) (shift + dilation * ybar)
          (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂) =
        A * (shift * _root_.GD.N0232.N0720.N1034.d012442 rho m n kappa
              xbar ybar sse₁ sse₂ +
          dilation * _root_.GD.N0232.N0720.N1034.d012443 rho m n kappa
              xbar ybar sse₁ sse₂) := by
    unfold _root_.GD.N0232.N0720.N1034.d012443 _root_.GD.N0232.N0720.N1034.d012442
    calc
      (∫ z, _root_.GD.N0232.N0720.N1034.d012437 m n kappa z
            (_root_.GD.N0232.N0720.N1034.d012420 m n z
              (shift + dilation * xbar) (shift + dilation * ybar)
              (dilation ^ 2 * sse₁) (dilation ^ 2 * sse₂)) *
          _root_.GD.N0232.N0720.N1034.d012416 z
            (shift + dilation * xbar) (shift + dilation * ybar) ∂rho) =
          ∫ z, (A * shift) * E z +
            (A * dilation) * (E z * M z) ∂rho := by
        apply integral_congr_ae
        filter_upwards [henergy] with z hz
        rw [_root_.GD.N0232.N0720.N1034.d012423,
          _root_.GD.N0232.N0720.N1034.d012440
            m n kappa z
              (_root_.GD.N0232.N0720.N1034.d012420 m n z xbar ybar sse₁ sse₂)
              hdilation hz,
          _root_.GD.N0232.N0720.N1034.d012421]
        change A * E z * (shift + dilation * M z) = _
        ring
      _ = (A * shift) * (∫ z, E z ∂rho) +
          (A * dilation) * (∫ z, E z * M z ∂rho) := by
        rw [integral_add (hweight.const_mul _) (hweightedCenter.const_mul _),
          integral_const_mul, integral_const_mul]
      _ = A * (shift * (∫ z, E z ∂rho) +
          dilation * (∫ z, E z * M z ∂rho)) := by ring
  unfold _root_.GD.N0232.N0720.N1034.d012444
  rw [hEvidenceTransform, hNumeratorTransform]
  field_simp [hA, hevidence]






def d012446 (c : ℝ) (density : _root_.GD.N0232.N0720.N1034.d012402 → ℝ) : Prop :=
  ∀ (shift dilation : ℝ), 0 < dilation →
    ∀ x : _root_.GD.N0232.N0720.N1034.d012402, 0 < x.radius →
      density (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x) *
          _root_.GD.N0232.N0720.N1034.d012408 dilation =
        dilation ^ c * density x


def d012447 (z : ℝ) : _root_.GD.N0232.N0720.N1034.d012402 :=
  ⟨0, 1, z⟩

@[simp] theorem d012448
    (mu r z : ℝ) :
    _root_.GD.N0232.N0720.N1034.d012403 mu r (_root_.GD.N0232.N0720.N1034.d012447 z) = ⟨mu, r, z⟩ := by
  ext <;> simp [_root_.GD.N0232.N0720.N1034.d012403, _root_.GD.N0232.N0720.N1034.d012447]


theorem d012449
    (r c : ℝ) (hr : 0 < r) :
    r ^ (c - 2) * r ^ 2 = r ^ c := by
  rw [show r ^ 2 = r ^ (2 : ℝ) by simp [Real.rpow_two],
    ← Real.rpow_add hr]
  congr 1
  ring




theorem d012450
    (c : ℝ) (density : _root_.GD.N0232.N0720.N1034.d012402 → ℝ) :
    _root_.GD.N0232.N0720.N1034.d012446 c density ↔
      ∀ x : _root_.GD.N0232.N0720.N1034.d012402, 0 < x.radius →
        density x =
          x.radius ^ (c - 2) * density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction) := by
  constructor
  · intro h x hx
    have hbase := h x.location x.radius hx
      (_root_.GD.N0232.N0720.N1034.d012447 x.fraction) (by simp [_root_.GD.N0232.N0720.N1034.d012447])
    rw [_root_.GD.N0232.N0720.N1034.d012448, _root_.GD.N0232.N0720.N1034.d012408] at hbase
    apply mul_right_cancel₀ (pow_ne_zero 2 hx.ne')
    calc
      density x * x.radius ^ 2 =
          x.radius ^ c * density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction) := hbase
      _ =
          (x.radius ^ (c - 2) * density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction)) *
            x.radius ^ 2 := by
        rw [mul_assoc, mul_comm (density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction)),
          ← mul_assoc, _root_.GD.N0232.N0720.N1034.d012449 x.radius c hx]
  · intro h shift dilation hdilation x hx
    have htransRadius : 0 < (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x).radius := by
      simp only [_root_.GD.N0232.N0720.N1034.d012405]
      exact mul_pos hdilation hx
    rw [h (_root_.GD.N0232.N0720.N1034.d012403 shift dilation x) htransRadius, h x hx]
    simp only [_root_.GD.N0232.N0720.N1034.d012405, _root_.GD.N0232.N0720.N1034.d012406,
      _root_.GD.N0232.N0720.N1034.d012408]
    rw [Real.mul_rpow hdilation.le hx.le]
    have hpower := _root_.GD.N0232.N0720.N1034.d012449 dilation c hdilation
    calc
      (dilation ^ (c - 2) * x.radius ^ (c - 2) *
              density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction)) *
            dilation ^ 2 =
          (dilation ^ (c - 2) * dilation ^ 2) *
            (x.radius ^ (c - 2) *
              density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction)) := by ring
      _ = dilation ^ c *
            (x.radius ^ (c - 2) *
              density (_root_.GD.N0232.N0720.N1034.d012447 x.fraction)) := by rw [hpower]



def d012451
    (k : ℝ) (profile : ℝ → ℝ) (x : _root_.GD.N0232.N0720.N1034.d012402) : ℝ :=
  x.radius ^ (-k) * profile x.fraction




theorem d012452
    (k : ℝ) (profile : ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1034.d012446 (2 - k) (_root_.GD.N0232.N0720.N1034.d012451 k profile) := by
  rw [_root_.GD.N0232.N0720.N1034.d012450]
  intro x hx
  simp only [_root_.GD.N0232.N0720.N1034.d012451, _root_.GD.N0232.N0720.N1034.d012447, Real.one_rpow, one_mul]
  congr 1
  ring




def d012453 (mass moment : ℝ) : ℝ := moment / mass








theorem d012454
    (mass moment transformedMass transformedMoment : ℝ)
    (shift dilation common : ℝ)
    (hmass : mass ≠ 0) (hcommon : common ≠ 0)
    (hmassTransform : transformedMass = common * mass)
    (hmomentTransform : transformedMoment =
      common * (shift * mass + dilation * moment)) :
    _root_.GD.N0232.N0720.N1034.d012453 transformedMass transformedMoment =
      shift + dilation * _root_.GD.N0232.N0720.N1034.d012453 mass moment := by
  unfold _root_.GD.N0232.N0720.N1034.d012453
  rw [hmassTransform, hmomentTransform]
  field_simp [hmass, hcommon]



theorem d012455
    (mass moment transformedMass transformedMoment : ℝ)
    (shift dilation priorCharacter likelihoodCocycle : ℝ)
    (hmass : mass ≠ 0) (hprior : priorCharacter ≠ 0)
    (hlikelihood : likelihoodCocycle ≠ 0)
    (hmassTransform : transformedMass =
      priorCharacter * likelihoodCocycle * mass)
    (hmomentTransform : transformedMoment =
      priorCharacter * likelihoodCocycle *
        (shift * mass + dilation * moment)) :
    _root_.GD.N0232.N0720.N1034.d012453 transformedMass transformedMoment =
      shift + dilation * _root_.GD.N0232.N0720.N1034.d012453 mass moment := by
  exact _root_.GD.N0232.N0720.N1034.d012454
    mass moment transformedMass transformedMoment shift dilation
      (priorCharacter * likelihoodCocycle) hmass
      (mul_ne_zero hprior hlikelihood) hmassTransform hmomentTransform





theorem d012456 (k : ℝ) :
    ¬ IntegrableOn (fun r : ℝ ↦ r ^ (-k)) (Ioi (0 : ℝ)) := by
  exact not_integrableOn_Ioi_rpow (-k)



theorem d012457 (c : ℝ) :
    ¬ IntegrableOn (fun r : ℝ ↦ r ^ (c - 2)) (Ioi (0 : ℝ)) := by
  exact not_integrableOn_Ioi_rpow (c - 2)

end

end N1034
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1034.d012412
#print axioms _root_.GD.N0232.N0720.N1034.d012422
#print axioms _root_.GD.N0232.N0720.N1034.d012427
#print axioms _root_.GD.N0232.N0720.N1034.d012431
#print axioms _root_.GD.N0232.N0720.N1034.d012434
#print axioms _root_.GD.N0232.N0720.N1034.d012436
#print axioms _root_.GD.N0232.N0720.N1034.d012438
#print axioms _root_.GD.N0232.N0720.N1034.d012445
#print axioms _root_.GD.N0232.N0720.N1034.d012450
#print axioms _root_.GD.N0232.N0720.N1034.d012452
#print axioms _root_.GD.N0232.N0720.N1034.d012454
#print axioms _root_.GD.N0232.N0720.N1034.d012455
#print axioms _root_.GD.N0232.N0720.N1034.d012456
