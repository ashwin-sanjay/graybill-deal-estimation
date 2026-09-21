import Mathlib



















namespace GD.N0232.N0720.N1254

noncomputable section



def d002510 (alpha beta : ℝ) : ℝ := alpha + beta

def d002511 (alpha beta : ℝ) : ℝ := alpha - beta

def d002512 (alpha beta : ℝ) : ℝ :=
  alpha * beta / _root_.GD.N0232.N0720.N1254.d002510 alpha beta

def d002513 (alpha beta : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002510 alpha beta + 3 / 2

def d002514 (alpha beta : ℝ) : ℝ :=
  alpha / _root_.GD.N0232.N0720.N1254.d002510 alpha beta

def d002515 (alpha beta e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002514 alpha beta - e

def d002516 (alpha beta e : ℝ) : ℝ :=
  beta - _root_.GD.N0232.N0720.N1254.d002510 alpha beta * e

def d002517 (e : ℝ) : ℝ := e * (1 - e) / 2


def d002518 (alpha beta : ℝ) : ℝ :=
  min alpha beta / _root_.GD.N0232.N0720.N1254.d002510 alpha beta

def d002519 (alpha beta : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002518 alpha beta / (16 * N)

def d002520 (alpha beta : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002512 alpha beta / (8 * N)


def d002521 (alpha beta e s t : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002512 alpha beta + _root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s + _root_.GD.N0232.N0720.N1254.d002517 e * t

theorem d002522 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002510 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1254.d002510
  positivity

theorem d002523 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002512 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1254.d002512
  exact div_pos (mul_pos halpha hbeta) (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta)

theorem d002524 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1 := by
  unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
  linarith

theorem d002525 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1254.d002514 alpha beta ∈ Set.Ioo (0 : ℝ) 1 := by
  have hsum := _root_.GD.N0232.N0720.N1254.d002522 halpha hbeta
  constructor
  · exact div_pos halpha hsum
  · unfold _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002510
    rw [div_lt_one (by simpa [_root_.GD.N0232.N0720.N1254.d002510] using hsum)]
    linarith

theorem d002526 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002518 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1254.d002518
  exact div_pos (lt_min halpha hbeta) (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta)


theorem d002527 {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    min alpha beta / 2 ≤ _root_.GD.N0232.N0720.N1254.d002512 alpha beta := by
  have hsum := _root_.GD.N0232.N0720.N1254.d002522 halpha hbeta
  rcases le_total alpha beta with hab | hba
  · rw [min_eq_left hab]
    unfold _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002510
    have hsum' : 0 < alpha + beta := by simpa [_root_.GD.N0232.N0720.N1254.d002510] using hsum
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsum']
    nlinarith
  · rw [min_eq_right hba]
    unfold _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002510
    have hsum' : 0 < alpha + beta := by simpa [_root_.GD.N0232.N0720.N1254.d002510] using hsum
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsum']
    nlinarith

theorem d002528 {alpha beta : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hN : 0 < N) :
    0 < _root_.GD.N0232.N0720.N1254.d002519 alpha beta N := by
  unfold _root_.GD.N0232.N0720.N1254.d002519
  exact div_pos (_root_.GD.N0232.N0720.N1254.d002526 halpha hbeta)
    (mul_pos (by norm_num) (by exact_mod_cast hN))

theorem d002529 {alpha beta : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hN : 0 < N) :
    0 < _root_.GD.N0232.N0720.N1254.d002520 alpha beta N := by
  unfold _root_.GD.N0232.N0720.N1254.d002520
  exact div_pos (_root_.GD.N0232.N0720.N1254.d002523 halpha hbeta)
    (mul_pos (by norm_num) (by exact_mod_cast hN))



theorem d002530
    {alpha beta : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hN : 0 < N) :
    3 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N * _root_.GD.N0232.N0720.N1254.d002510 alpha beta <
      _root_.GD.N0232.N0720.N1254.d002512 alpha beta := by
  have hsum := _root_.GD.N0232.N0720.N1254.d002522 halpha hbeta
  have hmin : 0 < min alpha beta := lt_min halpha hbeta
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalf := _root_.GD.N0232.N0720.N1254.d002527 halpha hbeta
  have hsumne := hsum.ne'
  have hsmall : 3 * min alpha beta / (16 * (N : ℝ)) < min alpha beta / 2 := by
    have hden : 0 < 16 * (N : ℝ) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith
  calc
    3 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N * _root_.GD.N0232.N0720.N1254.d002510 alpha beta =
        3 * min alpha beta / (16 * (N : ℝ)) := by
      unfold _root_.GD.N0232.N0720.N1254.d002519 _root_.GD.N0232.N0720.N1254.d002518
      field_simp [hsumne]
    _ < min alpha beta / 2 := hsmall
    _ ≤ _root_.GD.N0232.N0720.N1254.d002512 alpha beta := hhalf



theorem d002531
    {alpha beta e : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e| ≤ _root_.GD.N0232.N0720.N1254.d002510 alpha beta := by
  rw [abs_le]
  unfold _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002510
  have hsum : 0 ≤ alpha + beta := by nlinarith
  constructor
  · have hone : 0 ≤ 1 - e := sub_nonneg.mpr he.2
    have hprod := mul_nonneg hsum hone
    nlinarith
  · have hprod := mul_nonneg hsum he.1
    nlinarith

theorem d002532 {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ _root_.GD.N0232.N0720.N1254.d002517 e := by
  unfold _root_.GD.N0232.N0720.N1254.d002517
  exact div_nonneg (mul_nonneg he.1 (sub_nonneg.mpr he.2)) (by norm_num)



theorem d002533
    {alpha beta e s t : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (ht : 0 ≤ t)
    (hsmall : |s| * _root_.GD.N0232.N0720.N1254.d002510 alpha beta < _root_.GD.N0232.N0720.N1254.d002512 alpha beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002521 alpha beta e s t := by
  have hsum0 : 0 ≤ _root_.GD.N0232.N0720.N1254.d002510 alpha beta :=
    (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta).le
  have hd := _root_.GD.N0232.N0720.N1254.d002531 halpha hbeta he
  have habsmul :
      |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e| * |s| ≤ _root_.GD.N0232.N0720.N1254.d002510 alpha beta * |s| :=
    mul_le_mul_of_nonneg_right hd (abs_nonneg s)
  have hds :
      -(_root_.GD.N0232.N0720.N1254.d002510 alpha beta * |s|) ≤ _root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s := by
    calc
      -(_root_.GD.N0232.N0720.N1254.d002510 alpha beta * |s|) ≤
          -(|_root_.GD.N0232.N0720.N1254.d002516 alpha beta e| * |s|) := neg_le_neg habsmul
      _ = -|_root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s| := by rw [abs_mul]
      _ ≤ _root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s := neg_abs_le _
  have hht : 0 ≤ _root_.GD.N0232.N0720.N1254.d002517 e * t :=
    mul_nonneg (_root_.GD.N0232.N0720.N1254.d002532 he) ht
  unfold _root_.GD.N0232.N0720.N1254.d002521
  nlinarith



theorem d002534
    {alpha beta e s t : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hN : 0 < N)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (ht : 0 ≤ t)
    (hs : |s| ≤ 3 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N) :
    0 < _root_.GD.N0232.N0720.N1254.d002521 alpha beta e s t := by
  apply _root_.GD.N0232.N0720.N1254.d002533 halpha hbeta he ht
  have hsum0 : 0 ≤ _root_.GD.N0232.N0720.N1254.d002510 alpha beta :=
    (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta).le
  calc
    |s| * _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≤
        (3 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N) * _root_.GD.N0232.N0720.N1254.d002510 alpha beta :=
      mul_le_mul_of_nonneg_right hs hsum0
    _ < _root_.GD.N0232.N0720.N1254.d002512 alpha beta :=
      _root_.GD.N0232.N0720.N1254.d002530 halpha hbeta hN

theorem d002535
    (alpha beta e : ℝ) (hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0) :
    _root_.GD.N0232.N0720.N1254.d002515 alpha beta e =
      (_root_.GD.N0232.N0720.N1254.d002516 alpha beta e + _root_.GD.N0232.N0720.N1254.d002511 alpha beta) /
        _root_.GD.N0232.N0720.N1254.d002510 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1254.d002515 _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002511
  field_simp [hsum]
  ring



theorem d002536
    (alpha beta e : ℝ) (hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0) :
    _root_.GD.N0232.N0720.N1254.d002517 e =
      (alpha * beta - _root_.GD.N0232.N0720.N1254.d002511 alpha beta * _root_.GD.N0232.N0720.N1254.d002516 alpha beta e -
          _root_.GD.N0232.N0720.N1254.d002516 alpha beta e ^ 2) /
        (2 * _root_.GD.N0232.N0720.N1254.d002510 alpha beta ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1254.d002517 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002511 _root_.GD.N0232.N0720.N1254.d002510 at *
  field_simp [hsum]
  ring




def d002537 (alpha beta e : ℝ) : ℝ := _root_.GD.N0232.N0720.N1254.d002515 alpha beta e


def d002538 (alpha beta e : ℝ) : ℝ :=
  1 - _root_.GD.N0232.N0720.N1254.d002513 alpha beta * _root_.GD.N0232.N0720.N1254.d002515 alpha beta e *
    _root_.GD.N0232.N0720.N1254.d002516 alpha beta e / _root_.GD.N0232.N0720.N1254.d002512 alpha beta


def d002539 (alpha beta e : ℝ) : ℝ :=
  -2 * _root_.GD.N0232.N0720.N1254.d002513 alpha beta * _root_.GD.N0232.N0720.N1254.d002516 alpha beta e /
      _root_.GD.N0232.N0720.N1254.d002512 alpha beta +
    _root_.GD.N0232.N0720.N1254.d002513 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) *
      _root_.GD.N0232.N0720.N1254.d002515 alpha beta e * _root_.GD.N0232.N0720.N1254.d002516 alpha beta e ^ 2 /
        _root_.GD.N0232.N0720.N1254.d002512 alpha beta ^ 2


def d002540 (alpha beta e : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002513 alpha beta * _root_.GD.N0232.N0720.N1254.d002515 alpha beta e * _root_.GD.N0232.N0720.N1254.d002517 e /
    _root_.GD.N0232.N0720.N1254.d002512 alpha beta


def d002541 (alpha beta e : ℝ) : ℝ :=
  3 * _root_.GD.N0232.N0720.N1254.d002513 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) *
      _root_.GD.N0232.N0720.N1254.d002516 alpha beta e ^ 2 / _root_.GD.N0232.N0720.N1254.d002512 alpha beta ^ 2 -
    _root_.GD.N0232.N0720.N1254.d002513 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) *
      (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 2) * _root_.GD.N0232.N0720.N1254.d002515 alpha beta e *
        _root_.GD.N0232.N0720.N1254.d002516 alpha beta e ^ 3 / _root_.GD.N0232.N0720.N1254.d002512 alpha beta ^ 3


def d002542 (alpha beta e : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002513 alpha beta * _root_.GD.N0232.N0720.N1254.d002517 e / _root_.GD.N0232.N0720.N1254.d002512 alpha beta +
    _root_.GD.N0232.N0720.N1254.d002513 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) *
      _root_.GD.N0232.N0720.N1254.d002515 alpha beta e * _root_.GD.N0232.N0720.N1254.d002516 alpha beta e * _root_.GD.N0232.N0720.N1254.d002517 e /
        _root_.GD.N0232.N0720.N1254.d002512 alpha beta ^ 2






def d002543 (nu p delta r d : ℝ) : ℝ :=
  let c := p / nu
  let a := (d + delta) / nu
  let h := (p - delta * d - d ^ 2) / (2 * nu ^ 2)
  let j00 := a
  let j10 := 1 - r * a * d / c
  let j20 := -2 * r * d / c + r * (r + 1) * a * d ^ 2 / c ^ 2
  let j30 := 3 * r * (r + 1) * d ^ 2 / c ^ 2 -
    r * (r + 1) * (r + 2) * a * d ^ 3 / c ^ 3
  let j01 := -r * a * h / c
  let j11 := -r * h / c + r * (r + 1) * a * d * h / c ^ 2
  let v00 := delta * nu * r * (r + 1) / p
  let v10 :=
    (delta ^ 2 * r * (r + 1) - p * (r ^ 2 + r + 1)) /
      (p * (r - 1))
  let v20 := -2 * delta * (r + 1) / (nu * (r - 1))
  let v30 := p / (nu ^ 2 * (r - 1))
  let v01 := 2 * delta * nu ^ 2 * r * (r + 1) / (p * (r - 1))
  let v11 := -2 * nu * (r + 2) / (r - 1)
  v00 * j00 + v10 * j10 + v20 * j20 + v30 * j30 +
    v01 * j01 + v11 * j11



theorem d002544
    {nu p r delta d : ℝ} (hnu : nu ≠ 0) (hp : p ≠ 0)
    (hr : r - 1 ≠ 0) :
    _root_.GD.N0232.N0720.N1254.d002543 nu p delta r d = 1 := by
  unfold _root_.GD.N0232.N0720.N1254.d002543
  field_simp [hnu, hp, hr]
  ring



def d002545 (alpha beta : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002511 alpha beta * _root_.GD.N0232.N0720.N1254.d002510 alpha beta * _root_.GD.N0232.N0720.N1254.d002513 alpha beta *
    (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) / (alpha * beta)

def d002546 (alpha beta : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1254.d002511 alpha beta ^ 2 * _root_.GD.N0232.N0720.N1254.d002513 alpha beta *
      (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) -
    alpha * beta *
      (_root_.GD.N0232.N0720.N1254.d002513 alpha beta ^ 2 + _root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1)) /
    (alpha * beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1))

def d002547 (alpha beta : ℝ) : ℝ :=
  -2 * _root_.GD.N0232.N0720.N1254.d002511 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) /
    (_root_.GD.N0232.N0720.N1254.d002510 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1))

def d002548 (alpha beta : ℝ) : ℝ :=
  alpha * beta /
    (_root_.GD.N0232.N0720.N1254.d002510 alpha beta ^ 2 * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1))

def d002549 (alpha beta : ℝ) : ℝ :=
  2 * _root_.GD.N0232.N0720.N1254.d002511 alpha beta * _root_.GD.N0232.N0720.N1254.d002510 alpha beta ^ 2 *
    _root_.GD.N0232.N0720.N1254.d002513 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 1) /
      (alpha * beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1))

def d002550 (alpha beta : ℝ) : ℝ :=
  -2 * _root_.GD.N0232.N0720.N1254.d002510 alpha beta * (_root_.GD.N0232.N0720.N1254.d002513 alpha beta + 2) /
    (_root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1)


def d002551 (alpha beta e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002545 alpha beta * _root_.GD.N0232.N0720.N1254.d002537 alpha beta e +
    _root_.GD.N0232.N0720.N1254.d002546 alpha beta * _root_.GD.N0232.N0720.N1254.d002538 alpha beta e +
    _root_.GD.N0232.N0720.N1254.d002547 alpha beta * _root_.GD.N0232.N0720.N1254.d002539 alpha beta e +
    _root_.GD.N0232.N0720.N1254.d002548 alpha beta * _root_.GD.N0232.N0720.N1254.d002541 alpha beta e +
    _root_.GD.N0232.N0720.N1254.d002549 alpha beta * _root_.GD.N0232.N0720.N1254.d002540 alpha beta e +
    _root_.GD.N0232.N0720.N1254.d002550 alpha beta * _root_.GD.N0232.N0720.N1254.d002542 alpha beta e





theorem d002552
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (e : ℝ) : _root_.GD.N0232.N0720.N1254.d002551 alpha beta e = 1 := by
  have hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta).ne'
  have hprod : alpha * beta ≠ 0 := mul_ne_zero halpha.ne' hbeta.ne'
  have horder : _root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002524 halpha hbeta).ne'
  have ha := _root_.GD.N0232.N0720.N1254.d002535 alpha beta e hsum
  have hh := _root_.GD.N0232.N0720.N1254.d002536 alpha beta e hsum
  have habstract := _root_.GD.N0232.N0720.N1254.d002544
    (nu := _root_.GD.N0232.N0720.N1254.d002510 alpha beta) (p := alpha * beta)
    (delta := _root_.GD.N0232.N0720.N1254.d002511 alpha beta) (r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta)
    (d := _root_.GD.N0232.N0720.N1254.d002516 alpha beta e) hsum hprod horder
  unfold _root_.GD.N0232.N0720.N1254.d002543 at habstract
  unfold _root_.GD.N0232.N0720.N1254.d002551
  unfold _root_.GD.N0232.N0720.N1254.d002545 _root_.GD.N0232.N0720.N1254.d002546 _root_.GD.N0232.N0720.N1254.d002547 _root_.GD.N0232.N0720.N1254.d002548 _root_.GD.N0232.N0720.N1254.d002549 _root_.GD.N0232.N0720.N1254.d002550
  unfold _root_.GD.N0232.N0720.N1254.d002537 _root_.GD.N0232.N0720.N1254.d002538 _root_.GD.N0232.N0720.N1254.d002539 _root_.GD.N0232.N0720.N1254.d002541 _root_.GD.N0232.N0720.N1254.d002540 _root_.GD.N0232.N0720.N1254.d002542
  rw [ha, hh]
  simpa only [_root_.GD.N0232.N0720.N1254.d002512] using habstract





theorem d002553
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (e commonCarrier : ℝ) :
    _root_.GD.N0232.N0720.N1254.d002545 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002537 alpha beta e) +
      _root_.GD.N0232.N0720.N1254.d002546 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002538 alpha beta e) +
      _root_.GD.N0232.N0720.N1254.d002547 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002539 alpha beta e) +
      _root_.GD.N0232.N0720.N1254.d002548 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002541 alpha beta e) +
      _root_.GD.N0232.N0720.N1254.d002549 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002540 alpha beta e) +
      _root_.GD.N0232.N0720.N1254.d002550 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002542 alpha beta e) =
        commonCarrier := by
  calc
    _root_.GD.N0232.N0720.N1254.d002545 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002537 alpha beta e) +
        _root_.GD.N0232.N0720.N1254.d002546 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002538 alpha beta e) +
        _root_.GD.N0232.N0720.N1254.d002547 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002539 alpha beta e) +
        _root_.GD.N0232.N0720.N1254.d002548 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002541 alpha beta e) +
        _root_.GD.N0232.N0720.N1254.d002549 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002540 alpha beta e) +
        _root_.GD.N0232.N0720.N1254.d002550 alpha beta * (commonCarrier * _root_.GD.N0232.N0720.N1254.d002542 alpha beta e) =
      commonCarrier * _root_.GD.N0232.N0720.N1254.d002551 alpha beta e := by
        unfold _root_.GD.N0232.N0720.N1254.d002551
        ring
    _ = commonCarrier * 1 := by
      rw [_root_.GD.N0232.N0720.N1254.d002552 halpha hbeta e]
    _ = commonCarrier := by ring





theorem d002554
    {gamma : ℝ} (hgamma : 0 < gamma) :
    _root_.GD.N0232.N0720.N1254.d002545 gamma gamma = 0 ∧
      _root_.GD.N0232.N0720.N1254.d002547 gamma gamma = 0 ∧
      _root_.GD.N0232.N0720.N1254.d002549 gamma gamma = 0 ∧
      _root_.GD.N0232.N0720.N1254.d002546 gamma gamma =
        -(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma ^ 2 + _root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) /
          (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma - 1) ∧
      _root_.GD.N0232.N0720.N1254.d002548 gamma gamma =
        1 / (4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma - 1)) ∧
      _root_.GD.N0232.N0720.N1254.d002550 gamma gamma =
        -4 * gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 2) /
          (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma - 1) := by
  have horder : _root_.GD.N0232.N0720.N1254.d002513 gamma gamma - 1 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002524 hgamma hgamma).ne'
  have hgamma0 : gamma ≠ 0 := hgamma.ne'
  constructor
  · simp [_root_.GD.N0232.N0720.N1254.d002545, _root_.GD.N0232.N0720.N1254.d002511]
  constructor
  · simp [_root_.GD.N0232.N0720.N1254.d002547, _root_.GD.N0232.N0720.N1254.d002511]
  constructor
  · simp [_root_.GD.N0232.N0720.N1254.d002549, _root_.GD.N0232.N0720.N1254.d002511]
  constructor
  · unfold _root_.GD.N0232.N0720.N1254.d002546 _root_.GD.N0232.N0720.N1254.d002511
    field_simp [hgamma0, horder]
    ring
  constructor
  · unfold _root_.GD.N0232.N0720.N1254.d002548 _root_.GD.N0232.N0720.N1254.d002510
    field_simp [hgamma0, horder]
    ring
  · unfold _root_.GD.N0232.N0720.N1254.d002550 _root_.GD.N0232.N0720.N1254.d002510
    field_simp [horder]
    ring

def d002555
    (gamma v0 v1 v2 vt e : ℝ) : ℝ :=
  v0 * _root_.GD.N0232.N0720.N1254.d002537 gamma gamma e + v1 * _root_.GD.N0232.N0720.N1254.d002538 gamma gamma e +
    v2 * _root_.GD.N0232.N0720.N1254.d002539 gamma gamma e + vt * _root_.GD.N0232.N0720.N1254.d002540 gamma gamma e

theorem d002556
    {gamma v0 v1 v2 vt : ℝ} (hgamma : 0 < gamma) :
    _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt (1 / 2) = v1 := by
  have hgamma0 : gamma ≠ 0 := hgamma.ne'
  unfold _root_.GD.N0232.N0720.N1254.d002555 _root_.GD.N0232.N0720.N1254.d002537 _root_.GD.N0232.N0720.N1254.d002538 _root_.GD.N0232.N0720.N1254.d002539 _root_.GD.N0232.N0720.N1254.d002540
  unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002515 _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517
  unfold _root_.GD.N0232.N0720.N1254.d002510
  field_simp [hgamma0]
  ring


theorem d002557
    {gamma v0 v1 v2 vt : ℝ} (hgamma : 0 < gamma) :
    _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt 0 +
        _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt 1 =
      2 * v1 * (1 - _root_.GD.N0232.N0720.N1254.d002513 gamma gamma) := by
  have hgamma0 : gamma ≠ 0 := hgamma.ne'
  unfold _root_.GD.N0232.N0720.N1254.d002555 _root_.GD.N0232.N0720.N1254.d002537 _root_.GD.N0232.N0720.N1254.d002538 _root_.GD.N0232.N0720.N1254.d002539 _root_.GD.N0232.N0720.N1254.d002540
  unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002515 _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517
  unfold _root_.GD.N0232.N0720.N1254.d002510
  field_simp [hgamma0]
  ring





theorem d002558
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ¬ ∃ v0 v1 v2 vt : ℝ, ∀ e : ℝ,
      _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt e = 1 := by
  rintro ⟨v0, v1, v2, vt, hall⟩
  have hv1 : v1 = 1 := by
    have hmid := hall (1 / 2)
    rw [_root_.GD.N0232.N0720.N1254.d002556 (gamma := gamma) (v0 := v0)
      (v1 := v1) (v2 := v2) (vt := vt) hgamma] at hmid
    exact hmid
  have hone := hall 1
  have hsum :
      _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt 0 +
          _root_.GD.N0232.N0720.N1254.d002555 gamma v0 v1 v2 vt 1 = 2 := by
    rw [hall 0, hone]
    ring
  rw [_root_.GD.N0232.N0720.N1254.d002557 hgamma, hv1] at hsum
  have horder : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    linarith
  nlinarith






structure d002559 where
  minusTwoEta : ℝ
  minusEta : ℝ
  zeroEta : ℝ
  plusEta : ℝ
  plusTwoEta : ℝ
  minusTwoEtaLevel : ℝ
  zeroTwoEtaLevel : ℝ
  plusTwoEtaLevel : ℝ

def d002560 (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ := g.zeroEta

def d002561 (h : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  (g.plusEta - g.minusEta) / (2 * h)

def d002562 (h : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  (g.plusEta - 2 * g.zeroEta + g.minusEta) / h ^ 2

def d002563 (h : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  (g.plusTwoEta - 2 * g.plusEta + 2 * g.minusEta - g.minusTwoEta) /
    (2 * h ^ 3)

def d002564 (eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  (g.zeroTwoEtaLevel - g.zeroEta) / eta

def d002565 (h eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  ((g.plusTwoEtaLevel - g.minusTwoEtaLevel) -
      (g.plusEta - g.minusEta)) / (2 * h * eta)



def d002566
    (alpha beta h eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : ℝ :=
  -(_root_.GD.N0232.N0720.N1254.d002545 alpha beta * _root_.GD.N0232.N0720.N1254.d002560 g +
    _root_.GD.N0232.N0720.N1254.d002546 alpha beta * _root_.GD.N0232.N0720.N1254.d002561 h g +
    _root_.GD.N0232.N0720.N1254.d002547 alpha beta * _root_.GD.N0232.N0720.N1254.d002562 h g +
    _root_.GD.N0232.N0720.N1254.d002548 alpha beta * _root_.GD.N0232.N0720.N1254.d002563 h g +
    _root_.GD.N0232.N0720.N1254.d002549 alpha beta * _root_.GD.N0232.N0720.N1254.d002564 eta g +
    _root_.GD.N0232.N0720.N1254.d002550 alpha beta * _root_.GD.N0232.N0720.N1254.d002565 h eta g)


def d002567 (alpha beta h : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002548 alpha beta / (2 * h ^ 3)

def d002568 (alpha beta h eta : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002546 alpha beta / (2 * h) - _root_.GD.N0232.N0720.N1254.d002547 alpha beta / h ^ 2 -
    _root_.GD.N0232.N0720.N1254.d002548 alpha beta / h ^ 3 - _root_.GD.N0232.N0720.N1254.d002550 alpha beta / (2 * h * eta)

def d002569 (alpha beta h eta : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002545 alpha beta + 2 * _root_.GD.N0232.N0720.N1254.d002547 alpha beta / h ^ 2 +
    _root_.GD.N0232.N0720.N1254.d002549 alpha beta / eta

def d002570 (alpha beta h eta : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002546 alpha beta / (2 * h) - _root_.GD.N0232.N0720.N1254.d002547 alpha beta / h ^ 2 +
    _root_.GD.N0232.N0720.N1254.d002548 alpha beta / h ^ 3 + _root_.GD.N0232.N0720.N1254.d002550 alpha beta / (2 * h * eta)

def d002571 (alpha beta h : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002548 alpha beta / (2 * h ^ 3)

def d002572 (alpha beta h eta : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002550 alpha beta / (2 * h * eta)

def d002573 (alpha beta eta : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002549 alpha beta / eta

def d002574 (alpha beta h eta : ℝ) : ℝ :=
  -_root_.GD.N0232.N0720.N1254.d002550 alpha beta / (2 * h * eta)



theorem d002575
    (alpha beta h eta : ℝ) (hh : h ≠ 0) (heta : eta ≠ 0)
    (g : _root_.GD.N0232.N0720.N1254.d002559) :
    _root_.GD.N0232.N0720.N1254.d002566 alpha beta h eta g =
      _root_.GD.N0232.N0720.N1254.d002567 alpha beta h * g.minusTwoEta +
      _root_.GD.N0232.N0720.N1254.d002568 alpha beta h eta * g.minusEta +
      _root_.GD.N0232.N0720.N1254.d002569 alpha beta h eta * g.zeroEta +
      _root_.GD.N0232.N0720.N1254.d002570 alpha beta h eta * g.plusEta +
      _root_.GD.N0232.N0720.N1254.d002571 alpha beta h * g.plusTwoEta +
      _root_.GD.N0232.N0720.N1254.d002572 alpha beta h eta * g.minusTwoEtaLevel +
      _root_.GD.N0232.N0720.N1254.d002573 alpha beta eta * g.zeroTwoEtaLevel +
      _root_.GD.N0232.N0720.N1254.d002574 alpha beta h eta * g.plusTwoEtaLevel := by
  unfold _root_.GD.N0232.N0720.N1254.d002566
  unfold _root_.GD.N0232.N0720.N1254.d002560 _root_.GD.N0232.N0720.N1254.d002561 _root_.GD.N0232.N0720.N1254.d002562 _root_.GD.N0232.N0720.N1254.d002563 _root_.GD.N0232.N0720.N1254.d002564 _root_.GD.N0232.N0720.N1254.d002565
  unfold _root_.GD.N0232.N0720.N1254.d002567 _root_.GD.N0232.N0720.N1254.d002568 _root_.GD.N0232.N0720.N1254.d002569 _root_.GD.N0232.N0720.N1254.d002570
  unfold _root_.GD.N0232.N0720.N1254.d002571 _root_.GD.N0232.N0720.N1254.d002572 _root_.GD.N0232.N0720.N1254.d002573
  unfold _root_.GD.N0232.N0720.N1254.d002574
  field_simp [hh, heta]
  ring



def d002576 (ell f : ℝ) : Prop :=
  0 < ell ∧ ell < 1 ∧ 0 < f



theorem d002577
    {alpha beta h eta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hh : 0 < h) (heta : 0 < eta)
    (hwidth : 2 * h <
      min (_root_.GD.N0232.N0720.N1254.d002514 alpha beta) (1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta)) :
    _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - 2 * h) eta ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - h) eta ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta) eta ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + h) eta ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + 2 * h) eta ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - h) (2 * eta) ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta) (2 * eta) ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + h) (2 * eta) := by
  have hcenter := _root_.GD.N0232.N0720.N1254.d002525 halpha hbeta
  have hleft : 2 * h < _root_.GD.N0232.N0720.N1254.d002514 alpha beta :=
    hwidth.trans_le (min_le_left _ _)
  have hright : 2 * h < 1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta :=
    hwidth.trans_le (min_le_right _ _)
  unfold _root_.GD.N0232.N0720.N1254.d002576
  constructor
  · exact ⟨by nlinarith, by nlinarith, heta⟩
  constructor
  · exact ⟨by nlinarith, by nlinarith, heta⟩
  constructor
  · exact ⟨hcenter.1, hcenter.2, heta⟩
  constructor
  · exact ⟨by nlinarith, by nlinarith, heta⟩
  constructor
  · exact ⟨by nlinarith, by nlinarith, heta⟩
  constructor
  · exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  constructor
  · exact ⟨hcenter.1, hcenter.2, by positivity⟩
  · exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem d002578
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    min (_root_.GD.N0232.N0720.N1254.d002514 alpha beta) (1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta) =
      _root_.GD.N0232.N0720.N1254.d002518 alpha beta := by
  have hsum := _root_.GD.N0232.N0720.N1254.d002522 halpha hbeta
  rcases le_total alpha beta with hab | hba
  · have hcenter :
        _root_.GD.N0232.N0720.N1254.d002514 alpha beta ≤ 1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta := by
      unfold _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002510
      field_simp
      nlinarith
    rw [min_eq_left hcenter]
    unfold _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002518
    rw [min_eq_left hab]
  · have hcenter :
        1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta ≤ _root_.GD.N0232.N0720.N1254.d002514 alpha beta := by
      unfold _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002510
      field_simp
      nlinarith
    rw [min_eq_right hcenter]
    unfold _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002518
    rw [min_eq_right hba]
    unfold _root_.GD.N0232.N0720.N1254.d002510
    have hne : alpha + beta ≠ 0 := by nlinarith
    field_simp [hne]
    ring



theorem d002579
    {alpha beta : ℝ} {N : ℕ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hN : 0 < N) :
    _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - 2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta)
        (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + 2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta - _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta)
        (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N) ∧
      _root_.GD.N0232.N0720.N1254.d002576
        (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
        (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N) := by
  apply _root_.GD.N0232.N0720.N1254.d002577 halpha hbeta
    (_root_.GD.N0232.N0720.N1254.d002528 halpha hbeta hN)
    (_root_.GD.N0232.N0720.N1254.d002529 halpha hbeta hN)
  rw [_root_.GD.N0232.N0720.N1254.d002578 halpha hbeta]
  have hlam := _root_.GD.N0232.N0720.N1254.d002526 halpha hbeta
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 16 * (N : ℝ) := mul_pos (by norm_num) hNreal
  unfold _root_.GD.N0232.N0720.N1254.d002519
  calc
    2 * (_root_.GD.N0232.N0720.N1254.d002518 alpha beta / (16 * (N : ℝ))) =
        (2 * _root_.GD.N0232.N0720.N1254.d002518 alpha beta) / (16 * (N : ℝ)) := by ring
    _ < _root_.GD.N0232.N0720.N1254.d002518 alpha beta := by
      rw [div_lt_iff₀ hden]
      have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith





theorem d002580
    {alpha beta e : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (d00 d10 d20 d30 d01 d11 : ℕ → ℝ)
    (h00 : Filter.Tendsto d00 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002537 alpha beta e)))
    (h10 : Filter.Tendsto d10 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002538 alpha beta e)))
    (h20 : Filter.Tendsto d20 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002539 alpha beta e)))
    (h30 : Filter.Tendsto d30 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002541 alpha beta e)))
    (h01 : Filter.Tendsto d01 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002540 alpha beta e)))
    (h11 : Filter.Tendsto d11 Filter.atTop (nhds (_root_.GD.N0232.N0720.N1254.d002542 alpha beta e))) :
    Filter.Tendsto
      (fun n => -(_root_.GD.N0232.N0720.N1254.d002545 alpha beta * d00 n +
        _root_.GD.N0232.N0720.N1254.d002546 alpha beta * d10 n +
        _root_.GD.N0232.N0720.N1254.d002547 alpha beta * d20 n +
        _root_.GD.N0232.N0720.N1254.d002548 alpha beta * d30 n +
        _root_.GD.N0232.N0720.N1254.d002549 alpha beta * d01 n +
        _root_.GD.N0232.N0720.N1254.d002550 alpha beta * d11 n))
      Filter.atTop (nhds (-1)) := by
  have hcomb := (((((h00.const_mul (_root_.GD.N0232.N0720.N1254.d002545 alpha beta)).add
    (h10.const_mul (_root_.GD.N0232.N0720.N1254.d002546 alpha beta))).add
    (h20.const_mul (_root_.GD.N0232.N0720.N1254.d002547 alpha beta))).add
    (h30.const_mul (_root_.GD.N0232.N0720.N1254.d002548 alpha beta))).add
    (h01.const_mul (_root_.GD.N0232.N0720.N1254.d002549 alpha beta))).add
    (h11.const_mul (_root_.GD.N0232.N0720.N1254.d002550 alpha beta))
  have hneg := hcomb.neg
  have hid :
      _root_.GD.N0232.N0720.N1254.d002545 alpha beta * _root_.GD.N0232.N0720.N1254.d002537 alpha beta e +
        _root_.GD.N0232.N0720.N1254.d002546 alpha beta * _root_.GD.N0232.N0720.N1254.d002538 alpha beta e +
        _root_.GD.N0232.N0720.N1254.d002547 alpha beta * _root_.GD.N0232.N0720.N1254.d002539 alpha beta e +
        _root_.GD.N0232.N0720.N1254.d002548 alpha beta * _root_.GD.N0232.N0720.N1254.d002541 alpha beta e +
        _root_.GD.N0232.N0720.N1254.d002549 alpha beta * _root_.GD.N0232.N0720.N1254.d002540 alpha beta e +
        _root_.GD.N0232.N0720.N1254.d002550 alpha beta * _root_.GD.N0232.N0720.N1254.d002542 alpha beta e = 1 := by
    simpa only [_root_.GD.N0232.N0720.N1254.d002551] using
      _root_.GD.N0232.N0720.N1254.d002552 halpha hbeta e
  simpa only [hid] using hneg




theorem d002581
    {E : Type*} (domain : Set E) (target : E → ℝ)
    (action : ℕ → E → ℝ) {floor : ℝ} (hfloor : 0 < floor)
    (htarget : ∀ x ∈ domain, floor ≤ target x)
    (huniform : ∀ epsilon > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ domain,
      |action n x + target x| ≤ epsilon) :
    ∃ N, ∀ n ≥ N, ∀ x ∈ domain, action n x ≤ -(floor / 2) := by
  obtain ⟨N, hN⟩ := huniform (floor / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have habs := hN n hn x hx
  have hupp : action n x + target x ≤ floor / 2 :=
    (le_abs_self _).trans habs
  nlinarith [htarget x hx]




theorem d002582
    {E : Type*} (domain : Set E) (atomic smeared : E → ℝ)
    {margin : ℝ} (_hmargin : 0 < margin)
    (hatomic : ∀ x ∈ domain, atomic x ≤ -margin)
    (hsmear : ∀ x ∈ domain, |smeared x - atomic x| ≤ margin / 2) :
    ∀ x ∈ domain, smeared x ≤ -(margin / 2) := by
  intro x hx
  have hdiff : smeared x - atomic x ≤ margin / 2 :=
    (le_abs_self _).trans (hsmear x hx)
  nlinarith [hatomic x hx]



theorem d002583 (alpha beta e : ℝ)
    (hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0) :
    _root_.GD.N0232.N0720.N1254.d002510 beta alpha = _root_.GD.N0232.N0720.N1254.d002510 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002511 beta alpha = -_root_.GD.N0232.N0720.N1254.d002511 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002512 beta alpha = _root_.GD.N0232.N0720.N1254.d002512 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002513 beta alpha = _root_.GD.N0232.N0720.N1254.d002513 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002515 beta alpha (1 - e) = -_root_.GD.N0232.N0720.N1254.d002515 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002516 beta alpha (1 - e) = -_root_.GD.N0232.N0720.N1254.d002516 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002517 (1 - e) = _root_.GD.N0232.N0720.N1254.d002517 e := by
  unfold _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002515 _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517
  unfold _root_.GD.N0232.N0720.N1254.d002510 _root_.GD.N0232.N0720.N1254.d002511 at *
  constructor
  · ring
  constructor
  · ring
  constructor
  · field_simp [hsum, add_comm]
    ring
  constructor
  · ring
  constructor
  · field_simp [hsum, add_comm]
    ring
  constructor <;> ring


theorem d002584
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1254.d002545 beta alpha = -_root_.GD.N0232.N0720.N1254.d002545 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002546 beta alpha = _root_.GD.N0232.N0720.N1254.d002546 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002547 beta alpha = -_root_.GD.N0232.N0720.N1254.d002547 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002548 beta alpha = _root_.GD.N0232.N0720.N1254.d002548 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002549 beta alpha = -_root_.GD.N0232.N0720.N1254.d002549 alpha beta
      ∧ _root_.GD.N0232.N0720.N1254.d002550 beta alpha = _root_.GD.N0232.N0720.N1254.d002550 alpha beta := by
  have hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta).ne'
  have hprod : alpha * beta ≠ 0 := mul_ne_zero halpha.ne' hbeta.ne'
  have horder : _root_.GD.N0232.N0720.N1254.d002513 alpha beta - 1 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002524 halpha hbeta).ne'
  have htwo : 1 + 2 * alpha + 2 * beta ≠ 0 := by
    nlinarith
  unfold _root_.GD.N0232.N0720.N1254.d002545 _root_.GD.N0232.N0720.N1254.d002546 _root_.GD.N0232.N0720.N1254.d002547 _root_.GD.N0232.N0720.N1254.d002548 _root_.GD.N0232.N0720.N1254.d002549 _root_.GD.N0232.N0720.N1254.d002550
  unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510 _root_.GD.N0232.N0720.N1254.d002511 at *
  constructor
  · field_simp [hprod]
    ring
  constructor
  · field_simp [hprod, horder, htwo]
    ring
  constructor
  · field_simp [hsum, horder, htwo]
    ring
  constructor
  · field_simp [hsum, horder, htwo]
    ring
  constructor
  · field_simp [hprod, horder, htwo]
    ring
  · field_simp [horder, htwo]
    ring


theorem d002585
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (e : ℝ) :
    _root_.GD.N0232.N0720.N1254.d002537 beta alpha (1 - e) = -_root_.GD.N0232.N0720.N1254.d002537 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002538 beta alpha (1 - e) = _root_.GD.N0232.N0720.N1254.d002538 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002539 beta alpha (1 - e) = -_root_.GD.N0232.N0720.N1254.d002539 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002541 beta alpha (1 - e) = _root_.GD.N0232.N0720.N1254.d002541 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002540 beta alpha (1 - e) = -_root_.GD.N0232.N0720.N1254.d002540 alpha beta e
      ∧ _root_.GD.N0232.N0720.N1254.d002542 beta alpha (1 - e) = _root_.GD.N0232.N0720.N1254.d002542 alpha beta e := by
  have hsum : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002522 halpha hbeta).ne'
  have hscale : _root_.GD.N0232.N0720.N1254.d002512 alpha beta ≠ 0 :=
    (_root_.GD.N0232.N0720.N1254.d002523 halpha hbeta).ne'
  unfold _root_.GD.N0232.N0720.N1254.d002537 _root_.GD.N0232.N0720.N1254.d002538 _root_.GD.N0232.N0720.N1254.d002539 _root_.GD.N0232.N0720.N1254.d002541 _root_.GD.N0232.N0720.N1254.d002540 _root_.GD.N0232.N0720.N1254.d002542
  unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002515 _root_.GD.N0232.N0720.N1254.d002514 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517
  unfold _root_.GD.N0232.N0720.N1254.d002510 at *
  constructor
  · field_simp [hsum]
    ring
  constructor
  · field_simp [hsum, hscale]
    ring
  constructor
  · field_simp [hsum, hscale]
    ring
  constructor
  · field_simp [hsum, hscale]
    ring
  constructor
  · field_simp [hsum, hscale]
    ring
  · field_simp [hsum, hscale]
    ring

theorem d002586
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (e : ℝ) :
    _root_.GD.N0232.N0720.N1254.d002551 beta alpha (1 - e) =
      _root_.GD.N0232.N0720.N1254.d002551 alpha beta e := by
  rcases _root_.GD.N0232.N0720.N1254.d002584 halpha hbeta with
    ⟨hv00, hv10, hv20, hv30, hv01, hv11⟩
  rcases _root_.GD.N0232.N0720.N1254.d002585 halpha hbeta e with
    ⟨hj00, hj10, hj20, hj30, hj01, hj11⟩
  unfold _root_.GD.N0232.N0720.N1254.d002551
  rw [hv00, hv10, hv20, hv30, hv01, hv11,
    hj00, hj10, hj20, hj30, hj01, hj11]
  ring




def d002587 (g : _root_.GD.N0232.N0720.N1254.d002559) : _root_.GD.N0232.N0720.N1254.d002559 where
  minusTwoEta := -g.plusTwoEta
  minusEta := -g.plusEta
  zeroEta := -g.zeroEta
  plusEta := -g.minusEta
  plusTwoEta := -g.minusTwoEta
  minusTwoEtaLevel := -g.plusTwoEtaLevel
  zeroTwoEtaLevel := -g.zeroTwoEtaLevel
  plusTwoEtaLevel := -g.minusTwoEtaLevel

theorem d002588 (h eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) :
    _root_.GD.N0232.N0720.N1254.d002560 (_root_.GD.N0232.N0720.N1254.d002587 g) = -_root_.GD.N0232.N0720.N1254.d002560 g
      ∧ _root_.GD.N0232.N0720.N1254.d002561 h (_root_.GD.N0232.N0720.N1254.d002587 g) = _root_.GD.N0232.N0720.N1254.d002561 h g
      ∧ _root_.GD.N0232.N0720.N1254.d002562 h (_root_.GD.N0232.N0720.N1254.d002587 g) = -_root_.GD.N0232.N0720.N1254.d002562 h g
      ∧ _root_.GD.N0232.N0720.N1254.d002563 h (_root_.GD.N0232.N0720.N1254.d002587 g) = _root_.GD.N0232.N0720.N1254.d002563 h g
      ∧ _root_.GD.N0232.N0720.N1254.d002564 eta (_root_.GD.N0232.N0720.N1254.d002587 g) = -_root_.GD.N0232.N0720.N1254.d002564 eta g
      ∧ _root_.GD.N0232.N0720.N1254.d002565 h eta (_root_.GD.N0232.N0720.N1254.d002587 g) = _root_.GD.N0232.N0720.N1254.d002565 h eta g := by
  unfold _root_.GD.N0232.N0720.N1254.d002560 _root_.GD.N0232.N0720.N1254.d002561 _root_.GD.N0232.N0720.N1254.d002562 _root_.GD.N0232.N0720.N1254.d002563 _root_.GD.N0232.N0720.N1254.d002564 _root_.GD.N0232.N0720.N1254.d002565
  unfold _root_.GD.N0232.N0720.N1254.d002587
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring


theorem d002589
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (h eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) :
    _root_.GD.N0232.N0720.N1254.d002566 beta alpha h eta (_root_.GD.N0232.N0720.N1254.d002587 g) =
      _root_.GD.N0232.N0720.N1254.d002566 alpha beta h eta g := by
  rcases _root_.GD.N0232.N0720.N1254.d002584 halpha hbeta with
    ⟨hv00, hv10, hv20, hv30, hv01, hv11⟩
  rcases _root_.GD.N0232.N0720.N1254.d002588 h eta g with
    ⟨hd00, hd10, hd20, hd30, hd01, hd11⟩
  unfold _root_.GD.N0232.N0720.N1254.d002566
  rw [hv00, hv10, hv20, hv30, hv01, hv11,
    hd00, hd10, hd20, hd30, hd01, hd11]
  ring





theorem d002590
    {trace energy margin ceiling : ℝ}
    (htrace : trace ≤ -margin) (henergy : energy ≤ ceiling)
    (hmargin : 0 < margin) (hceiling : 0 < ceiling) :
    let step := margin / ceiling
    0 < step ∧ 2 * step * trace + step ^ 2 * energy < 0 := by
  dsimp only
  have hstep : 0 < margin / ceiling := div_pos hmargin hceiling
  constructor
  · exact hstep
  have hlinear :
      2 * (margin / ceiling) * trace ≤
        2 * (margin / ceiling) * (-margin) :=
    mul_le_mul_of_nonneg_left htrace (by positivity)
  have hquadratic :
      (margin / ceiling) ^ 2 * energy ≤
        (margin / ceiling) ^ 2 * ceiling :=
    mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
  calc
    2 * (margin / ceiling) * trace +
        (margin / ceiling) ^ 2 * energy ≤
      2 * (margin / ceiling) * (-margin) +
        (margin / ceiling) ^ 2 * ceiling :=
      add_le_add hlinear hquadratic
    _ = -(margin ^ 2 / ceiling) := by
      field_simp [hceiling.ne']
      ring
    _ < 0 := neg_lt_zero.mpr (div_pos (sq_pos_of_pos hmargin) hceiling)





theorem d002591 (alpha k : ℝ) :
    -1 < alpha - 1 - 2 * k ↔ 2 * k < alpha := by
  constructor <;> intro h <;> linarith

theorem d002592
    {alpha k : ℝ} (hwall : alpha ≤ 2 * k) :
    alpha - 1 - 2 * k ≤ -1 := by
  linarith

end

end GD.N0232.N0720.N1254

#print axioms _root_.GD.N0232.N0720.N1254.d002552
#print axioms _root_.GD.N0232.N0720.N1254.d002554
#print axioms _root_.GD.N0232.N0720.N1254.d002558
#print axioms _root_.GD.N0232.N0720.N1254.d002575
#print axioms _root_.GD.N0232.N0720.N1254.d002534
#print axioms _root_.GD.N0232.N0720.N1254.d002579
#print axioms _root_.GD.N0232.N0720.N1254.d002589
#print axioms _root_.GD.N0232.N0720.N1254.d002590
