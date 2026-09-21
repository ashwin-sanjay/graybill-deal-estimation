import GD.Module0650
import GD.Module0651
import GD.Module0662
import GD.Module0697












































open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0950

noncomputable section










def d010582
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0853.d009592 hk triangle

theorem d010583
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    0 < _root_.GD.N0232.N0719.N0950.d010582 hk triangle :=
  _root_.GD.N0232.N0719.N0853.d009593 hk triangle

theorem d010584
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    _root_.GD.N0232.N0719.N0950.d010582 hk triangle ≤
      ∫ u,
        _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w
          ∂_root_.GD.N0232.N0719.N0856.d009559 k :=
  by
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0856.d009559 k) :=
      _root_.GD.N0232.N0719.N0856.d009560 k
    have hconst :
        Integrable
          (fun _ : _root_.GD.N0232.N0719.N0857.d009377 k =>
            _root_.GD.N0232.N0719.N0950.d010582 hk triangle)
          (_root_.GD.N0232.N0719.N0856.d009559 k) :=
      integrable_const _
    have hpair :=
      _root_.GD.N0232.N0719.N0856.d009562
        hk triangle w
    have hpoint :
        ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k,
          _root_.GD.N0232.N0719.N0950.d010582 hk triangle ≤
            _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
      filter_upwards [_root_.GD.N0232.N0719.N0856.d009561 k] with u hu
      exact _root_.GD.N0232.N0719.N0853.d009594 hk triangle hu hw
    have hmono :=
      integral_mono_ae hconst hpair hpoint
    simpa using hmono



def d010585 (k : ℕ) : ℝ :=
  _root_.GD.N0232.N0719.N0857.d009401 k * (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal

theorem d010586
    {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0950.d010585 k := by
  unfold _root_.GD.N0232.N0719.N0950.d010585
  apply mul_pos (_root_.GD.N0232.N0719.N0857.d009402 hk)
  exact ENNReal.toReal_pos
    (_root_.GD.N0232.N0719.N0857.d009403 (k := k)).ne'
    (_root_.GD.N0232.N0719.N0857.d009404 (k := k))


def d010587 (k : ℕ) : ℝ :=
  9 / (4 * (k : ℝ))


def d010588 (k : ℕ) : ℝ :=
  15 / (4 * (k : ℝ))

theorem d010589
    {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0950.d010587 k := by
  unfold _root_.GD.N0232.N0719.N0950.d010587
  positivity

theorem d010590
    {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0950.d010588 k := by
  unfold _root_.GD.N0232.N0719.N0950.d010588
  positivity






def d010591
    {k : ℕ} (shape : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  1 /
    (1 + 5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
      (4 * (k : ℝ) * shape (triangle 0)))

theorem d010592
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (triangle : Fin 3 ↪ Fin k) :
    0 < _root_.GD.N0232.N0719.N0950.d010591 shape triangle := by
  unfold _root_.GD.N0232.N0719.N0950.d010591
  apply one_div_pos.mpr
  have hA := _root_.GD.N0232.N0719.N0954.d009504 hk hshape
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < 4 * (k : ℝ) * shape (triangle 0) :=
    mul_pos (mul_pos (by norm_num) hkR) (hshape (triangle 0))
  have hquot : 0 <
      5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
        (4 * (k : ℝ) * shape (triangle 0)) :=
    div_pos (mul_pos (by norm_num) hA) hden
  linarith












def d010593
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  (3 / 128) *
    _root_.GD.N0232.N0719.N0950.d010591 shape triangle *
    _root_.GD.N0232.N0719.N0950.d010587 k ^ 3 *
    _root_.GD.N0232.N0719.N0950.d010585 k *
    _root_.GD.N0232.N0719.N0950.d010582 hk triangle *
    _root_.GD.N0232.N0719.N0954.d009517 shape

theorem d010594
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (triangle : Fin 3 ↪ Fin k) :
    0 < _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle := by
  unfold _root_.GD.N0232.N0719.N0950.d010593
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (_root_.GD.N0232.N0719.N0950.d010592 hk hshape triangle))
          (pow_pos (_root_.GD.N0232.N0719.N0950.d010589 hk) 3))
        (_root_.GD.N0232.N0719.N0950.d010586 hk))
      (_root_.GD.N0232.N0719.N0950.d010583 hk triangle))
    (_root_.GD.N0232.N0719.N0954.d009519 hk hshape)










def d010595
    {k : ℕ} (shape : Fin k → ℝ) : ℝ :=
  250000 * _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 *
    _root_.GD.N0232.N0719.N0954.d009518 shape

theorem d010596
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) :
    0 < _root_.GD.N0232.N0719.N0950.d010595 shape := by
  unfold _root_.GD.N0232.N0719.N0950.d010595
  exact mul_pos
    (mul_pos (by norm_num)
      (sq_pos_of_pos (_root_.GD.N0232.N0719.N0950.d010590 hk)))
    (_root_.GD.N0232.N0719.N0954.d009520 hk hshape)


def d010597
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0950.d010595 shape /
    _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle

theorem d010598
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (triangle : Fin 3 ↪ Fin k) :
    0 < _root_.GD.N0232.N0719.N0950.d010597 hk shape triangle :=
  div_pos
    (_root_.GD.N0232.N0719.N0950.d010596 hk hshape)
    (_root_.GD.N0232.N0719.N0950.d010594 hk hshape triangle)









theorem d010599
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (triangle : Fin 3 ↪ Fin k)
    {prefactor V B gain : ℝ}
    (hprefactor : 0 < prefactor)
    (hV : 0 < V)
    (henergy :
      B ≤ prefactor * V *
        _root_.GD.N0232.N0719.N0950.d010595 shape)
    (hgain :
      prefactor * V *
          _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle ≤ gain) :
    B ≤
      _root_.GD.N0232.N0719.N0950.d010597 hk shape triangle * gain := by
  let E := _root_.GD.N0232.N0719.N0950.d010595 shape
  let G := _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle
  have hG : 0 < G :=
    _root_.GD.N0232.N0719.N0950.d010594 hk hshape triangle
  have hPV : 0 < prefactor * V := mul_pos hprefactor hV
  have hratio :
      prefactor * V * E =
        (E / G) * (prefactor * V * G) := by
    field_simp [hG.ne']
  calc
    B ≤ prefactor * V * E := henergy
    _ =
        (E / G) * (prefactor * V * G) := hratio
    _ ≤ (E / G) * gain :=
      mul_le_mul_of_nonneg_left hgain
        (div_nonneg
          (_root_.GD.N0232.N0719.N0950.d010596 hk hshape).le
          hG.le)
    _ =
        _root_.GD.N0232.N0719.N0950.d010597 hk shape triangle * gain := rfl






theorem d010600
    {k : ℕ} (hk : 0 < k)
    {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (triangle : Fin 3 ↪ Fin k)
    {prefactor V B C : ℝ}
    (hprefactor : 0 < prefactor)
    (hV : 0 < V)
    (henergy :
      B ≤ prefactor * V *
        _root_.GD.N0232.N0719.N0950.d010595 shape)
    (hgain :
      prefactor * V *
          _root_.GD.N0232.N0719.N0950.d010593 hk shape triangle ≤ -C) :
    B ≤
      _root_.GD.N0232.N0719.N0950.d010597 hk shape triangle * (-C) :=
  _root_.GD.N0232.N0719.N0950.d010599
    hk hshape triangle hprefactor hV henergy hgain

end

end GD.N0232.N0719.N0950
