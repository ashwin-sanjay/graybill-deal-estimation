import GD.Module0651
import GD.Module0713



















open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0855

noncomputable section


def d010601
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) : ℝ :=
  _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0853.d009567 hk q)



def d010602
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k)
    (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ^ 2 *
    _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w



def d010603
    {k : ℕ} (hk : 0 < k)
    (shape rate : Fin k → ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009510 shape
    (_root_.GD.N0232.N0719.N0954.d009506 rate)
    (_root_.GD.N0232.N0719.N0853.d009567 hk q)



def d010604
    {k : ℕ} (hk : 0 < k)
    (shape rate : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009509 shape rate *
    ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
      _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
        _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w

theorem d010605
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk) :
    _root_.GD.N0232.N0719.N0950.d010587 k ≤
      _root_.GD.N0232.N0719.N0855.d010601 hk triangle q := by
  exact _root_.GD.N0232.N0719.N0951.d003591 hk triangle hq

theorem d010606
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk) :
    _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ≤
      _root_.GD.N0232.N0719.N0950.d010588 k := by
  exact _root_.GD.N0232.N0719.N0951.d003592 hk triangle hq

theorem d010607
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk)
    (w : Fin 3 → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w :=
  _root_.GD.N0232.N0719.N0856.d009544 hk triangle hq w

theorem d010608
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk)
    (w : Fin 3 → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w :=
  mul_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0719.N0855.d010607 hk triangle hq w)

theorem d010609
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk) :
    _root_.GD.N0232.N0719.N0954.d009517 shape ≤
      _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q :=
  _root_.GD.N0232.N0719.N0954.d009521 hk hshape
    (_root_.GD.N0232.N0719.N0954.d009513 hk hrate) hq

theorem d010610
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk) :
    _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q ≤
      _root_.GD.N0232.N0719.N0954.d009518 shape :=
  _root_.GD.N0232.N0719.N0954.d009522
    hk hshape
    (_root_.GD.N0232.N0719.N0954.d009513 hk hrate) hq

def d010611
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Set (_root_.GD.N0232.N0719.N0857.d009377 k) :=
  (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003821 k) '' _root_.GD.N0232.N0719.N0857.d009383 k) ∪
    (_root_.GD.N0232.N0719.N0853.d009572 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) '' _root_.GD.N0232.N0719.N0857.d009383 k)

theorem d010612
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0855.d010611 hk triangle ⊆
      _root_.GD.N0232.N0719.N0853.d009581 hk :=
  union_subset
    (_root_.GD.N0232.N0719.N0853.d009586 hk)
    (_root_.GD.N0232.N0719.N0853.d009587 hk triangle)

theorem d010613
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    MeasurableSet (_root_.GD.N0232.N0719.N0855.d010611 hk triangle) :=
  (_root_.GD.N0232.N0719.N0853.d009580 hk
    (_root_.GD.N0232.N0719.N0854.d003821 k)).union
    (_root_.GD.N0232.N0719.N0853.d009580 hk
      (_root_.GD.N0232.N0719.N0854.d003822 triangle))

theorem d010614
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun q => _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w)
      (_root_.GD.N0232.N0719.N0855.d010611 hk triangle) := by
  rw [_root_.GD.N0232.N0719.N0855.d010611]
  exact IntegrableOn.union
    (_root_.GD.N0232.N0719.N0853.d009598
      hk triangle w)
    (_root_.GD.N0232.N0719.N0853.d009599
      hk triangle w)






theorem d010615
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532)
    (hfull :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    _root_.GD.N0232.N0719.N0954.d009517 shape *
        _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
        _root_.GD.N0232.N0719.N0857.d009401 k *
        (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
          (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal) ≤
      ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
          _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w := by
  let S := _root_.GD.N0232.N0719.N0855.d010611 hk triangle
  let F : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w
  let H : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q =>
      _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
        _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w
  have hF :
      IntegrableOn F S :=
    _root_.GD.N0232.N0719.N0855.d010614 hk triangle w
  have hH :
      IntegrableOn H S :=
    hfull.mono_set
      (_root_.GD.N0232.N0719.N0855.d010612 hk triangle)
  have hpoint :
      ∀ q ∈ S,
        _root_.GD.N0232.N0719.N0954.d009517 shape *
              _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 * F q ≤
          H q := by
    intro q hq
    have hqBal :
        q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk :=
      _root_.GD.N0232.N0719.N0855.d010612 hk triangle hq
    have hL :=
      _root_.GD.N0232.N0719.N0855.d010609 hk hshape hrate hqBal
    have hr :=
      _root_.GD.N0232.N0719.N0855.d010605 hk triangle hqBal
    have hr0 : 0 ≤ _root_.GD.N0232.N0719.N0950.d010587 k :=
      (_root_.GD.N0232.N0719.N0950.d010589 hk).le
    have hF0 :
        0 ≤ F q :=
      _root_.GD.N0232.N0719.N0855.d010607 hk triangle hqBal w
    dsimp [F, H, _root_.GD.N0232.N0719.N0855.d010602]
    have hrsq :
        _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 ≤
          _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ^ 2 :=
      (sq_le_sq₀ hr0
        ((_root_.GD.N0232.N0719.N0950.d010589 hk).le.trans hr)).2 hr
    have hkernel0 :
        0 ≤ _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q :=
      (_root_.GD.N0232.N0719.N0954.d009519 hk hshape).le.trans hL
    have hprod :
        _root_.GD.N0232.N0719.N0954.d009517 shape *
            _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 ≤
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ^ 2 :=
      mul_le_mul hL hrsq (sq_nonneg _) hkernel0
    calc
      _root_.GD.N0232.N0719.N0954.d009517 shape *
              _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 * F q ≤
          (_root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0855.d010601 hk triangle q ^ 2) * F q :=
        mul_le_mul_of_nonneg_right hprod hF0
      _ = H q := by
        simp [H, F, _root_.GD.N0232.N0719.N0855.d010602]
        ring
  have hlocal :
      _root_.GD.N0232.N0719.N0954.d009517 shape *
          _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
          (∫ q in S, F q) ≤
        ∫ q in S, H q := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on
      (hF.const_mul
        (_root_.GD.N0232.N0719.N0954.d009517 shape *
          _root_.GD.N0232.N0719.N0950.d010587 k ^ 2))
      hH (_root_.GD.N0232.N0719.N0855.d010613 hk triangle)
      hpoint
  have hmismatch :
      _root_.GD.N0232.N0719.N0857.d009401 k *
            (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
              (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal) ≤
        ∫ q in S, F q := by
    simpa [S, F, _root_.GD.N0232.N0719.N0855.d010611] using
      _root_.GD.N0232.N0719.N0853.d009600 hk triangle hw
  have hcoef :
      0 ≤ _root_.GD.N0232.N0719.N0954.d009517 shape *
          _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 :=
    mul_nonneg
      (_root_.GD.N0232.N0719.N0954.d009519 hk hshape).le
      (sq_nonneg _)
  have hfromPatch :
      _root_.GD.N0232.N0719.N0954.d009517 shape *
          _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
          (_root_.GD.N0232.N0719.N0857.d009401 k *
            (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
              (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal)) ≤
        ∫ q in S, H q := by
    exact
      (mul_le_mul_of_nonneg_left hmismatch hcoef).trans
        hlocal
  have hnonneg :
      0 ≤ᵐ[volume.restrict
        (_root_.GD.N0232.N0719.N0853.d009581 hk)] H := by
    filter_upwards [
      ae_restrict_mem
        (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet] with q hq
    exact mul_nonneg
      ((_root_.GD.N0232.N0719.N0855.d010609 hk hshape hrate hq).trans'
        (_root_.GD.N0232.N0719.N0954.d009519 hk hshape).le)
      (_root_.GD.N0232.N0719.N0855.d010608 hk triangle hq w)
  have hglobal :
      (∫ q in S, H q) ≤
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk, H q :=
    setIntegral_mono_set hfull hnonneg
      (Filter.Eventually.of_forall
        (_root_.GD.N0232.N0719.N0855.d010612 hk triangle))
  dsimp [S, F, H] at hfromPatch hglobal ⊢
  exact le_trans (by nlinarith) hglobal



theorem d010616
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532)
    (hfull :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        (_root_.GD.N0232.N0719.N0954.d009517 shape *
          _root_.GD.N0232.N0719.N0950.d010587 k ^ 2 *
          _root_.GD.N0232.N0719.N0857.d009401 k *
          (_root_.GD.N0232.N0719.N0853.d009592 hk triangle *
            (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal)) ≤
      _root_.GD.N0232.N0719.N0855.d010604 hk shape rate triangle w := by
  unfold _root_.GD.N0232.N0719.N0855.d010604
  exact mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0719.N0855.d010615
      hk hshape hrate triangle hw hfull)
    (_root_.GD.N0232.N0719.N0954.d009516
      hk hshape hrate).le







theorem d010617
    {k : ℕ} (hk : 0 < k)
    (hk3 : 3 ≤ k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {V : ℝ} (hV : 0 ≤ V)
    (E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ)
    (hE_nonneg :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk, 0 ≤ E q)
    (hE_upper :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk,
        E q ≤
          250000 *
            _root_.GD.N0232.N0719.N0855.d010601 hk
              (Fin.castLEEmb hk3) q ^ 2 * V)
    (hfull :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q)
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q) ≤
      _root_.GD.N0232.N0719.N0954.d009518 shape *
        (250000 *
          _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V) := by
  have hvol :
      volume (_root_.GD.N0232.N0719.N0853.d009581 hk) ≤ 1 :=
    _root_.GD.N0232.N0719.N0853.d009585 hk hk3
  have hvolTop :
      volume (_root_.GD.N0232.N0719.N0853.d009581 hk) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hvol
  have hconst :
      IntegrableOn
        (fun _ : _root_.GD.N0232.N0719.N0857.d009377 k =>
          _root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 *
              _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V))
        (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
    integrableOn_const hvolTop
  have hpoint :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk,
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q ≤
          _root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 *
              _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V) := by
    intro q hq
    have hK :=
      _root_.GD.N0232.N0719.N0855.d010610 hk hshape hrate hq
    have hr :=
      _root_.GD.N0232.N0719.N0855.d010606 hk (Fin.castLEEmb hk3) hq
    have hr0 :
        0 ≤ _root_.GD.N0232.N0719.N0855.d010601 hk
          (Fin.castLEEmb hk3) q :=
      (_root_.GD.N0232.N0719.N0855.d010605 hk
        (Fin.castLEEmb hk3) hq).trans'
        (_root_.GD.N0232.N0719.N0950.d010589 hk).le
    have hceil0 :
        0 ≤ _root_.GD.N0232.N0719.N0950.d010588 k :=
      (_root_.GD.N0232.N0719.N0950.d010590 hk).le
    have hrsq :
        _root_.GD.N0232.N0719.N0855.d010601 hk
              (Fin.castLEEmb hk3) q ^ 2 ≤
          _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 :=
      (sq_le_sq₀ hr0 hceil0).2 hr
    have hE := hE_upper q hq
    have hE0 := hE_nonneg q hq
    have hK0 :
        0 ≤ _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q :=
      (_root_.GD.N0232.N0719.N0954.d009519 hk hshape).le.trans
        (_root_.GD.N0232.N0719.N0855.d010609 hk hshape hrate hq)
    nlinarith [
      mul_le_mul hK hE
        hE0
        (_root_.GD.N0232.N0719.N0954.d009520 hk hshape).le,
      mul_le_mul_of_nonneg_right hrsq hV]
  calc
    (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q) ≤
        ∫ _q : _root_.GD.N0232.N0719.N0857.d009377 k in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 *
              _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V) :=
      setIntegral_mono_on hfull hconst
        (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet hpoint
    _ =
        volume.real (_root_.GD.N0232.N0719.N0853.d009581 hk) *
          (_root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 *
              _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V)) := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
    _ ≤
        _root_.GD.N0232.N0719.N0954.d009518 shape *
          (250000 *
            _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V) := by
      have hvolReal :
          volume.real (_root_.GD.N0232.N0719.N0853.d009581 hk) ≤ 1 := by
        simpa [Measure.real] using ENNReal.toReal_mono
          ENNReal.one_ne_top hvol
      have hconstNonneg :
          0 ≤ _root_.GD.N0232.N0719.N0954.d009518 shape *
            (250000 *
              _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V) := by
        exact mul_nonneg
          (_root_.GD.N0232.N0719.N0954.d009520 hk hshape).le
          (mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg _)) hV)
      calc
        volume.real (_root_.GD.N0232.N0719.N0853.d009581 hk) *
              (_root_.GD.N0232.N0719.N0954.d009518 shape *
                (250000 *
                  _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V)) ≤
            1 *
              (_root_.GD.N0232.N0719.N0954.d009518 shape *
                (250000 *
                  _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V)) :=
          mul_le_mul_of_nonneg_right hvolReal hconstNonneg
        _ = _ := one_mul _


theorem d010618
    {k : ℕ} (hk : 0 < k)
    (hk3 : 3 ≤ k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {V : ℝ} (hV : 0 ≤ V)
    (E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ)
    (hE_nonneg :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk, 0 ≤ E q)
    (hE_upper :
      ∀ q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk,
        E q ≤
          250000 *
            _root_.GD.N0232.N0719.N0855.d010601 hk
              (Fin.castLEEmb hk3) q ^ 2 * V)
    (hfull :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q)
        (_root_.GD.N0232.N0719.N0853.d009581 hk)) :
    _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        (∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q * E q) ≤
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        (_root_.GD.N0232.N0719.N0954.d009518 shape *
          (250000 *
            _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V)) :=
  mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0719.N0855.d010617
      hk hk3 hshape hrate hV E
      hE_nonneg hE_upper hfull)
    (_root_.GD.N0232.N0719.N0954.d009516 hk hshape hrate).le

end

end GD.N0232.N0719.N0855
