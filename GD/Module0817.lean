import GD.Module0760
import GD.Module0217




































namespace GD
namespace N0232
namespace N0720
namespace N1209

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0720.N1437



def d012458 (xbar ybar vx vy : ℝ) : _root_.GD.N0232.N0719.N0900.d009096 2 where
  mean := ![xbar, ybar]
  meanVariance := ![vx, vy]

@[simp] theorem d012459
    (xbar ybar vx vy : ℝ) :
    (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy).mean 0 = xbar := rfl

@[simp] theorem d012460
    (xbar ybar vx vy : ℝ) :
    (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy).mean 1 = ybar := rfl

@[simp] theorem d012461
    (xbar ybar vx vy : ℝ) :
    (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy).meanVariance 0 = vx := rfl

@[simp] theorem d012462
    (xbar ybar vx vy : ℝ) :
    (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy).meanVariance 1 = vy := rfl




def d012463 (r s orientation : ℝ) : _root_.GD.N0232.N0719.N0900.d009096 2 :=
  _root_.GD.N0232.N0720.N1209.d012458 orientation 0 ((1 - r) / s) (r / s)




def d012464
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (r s orientation : ℝ) : ℝ :=
  orientation * d (_root_.GD.N0232.N0720.N1209.d012463 r s orientation)


theorem d012465
    {xbar ybar vx vy : ℝ} (hvx : 0 ≤ vx) (hvy : 0 ≤ vy) :
    _root_.GD.N0232.N0719.N0860.d011426 (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) := by
  intro i
  fin_cases i <;> simp [hvx, hvy]



theorem d012466
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : xbar - ybar ≠ 0) :
    (1 - _root_.GD.N0232.N0720.N1437.d002996 vx vy) /
        _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy =
      vx / (xbar - ybar) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
  field_simp
  ring


theorem d012467
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : xbar - ybar ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d002996 vx vy /
        _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy =
      vy / (xbar - ybar) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
  field_simp



theorem d012468
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : xbar - ybar ≠ 0) :
    _root_.GD.N0232.N0719.N0900.d009101 ybar |xbar - ybar|
        (_root_.GD.N0232.N0720.N1209.d012463
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
          (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)
          (SignType.sign (xbar - ybar) : ℝ)) =
      _root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    fin_cases i
    · change ybar + |xbar - ybar| *
          (SignType.sign (xbar - ybar) : ℝ) = xbar
      rw [abs_mul_sign]
      ring
    · simp [_root_.GD.N0232.N0720.N1209.d012463, _root_.GD.N0232.N0720.N1209.d012458,
        _root_.GD.N0232.N0719.N0900.d009101]
  · funext i
    fin_cases i
    · change |xbar - ybar| ^ 2 *
          ((1 - _root_.GD.N0232.N0720.N1437.d002996 vx vy) /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vx
      rw [_root_.GD.N0232.N0720.N1209.d012466 hsum hcontrast, sq_abs]
      field_simp
    · change |xbar - ybar| ^ 2 *
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vy
      rw [_root_.GD.N0232.N0720.N1209.d012467 hsum hcontrast, sq_abs]
      field_simp



theorem d012469
    {xbar ybar vx vy : ℝ}
    (hvx : 0 < vx) (hvy : 0 < vy) (hcontrast : xbar - ybar ≠ 0) :
    _root_.GD.N0232.N0719.N0860.d011426
      (_root_.GD.N0232.N0720.N1209.d012463
        (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
        (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)
        (SignType.sign (xbar - ybar) : ℝ)) := by
  have hsum : vx + vy ≠ 0 := (add_pos hvx hvy).ne'
  rw [show _root_.GD.N0232.N0720.N1209.d012463
      (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
      (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)
      (SignType.sign (xbar - ybar) : ℝ) =
      _root_.GD.N0232.N0720.N1209.d012458
        (SignType.sign (xbar - ybar) : ℝ) 0
        (vx / (xbar - ybar) ^ 2)
        (vy / (xbar - ybar) ^ 2) by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · exact _root_.GD.N0232.N0720.N1209.d012466 hsum hcontrast
    · exact _root_.GD.N0232.N0720.N1209.d012467 hsum hcontrast]
  apply _root_.GD.N0232.N0720.N1209.d012465
  · exact div_nonneg hvx.le (sq_nonneg _)
  · exact div_nonneg hvy.le (sq_nonneg _)






theorem d012470
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (hd : _root_.GD.N0232.N0719.N0860.d011448 d)
    {xbar ybar vx vy : ℝ}
    (hvx : 0 < vx) (hvy : 0 < vy) (hcontrast : xbar - ybar ≠ 0) :
    d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) =
      ybar + (xbar - ybar) *
        _root_.GD.N0232.N0720.N1209.d012464 d
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
          (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)
          (SignType.sign (xbar - ybar) : ℝ) := by
  have habs : 0 < |xbar - ybar| := abs_pos.mpr hcontrast
  have hsum : vx + vy ≠ 0 := (add_pos hvx hvy).ne'
  let canonical := _root_.GD.N0232.N0720.N1209.d012463
    (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
    (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy)
    (SignType.sign (xbar - ybar) : ℝ)
  have hphysical : _root_.GD.N0232.N0719.N0860.d011426 canonical := by
    exact _root_.GD.N0232.N0720.N1209.d012469 hvx hvy hcontrast
  have hcov := hd ybar |xbar - ybar| habs canonical hphysical
  have horbit :
      _root_.GD.N0232.N0719.N0900.d009101 ybar |xbar - ybar| canonical =
        _root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy := by
    exact _root_.GD.N0232.N0720.N1209.d012468 hsum hcontrast
  rw [horbit] at hcov
  rw [hcov]
  unfold _root_.GD.N0232.N0720.N1209.d012464 canonical
  rw [← mul_assoc, self_mul_sign]






def d012471
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (r s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1209.d012464 d r s 1



theorem d012472
    (orientation : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1209.d012463 p.1 p.2 orientation) := by
  rw [measurable_comap_iff]
  change Measurable (fun p : ℝ × ℝ ↦
    ((fun i : Fin 2 ↦ ![orientation, 0] i),
      fun i : Fin 2 ↦ ![(1 - p.1) / p.2, p.1 / p.2] i))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop




theorem d012473
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : Measurable d) :
    Measurable (fun p : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1209.d012471 d p.1 p.2) := by
  simp only [_root_.GD.N0232.N0720.N1209.d012471, _root_.GD.N0232.N0720.N1209.d012464, one_mul]
  change Measurable (d ∘ fun p : ℝ × ℝ ↦
    _root_.GD.N0232.N0720.N1209.d012463 p.1 p.2 1)
  exact hd.comp
    (_root_.GD.N0232.N0720.N1209.d012472 (1 : ℝ))




def d012474
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (r s : ℝ) : ℝ :=
  if s = 0 then 1 / 2 else _root_.GD.N0232.N0720.N1209.d012471 d r s


theorem d012475
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : Measurable d) :
    Measurable (fun p : ℝ × ℝ ↦ _root_.GD.N0232.N0720.N1209.d012474 d p.1 p.2) := by
  apply Measurable.piecewise
    (measurableSet_eq_fun measurable_snd measurable_const)
  · exact measurable_const
  · exact _root_.GD.N0232.N0720.N1209.d012473 d hd

@[simp] theorem d012476
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (r : ℝ) :
    _root_.GD.N0232.N0720.N1209.d012474 d r 0 = 1 / 2 := by
  simp [_root_.GD.N0232.N0720.N1209.d012474]

theorem d012477
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (r s : ℝ) (hs : s ≠ 0) :
    _root_.GD.N0232.N0720.N1209.d012474 d r s = _root_.GD.N0232.N0720.N1209.d012471 d r s := by
  simp [_root_.GD.N0232.N0720.N1209.d012474, hs]



def d012478
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) : Prop :=
  ∀ xbar ybar vx vy,
    d (_root_.GD.N0232.N0720.N1209.d012458 (-xbar) (-ybar) vx vy) =
      -d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy)


def d012479
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) : Prop :=
  ∀ xbar ybar vx vy,
    d (_root_.GD.N0232.N0720.N1209.d012458 ybar xbar vy vx) =
      d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy)



theorem d012480
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (r s : ℝ) :
    _root_.GD.N0232.N0720.N1209.d012464 d r s (-1) =
      _root_.GD.N0232.N0720.N1209.d012471 d r s := by
  have h := hreflect 1 0 ((1 - r) / s) (r / s)
  have h' :
      d (_root_.GD.N0232.N0720.N1209.d012458 (-1) 0 ((1 - r) / s) (r / s)) =
        -d (_root_.GD.N0232.N0720.N1209.d012458 1 0 ((1 - r) / s) (r / s)) := by
    simpa only [neg_zero] using h
  change
    (-1 : ℝ) *
        d (_root_.GD.N0232.N0720.N1209.d012458 (-1) 0 ((1 - r) / s) (r / s)) =
      1 * d (_root_.GD.N0232.N0720.N1209.d012458 1 0 ((1 - r) / s) (r / s))
  rw [h']
  ring



theorem d012481
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (hswap : _root_.GD.N0232.N0720.N1209.d012479 d)
    (r s : ℝ) :
    _root_.GD.N0232.N0720.N1209.d012471 d (1 - r) s =
      1 - _root_.GD.N0232.N0720.N1209.d012471 d r s := by
  have haff := haffine 1 1 (by norm_num : (0 : ℝ) < 1)
    (_root_.GD.N0232.N0720.N1209.d012458 0 (-1) (r / s) ((1 - r) / s))
  have href := hreflect 0 1 (r / s) ((1 - r) / s)
  have href' :
      d (_root_.GD.N0232.N0720.N1209.d012458 0 (-1) (r / s) ((1 - r) / s)) =
        -d (_root_.GD.N0232.N0720.N1209.d012458 0 1 (r / s) ((1 - r) / s)) := by
    simpa only [neg_zero] using href
  have hsw := hswap 1 0 ((1 - r) / s) (r / s)
  simp only [_root_.GD.N0232.N0720.N1209.d012471, _root_.GD.N0232.N0720.N1209.d012464,
    one_mul, _root_.GD.N0232.N0720.N1209.d012463]
  rw [show 1 - (1 - r) = r by ring]
  have hsummary :
      _root_.GD.N0232.N0719.N0900.d009101 1 1
          (_root_.GD.N0232.N0720.N1209.d012458 0 (-1) (r / s) ((1 - r) / s)) =
        _root_.GD.N0232.N0720.N1209.d012458 1 0 (r / s) ((1 - r) / s) := by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
      simp [_root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458]
  have haff' :
      d (_root_.GD.N0232.N0720.N1209.d012458 1 0 (r / s) ((1 - r) / s)) =
        1 + d (_root_.GD.N0232.N0720.N1209.d012458 0 (-1) (r / s) ((1 - r) / s)) := by
    rw [hsummary] at haff
    simpa using haff
  rw [haff', href', hsw]
  ring



theorem d012482
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (hswap : _root_.GD.N0232.N0720.N1209.d012479 d)
    (r s : ℝ) :
    _root_.GD.N0232.N0720.N1209.d012474 d (1 - r) s =
      1 - _root_.GD.N0232.N0720.N1209.d012474 d r s := by
  by_cases hs : s = 0
  · subst s
    norm_num [_root_.GD.N0232.N0720.N1209.d012474]
  · simp only [_root_.GD.N0232.N0720.N1209.d012474, if_neg hs]
    exact _root_.GD.N0232.N0720.N1209.d012481
      d haffine hreflect hswap r s



theorem d012483
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : 0 < xbar - ybar) :
    _root_.GD.N0232.N0719.N0900.d009101 ybar (xbar - ybar)
        (_root_.GD.N0232.N0720.N1209.d012463
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
          (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) 1) =
      _root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1209.d012463, _root_.GD.N0232.N0720.N1209.d012458,
        _root_.GD.N0232.N0719.N0900.d009101] <;>
      ring
  · funext i
    fin_cases i
    · change (xbar - ybar) ^ 2 *
          ((1 - _root_.GD.N0232.N0720.N1437.d002996 vx vy) /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vx
      rw [_root_.GD.N0232.N0720.N1209.d012466 hsum hcontrast.ne']
      field_simp [hcontrast.ne']
    · change (xbar - ybar) ^ 2 *
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vy
      rw [_root_.GD.N0232.N0720.N1209.d012467 hsum hcontrast.ne']
      field_simp [hcontrast.ne']



theorem d012484
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : xbar - ybar < 0) :
    _root_.GD.N0232.N0719.N0900.d009101 ybar (-(xbar - ybar))
        (_root_.GD.N0232.N0720.N1209.d012463
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
          (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) (-1)) =
      _root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1209.d012463, _root_.GD.N0232.N0720.N1209.d012458,
        _root_.GD.N0232.N0719.N0900.d009101] <;>
      ring
  · funext i
    fin_cases i
    · change (-(xbar - ybar)) ^ 2 *
          ((1 - _root_.GD.N0232.N0720.N1437.d002996 vx vy) /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vx
      rw [_root_.GD.N0232.N0720.N1209.d012466 hsum hcontrast.ne]
      field_simp [hcontrast.ne]
    · change (-(xbar - ybar)) ^ 2 *
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy /
            _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) = vy
      rw [_root_.GD.N0232.N0720.N1209.d012467 hsum hcontrast.ne]
      field_simp [hcontrast.ne]







theorem d012485
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    {xbar ybar vx vy : ℝ}
    (hsum : vx + vy ≠ 0) (hcontrast : xbar - ybar ≠ 0) :
    d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) =
      ybar + (xbar - ybar) *
        _root_.GD.N0232.N0720.N1209.d012471 d
          (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
          (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) := by
  rcases lt_or_gt_of_ne hcontrast with hneg | hpos
  · let r := _root_.GD.N0232.N0720.N1437.d002996 vx vy
    let s := _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy
    have hreconstruct := _root_.GD.N0232.N0720.N1209.d012484 hsum hneg
    have hcov := haffine ybar (-(xbar - ybar)) (by linarith)
      (_root_.GD.N0232.N0720.N1209.d012463 r s (-1))
    rw [hreconstruct] at hcov
    rw [hcov]
    have hbranch := _root_.GD.N0232.N0720.N1209.d012480
      d hreflect r s
    unfold _root_.GD.N0232.N0720.N1209.d012464 at hbranch
    norm_num at hbranch
    dsimp only [r, s] at hbranch ⊢
    rw [← hbranch]
    ring
  · let r := _root_.GD.N0232.N0720.N1437.d002996 vx vy
    let s := _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy
    have hreconstruct := _root_.GD.N0232.N0720.N1209.d012483 hsum hpos
    have hcov := haffine ybar (xbar - ybar) hpos
      (_root_.GD.N0232.N0720.N1209.d012463 r s 1)
    rw [hreconstruct] at hcov
    simpa only [_root_.GD.N0232.N0720.N1209.d012471, _root_.GD.N0232.N0720.N1209.d012464,
      one_mul, r, s] using hcov

end

end N1209
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1209.d012468
#print axioms _root_.GD.N0232.N0720.N1209.d012470
