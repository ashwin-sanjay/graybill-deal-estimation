import GD.Module0606

open Set

namespace GD.N0131

open _root_.GD.N0118
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0113
open _root_.GD.N0113.d008651





theorem d008800
    {rhoQ : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0)
    (hUpper : ∀ z, T.d008697 i z ≠ 0 →
      _root_.GD.N0131.d008765 D z ≤ ((T.boxes i).upper : ℝ)) :
    _root_.GD.N0131.d008765 D x < ((T.boxes i).upper : ℝ) := by
  have hbox := _root_.GD.N0131.d008777 T i x hx
  have hgeo := _root_.GD.N0131.d008780 T i x hbox
  let c : ℝ := ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)
  let w : ℝ := (T.width : ℝ)
  let y : ℝ × ℝ := (x.1, (x.2 + c + w) / 2)
  have hw : 0 < w := by
    dsimp [w]
    exact_mod_cast T.width_pos
  have hbox' :
      |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)| < w ∧
        |x.2 - c| < w := by
    simpa [_root_.GD.N0131.d008760, c, w] using hbox
  have hxfUpper : x.2 < c + w := by
    linarith [(abs_lt.mp hbox'.2).2]
  have hxfLower : c - w < x.2 := by
    linarith [(abs_lt.mp hbox'.2).1]
  have hxy : x.2 < y.2 := by
    dsimp [y]
    linarith
  have hybox : y ∈ _root_.GD.N0131.d008760 (_root_.GD.N0115.d006635 (T.d008652 i)) T.width := by
    change
      |y.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)| < (T.width : ℝ) ∧
        |y.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)| < (T.width : ℝ)
    constructor
    · simpa [y, w] using hbox'.1
    · rw [abs_lt]
      dsimp [y, c, w] at ⊢
      constructor <;> linarith
  have hygeo := _root_.GD.N0131.d008780 T i y hybox
  have hxTentParts :
      _root_.GD.N0118.d008582 ((T.d008652 i).ell : ℝ) (T.width : ℝ) x.1 ≠ 0 ∧
        _root_.GD.N0118.d008582 ((T.d008652 i).f : ℝ) (T.width : ℝ) x.2 ≠ 0 := by
    exact mul_ne_zero_iff.mp (by simpa [_root_.GD.N0113.d008651.d008697, _root_.GD.N0118.d008583] using hx)
  have hyFLeft : c < y.2 := by
    dsimp [y]
    linarith
  have hyFRight : y.2 < c + w := by
    dsimp [y]
    linarith
  have hyFMem : y.2 ∈ Ioc c (c + w) := ⟨hyFLeft, hyFRight.le⟩
  have hyFNotLeft : y.2 ∉ Ioc (c - w) c := by
    intro h
    exact (not_lt_of_ge h.2) hyFLeft
  have hyFTent :
      _root_.GD.N0118.d008582 ((T.d008652 i).f : ℝ) (T.width : ℝ) y.2 ≠ 0 := by
    change _root_.GD.N0118.d008582 c w y.2 ≠ 0
    simp only [_root_.GD.N0118.d008582, Set.indicator_of_notMem hyFNotLeft, zero_add,
      Set.indicator_of_mem hyFMem]
    unfold _root_.GD.N0118.d008581
    exact div_ne_zero (sub_ne_zero.mpr hyFRight.ne') (pow_ne_zero 2 hw.ne')
  have hyTent : T.d008697 i y ≠ 0 := by
    change
      _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
        (T.width : ℝ) y ≠ 0
    unfold _root_.GD.N0118.d008583
    exact mul_ne_zero (by simpa [y] using hxTentParts.1) hyFTent
  have hyUpper : _root_.GD.N0131.d008765 D y ≤ ((T.boxes i).upper : ℝ) :=
    hUpper y hyTent
  have hfactor :
      0 < x.1 ^ ((D.beta : ℝ) - 1) *
        (1 - x.1) ^ ((D.alpha : ℝ) - 1) := by
    exact mul_pos
      (Real.rpow_pos_of_pos hgeo.2.1 _)
      (Real.rpow_pos_of_pos (sub_pos.mpr hgeo.2.2.1) _)
  have hFpow :
      x.2 ^ ((1 : ℝ) / 2) < y.2 ^ ((1 : ℝ) / 2) := by
    exact Real.rpow_lt_rpow hgeo.2.2.2.le hxy (by norm_num)
  have hRho : _root_.GD.N0131.d008765 D x < _root_.GD.N0131.d008765 D y := by
    unfold _root_.GD.N0131.d008765
    dsimp [y]
    exact mul_lt_mul_of_pos_left hFpow hfactor
  exact hRho.trans_le hyUpper

end GD.N0131
