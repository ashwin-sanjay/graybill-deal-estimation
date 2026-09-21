import GD.Module0906
import GD.Module0608








open Set

namespace GD.N0145

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0111
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131
open _root_.GD.N0128

def d014133 (D : _root_.GD.N0134.d006518) (k : ℕ) : ℚ :=
  ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
    |((_root_.GD.N0146.d008622 D k).get i).weight|

@[simp] theorem d014134
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k) :
    _root_.GD.N0113.d008667 T = _root_.GD.N0145.d014133 D k := by
  rfl

theorem d014135
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    0 ≤ _root_.GD.N0145.d014133 D k := by
  unfold _root_.GD.N0145.d014133
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem d014136 (x : ℝ) :
    ∃ q : ℚ, 0 < q ∧ x ≤ (q : ℝ) := by
  obtain ⟨q : ℚ, hq⟩ := exists_rat_gt (max x 0)
  refine ⟨q, ?_, ?_⟩
  · exact_mod_cast
      (show (0 : ℝ) < (q : ℝ) from
        lt_of_le_of_lt (le_max_right x 0) hq)
  · exact (le_max_left x 0).trans hq.le

theorem d014137
    {C a b w : ℚ}
    (hC : 0 < C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : w ≤ C / (16 * (1 + a) * (1 + b))) :
    w * a * b ≤ C / 16 := by
  let denom : ℚ := 16 * (1 + a) * (1 + b)
  have hdenom : 0 < denom := by
    dsimp [denom]
    positivity
  have hquot : 0 ≤ C / denom := (div_pos hC hdenom).le
  have hab : a * b ≤ (1 + a) * (1 + b) := by
    nlinarith [mul_nonneg ha hb]
  calc
    w * a * b
        ≤ (C / denom) * a * b := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hw ha) hb
    _ = (C / denom) * (a * b) := by ring
    _ ≤ (C / denom) * ((1 + a) * (1 + b)) :=
      mul_le_mul_of_nonneg_left hab hquot
    _ = C / 16 := by
      dsimp [denom]
      field_simp






theorem d014138
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Nonempty (_root_.GD.N0145.d014114 m n hm hn) := by
  let D := _root_.GD.N0134.d006543 m n hm hn
  obtain ⟨H, hatomicHeader⟩ :=
    _root_.GD.N0113.d008651.d008758
      (rhoQ := _root_.GD.N0131.d008766 D)
      (m := m) (n := n) (hm := hm) (hn := hn) D
  let G : ℝ :=
    _root_.GD.N0111.d006160
        (D.alpha : ℝ) (D.beta : ℝ)
        (D.d006524 : ℝ) 1 0
      +
    _root_.GD.N0111.d006160
        (D.alpha : ℝ) (D.beta : ℝ)
        (D.d006524 : ℝ) 0 1
  let B : ℝ :=
    _root_.GD.N0111.d006160
      (D.alpha : ℝ) (D.beta : ℝ)
      (D.d006524 : ℝ) 0 0
  let P : ℝ :=
    _root_.GD.N0111.d006153
      (_root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ))
      (D.d006524 : ℝ) 0
  obtain ⟨gradientBound, hgradientPos, hgradientMajorant⟩ :=
    _root_.GD.N0145.d014136 G
  obtain ⟨carrierBound, hcarrierPos, hcarrierMajorant⟩ :=
    _root_.GD.N0145.d014136 B
  obtain ⟨inversePower, hinversePos, hinverseMajorant⟩ :=
    _root_.GD.N0145.d014136 P
  let V : ℚ := _root_.GD.N0145.d014133 D H.k
  have hV : 0 ≤ V := _root_.GD.N0145.d014135 D H.k
  let wMax : ℚ :=
    H.Cstar /
      (16 * (1 + gradientBound) * (1 + V))
  let eta : ℚ :=
    H.Cstar /
      (16 * (1 + carrierBound) * (1 + V))
  have hwMax : 0 < wMax := by
    dsimp [wMax]
    apply div_pos H.Cstar_pos
    exact mul_pos
      (mul_pos (by norm_num) (by linarith [hgradientPos]))
      (by linarith [hV])
  have heta : 0 < eta := by
    dsimp [eta]
    apply div_pos H.Cstar_pos
    exact mul_pos
      (mul_pos (by norm_num) (by linarith [hcarrierPos]))
      (by linarith [hV])
  obtain ⟨T, hwidth, hrelative⟩ :=
    _root_.GD.N0128.d008807
      D H.k eta wMax heta hwMax
  have hsmear :
      _root_.GD.N0113.d008668 T gradientBound ≤ H.Cstar / 16 := by
    rw [_root_.GD.N0113.d008668, _root_.GD.N0145.d014134]
    change T.width * gradientBound * V ≤ H.Cstar / 16
    exact _root_.GD.N0145.d014137 H.Cstar_pos hgradientPos.le hV
      (by simpa [wMax] using hwidth)
  have hdensity :
      _root_.GD.N0113.d008669 T carrierBound ≤ H.Cstar / 16 := by
    calc
      _root_.GD.N0113.d008669 T carrierBound
          ≤ eta * carrierBound * _root_.GD.N0113.d008667 T :=
        _root_.GD.N0145.d014112 T
          heta.le hcarrierPos.le (fun i => (hrelative i).le)
      _ = eta * carrierBound * V := by
        rw [_root_.GD.N0145.d014134]
      _ ≤ H.Cstar / 16 :=
        _root_.GD.N0145.d014137 H.Cstar_pos hcarrierPos.le hV
          (by simp [eta])
  apply _root_.GD.N0145.d014116
    H T gradientBound carrierBound inversePower
    hgradientPos.le hcarrierPos.le hinversePos
  · simpa [D, G] using hgradientMajorant
  · simpa [D, B] using hcarrierMajorant
  · simpa [D, P] using hinverseMajorant
  · intro e he
    change
      T.d008711
          (_root_.GD.N0113.d008651.d008730
            D e)
        ≤ -(3 * (H.Cstar : ℝ) / 4)
    exact hatomicHeader e he.1 he.2 T
  · exact hsmear
  · exact hdensity

end

end GD.N0145
