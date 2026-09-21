import GD.Module0213
import GD.Module0309






open Set Filter MeasureTheory
open scoped Topology

namespace GD.N0232.N0720.N1383

open _root_.GD.N0232.N0720.N1376

noncomputable section

def d004672 (t X R Y S : ℝ) : ℝ := _root_.GD.N0232.N0720.N1376.d002892 t X Y (R ^ 2 / 2) (S ^ 2 / 2)

theorem d004673 (t X R Y S : ℝ) :
    _root_.GD.N0232.N0720.N1383.d004672 t X R Y S = (1 - t) * (X ^ 2 + R ^ 2) + t * (Y ^ 2 + S ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1383.d004672 _root_.GD.N0232.N0720.N1376.d002892
  ring


theorem d004674 {t x y lo hi : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    (1 - t) * x + t * y ∈ Icc lo hi := by
  constructor
  · have h0 := mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.mpr ht.2)
    have h1 := mul_le_mul_of_nonneg_left hy.1 ht.1
    nlinarith
  · have h0 := mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr ht.2)
    have h1 := mul_le_mul_of_nonneg_left hy.2 ht.1
    nlinarith


theorem d004675 {t X R Y S lo hi : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 ≤ lo)
    (hX : X ∈ Icc lo hi) (hY : Y ∈ Icc lo hi)
    (hR : R ∈ Icc (1 : ℝ) 2) (hS : S ∈ Icc (1 : ℝ) 2) :
    _root_.GD.N0232.N0720.N1376.d002893 t X Y ∈ Icc lo hi ∧
      _root_.GD.N0232.N0720.N1383.d004672 t X R Y S ∈ Icc (lo ^ 2 + 1) (hi ^ 2 + 4) := by
  refine ⟨_root_.GD.N0232.N0720.N1383.d004674 ht hX hY, ?_⟩
  rw [_root_.GD.N0232.N0720.N1383.d004673]
  apply _root_.GD.N0232.N0720.N1383.d004674 ht
  · constructor
    · have hx := (sq_le_sq₀ hlo (hlo.trans hX.1)).2 hX.1
      nlinarith [hR.1, sq_nonneg (R - 1)]
    · have hx := (sq_le_sq₀ (hlo.trans hX.1) (hlo.trans (hX.1.trans hX.2))).2 hX.2
      nlinarith [hR.2, mul_nonneg (sub_nonneg.mpr hR.1) (sub_nonneg.mpr hR.2)]
  · constructor
    · have hy := (sq_le_sq₀ hlo (hlo.trans hY.1)).2 hY.1
      nlinarith [hS.1, sq_nonneg (S - 1)]
    · have hy := (sq_le_sq₀ (hlo.trans hY.1) (hlo.trans (hY.1.trans hY.2))).2 hY.2
      nlinarith [hS.2, mul_nonneg (sub_nonneg.mpr hS.1) (sub_nonneg.mpr hS.2)]


theorem d004676 {t X R Y S lo hi level delta : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 < lo)
    (hX : X ∈ Icc lo hi) (hY : Y ∈ Icc lo hi)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hlevel : hi ≤ level + delta)
    (hmargin : (level + delta - lo) * hi ≤ 1) :
    level + delta ≤ _root_.GD.N0232.N0720.N1383.d004672 t X R Y S / _root_.GD.N0232.N0720.N1376.d002893 t X Y := by
  have hB : 0 < _root_.GD.N0232.N0720.N1376.d002893 t X Y :=
    hlo.trans_le (_root_.GD.N0232.N0720.N1383.d004674 ht hX hY).1
  apply (le_div_iff₀ hB).2
  have hsingle (x r : ℝ) (hx : x ∈ Icc lo hi) (hr : 1 ≤ r) :
      (level + delta) * x ≤ x ^ 2 + r ^ 2 := by
    have hxpos : 0 ≤ x := (hlo.trans_le hx.1).le
    have hg : 0 ≤ level + delta - lo := by linarith [hx.1, hx.2]
    have hm := mul_le_mul_of_nonneg_left hx.2 hg
    have hl := mul_le_mul_of_nonneg_right hx.1 hxpos
    nlinarith [sq_nonneg (r - 1)]
  have h0 := mul_le_mul_of_nonneg_left (hsingle X R hX hR) (sub_nonneg.mpr ht.2)
  have h1 := mul_le_mul_of_nonneg_left (hsingle Y S hY hS) ht.1
  rw [_root_.GD.N0232.N0720.N1383.d004673]
  unfold _root_.GD.N0232.N0720.N1376.d002893
  nlinarith



theorem d004677 {t X R Y S lo hi beta : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 < lo) (hbeta : 0 ≤ beta)
    (hX : X ∈ Icc lo hi) (hY : Y ∈ Icc lo hi)
    (hR : R ∈ Icc (1 : ℝ) 2) (hS : S ∈ Icc (1 : ℝ) 2)
    (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2) :
    beta ≤ _root_.GD.N0232.N0720.N1376.d002893 t X Y ^ 2 / (2 * _root_.GD.N0232.N0720.N1383.d004672 t X R Y S) := by
  obtain ⟨hB, hA⟩ := _root_.GD.N0232.N0720.N1383.d004675 ht hlo.le hX hY hR hS
  have hApos : 0 < _root_.GD.N0232.N0720.N1383.d004672 t X R Y S := by nlinarith [hA.1, sq_nonneg lo]
  apply (le_div_iff₀ (mul_pos (by norm_num) hApos)).2
  have hBsquare := (sq_le_sq₀ hlo.le (hlo.trans_le hB.1).le).2 hB.1
  have hupper := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 2 * beta)
  nlinarith



theorem d004678 {beta : ℝ} (hbeta : 0 ≤ beta)
    (hhalf : beta < (1 / 2 : ℝ)) :
    ∃ lo hi level delta : ℝ,
      0 < lo ∧ lo < hi ∧ hi < level ∧ 0 < delta ∧
      hi ≤ level + delta ∧ (level + delta - lo) * hi ≤ 1 ∧
      2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2 := by
  let gap : ℝ := 1 - 2 * beta
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let lo : ℝ := Real.sqrt (8 * beta / gap + 1)
  have hinside : 0 < 8 * beta / gap + 1 := by positivity
  have hlo : 0 < lo := Real.sqrt_pos.2 hinside
  have hsq : lo ^ 2 = 8 * beta / gap + 1 := Real.sq_sqrt hinside.le
  have hprod : gap * lo ^ 2 = 8 * beta + gap := by
    rw [hsq, mul_add, mul_div_cancel₀ _ hgap.ne', mul_one]
  have hrate0 : 2 * beta * (lo ^ 2 + 4) < lo ^ 2 := by
    dsimp [gap] at hprod hgap
    nlinarith
  have hrateContinuous : Continuous (fun e : ℝ ↦
      2 * beta * ((lo + e) ^ 2 + 4)) := by fun_prop
  have hmarginContinuous : Continuous (fun e : ℝ ↦ 3 * e * (lo + e)) := by fun_prop
  have hopen : IsOpen {e : ℝ |
      2 * beta * ((lo + e) ^ 2 + 4) < lo ^ 2 ∧ 3 * e * (lo + e) < 1} :=
    (isOpen_lt hrateContinuous (continuous_const (y := lo ^ 2))).inter
      (isOpen_lt hmarginContinuous (continuous_const (y := (1 : ℝ))))
  have hzero : (0 : ℝ) ∈ {e : ℝ |
      2 * beta * ((lo + e) ^ 2 + 4) < lo ^ 2 ∧ 3 * e * (lo + e) < 1} := by
    simpa only [Set.mem_setOf_eq, add_zero, mul_zero, zero_mul] using!
      And.intro hrate0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  have he : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  obtain ⟨hrate, hmargin⟩ := hball he
  refine ⟨lo, lo + r / 2, lo + r, r / 2, hlo, by linarith,
    by linarith, by positivity, by linarith, ?_, hrate.le⟩
  nlinarith

abbrev d004679 := _root_.GD.N0232.N0720.N1393.d004492

def d004680 (lo hi : ℝ) : Set _root_.GD.N0232.N0720.N1383.d004679 :=
  {x | x 0 ∈ Ioo lo hi ∧ x 2 ∈ Ioo lo hi ∧
    x 1 ∈ Ioo (1 : ℝ) 2 ∧ x 3 ∈ Ioo (1 : ℝ) 2}

theorem d004681 (lo hi : ℝ) : IsOpen (_root_.GD.N0232.N0720.N1383.d004680 lo hi) := by
  unfold _root_.GD.N0232.N0720.N1383.d004680
  have hcoord (i : Fin 4) : Continuous (fun x : _root_.GD.N0232.N0720.N1383.d004679 ↦ x i) := by fun_prop
  exact (isOpen_Ioo.preimage (hcoord 0)).inter
    ((isOpen_Ioo.preimage (hcoord 2)).inter
      ((isOpen_Ioo.preimage (hcoord 1)).inter (isOpen_Ioo.preimage (hcoord 3))))

theorem d004682 {lo hi : ℝ} (h : lo < hi) : (_root_.GD.N0232.N0720.N1383.d004680 lo hi).Nonempty := by
  refine ⟨WithLp.toLp 2 ![(lo + hi) / 2, (3 / 2 : ℝ), (lo + hi) / 2, (3 / 2 : ℝ)], ?_⟩
  change ((lo + hi) / 2 ∈ Ioo lo hi) ∧ ((lo + hi) / 2 ∈ Ioo lo hi) ∧
    ((3 / 2 : ℝ) ∈ Ioo 1 2) ∧ ((3 / 2 : ℝ) ∈ Ioo 1 2)
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  norm_num



theorem d004683 {lo hi : ℝ} (h : lo < hi)
    {P : _root_.GD.N0232.N0720.N1383.d004679 → Prop} (hP : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679), P x) :
    ∃ x ∈ _root_.GD.N0232.N0720.N1383.d004680 lo hi, P x := by
  have hpos := (_root_.GD.N0232.N0720.N1383.d004681 lo hi).measure_pos volume (_root_.GD.N0232.N0720.N1383.d004682 h)
  by_contra hn
  have hempty : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1383.d004679), x ∉ _root_.GD.N0232.N0720.N1383.d004680 lo hi := by
    filter_upwards [hP] with x hx hbox
    exact hn ⟨x, hbox, hx⟩
  have hzero : (volume : Measure _root_.GD.N0232.N0720.N1383.d004679) (_root_.GD.N0232.N0720.N1383.d004680 lo hi) = 0 := by
    simpa only [ae_iff, not_not] using! hempty
  exact hpos.ne' hzero

end
end GD.N0232.N0720.N1383
