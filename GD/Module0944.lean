import GD.Module0940
import GD.Module0912
import GD.Module0023















open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace GD.N0232.N0720.N1396

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0230.N0637

section Algebra

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}


theorem d014771
    {u c : Omega → ℝ} (hu : MemLp u 2 P) (hc : MemLp c 2 P) :
    _root_.GD.N0141.d006684 P (fun w ↦ u w + c w) =
      _root_.GD.N0141.d006684 P u + _root_.GD.N0141.d006684 P c +
        2 * ∫ w, u w * c w ∂P := by
  have huc : Integrable (fun w ↦ u w * c w) P :=
    MemLp.integrable_mul (p := 2) (q := 2) hu hc
  unfold _root_.GD.N0141.d006684
  calc
    (∫ w, (u w + c w) ^ 2 ∂P) =
        ∫ w, (u w ^ 2 + c w ^ 2) + 2 * (u w * c w) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = (∫ w, u w ^ 2 ∂P) + (∫ w, c w ^ 2 ∂P) +
        2 * ∫ w, u w * c w ∂P := by
      rw [integral_add (hu.integrable_sq.fun_add hc.integrable_sq)
        (huc.const_mul 2),
        integral_add hu.integrable_sq hc.integrable_sq,
        integral_const_mul]


theorem d014772
    {u a b : Omega → ℝ}
    (hu : MemLp u 2 P) (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    _root_.GD.N0141.d006684 P a - _root_.GD.N0141.d006684 P b =
      _root_.GD.N0141.d006684 P (fun w ↦ a w - u w) -
        _root_.GD.N0141.d006684 P (fun w ↦ b w - u w) +
        2 * ∫ w, u w * (a w - b w) ∂P := by
  have hca : MemLp (fun w ↦ a w - u w) 2 P := ha.sub hu
  have hcb : MemLp (fun w ↦ b w - u w) 2 P := hb.sub hu
  have hA := _root_.GD.N0232.N0720.N1396.d014771 hu hca
  have hB := _root_.GD.N0232.N0720.N1396.d014771 hu hcb
  have heqa : (fun w ↦ u w + (a w - u w)) = a := by
    funext w
    ring
  have heqb : (fun w ↦ u w + (b w - u w)) = b := by
    funext w
    ring
  change _root_.GD.N0141.d006684 P (fun w ↦ u w + (a w - u w)) = _ at hA
  change _root_.GD.N0141.d006684 P (fun w ↦ u w + (b w - u w)) = _ at hB
  rw [heqa] at hA
  rw [heqb] at hB
  have hcross : (∫ w, u w * (a w - b w) ∂P) =
      (∫ w, u w * (a w - u w) ∂P) -
        ∫ w, u w * (b w - u w) ∂P := by
    calc
      (∫ w, u w * (a w - b w) ∂P) =
          ∫ w, u w * (a w - u w) - u w * (b w - u w) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with w
        ring
      _ = _ := integral_sub
        (MemLp.integrable_mul (p := 2) (q := 2) hu hca)
        (MemLp.integrable_mul (p := 2) (q := 2) hu hcb)
  rw [hcross]
  linarith

end Algebra





def d014773 (y d z : ℝ) : ℝ :=
  y + d * _root_.GD.N0230.N0637.d000240 ((z - y) / d)

theorem d014774
    (y d z t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1396.d014773 y d z - (y + t * d)| ≤ |z - (y + t * d)| := by
  by_cases hd : d = 0
  · simp [_root_.GD.N0232.N0720.N1396.d014773, hd]
  · have hraw : z - (y + t * d) = d * ((z - y) / d - t) := by
      field_simp [hd]
      ring
    have hclip : _root_.GD.N0232.N0720.N1396.d014773 y d z - (y + t * d) =
        d * (_root_.GD.N0230.N0637.d000240 ((z - y) / d) - t) := by
      unfold _root_.GD.N0232.N0720.N1396.d014773
      ring
    rw [hraw, hclip, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (_root_.GD.N0230.N0637.d000245 ht) (abs_nonneg d)

theorem d014775
    (y d z t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1396.d014773 y d z - (y + t * d)) ^ 2 ≤
      (z - (y + t * d)) ^ 2 :=
  (sq_le_sq).2 (_root_.GD.N0232.N0720.N1396.d014774 y d z t ht)

theorem d014776 (y d z : ℝ) :
    _root_.GD.N0232.N0720.N1396.d014773 (-y) (-d) (-z) = -_root_.GD.N0232.N0720.N1396.d014773 y d z := by
  have hratio : (-z - -y) / -d = (z - y) / d := by
    rw [show -z - -y = -(z - y) by ring, neg_div_neg_eq]
  unfold _root_.GD.N0232.N0720.N1396.d014773
  rw [hratio]
  ring



theorem d014777 :
    (_root_.GD.N0232.N0720.N1396.d014773 2 1 0 - (0 : ℝ)) ^ 2 > (0 - (0 : ℝ)) ^ 2 ∧
      (_root_.GD.N0232.N0720.N1396.d014773 2 1 0 - (2 + (1 / 2 : ℝ) * 1)) ^ 2 <
        (0 - (2 + (1 / 2 : ℝ) * 1)) ^ 2 := by
  norm_num [_root_.GD.N0232.N0720.N1396.d014773, _root_.GD.N0230.N0637.d000240]





def d014778 (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0107.d012732 m n theta.location
    (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)


def d014779 (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun w ↦ e w - theta.location - _root_.GD.N0232.N0720.N1396.d014778 m n theta w


def d014780 (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ :=
  ∫ w, _root_.GD.N0232.N0720.N1396.d014778 m n theta w * _root_.GD.N0232.N0720.N1396.d014779 m n theta e w ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta


def d014781 (m n : ℕ) (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun w ↦ _root_.GD.N0232.N0720.N1396.d014773 (_root_.GD.N0107.d009084 w.2)
    (_root_.GD.N0107.d009090 m n w) (e w)

theorem d014782 (m n : ℕ)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e) :
    Measurable (_root_.GD.N0232.N0720.N1396.d014781 m n e) := by
  unfold _root_.GD.N0232.N0720.N1396.d014781 _root_.GD.N0232.N0720.N1396.d014773 _root_.GD.N0230.N0637.d000240
  fun_prop

theorem d014783 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : MemLp (_root_.GD.N0232.N0720.N1396.d014778 m n theta) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  exact _root_.GD.N0107.d012747 m n hm hn
    theta.location theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos


theorem d014784
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤) :
    MemLp (fun w ↦ e w - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hmeas : Measurable (fun w : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ e w - theta.location) :=
    he.sub measurable_const
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  have hlin : (∫⁻ w, ENNReal.ofReal ((e w - theta.location) ^ 2)
      ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≠ ⊤ := hfinite
  have hint := integrable_toReal_of_lintegral_ne_top
    ((hmeas.pow_const 2).ennreal_ofReal.aemeasurable) hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint

theorem d014785
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (he : MemLp (fun w ↦ e w - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta e =
      ENNReal.ofReal (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ e w - theta.location)) := by
  unfold _root_.GD.N0232.N0720.N1080.d014197 _root_.GD.N0141.d006684
  exact (ofReal_integral_eq_lintegral_ofReal he.integrable_sq
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).symm

theorem d014786
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (he : MemLp (fun w ↦ e w - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    MemLp (_root_.GD.N0232.N0720.N1396.d014779 m n theta e) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
  he.sub (_root_.GD.N0232.N0720.N1396.d014783 m n hm hn theta)



theorem d014787
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ e w - theta.location) =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014778 m n theta) +
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014779 m n theta e) +
          2 * _root_.GD.N0232.N0720.N1396.d014780 m n theta e := by
  have hE := _root_.GD.N0232.N0720.N1396.d014784 m n theta he hfinite
  have hC := _root_.GD.N0232.N0720.N1396.d014786 m n hm hn theta hE
  have h := _root_.GD.N0232.N0720.N1396.d014771 (_root_.GD.N0232.N0720.N1396.d014783 m n hm hn theta) hC
  have heq : (fun w ↦ _root_.GD.N0232.N0720.N1396.d014778 m n theta w + _root_.GD.N0232.N0720.N1396.d014779 m n theta e w) =
      (fun w ↦ e w - theta.location) := by
    funext w
    unfold _root_.GD.N0232.N0720.N1396.d014779
    ring
  rw [heq] at h
  exact h



theorem d014788
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (he : Measurable e) (hd : Measurable d)
    (hefinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤)
    (hdfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ e w - theta.location) -
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ d w - theta.location) =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014779 m n theta e) -
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014779 m n theta d) +
          2 * ∫ w, _root_.GD.N0232.N0720.N1396.d014778 m n theta w * (e w - d w) ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  have h := _root_.GD.N0232.N0720.N1396.d014772
    (_root_.GD.N0232.N0720.N1396.d014783 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1396.d014784 m n theta he hefinite)
    (_root_.GD.N0232.N0720.N1396.d014784 m n theta hd hdfinite)
  simpa only [_root_.GD.N0232.N0720.N1396.d014779, sub_sub_sub_cancel_right] using! h


theorem d014789
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (w : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    |_root_.GD.N0232.N0720.N1396.d014779 m n theta (_root_.GD.N0232.N0720.N1396.d014781 m n e) w| ≤
      |_root_.GD.N0232.N0720.N1396.d014779 m n theta e w| := by
  let t := _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(_root_.GD.N0107.d009050
        (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos).le,
      (_root_.GD.N0107.d009051
        (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos).le⟩
  have h := _root_.GD.N0232.N0720.N1396.d014774 (_root_.GD.N0107.d009084 w.2)
    (_root_.GD.N0107.d009090 m n w) (e w) t ht
  have hform (a : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
      _root_.GD.N0232.N0720.N1396.d014779 m n theta a w = a w -
        (_root_.GD.N0107.d009084 w.2 + t * _root_.GD.N0107.d009090 m n w) := by
    unfold _root_.GD.N0232.N0720.N1396.d014779 _root_.GD.N0232.N0720.N1396.d014778 _root_.GD.N0107.d012732
    dsimp only [t]
    ring
  rw [hform, hform]
  exact h


theorem d014790
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e)
    (hE : MemLp (fun w ↦ e w - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    MemLp (fun w ↦ _root_.GD.N0232.N0720.N1396.d014781 m n e w - theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hC := _root_.GD.N0232.N0720.N1396.d014786 m n hm hn theta hE
  have hclipC : MemLp (_root_.GD.N0232.N0720.N1396.d014779 m n theta (_root_.GD.N0232.N0720.N1396.d014781 m n e))
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply hC.mono
    · unfold _root_.GD.N0232.N0720.N1396.d014779 _root_.GD.N0232.N0720.N1396.d014778 _root_.GD.N0107.d012732
      exact ((_root_.GD.N0232.N0720.N1396.d014782 m n he).sub measurable_const).sub
        (by fun_prop) |>.aestronglyMeasurable
    · filter_upwards [] with w
      simpa only [Real.norm_eq_abs] using
        _root_.GD.N0232.N0720.N1396.d014789 m n hm hn theta e w
  have hsum := (_root_.GD.N0232.N0720.N1396.d014783 m n hm hn theta).add hclipC
  apply (memLp_congr_ae ?_).2 hsum
  filter_upwards [] with w
  unfold _root_.GD.N0232.N0720.N1396.d014779
  simp only [Pi.add_apply]
  ring


def d014791 (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ :=
  _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014779 m n theta e) -
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014779 m n theta (_root_.GD.N0232.N0720.N1396.d014781 m n e))

theorem d014792
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤) :
    0 ≤ _root_.GD.N0232.N0720.N1396.d014791 m n theta e := by
  have hE := _root_.GD.N0232.N0720.N1396.d014784 m n theta he hfinite
  have hC := _root_.GD.N0232.N0720.N1396.d014786 m n hm hn theta hE
  have hclipC := _root_.GD.N0232.N0720.N1396.d014786 m n hm hn theta
    (_root_.GD.N0232.N0720.N1396.d014790 m n hm hn theta he hE)
  unfold _root_.GD.N0232.N0720.N1396.d014791
  apply sub_nonneg.mpr
  unfold _root_.GD.N0141.d006684
  apply integral_mono hclipC.integrable_sq hC.integrable_sq
  intro w
  exact (sq_le_sq).2 (_root_.GD.N0232.N0720.N1396.d014789 m n hm hn theta e w)



theorem d014793
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (he : Measurable e)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ _root_.GD.N0232.N0720.N1396.d014781 m n e w - theta.location) -
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (fun w ↦ e w - theta.location) =
      -_root_.GD.N0232.N0720.N1396.d014791 m n theta e +
        2 * (_root_.GD.N0232.N0720.N1396.d014780 m n theta (_root_.GD.N0232.N0720.N1396.d014781 m n e) - _root_.GD.N0232.N0720.N1396.d014780 m n theta e) := by
  have hE := _root_.GD.N0232.N0720.N1396.d014784 m n theta he hfinite
  have hclipE := _root_.GD.N0232.N0720.N1396.d014790 m n hm hn theta he hE
  have hclipfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1396.d014781 m n e) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1396.d014785 m n theta hclipE]
    exact ENNReal.ofReal_ne_top
  have hraw := _root_.GD.N0232.N0720.N1396.d014787 m n hm hn theta he hfinite
  have hclip := _root_.GD.N0232.N0720.N1396.d014787 m n hm hn theta
    (_root_.GD.N0232.N0720.N1396.d014782 m n he) hclipfinite
  unfold _root_.GD.N0232.N0720.N1396.d014791
  linarith



theorem d014794
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) (hmu : theta.location = 0) :
    _root_.GD.N0232.N0720.N1396.d014780 m n theta (fun _ ↦ 0) =
      -_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014778 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1396.d014780 _root_.GD.N0141.d006684
  have hpoint : (fun w ↦ _root_.GD.N0232.N0720.N1396.d014778 m n theta w *
      _root_.GD.N0232.N0720.N1396.d014779 m n theta (fun _ ↦ 0) w) =
      (fun w ↦ -(_root_.GD.N0232.N0720.N1396.d014778 m n theta w ^ 2)) := by
    funext w
    unfold _root_.GD.N0232.N0720.N1396.d014779
    rw [hmu]
    ring
  rw [hpoint, integral_neg]



theorem d014795
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) (_root_.GD.N0232.N0720.N1396.d014778 m n theta) =
      _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
        _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂ *
        (1 - _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂) := by
  let t := _root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂
  let Sigma := _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂
  have ht0 : 0 < t := _root_.GD.N0107.d009050
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have ht1 : t < 1 := _root_.GD.N0107.d009051
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have hSigma : 0 < Sigma := _root_.GD.N0107.d009049
    (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have hLaw : HasLaw (_root_.GD.N0137.d008931 m n t) (gaussianReal 0 1)
      (_root_.GD.N0137.d008914 m n) := ⟨
    (_root_.GD.N0137.d008936 m n t).aemeasurable,
    _root_.GD.N0137.d008939 m n hm hn ht0.le ht1.le⟩
  have hSecond : (∫ w, _root_.GD.N0137.d008931 m n t w ^ 2 ∂_root_.GD.N0137.d008914 m n) = 1 := by
    have hvar : Var[_root_.GD.N0137.d008931 m n t; _root_.GD.N0137.d008914 m n] = 1 := by
      simpa using hLaw.variance_eq
    rw [variance_eq_integral (_root_.GD.N0137.d008936 m n t).aemeasurable,
      _root_.GD.N0137.d008941 m n hm hn ht0.le ht1.le] at hvar
    simpa only [sub_zero] using hvar
  have hPhysical : (∫ w, _root_.GD.N0137.d008945 m n t Sigma w ^ 2 ∂_root_.GD.N0137.d008914 m n) =
      Sigma * t * (1 - t) := by
    calc
      (∫ w, _root_.GD.N0137.d008945 m n t Sigma w ^ 2 ∂_root_.GD.N0137.d008914 m n) =
          ∫ w, (Sigma * t * (1 - t)) * _root_.GD.N0137.d008931 m n t w ^ 2
            ∂_root_.GD.N0137.d008914 m n := by
        apply integral_congr_ae
        filter_upwards [] with w
        unfold _root_.GD.N0137.d008945
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      _ = Sigma * t * (1 - t) := by
        rw [integral_const_mul, hSecond, mul_one]
  let f : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ :=
    fun w ↦ _root_.GD.N0137.d008945 m n t Sigma w ^ 2
  have hpull := _root_.GD.N0107.d012742
    (P := _root_.GD.N0107.d009030 m n theta.location theta.scale₁ theta.scale₂)
    (Q := _root_.GD.N0137.d008914 m n)
    (S := _root_.GD.N0107.d009025 m n theta.location theta.scale₁ theta.scale₂)
    (f := f)
    (_root_.GD.N0107.d009027 m n theta.location theta.scale₁ theta.scale₂)
    (show Measurable f by unfold f _root_.GD.N0137.d008945; fun_prop)
    (_root_.GD.N0107.d009031 m n theta.location
      theta.scale₁ theta.scale₂ theta.scale₁_pos.ne' theta.scale₂_pos.ne')
  rw [hPhysical] at hpull
  have hOracle : _root_.GD.N0107.d012738 m n theta.location theta.scale₁ theta.scale₂
      t Sigma = _root_.GD.N0107.d012732 m n theta.location t := by
    funext w
    exact _root_.GD.N0107.d012740 m n hm hn theta.location
      theta.scale₁ theta.scale₂ theta.scale₁_pos theta.scale₂_pos w
  unfold _root_.GD.N0141.d006684 _root_.GD.N0232.N0720.N1396.d014778 _root_.GD.N0232.N0720.N1080.d014171
  rw [← hOracle]
  simpa only [_root_.GD.N0107.d012738, Function.comp_apply, f, t, Sigma] using hpull



theorem d014796
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1396.d014780 m n _root_.GD.N0232.N0720.N1080.d014169 (fun _ ↦ 0) =
      -(1 / ((m : ℝ) + (n : ℝ))) := by
  rw [_root_.GD.N0232.N0720.N1396.d014794 m n _root_.GD.N0232.N0720.N1080.d014169 rfl,
    _root_.GD.N0232.N0720.N1396.d014795 m n hm hn _root_.GD.N0232.N0720.N1080.d014169]
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hV : (0 : ℝ) < 1 / (m : ℝ) + 1 / (n : ℝ) := by positivity
  simp only [_root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0107.d009046,
    _root_.GD.N0107.d009045,
    _root_.GD.N0107.d009043,
    _root_.GD.N0107.d009044, one_pow]
  field_simp [hmR.ne', hnR.ne', hV.ne', (add_pos hmR hnR).ne']
  ring

theorem d014797
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1396.d014780 m n _root_.GD.N0232.N0720.N1080.d014169 (fun _ ↦ 0) < 0 := by
  rw [_root_.GD.N0232.N0720.N1396.d014796 m n hm hn]
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact neg_neg_of_pos (one_div_pos.mpr (add_pos hmR hnR))

end
end GD.N0232.N0720.N1396

#print axioms _root_.GD.N0232.N0720.N1396.d014771
#print axioms _root_.GD.N0232.N0720.N1396.d014772
#print axioms _root_.GD.N0232.N0720.N1396.d014777
#print axioms _root_.GD.N0232.N0720.N1396.d014787
#print axioms _root_.GD.N0232.N0720.N1396.d014788
#print axioms _root_.GD.N0232.N0720.N1396.d014790
#print axioms _root_.GD.N0232.N0720.N1396.d014792
#print axioms _root_.GD.N0232.N0720.N1396.d014793
#print axioms _root_.GD.N0232.N0720.N1396.d014794

#print axioms _root_.GD.N0232.N0720.N1396.d014795
#print axioms _root_.GD.N0232.N0720.N1396.d014796
#print axioms _root_.GD.N0232.N0720.N1396.d014797
