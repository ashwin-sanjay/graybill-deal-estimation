import GD.Module1319
import GD.Module1741














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace GD.N0106.N0428.N0765.N1676
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672
open _root_.GD.N0106.N0428.N0765.N1528 _root_.GD.N0106.N0428.N0765.N1661 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521
open _root_.GD.N0106.N0428.N0765.N1584 _root_.GD.N0106.N0428.N0765.N1675
open _root_.GD.N0106.N0428.N0765.N1585


def d028908 (e a b α β : ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β

def d028909 (e b β : ℝ) : ℂ :=
  Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I) /
    (1 + (e : ℂ) * Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I))

def d028910 (e a b α β : ℝ) : ℂ :=
  (_root_.GD.N0106.N0428.N0765.N1676.d028909 e b β - (((1 + e)⁻¹ : ℝ) : ℂ)) ^ 2 -
    (_root_.GD.N0106.N0428.N0765.N1676.d028908 e a b α β - (((1 + e)⁻¹ : ℝ) : ℂ)) ^ 2

def d028911 (e a b α β : ℝ) : ℂ :=
  (((1 + e) / 11 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1676.d028910 e a b α β

abbrev d028912 (α β : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1675.d021511 α β

def d028913 (C B : ℝ) : ℝ :=
  (1 + C ^ 2) * B ^ 2 + 2 * (1 + C) * B

def d028914 (C : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1676.d028913 C (Real.exp p.2)

def d028915 (C : ℝ) : ℝ :=
  (5 / 2 : ℝ) * (1 + C ^ 2) + (5 / 2 : ℝ) * (1 + C)

theorem d028916 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 ≤ Real.cos β := by
  exact (Real.cos_pos_of_mem_Ioo (abs_lt.mp (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2)).le


theorem d028917 {e : ℝ} (he : 0 ≤ e) (b β : ℝ)
    (hβ : 0 ≤ Real.cos β) : ‖_root_.GD.N0106.N0428.N0765.N1676.d028909 e b β‖ ≤ Real.exp b := by
  let z : ℂ := Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I)
  have hzre : z.re = Real.exp b * Real.cos β := by
    simp [z, Complex.exp_re]
  have hdre : 1 ≤ (1 + (e : ℂ) * z).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hzre]
    exact le_add_of_nonneg_right (mul_nonneg he (mul_nonneg (Real.exp_pos b).le hβ))
  have hd : 1 ≤ ‖1 + (e : ℂ) * z‖ := hdre.trans (Complex.re_le_norm _)
  have hz : ‖z‖ = Real.exp b := by simp [z, Complex.norm_exp]
  change ‖z / (1 + (e : ℂ) * z)‖ ≤ Real.exp b
  rw [norm_div, hz]
  exact (div_le_iff₀ (zero_lt_one.trans_le hd)).2
    (by nlinarith [Real.exp_pos b])


theorem d028918 (g h : ℂ) {o B C : ℝ}
    (ho : |o| ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : ‖g‖ ≤ B) (hh : ‖h‖ ≤ C * B) :
    ‖(g - (o : ℂ)) ^ 2 - (h - (o : ℂ)) ^ 2‖ ≤ _root_.GD.N0106.N0428.N0765.N1676.d028913 C B := by
  have hid : (g - (o : ℂ)) ^ 2 - (h - (o : ℂ)) ^ 2 =
      (g ^ 2 - h ^ 2) - (2 : ℂ) * (o : ℂ) * (g - h) := by ring
  rw [hid]
  calc
    ‖g ^ 2 - h ^ 2 - 2 * (o : ℂ) * (g - h)‖
        ≤ ‖g ^ 2 - h ^ 2‖ + ‖2 * (o : ℂ) * (g - h)‖ := norm_sub_le _ _
    _ ≤ (‖g‖ ^ 2 + ‖h‖ ^ 2) + 2 * |o| * (‖g‖ + ‖h‖) := by
      apply add_le_add
      · calc
          ‖g ^ 2 - h ^ 2‖ ≤ ‖g ^ 2‖ + ‖h ^ 2‖ := norm_sub_le _ _
          _ = ‖g‖ ^ 2 + ‖h‖ ^ 2 := by rw [norm_pow, norm_pow]
      · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_sub_le g h) (by positivity)
    _ ≤ (B ^ 2 + (C * B) ^ 2) + 2 * 1 * (B + C * B) := by gcongr
    _ = _root_.GD.N0106.N0428.N0765.N1676.d028913 C B := by unfold _root_.GD.N0106.N0428.N0765.N1676.d028913; ring

theorem d028919 {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1676.d028913 C B := by unfold _root_.GD.N0106.N0428.N0765.N1676.d028913; positivity


theorem d028920 {e : ℝ} (he : 0 ≤ e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1676.d028910 e a b α β‖ ≤
      _root_.GD.N0106.N0428.N0765.N1676.d028913 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) (Real.exp b) := by
  have ho0 : 0 ≤ (1 + e)⁻¹ := inv_nonneg.mpr (by linarith)
  have ho1 : (1 + e)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  exact _root_.GD.N0106.N0428.N0765.N1676.d028918 _ _ (by rwa [abs_of_nonneg ho0])
    (Real.exp_pos b).le (_root_.GD.N0106.N0428.N0765.N1675.d021512 hw).le
    (_root_.GD.N0106.N0428.N0765.N1676.d028917 he b β (_root_.GD.N0106.N0428.N0765.N1676.d028916 hw)) (_root_.GD.N0106.N0428.N0765.N1675.d021513 he α β hw (a, b))

theorem d028921 {e E : ℝ} (he : 0 ≤ e) (heE : e ≤ E)
    (a b α β : ℝ) (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1676.d028911 e a b α β‖ ≤
      ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028913 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) (Real.exp b) := by
  rw [_root_.GD.N0106.N0428.N0765.N1676.d028911, norm_mul, Complex.norm_of_nonneg (by positivity)]
  exact mul_le_mul (by linarith) (_root_.GD.N0106.N0428.N0765.N1676.d028920 he a b α β hw)
    (norm_nonneg _) (by linarith)


theorem d028922 (C : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1676.d028914 C) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul (1 + C ^ 2)).add
    (_root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul (2 * (1 + C)))
  exact h.congr (Filter.Eventually.of_forall fun p => by
    change (1 + C ^ 2) * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2 ^ 2) +
      2 * (1 + C) * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) = _root_.GD.N0106.N0428.N0765.N1676.d028914 C p
    unfold _root_.GD.N0106.N0428.N0765.N1676.d028914 _root_.GD.N0106.N0428.N0765.N1676.d028913
    ring)

theorem d028923 (C : ℝ) :
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1676.d028914 C p) = _root_.GD.N0106.N0428.N0765.N1676.d028915 C := by
  have hfun : _root_.GD.N0106.N0428.N0765.N1676.d028914 C = fun p : ℝ × ℝ =>
      (1 + C ^ 2) * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2) ^ 2) +
        (2 * (1 + C)) * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) := by
    funext p
    unfold _root_.GD.N0106.N0428.N0765.N1676.d028914 _root_.GD.N0106.N0428.N0765.N1676.d028913
    ring
  rw [hfun, integral_add (_root_.GD.N0106.N0428.N0765.N1584.d021373.const_mul _) (_root_.GD.N0106.N0428.N0765.N1584.d021372.const_mul _),
    integral_const_mul, integral_const_mul, _root_.GD.N0106.N0428.N0765.N1584.d021375, _root_.GD.N0106.N0428.N0765.N1584.d021374]
  unfold _root_.GD.N0106.N0428.N0765.N1676.d028915
  ring

theorem d028924 (e α β : ℝ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1676.d028910 e p.1 p.2 α β) := by
  have hg : Measurable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1676.d028909 e p.2 β) := by unfold _root_.GD.N0106.N0428.N0765.N1676.d028909; fun_prop
  exact ((hg.sub measurable_const).pow_const 2).sub
    (((_root_.GD.N0106.N0428.N0765.N1675.d021518 e α β).sub measurable_const).pow_const 2)


theorem d028925 {e : ℝ} (he : 0 ≤ e) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Integrable (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1676.d028910 e p.1 p.2 α β) := by
  have hm : Measurable (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1676.d028910 e p.1 p.2 α β) :=
    (Complex.measurable_ofReal.comp _root_.GD.N0106.N0428.N0765.N1584.d021369).mul
      (_root_.GD.N0106.N0428.N0765.N1676.d028924 e α β)
  refine Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1676.d028922 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β))
    hm.aestronglyMeasurable ?_
  filter_upwards with p
  rw [norm_mul, Complex.norm_of_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1676.d028920 he p.1 p.2 α β hw)
    (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)


theorem d028926 {e : ℝ} (he : 0 ≤ e) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p : ℝ × ℝ, ‖(_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) * _root_.GD.N0106.N0428.N0765.N1676.d028910 e p.1 p.2 α β‖) ≤
      _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1676.d028923]
  apply integral_mono (_root_.GD.N0106.N0428.N0765.N1676.d028925 he α β hw).norm
    (_root_.GD.N0106.N0428.N0765.N1676.d028922 _)
  intro p
  change ‖(_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) * _root_.GD.N0106.N0428.N0765.N1676.d028910 e p.1 p.2 α β‖ ≤
    _root_.GD.N0106.N0428.N0765.N1676.d028914 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) p
  rw [norm_mul, Complex.norm_of_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1676.d028920 he p.1 p.2 α β hw)
    (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)

theorem d028927 {e : ℝ} (he : 0 ≤ e) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Integrable (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1676.d028911 e p.1 p.2 α β) := by
  have hi := (_root_.GD.N0106.N0428.N0765.N1676.d028925 he α β hw).const_mul
    (((1 + e) / 11 : ℝ) : ℂ)
  simpa only [_root_.GD.N0106.N0428.N0765.N1676.d028911, mul_left_comm] using hi


theorem d028928 {e E : ℝ}
    (he : 0 ≤ e) (heE : e ≤ E) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p : ℝ × ℝ, ‖(_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1676.d028911 e p.1 p.2 α β‖) ≤
      ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) := by
  have hpoint (p : ℝ × ℝ) :
      ‖(_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) * _root_.GD.N0106.N0428.N0765.N1676.d028911 e p.1 p.2 α β‖ ≤
        ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028914 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) p := by
    rw [norm_mul, Complex.norm_of_nonneg (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)]
    have h := mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1676.d028921 he heE p.1 p.2 α β hw)
      (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)
    simpa only [_root_.GD.N0106.N0428.N0765.N1676.d028914, mul_left_comm] using h
  calc
    _ ≤ ∫ p : ℝ × ℝ, ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028914 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) p :=
      integral_mono (_root_.GD.N0106.N0428.N0765.N1676.d028927 he α β hw).norm
        ((_root_.GD.N0106.N0428.N0765.N1676.d028922 _).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1676.d028923]



abbrev d028929 (α β : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1537.d021527 α β p

abbrev d028930 (α β : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1537.d021528 α β

def d028931 (e α β : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1676.d028929 α β p * _root_.GD.N0106.N0428.N0765.N1676.d028911 e p.1 p.2 α β


theorem d028932 (e α β : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p = (((1 + e) / 11 : ℝ) : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p := by
  unfold _root_.GD.N0106.N0428.N0765.N1676.d028931 _root_.GD.N0106.N0428.N0765.N1676.d028911 _root_.GD.N0106.N0428.N0765.N1676.d028910 _root_.GD.N0106.N0428.N0765.N1676.d028909 _root_.GD.N0106.N0428.N0765.N1676.d028908
    _root_.GD.N0106.N0428.N0765.N1537.d021532 _root_.GD.N0106.N0428.N0765.N1537.d021530
    _root_.GD.N0106.N0428.N0765.N1537.d021531 _root_.GD.N0106.N0428.N0765.N1537.d021524
    _root_.GD.N0106.N0428.N0765.N1675.d021510
  ring


theorem d028933 {e E : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (p : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1676.d028930 α β * ((1 + E) / 11)) * _root_.GD.N0106.N0428.N0765.N1676.d028914 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) p := by
  have hd := _root_.GD.N0106.N0428.N0765.N1537.d021539 hw p
  have hf := _root_.GD.N0106.N0428.N0765.N1676.d028921 he heE p.1 p.2 α β hw
  have hnonneg : 0 ≤ _root_.GD.N0106.N0428.N0765.N1676.d028930 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 p :=
    mul_nonneg (_root_.GD.N0106.N0428.N0765.N1537.d021537 hw).le (_root_.GD.N0106.N0428.N0765.N1584.d021368 p)
  have h := mul_le_mul hd hf (norm_nonneg _) hnonneg
  rw [← norm_mul] at h
  change ‖_root_.GD.N0106.N0428.N0765.N1537.d021527 α β p * _root_.GD.N0106.N0428.N0765.N1676.d028911 e p.1 p.2 α β‖ ≤ _
  calc
    _ ≤ (_root_.GD.N0106.N0428.N0765.N1676.d028930 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 p) *
        (((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028913 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) (Real.exp p.2)) := h
    _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1676.d028914; ring

theorem d028934 {e : ℝ} (he : 0 ≤ e) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : Integrable (_root_.GD.N0106.N0428.N0765.N1676.d028931 e α β) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1537.d021550 he hw).const_mul
    (((1 + e) / 11 : ℝ) : ℂ)
  exact h.congr (Filter.Eventually.of_forall fun p => (_root_.GD.N0106.N0428.N0765.N1676.d028932 e α β p).symm)


theorem d028935 {e E : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p‖) ≤
      _root_.GD.N0106.N0428.N0765.N1676.d028930 α β * ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) := by
  calc
    _ ≤ ∫ p : ℝ × ℝ, (_root_.GD.N0106.N0428.N0765.N1676.d028930 α β * ((1 + E) / 11)) *
        _root_.GD.N0106.N0428.N0765.N1676.d028914 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) p :=
      integral_mono (_root_.GD.N0106.N0428.N0765.N1676.d028934 he α β hw).norm
        ((_root_.GD.N0106.N0428.N0765.N1676.d028922 _).const_mul _) (_root_.GD.N0106.N0428.N0765.N1676.d028933 he heE α β hw)
    _ = _ := by rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1676.d028923]

theorem d028936 (e α β : ℝ) :
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p) = _root_.GD.N0106.N0428.N0765.N1680.d021557 e α β := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1676.d028932]
  rw [integral_const_mul]
  rfl

def d028937 (α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1676.d028930 α β * _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β)


theorem d028938 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1676.d028937 α β + 2 * _root_.GD.N0106.N0428.N0765.N1676.d028930 α β ≤ _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005527 (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2
  have hg : 1 ≤ _root_.GD.N0106.N0428.N0765.N1537.d021529 β := by
    exact (one_le_inv₀ hc).2 (Real.cos_le_one _)
  have hgsq : 1 ≤ (_root_.GD.N0106.N0428.N0765.N1537.d021529 β) ^ 2 := by
    nlinarith [sq_nonneg (_root_.GD.N0106.N0428.N0765.N1537.d021529 β - 1)]
  have hdiff : _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) + 2 ≤
      (5 / 2) * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β) ^ 2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β) ^ 2) +
        (5 / 2) * (_root_.GD.N0106.N0428.N0765.N1537.d021529 β + _root_.GD.N0106.N0428.N0765.N1675.d021511 α β) + 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1676.d028915 _root_.GD.N0106.N0428.N0765.N1676.d028912
    nlinarith
  have h := mul_le_mul_of_nonneg_left hdiff (_root_.GD.N0106.N0428.N0765.N1537.d021537 hw).le
  unfold _root_.GD.N0106.N0428.N0765.N1676.d028937 _root_.GD.N0106.N0428.N0765.N1537.d021534
  nlinarith only [h]

theorem d028939 {α β : ℝ}
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1676.d028937 α β < _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  have h := _root_.GD.N0106.N0428.N0765.N1676.d028938 hw
  have hp : 0 < _root_.GD.N0106.N0428.N0765.N1676.d028930 α β := _root_.GD.N0106.N0428.N0765.N1537.d021537 hw
  linarith

theorem d028940 : _root_.GD.N0106.N0428.N0765.N1676.d028937 0 0 = 115 / 8 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1676.d028937, _root_.GD.N0106.N0428.N0765.N1676.d028930, _root_.GD.N0106.N0428.N0765.N1537.d021528,
    _root_.GD.N0106.N0428.N0765.N1676.d028915, _root_.GD.N0106.N0428.N0765.N1676.d028912, _root_.GD.N0106.N0428.N0765.N1675.d021511, _root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1538.d021231]


theorem d028941 {e E : ℝ} (he : 0 ≤ e) (heE : e ≤ E)
    (α β : ℝ) (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1680.d021557 e α β‖ ≤ ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028937 α β := by
  rw [← _root_.GD.N0106.N0428.N0765.N1676.d028936]
  have h := (norm_integral_le_integral_norm (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p)).trans
    (_root_.GD.N0106.N0428.N0765.N1676.d028935 he heE α β hw)
  simpa only [_root_.GD.N0106.N0428.N0765.N1676.d028937, mul_assoc, mul_left_comm] using h

theorem d028942 {e α β : ℝ}
    (he : e ∈ Icc (0 : ℝ) (1 / 50))
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1680.d021557 e α β‖ ≤ (51 / 550) * _root_.GD.N0106.N0428.N0765.N1676.d028937 α β := by
  convert _root_.GD.N0106.N0428.N0765.N1676.d028941 he.1 he.2 α β hw using 1 <;> norm_num


theorem d028943 (e : ℝ) (z w : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1676.d028911 e z.re w.re z.im w.im =
      _root_.GD.N0106.N0428.N0765.N1677.d028897 e z w := by
  simp only [_root_.GD.N0106.N0428.N0765.N1676.d028911, _root_.GD.N0106.N0428.N0765.N1676.d028910, _root_.GD.N0106.N0428.N0765.N1676.d028909, _root_.GD.N0106.N0428.N0765.N1676.d028908,
    _root_.GD.N0106.N0428.N0765.N1677.d028897, _root_.GD.N0106.N0428.N0765.N1677.d028890,
    _root_.GD.N0106.N0428.N0765.N1677.d028883, _root_.GD.N0106.N0428.N0765.N1677.d028891, one_div,
    Complex.re_add_im]


def d028944 (e : ℝ) (z w : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z * _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 w *
    _root_.GD.N0106.N0428.N0765.N1677.d028897 e z w

theorem d028945 (e α β : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1676.d028931 e α β p =
      _root_.GD.N0106.N0428.N0765.N1676.d028944 e ((p.1 : ℂ) + (α : ℂ) * Complex.I)
        ((p.2 : ℂ) + (β : ℂ) * Complex.I) := by
  have h := _root_.GD.N0106.N0428.N0765.N1676.d028943 e
    ((p.1 : ℂ) + (α : ℂ) * Complex.I) ((p.2 : ℂ) + (β : ℂ) * Complex.I)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add, Complex.add_re, Complex.mul_I_re, neg_zero, add_zero] at h
  simp only [_root_.GD.N0106.N0428.N0765.N1676.d028931, _root_.GD.N0106.N0428.N0765.N1676.d028929, _root_.GD.N0106.N0428.N0765.N1537.d021527,
    _root_.GD.N0106.N0428.N0765.N1537.d021524, _root_.GD.N0106.N0428.N0765.N1676.d028944, h]

theorem d028946 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1676.d028944 e q w) z := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).1
  have hd := (_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (3 : ℝ) / 2) (b := 10)
    (by norm_num) (by norm_num)) z hphase
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hda := hd.differentiableAt (hopen.mem_nhds hphase)
  exact (hda.mul_const (_root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 w)).mul
    (_root_.GD.N0106.N0428.N0765.N1677.d028901 he hw).differentiableAt

theorem d028947 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hw : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1676.d028944 e z q) w := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2
  have hd := (_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (5 : ℝ)) (b := 5)
    (by norm_num) (by norm_num)) w hphase
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hda := hd.differentiableAt (hopen.mem_nhds hphase)
  exact (hda.const_mul (_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z)).mul
    (_root_.GD.N0106.N0428.N0765.N1677.d028902 he hw).differentiableAt


theorem d028948 {e E : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1676.d028944 e ((p.1 : ℂ) + (α : ℂ) * Complex.I)
      ((p.2 : ℂ) + (β : ℂ) * Complex.I)‖) ≤
      _root_.GD.N0106.N0428.N0765.N1676.d028930 α β * ((1 + E) / 11) * _root_.GD.N0106.N0428.N0765.N1676.d028915 (_root_.GD.N0106.N0428.N0765.N1676.d028912 α β) := by
  simp_rw [← _root_.GD.N0106.N0428.N0765.N1676.d028945]
  exact _root_.GD.N0106.N0428.N0765.N1676.d028935 he heE α β hw

end
end GD.N0106.N0428.N0765.N1676
