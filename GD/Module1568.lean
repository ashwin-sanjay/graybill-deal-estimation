import GD.Module0445
import GD.Module1565








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open Set
open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0770.N1725
namespace GD.N0106.N0428.N0770.N1719
noncomputable section

def d024260 (x : ℚ) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨x, x⟩
def d024261 (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0232.N0720.N1164.d006809.d006811.d006813 I

theorem d024262 (x : ℚ) : (_root_.GD.N0106.N0428.N0770.N1719.d024260 x).d006810 (x : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem d024263 {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ} (h : I.d006810 x) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024261 I).d006810 (1 - x) :=
  _root_.GD.N0232.N0720.N1164.d006809.d006820 _root_.GD.N0232.N0720.N1164.d006809.d006818 h


def d024264 (q e F : ℚ) : ℚ := e + (1 - 2 * e + F) * q - F * q ^ 2

def d024265 (e F : ℚ) : ℚ := (1 - 2 * e + F) / (2 * F)

def d024266 (I : _root_.GD.N0232.N0720.N1164.d006809) (e F : ℚ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  let na := _root_.GD.N0106.N0428.N0770.N1719.d024264 I.lo e F
  let nb := _root_.GD.N0106.N0428.N0770.N1719.d024264 I.hi e F
  let nv := _root_.GD.N0106.N0428.N0770.N1719.d024264 (_root_.GD.N0106.N0428.N0770.N1719.d024265 e F) e F
  ⟨min na nb, if I.lo ≤ _root_.GD.N0106.N0428.N0770.N1719.d024265 e F ∧ _root_.GD.N0106.N0428.N0770.N1719.d024265 e F ≤ I.hi
    then max (max na nb) nv else max na nb⟩

theorem d024267 (q e F : ℚ) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024264 q e F : ℝ) = _root_.GD.N0106.N0428.N0770.N1725.d024169 (q : ℝ) (e : ℝ) (F : ℝ) := by
  norm_num [_root_.GD.N0106.N0428.N0770.N1719.d024264, _root_.GD.N0106.N0428.N0770.N1725.d024169]

theorem d024268 {e F : ℚ} (hF : 0 < F) :
    2 * (F : ℝ) * (_root_.GD.N0106.N0428.N0770.N1719.d024265 e F : ℝ) = 1 - 2 * (e : ℝ) + (F : ℝ) := by
  have hFR : (F : ℝ) ≠ 0 := by exact_mod_cast hF.ne'
  norm_num [_root_.GD.N0106.N0428.N0770.N1719.d024265]
  field_simp [hFR]
  <;> ring


theorem d024269 {a b q e F : ℝ} (ha : a ≤ q) (hb : q ≤ b)
    (hF : 0 ≤ F) : min (_root_.GD.N0106.N0428.N0770.N1725.d024169 a e F) (_root_.GD.N0106.N0428.N0770.N1725.d024169 b e F) ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
  by_cases hab : a = b
  · have hq : q = a := by linarith
    simp [hq, hab]
  · have hd : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (ha.trans hb) hab)
    let m := min (_root_.GD.N0106.N0428.N0770.N1725.d024169 a e F) (_root_.GD.N0106.N0428.N0770.N1725.d024169 b e F)
    have hma : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 a e F - m := sub_nonneg.mpr (min_le_left _ _)
    have hmb : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 b e F - m := sub_nonneg.mpr (min_le_right _ _)
    have hid : (b - a) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F - m) =
        (b - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 a e F - m) + (q - a) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 b e F - m) +
          F * (b - a) * (q - a) * (b - q) := by
      unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
      ring
    have hpos : 0 ≤ (b - a) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F - m) := by
      rw [hid]
      exact add_nonneg (add_nonneg
        (mul_nonneg (sub_nonneg.mpr hb) hma)
        (mul_nonneg (sub_nonneg.mpr ha) hmb))
        (mul_nonneg (mul_nonneg (mul_nonneg hF hd.le) (sub_nonneg.mpr ha))
          (sub_nonneg.mpr hb))
    dsimp [m] at hpos
    nlinarith


theorem d024270 {q e F v : ℝ} (hF : 0 ≤ F)
    (hv : 2 * F * v = 1 - 2 * e + F) : _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 v e F := by
  have hid : _root_.GD.N0106.N0428.N0770.N1725.d024169 v e F - _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F = F * (q - v) ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    simp only [← hv]
    ring
  have h := mul_nonneg hF (sq_nonneg (q - v))
  rw [← hid] at h
  exact sub_nonneg.mp h


theorem d024271 {a q e F v : ℝ} (ha : a ≤ q) (hvle : v ≤ a)
    (hF : 0 ≤ F) (hv : 2 * F * v = 1 - 2 * e + F) :
    _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 a e F := by
  have hid : _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F - _root_.GD.N0106.N0428.N0770.N1725.d024169 a e F = F * (q - a) * (2 * v - a - q) := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    simp only [← hv]
    ring
  have h := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hF (sub_nonneg.mpr ha)) (show 2 * v - a - q ≤ 0 by linarith)
  rw [← hid] at h
  exact sub_nonpos.mp h


theorem d024272 {b q e F v : ℝ} (hb : q ≤ b) (hvle : b ≤ v)
    (hF : 0 ≤ F) (hv : 2 * F * v = 1 - 2 * e + F) :
    _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 b e F := by
  have hid : _root_.GD.N0106.N0428.N0770.N1725.d024169 b e F - _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F = F * (b - q) * (2 * v - b - q) := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    simp only [← hv]
    ring
  have h := mul_nonneg (mul_nonneg hF (sub_nonneg.mpr hb))
    (show 0 ≤ 2 * v - b - q by linarith)
  rw [← hid] at h
  exact sub_nonneg.mp h


theorem d024273 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ} (e F : ℚ)
    (hF : 0 < F) (hq : I.d006810 q) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024266 I e F).d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024169 q (e : ℝ) (F : ℝ)) := by
  have hFR : (0 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF.le
  have hv := _root_.GD.N0106.N0428.N0770.N1719.d024268 (e := e) hF
  constructor
  · change ((min (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.lo e F) (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.hi e F) : ℚ) : ℝ) ≤ _
    push_cast
    rw [_root_.GD.N0106.N0428.N0770.N1719.d024267, _root_.GD.N0106.N0428.N0770.N1719.d024267]
    exact _root_.GD.N0106.N0428.N0770.N1719.d024269 hq.1 hq.2 hFR
  · by_cases hin : I.lo ≤ _root_.GD.N0106.N0428.N0770.N1719.d024265 e F ∧ _root_.GD.N0106.N0428.N0770.N1719.d024265 e F ≤ I.hi
    · simp only [_root_.GD.N0106.N0428.N0770.N1719.d024266, if_pos hin]
      change _root_.GD.N0106.N0428.N0770.N1725.d024169 q (e : ℝ) (F : ℝ) ≤
        ((max (max (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.lo e F) (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.hi e F))
          (_root_.GD.N0106.N0428.N0770.N1719.d024264 (_root_.GD.N0106.N0428.N0770.N1719.d024265 e F) e F) : ℚ) : ℝ)
      push_cast
      rw [_root_.GD.N0106.N0428.N0770.N1719.d024267, _root_.GD.N0106.N0428.N0770.N1719.d024267, _root_.GD.N0106.N0428.N0770.N1719.d024267]
      exact (_root_.GD.N0106.N0428.N0770.N1719.d024270 hFR hv).trans (le_max_right _ _)
    · simp only [_root_.GD.N0106.N0428.N0770.N1719.d024266, if_neg hin]
      change _root_.GD.N0106.N0428.N0770.N1725.d024169 q (e : ℝ) (F : ℝ) ≤
        ((max (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.lo e F) (_root_.GD.N0106.N0428.N0770.N1719.d024264 I.hi e F) : ℚ) : ℝ)
      push_cast
      rw [_root_.GD.N0106.N0428.N0770.N1719.d024267, _root_.GD.N0106.N0428.N0770.N1719.d024267]
      by_cases ha : I.lo ≤ _root_.GD.N0106.N0428.N0770.N1719.d024265 e F
      · have hvb : I.hi < _root_.GD.N0106.N0428.N0770.N1719.d024265 e F := lt_of_not_ge (fun hb => hin ⟨ha, hb⟩)
        have hvbR : (I.hi : ℝ) ≤ (_root_.GD.N0106.N0428.N0770.N1719.d024265 e F : ℝ) := by exact_mod_cast hvb.le
        exact (_root_.GD.N0106.N0428.N0770.N1719.d024272 hq.2 hvbR hFR hv).trans (le_max_right _ _)
      · have hva : _root_.GD.N0106.N0428.N0770.N1719.d024265 e F ≤ I.lo := le_of_not_ge ha
        have hvaR : (_root_.GD.N0106.N0428.N0770.N1719.d024265 e F : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hva
        exact (_root_.GD.N0106.N0428.N0770.N1719.d024271 hq.1 hvaR hFR hv).trans (le_max_left _ _)


structure d024274 where
  q : _root_.GD.N0232.N0720.N1164.d006809
  e : _root_.GD.N0232.N0720.N1164.d006809
  f : _root_.GD.N0232.N0720.N1164.d006809

structure d024274.d024275 (B : _root_.GD.N0106.N0428.N0770.N1719.d024274) : Prop where
  qlo : 0 ≤ B.q.lo
  qorder : B.q.lo ≤ B.q.hi
  qhi : B.q.hi ≤ 1 / 2
  elo : 0 < B.e.lo
  eorder : B.e.lo ≤ B.e.hi
  ehi : B.e.hi < 1
  flo : 0 < B.f.lo
  forder : B.f.lo ≤ B.f.hi




def d024276 (B : _root_.GD.N0106.N0428.N0770.N1719.d024274) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ((B.e.d006812 B.q).d006813 ((B.e.d006814 B.q).d006817 2)).d006812
    (B.f.d006814 (B.q.d006814 (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.q)))

def d024277 (B : _root_.GD.N0106.N0428.N0770.N1719.d024274) : _root_.GD.N0232.N0720.N1164.d006809 :=
  (B.e.d006814 (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.e)).d006815 |>.d006814 B.f

theorem d024278 {B : _root_.GD.N0106.N0428.N0770.N1719.d024274} (h : B.d024275)
    {q e F : ℝ} (hq : B.q.d006810 q) (he : B.e.d006810 e) (hf : B.f.d006810 F) :
    q ∈ Icc (0 : ℝ) 1 ∧ e ∈ Ioo (0 : ℝ) 1 ∧ 0 < F := by
  have hq0 : (0 : ℝ) ≤ (B.q.lo : ℝ) := by exact_mod_cast h.qlo
  have hq1 : (B.q.hi : ℝ) ≤ 1 := by exact_mod_cast h.qhi.trans (by norm_num : (1 / 2 : ℚ) ≤ 1)
  have he0 : (0 : ℝ) < (B.e.lo : ℝ) := by exact_mod_cast h.elo
  have he1 : (B.e.hi : ℝ) < 1 := by exact_mod_cast h.ehi
  have hf0 : (0 : ℝ) < (B.f.lo : ℝ) := by exact_mod_cast h.flo
  exact ⟨⟨hq0.trans hq.1, hq.2.trans hq1⟩,
    ⟨he0.trans_le he.1, he.2.trans_lt he1⟩, hf0.trans_le hf.1⟩

theorem d024279 {B : _root_.GD.N0106.N0428.N0770.N1719.d024274} (h : B.d024275)
    {q e F : ℝ} (hq : B.q.d006810 q) (he : B.e.d006810 e) (hf : B.f.d006810 F) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024276 B).d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) := by
  have hqc : 0 ≤ (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.q).lo := by
    change 0 ≤ 1 - B.q.hi
    linarith [h.qhi]
  have hEq := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.elo.le h.qlo he hq
  have hTwo := _root_.GD.N0232.N0720.N1164.d006809.d006824 2 hEq
  have hLinear := _root_.GD.N0232.N0720.N1164.d006809.d006820 (_root_.GD.N0232.N0720.N1164.d006809.d006819 he hq) hTwo
  have hqprod := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.qlo hqc hq (_root_.GD.N0106.N0428.N0770.N1719.d024263 hq)
  have hFprod := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.flo.le (mul_nonneg h.qlo hqc) hf hqprod
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006819 hLinear hFprod
  have heq : e + q - ((2 : ℚ) : ℝ) * (e * q) + F * (q * (1 - q)) = _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
    norm_num only [Rat.cast_ofNat]
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    ring
  simpa only [_root_.GD.N0106.N0428.N0770.N1719.d024276, heq] using hs

theorem d024280 {B : _root_.GD.N0106.N0428.N0770.N1719.d024274} (h : B.d024275)
    {e F : ℝ} (he : B.e.d006810 e) (hf : B.f.d006810 F) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024277 B).d006810 (F / (e * (1 - e))) := by
  have hc : 0 ≤ (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.e).lo := by
    change 0 ≤ 1 - B.e.hi
    linarith [h.ehi]
  have hp := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.elo.le hc he (_root_.GD.N0106.N0428.N0770.N1719.d024263 he)
  have hlo : 0 < (B.e.d006814 (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.e)).lo := by
    change 0 < B.e.lo * (1 - B.e.hi)
    exact mul_pos h.elo (sub_pos.mpr h.ehi)
  have hhi : 0 < (B.e.d006814 (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.e)).hi := by
    change 0 < B.e.hi * (1 - B.e.lo)
    exact mul_pos (h.elo.trans_le h.eorder) (sub_pos.mpr (h.eorder.trans_lt h.ehi))
  have hi := _root_.GD.N0232.N0720.N1164.d006809.d006822 hlo hp
  have hi0 : 0 ≤ (B.e.d006814 (_root_.GD.N0106.N0428.N0770.N1719.d024261 B.e)).d006815.lo := by
    exact (one_div_pos.mpr hhi).le
  have hp' := _root_.GD.N0232.N0720.N1164.d006809.d006821 hi0 h.flo.le hi hf
  simpa only [_root_.GD.N0106.N0428.N0770.N1719.d024277, div_eq_mul_inv, mul_comm, one_mul] using hp'


structure d024281 where
  ratioRoot : _root_.GD.N0232.N0720.N1164.d006809
  nRoot : _root_.GD.N0232.N0720.N1164.d006809

structure d024281.d024282 (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) (J K : _root_.GD.N0232.N0720.N1164.d006809) : Prop where
  nlo : 0 < J.lo
  norder : J.lo ≤ J.hi
  ratioLo : 0 ≤ R.ratioRoot.lo
  ratioOrder : R.ratioRoot.lo ≤ R.ratioRoot.hi
  ratioLower : R.ratioRoot.lo ^ 2 ≤ K.lo
  ratioUpper : K.hi ≤ R.ratioRoot.hi ^ 2
  rootLo : 0 < R.nRoot.lo
  rootOrder : R.nRoot.lo ≤ R.nRoot.hi
  rootLower : R.nRoot.lo ^ 2 ≤ J.lo
  rootUpper : J.hi ≤ R.nRoot.hi ^ 2

def d024283 (J : _root_.GD.N0232.N0720.N1164.d006809) (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) : _root_.GD.N0232.N0720.N1164.d006809 :=
  R.ratioRoot.d006814 (((J.d006814 J).d006814 R.nRoot).d006815)

theorem d024284 {J K : _root_.GD.N0232.N0720.N1164.d006809} {R : _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (h : R.d024282 J K) : 0 ≤ (_root_.GD.N0106.N0428.N0770.N1719.d024283 J R).lo := by
  have hnhi : 0 < J.hi := h.nlo.trans_le h.norder
  have hrhi : 0 < R.nRoot.hi := h.rootLo.trans_le h.rootOrder
  change 0 ≤ R.ratioRoot.lo * (1 / ((J.hi * J.hi) * R.nRoot.hi))
  exact mul_nonneg h.ratioLo (one_div_nonneg.mpr
    (mul_nonneg (mul_nonneg hnhi.le hnhi.le) hrhi.le))


theorem d024285 {J K : _root_.GD.N0232.N0720.N1164.d006809} {R : _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (h : R.d024282 J K) {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) 1) (hf : 0 < F)
    (hN : J.d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)) (hK : K.d006810 (F / (e * (1 - e)))) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 J R).d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) := by
  have hroot := _root_.GD.N0232.N0720.N1164.d006827 hN h.rootLo.le h.rootOrder h.rootLower h.rootUpper
  have hratio := _root_.GD.N0232.N0720.N1164.d006827 hK h.ratioLo h.ratioOrder h.ratioLower h.ratioUpper
  have hsq := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.nlo.le h.nlo.le hN hN
  have hden := _root_.GD.N0232.N0720.N1164.d006809.d006821 (mul_nonneg h.nlo.le h.nlo.le) h.rootLo.le hsq hroot
  have hdlo : 0 < ((J.d006814 J).d006814 R.nRoot).lo := by
    exact mul_pos (mul_pos h.nlo h.nlo) h.rootLo
  have hdhi : 0 < ((J.d006814 J).d006814 R.nRoot).hi := by
    exact mul_pos (mul_pos (h.nlo.trans_le h.norder) (h.nlo.trans_le h.norder))
      (h.rootLo.trans_le h.rootOrder)
  have hinv := _root_.GD.N0232.N0720.N1164.d006809.d006822 hdlo hden
  have hinv0 : 0 ≤ ((J.d006814 J).d006814 R.nRoot).d006815.lo :=
    (one_div_pos.mpr hdhi).le
  have hp := _root_.GD.N0232.N0720.N1164.d006809.d006821 h.ratioLo hinv0 hratio hinv
  simpa only [_root_.GD.N0106.N0428.N0770.N1719.d024283, _root_.GD.N0106.N0428.N0770.N1725.d024174 hq he hf, pow_two, div_eq_mul_inv, one_mul] using hp


theorem d024286 {B : _root_.GD.N0106.N0428.N0770.N1719.d024274} (hB : B.d024275)
    {R : _root_.GD.N0106.N0428.N0770.N1719.d024281} (hR : R.d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024276 B) (_root_.GD.N0106.N0428.N0770.N1719.d024277 B))
    {q e F : ℝ} (hq : B.q.d006810 q) (he : B.e.d006810 e) (hf : B.f.d006810 F) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 (_root_.GD.N0106.N0428.N0770.N1719.d024276 B) R).d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) := by
  have h := _root_.GD.N0106.N0428.N0770.N1719.d024278 hB hq he hf
  exact _root_.GD.N0106.N0428.N0770.N1719.d024285 hR h.1 h.2.1 h.2.2
    (_root_.GD.N0106.N0428.N0770.N1719.d024279 hB hq he hf) (_root_.GD.N0106.N0428.N0770.N1719.d024280 hB he hf)


theorem d024287 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ}
    (e F : ℚ) (hq : q ∈ Icc (0 : ℝ) 1) (hI : I.d006810 q)
    (he0 : 0 < e) (he1 : e < 1) (hf : 0 < F)
    {R : _root_.GD.N0106.N0428.N0770.N1719.d024281} (hR : R.d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I e F)
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (F / (e * (1 - e))))) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I e F) R).d006810 (_root_.GD.N0106.N0428.N0770.N1725.d024170 q ((e : ℝ), (F : ℝ))) := by
  have he : (e : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast he0
    · exact_mod_cast he1
  have hfR : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hf
  have hK : (_root_.GD.N0106.N0428.N0770.N1719.d024260 (F / (e * (1 - e)))).d006810
      ((F : ℝ) / ((e : ℝ) * (1 - (e : ℝ)))) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] using
      _root_.GD.N0106.N0428.N0770.N1719.d024262 (F / (e * (1 - e)))
  exact _root_.GD.N0106.N0428.N0770.N1719.d024285 hR hq he hfR (_root_.GD.N0106.N0428.N0770.N1719.d024273 e F hf hI) hK

end
end GD.N0106.N0428.N0770.N1719

#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024262
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024263
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024267
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024268
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024269
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024270
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024271
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024272
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024273
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024278
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024279
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024280
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024284
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024285
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024286
#print axioms _root_.GD.N0106.N0428.N0770.N1719.d024287
