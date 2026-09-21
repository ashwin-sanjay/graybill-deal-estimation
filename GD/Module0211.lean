import GD.Module0208
import GD.Module0210
















open MeasureTheory Set

namespace GD.N0232.N0720.N1380

open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1378
open _root_.GD.N0232.N0720.N1376

noncomputable section



theorem d002920 (n : ℕ) {Alo Ahi blo bhi : ℝ}
    (hAlo : 0 < Alo) (hAhi : 0 < Ahi) (hA : Alo ≤ Ahi) (hb : blo ≤ bhi) :
    _root_.GD.N0232.N0720.N1377.d002852 n Ahi blo ≤ _root_.GD.N0232.N0720.N1377.d002852 n Alo bhi := by
  apply integral_mono_ae (_root_.GD.N0232.N0720.N1377.d002860 n hAhi blo)
    (_root_.GD.N0232.N0720.N1377.d002860 n hAlo bhi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  unfold _root_.GD.N0232.N0720.N1377.d002851
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le _)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg r),
    mul_nonneg (sub_nonneg.mpr hb) hr.le]


theorem d002921 {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    _root_.GD.N0232.N0720.N1377.d002852 3 A b / _root_.GD.N0232.N0720.N1377.d002852 5 A b ≤ A ^ 2 / b ^ 2 := by
  apply (div_le_div_iff₀ (_root_.GD.N0232.N0720.N1377.d002861 5 hA b) (sq_pos_of_pos hb)).2
  have h := _root_.GD.N0232.N0720.N1378.d002875 2 hA hb.le
  norm_num only [Nat.reduceAdd] at h
  nlinarith


theorem d002922 {A B : ℝ} (hA : 0 < A) (hB : B ≠ 0) (kappa : ℝ) :
    kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) =
      A / B - 4 * _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) /
        (B * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa)) := by
  have hI := (_root_.GD.N0232.N0720.N1377.d002861 5 hA (B * kappa)).ne'
  have hrec := _root_.GD.N0232.N0720.N1378.d002873 3 hA (B * kappa)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hrec
  generalize _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) = I3 at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) = I4 at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) = I5 at hI hrec ⊢
  field_simp [hB, hI]
  nlinarith [hrec]


theorem d002923 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (kappa : ℝ) :
    kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) < A / B := by
  rw [_root_.GD.N0232.N0720.N1380.d002922 hA hB.ne' kappa]
  have hrem : 0 < 4 * _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) /
      (B * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa)) :=
    div_pos (mul_pos (by norm_num) (_root_.GD.N0232.N0720.N1377.d002861 3 hA (B * kappa)))
      (mul_pos hB (_root_.GD.N0232.N0720.N1377.d002861 5 hA (B * kappa)))
  linarith


theorem d002924 {A B kappa : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hkappa : 0 < kappa) :
    A / B - 4 * A ^ 2 / (B ^ 3 * kappa ^ 2) ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) := by
  have hratio := _root_.GD.N0232.N0720.N1380.d002921 hA (mul_pos hB hkappa)
  have hrem := mul_le_mul_of_nonneg_left hratio
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB.le)
  have heq1 : (4 / B) *
      (_root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa)) =
      4 * _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) /
        (B * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa)) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have heq2 : (4 / B) * (A ^ 2 / (B * kappa) ^ 2) =
      4 * A ^ 2 / (B ^ 3 * kappa ^ 2) := by
    field_simp [hB.ne', hkappa.ne']
    <;> ring
  rw [heq1, heq2] at hrem
  rw [_root_.GD.N0232.N0720.N1380.d002922 hA hB.ne' kappa]
  linarith


theorem d002925 {A B Amax Bmin kappa : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 < kappa) :
    A / B - 4 * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) := by
  have hAmax : 0 < Amax := hA.trans_le hAupper
  have hB : 0 < B := hBmin.trans_le hBlower
  have hAsq : A ^ 2 ≤ Amax ^ 2 := (sq_le_sq₀ hA.le hAmax.le).2 hAupper
  have hBcube : Bmin ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hBmin.le hBlower 3
  have hrem : 4 * A ^ 2 / (B ^ 3 * kappa ^ 2) ≤
      4 * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) := by
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hAsq (by norm_num))
      (mul_pos (pow_pos hBmin 3) (sq_pos_of_pos hkappa))
      (mul_le_mul_of_nonneg_right hBcube (sq_nonneg kappa))
  have hlower := _root_.GD.N0232.N0720.N1380.d002924 hA hB hkappa
  linarith


theorem d002926 {A B Amax Bmin kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 < kappa) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    level + delta / 2 ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) := by
  have hrem : 4 * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) ≤ delta / 2 := by
    apply (div_le_iff₀ (mul_pos (pow_pos hBmin 3) (sq_pos_of_pos hkappa))).2
    nlinarith [hcutoff]
  have hlower := _root_.GD.N0232.N0720.N1380.d002925 hA hAupper hBmin hBlower hkappa
  linarith


theorem d002927 {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b) :
    b ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 A b ≤ A ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 5 A b := by
  have h1 := mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0720.N1378.d002875 0 hA hb) (sq_nonneg b)
  have h2 := mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0720.N1378.d002875 2 hA hb) (sq_nonneg A)
  norm_num only [Nat.reduceAdd] at h1 h2
  nlinarith


def d002928 (Amax Bmin : ℝ) : ℝ :=
  Bmin ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 Amax 0 / (8 * Amax ^ 4)

theorem d002929 {Amax Bmin : ℝ}
    (hAmax : 0 < Amax) (hBmin : 0 < Bmin) :
    0 < _root_.GD.N0232.N0720.N1380.d002928 Amax Bmin := by
  exact div_pos (mul_pos (pow_pos hBmin 4) (_root_.GD.N0232.N0720.N1377.d002861 1 hAmax 0))
    (mul_pos (by norm_num) (pow_pos hAmax 4))



theorem d002930 {A B Amax Bmin kappa : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 ≤ kappa) :
    _root_.GD.N0232.N0720.N1380.d002928 Amax Bmin * kappa ^ 4 ≤ _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8 := by
  have hAmax : 0 < Amax := hA.trans_le hAupper
  have hB : 0 < B := hBmin.trans_le hBlower
  have hb : 0 ≤ B * kappa := mul_nonneg hB.le hkappa
  have hIbase : _root_.GD.N0232.N0720.N1377.d002852 1 Amax 0 ≤ _root_.GD.N0232.N0720.N1377.d002852 1 A (B * kappa) :=
    _root_.GD.N0232.N0720.N1380.d002920 1 hA hAmax hAupper hb
  have hbasepos := _root_.GD.N0232.N0720.N1377.d002861 1 hAmax 0
  have hBpow : Bmin ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hBmin.le hBlower 4
  have hApow : A ^ 4 ≤ Amax ^ 4 := pow_le_pow_left₀ hA.le hAupper 4
  have hleft : Bmin ^ 4 * kappa ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 Amax 0 ≤
      (B * kappa) ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 A (B * kappa) := by
    calc
      Bmin ^ 4 * kappa ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 Amax 0 ≤
          B ^ 4 * kappa ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 Amax 0 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBpow (pow_nonneg hkappa 4)) hbasepos.le
      _ ≤ B ^ 4 * kappa ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 A (B * kappa) :=
        mul_le_mul_of_nonneg_left hIbase (by positivity)
      _ = (B * kappa) ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 1 A (B * kappa) := by ring
  have hright : A ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) ≤
      Amax ^ 4 * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) :=
    mul_le_mul_of_nonneg_right hApow (_root_.GD.N0232.N0720.N1377.d002861 5 hA (B * kappa)).le
  have hcomplete := hleft.trans ((_root_.GD.N0232.N0720.N1380.d002927 hA hb).trans hright)
  unfold _root_.GD.N0232.N0720.N1380.d002928
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀
    (mul_pos (by norm_num : (0 : ℝ) < 8) (pow_pos hAmax 4))
    (by norm_num : (0 : ℝ) < 8)).2
  nlinarith [hcomplete]


theorem d002931 {A B Amax Bmin kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 < kappa) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    delta / 2 * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8) ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / 8 -
        level * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8) := by
  have hratio := _root_.GD.N0232.N0720.N1380.d002926 hA hAupper hBmin hBlower
    hkappa hgeometry hcutoff
  have h := (le_div_iff₀ (_root_.GD.N0232.N0720.N1377.d002861 5 hA (B * kappa))).1 hratio
  nlinarith




theorem d002932 {A B Amax Bmin kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 < kappa) (hdelta : 0 ≤ delta) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    (delta / 2 * _root_.GD.N0232.N0720.N1380.d002928 Amax Bmin) * kappa ^ 4 ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / 8 -
        level * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8) := by
  calc
    (delta / 2 * _root_.GD.N0232.N0720.N1380.d002928 Amax Bmin) * kappa ^ 4 =
        delta / 2 * (_root_.GD.N0232.N0720.N1380.d002928 Amax Bmin * kappa ^ 4) := by ring
    _ ≤ delta / 2 * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8) :=
      mul_le_mul_of_nonneg_left
        (_root_.GD.N0232.N0720.N1380.d002930 hA hAupper hBmin hBlower hkappa.le)
        (by positivity)
    _ ≤ _ := _root_.GD.N0232.N0720.N1380.d002931 hA hAupper hBmin hBlower hkappa
      hgeometry hcutoff


theorem d002933
    (kappa t X Y z w Amax Bmin level delta : ℝ)
    (hA : 0 < _root_.GD.N0232.N0720.N1376.d002892 t X Y z w) (hAupper : _root_.GD.N0232.N0720.N1376.d002892 t X Y z w ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : Bmin ≤ _root_.GD.N0232.N0720.N1376.d002893 t X Y)
    (hkappa : 0 < kappa) (hdelta : 0 ≤ delta)
    (hgeometry : level + delta ≤ _root_.GD.N0232.N0720.N1376.d002892 t X Y z w / _root_.GD.N0232.N0720.N1376.d002893 t X Y)
    (hcutoff : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    (delta / 2 * _root_.GD.N0232.N0720.N1380.d002928 Amax Bmin) * kappa ^ 4 ≤
      _root_.GD.N0232.N0720.N1376.d002895 kappa t X Y z w - level * _root_.GD.N0232.N0720.N1376.d002894 kappa t X Y z w := by
  exact _root_.GD.N0232.N0720.N1380.d002932 hA hAupper hBmin hBlower hkappa hdelta
    hgeometry hcutoff

end

end GD.N0232.N0720.N1380

#print axioms _root_.GD.N0232.N0720.N1380.d002920
#print axioms _root_.GD.N0232.N0720.N1380.d002922
#print axioms _root_.GD.N0232.N0720.N1380.d002925
#print axioms _root_.GD.N0232.N0720.N1380.d002930
#print axioms _root_.GD.N0232.N0720.N1380.d002933
