import GD.Module0213













open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0720.N1324

open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1378
open _root_.GD.N0232.N0720.N1380 _root_.GD.N0232.N0720.N1374
open _root_.GD.N0232.N0720.N1385

noncomputable section

def d002945 (N : ℕ) (A B level kappa : ℝ) : ℝ :=
  kappa * _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) - level * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa)

def d002946 (N : ℕ) (Amax Bmin : ℝ) : ℝ :=
  (Bmin / Amax) ^ (N + 1) * Real.exp (-Amax / 2)

theorem d002947 (N : ℕ) {Amax Bmin : ℝ}
    (hAmax : 0 < Amax) (hBmin : 0 < Bmin) :
    0 < _root_.GD.N0232.N0720.N1324.d002946 N Amax Bmin := by
  unfold _root_.GD.N0232.N0720.N1324.d002946
  positivity

theorem d002948 (N : ℕ) (hN : 1 ≤ N) {A B : ℝ}
    (hA : 0 < A) (hB : B ≠ 0) (level kappa : ℝ) :
    _root_.GD.N0232.N0720.N1324.d002945 N A B level kappa =
      (A / B - level) * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) -
        (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) / B := by
  have hrec := _root_.GD.N0232.N0720.N1378.d002873 (N - 1) hA (B * kappa)
  rw [show N - 1 + 2 = N + 1 by omega, show N - 1 + 1 = N by omega] at hrec
  unfold _root_.GD.N0232.N0720.N1324.d002945
  generalize _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) = Iprev at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) = Icur at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) = Inext at hrec ⊢
  field_simp [hB]
  nlinarith [hrec]

theorem d002949 (N : ℕ) (hN : 2 ≤ N) {A b : ℝ}
    (hA : 0 < A) (hb : 0 < b) :
    _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A b / _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A b ≤ A ^ 2 / b ^ 2 := by
  apply (div_le_div_iff₀ (_root_.GD.N0232.N0720.N1377.d002861 (N + 1) hA b) (sq_pos_of_pos hb)).2
  have h := _root_.GD.N0232.N0720.N1378.d002875 (N - 2) hA hb.le
  rw [show N - 2 + 1 = N - 1 by omega, show N - 2 + 3 = N + 1 by omega] at h
  nlinarith

theorem d002950 (N : ℕ) (hN : 1 ≤ N) {A B : ℝ}
    (hA : 0 < A) (hB : B ≠ 0) (kappa : ℝ) :
    kappa * _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) =
      A / B - (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) /
        (B * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa)) := by
  have hI := (_root_.GD.N0232.N0720.N1377.d002861 (N + 1) hA (B * kappa)).ne'
  have hrec := _root_.GD.N0232.N0720.N1378.d002873 (N - 1) hA (B * kappa)
  rw [show N - 1 + 2 = N + 1 by omega, show N - 1 + 1 = N by omega] at hrec
  generalize _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) = Iprev at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) = Icur at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) = Inext at hI hrec ⊢
  field_simp [hB, hI]
  nlinarith [hrec]

theorem d002951 (N : ℕ) (hN : 2 ≤ N)
    {A B Amax Bmin kappa : ℝ} (hA : 0 < A) (hAupper : A ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B) (hkappa : 0 < kappa) :
    A / B - (N : ℝ) * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) := by
  have hAmax : 0 < Amax := hA.trans_le hAupper
  have hB : 0 < B := hBmin.trans_le hBlower
  have hratio := _root_.GD.N0232.N0720.N1324.d002949 N hN hA (mul_pos hB hkappa)
  have hrem := mul_le_mul_of_nonneg_left hratio
    (div_nonneg (Nat.cast_nonneg N) hB.le)
  have heq1 : ((N : ℝ) / B) *
      (_root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa)) =
      (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) /
        (B * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa)) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have heq2 : ((N : ℝ) / B) * (A ^ 2 / (B * kappa) ^ 2) =
      (N : ℝ) * A ^ 2 / (B ^ 3 * kappa ^ 2) := by
    field_simp [hB.ne', hkappa.ne']
  rw [heq1, heq2] at hrem
  have hAsq : A ^ 2 ≤ Amax ^ 2 := (sq_le_sq₀ hA.le hAmax.le).2 hAupper
  have hBcube : Bmin ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hBmin.le hBlower 3
  have huniform : (N : ℝ) * A ^ 2 / (B ^ 3 * kappa ^ 2) ≤
      (N : ℝ) * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) := by
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hAsq (Nat.cast_nonneg N))
      (mul_pos (pow_pos hBmin 3) (sq_pos_of_pos hkappa))
      (mul_le_mul_of_nonneg_right hBcube (sq_nonneg kappa))
  rw [_root_.GD.N0232.N0720.N1324.d002950 N (by omega) hA hB.ne' kappa]
  linarith

theorem d002952 (N : ℕ) (hN : 2 ≤ N)
    {A B Amax Bmin kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 0 < kappa) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 2 * (N : ℝ) * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    delta / 2 * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) ≤ _root_.GD.N0232.N0720.N1324.d002945 N A B level kappa := by
  have hrem : (N : ℝ) * Amax ^ 2 / (Bmin ^ 3 * kappa ^ 2) ≤ delta / 2 := by
    apply (div_le_iff₀ (mul_pos (pow_pos hBmin 3) (sq_pos_of_pos hkappa))).2
    nlinarith [hcutoff]
  have hlower := _root_.GD.N0232.N0720.N1324.d002951 N hN hA hAupper hBmin hBlower hkappa
  have hratio : level + delta / 2 ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 N A (B * kappa) / _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) := by
    linarith
  have h := (le_div_iff₀ (_root_.GD.N0232.N0720.N1377.d002861 (N + 1) hA (B * kappa))).1 hratio
  unfold _root_.GD.N0232.N0720.N1324.d002945
  nlinarith

theorem d002953 (N : ℕ) {A Amax B Bmin beta kappa : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 1 ≤ kappa) (hrate : beta ≤ B ^ 2 / (2 * A)) :
    _root_.GD.N0232.N0720.N1324.d002946 N Amax Bmin * Real.exp (beta * kappa ^ 2) ≤
      _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) := by
  have hAmax : 0 < Amax := hA.trans_le hAupper
  have hB : 0 < B := hBmin.trans_le hBlower
  have hk : 0 ≤ kappa := le_trans zero_le_one hkappa
  have hBk : B ≤ B * kappa := by nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hkappa)]
  have hcenter : Bmin / Amax ≤ B * kappa / A := by
    apply (div_le_div_iff₀ hAmax hA).2
    calc
      Bmin * A ≤ Bmin * Amax := mul_le_mul_of_nonneg_left hAupper hBmin.le
      _ ≤ B * Amax := mul_le_mul_of_nonneg_right hBlower hAmax.le
      _ ≤ (B * kappa) * Amax := mul_le_mul_of_nonneg_right hBk hAmax.le
  have hrate' : beta * kappa ^ 2 ≤ (B * kappa) ^ 2 / (2 * A) := by
    calc
      beta * kappa ^ 2 ≤ (B ^ 2 / (2 * A)) * kappa ^ 2 :=
        mul_le_mul_of_nonneg_right hrate (sq_nonneg kappa)
      _ = _ := by ring
  have hexponent : beta * kappa ^ 2 - Amax / 2 ≤ (B * kappa) ^ 2 / (2 * A) - A / 2 := by
    linarith
  have hproduct := mul_le_mul
    (pow_le_pow_left₀ (div_nonneg hBmin.le hAmax.le) hcenter (N + 1))
    (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
    (pow_nonneg (div_nonneg (mul_nonneg hB.le hk) hA.le) (N + 1))
  have hlower := hproduct.trans
    (_root_.GD.N0232.N0720.N1374.d002870 (N + 1) hA (mul_nonneg hB.le hk))
  convert! hlower using 1
  simp only [_root_.GD.N0232.N0720.N1324.d002946, sub_eq_add_neg, Real.exp_add, neg_div]
  ring

theorem d002954 (N : ℕ) (hN : 2 ≤ N)
    {A Amax B Bmin beta kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax) (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 1 ≤ kappa) (hdelta : 0 ≤ delta)
    (hrate : beta ≤ B ^ 2 / (2 * A)) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 2 * (N : ℝ) * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    (delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 N Amax Bmin) * Real.exp (beta * kappa ^ 2) ≤
      _root_.GD.N0232.N0720.N1324.d002945 N A B level kappa := by
  have h := mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0720.N1324.d002953 N hA hAupper hBmin hBlower hkappa hrate)
    (by positivity : 0 ≤ delta / 2)
  rw [← mul_assoc] at h
  exact h.trans (_root_.GD.N0232.N0720.N1324.d002952 N hN hA hAupper hBmin hBlower
    (lt_of_lt_of_le zero_lt_one hkappa) hgeometry hcutoff)

theorem d002955 (N : ℕ) (hN : 1 ≤ N)
    {A Amin B Bmin Bmax level kappa cutoff : ℝ}
    (hAmin : 0 < Amin) (hA : Amin ≤ A) (hBmin : 0 < Bmin)
    (hBlower : Bmin ≤ B) (hBupper : B ≤ Bmax)
    (hcutoff : 0 ≤ cutoff) (hkappa : kappa ≤ cutoff) (hgeometry : level ≤ A / B) :
    -((N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) Amin (Bmax * cutoff) / Bmin) ≤
      _root_.GD.N0232.N0720.N1324.d002945 N A B level kappa := by
  have hApos : 0 < A := hAmin.trans_le hA
  have hB : 0 < B := hBmin.trans_le hBlower
  have hlinear : B * kappa ≤ Bmax * cutoff :=
    (mul_le_mul_of_nonneg_left hkappa hB.le).trans
      (mul_le_mul_of_nonneg_right hBupper hcutoff)
  have hmoment := _root_.GD.N0232.N0720.N1380.d002920 (N - 1) hAmin hApos hA hlinear
  have hquot : (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) A (B * kappa) / B ≤
      (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) Amin (Bmax * cutoff) / Bmin := by
    exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg N)
      (_root_.GD.N0232.N0720.N1377.d002861 (N - 1) hAmin (Bmax * cutoff)).le)
      (mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg N)) hBmin hBlower
  rw [_root_.GD.N0232.N0720.N1324.d002948 N hN hApos hB.ne']
  have hpositive : 0 ≤ (A / B - level) * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) A (B * kappa) :=
    mul_nonneg (sub_nonneg.mpr hgeometry) (_root_.GD.N0232.N0720.N1377.d002861 (N + 1) hApos _).le
  linarith

variable {I : Type*} [Fintype I]

theorem d002956 (N : ℕ) (hN : 2 ≤ N)
    (weight A B kappa : I → ℝ)
    {Amin Amax Bmin Bmax level delta beta cutoff : ℝ}
    (hAmin : 0 < Amin) (hA : ∀ i, Amin ≤ A i) (hAupper : ∀ i, A i ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : ∀ i, Bmin ≤ B i) (hBupper : ∀ i, B i ≤ Bmax)
    (hdelta : 0 ≤ delta) (hcutoff : 1 ≤ cutoff)
    (hgeometry : ∀ i, level + delta ≤ A i / B i)
    (hrate : ∀ i, beta ≤ B i ^ 2 / (2 * A i))
    (hthreshold : 2 * (N : ℝ) * Amax ^ 2 ≤ delta * Bmin ^ 3 * cutoff ^ 2)
    (hweight : ∀ i, 0 ≤ weight i) (hprobability : ∑ i, weight i = 1)
    (hdenominator : 0 < ∑ i, weight i * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) (A i) (B i * kappa i))
    (hposterior :
      (∑ i, weight i * (kappa i * _root_.GD.N0232.N0720.N1377.d002852 N (A i) (B i * kappa i))) /
        (∑ i, weight i * _root_.GD.N0232.N0720.N1377.d002852 (N + 1) (A i) (B i * kappa i)) ≤ level) :
    (∑ i, weight i * (if cutoff ≤ kappa i then
      (delta / 2 * _root_.GD.N0232.N0720.N1324.d002946 N Amax Bmin) * Real.exp (beta * kappa i ^ 2)
      else 0)) ≤ (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) Amin (Bmax * cutoff) / Bmin := by
  classical
  apply _root_.GD.N0232.N0720.N1385.d002943 weight
    (fun i ↦ _root_.GD.N0232.N0720.N1377.d002852 (N + 1) (A i) (B i * kappa i))
    (fun i ↦ kappa i * _root_.GD.N0232.N0720.N1377.d002852 N (A i) (B i * kappa i))
    _ hweight hprobability hdenominator hposterior
  intro i
  have hApos : 0 < A i := hAmin.trans_le (hA i)
  have hC : 0 ≤ (N : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (N - 1) Amin (Bmax * cutoff) / Bmin := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (_root_.GD.N0232.N0720.N1377.d002861 (N - 1) hAmin _).le) hBmin.le
  split_ifs with hi
  · have hsq : cutoff ^ 2 ≤ kappa i ^ 2 :=
      (sq_le_sq₀ (le_trans zero_le_one hcutoff)
        (le_trans (le_trans zero_le_one hcutoff) hi)).2 hi
    have ht : 2 * (N : ℝ) * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa i ^ 2 :=
      hthreshold.trans (mul_le_mul_of_nonneg_left hsq
        (mul_nonneg hdelta (pow_nonneg hBmin.le _)))
    have hl := _root_.GD.N0232.N0720.N1324.d002954 N hN hApos (hAupper i) hBmin
      (hBlower i) (hcutoff.trans hi) hdelta (hrate i) (hgeometry i) ht
    unfold _root_.GD.N0232.N0720.N1324.d002945 at hl
    linarith
  · have hl := _root_.GD.N0232.N0720.N1324.d002955 N (by omega) hAmin (hA i) hBmin (hBlower i)
      (hBupper i) (le_trans zero_le_one hcutoff) (le_of_not_ge hi)
      (by linarith [hgeometry i] : level ≤ A i / B i)
    unfold _root_.GD.N0232.N0720.N1324.d002945 at hl
    linarith

end
end GD.N0232.N0720.N1324

#print axioms _root_.GD.N0232.N0720.N1324.d002951
#print axioms _root_.GD.N0232.N0720.N1324.d002956
