import GD.Module0212






open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace GD.N0232.N0720.N1385

open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1378
open _root_.GD.N0232.N0720.N1380 _root_.GD.N0232.N0720.N1375

noncomputable section

def d002940 (A B level kappa : ℝ) : ℝ :=
  kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / 8 -
    level * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8)


theorem d002941 {A B : ℝ} (hA : 0 < A) (hB : B ≠ 0)
    (level kappa : ℝ) :
    _root_.GD.N0232.N0720.N1385.d002940 A B level kappa =
      (A / B - level) * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8 -
        _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) / (2 * B) := by
  have hrec := _root_.GD.N0232.N0720.N1378.d002873 3 hA (B * kappa)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hrec
  unfold _root_.GD.N0232.N0720.N1385.d002940
  generalize _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) = I3 at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) = I4 at hrec ⊢
  generalize _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) = I5 at hrec ⊢
  field_simp [hB]
  nlinarith [hrec]



theorem d002942
    {A Amin B Bmin Bmax level kappa cutoff : ℝ}
    (hAmin : 0 < Amin) (hA : Amin ≤ A)
    (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B) (hBupper : B ≤ Bmax)
    (hcutoff : 0 ≤ cutoff) (hkappa : kappa ≤ cutoff)
    (hgeometry : level ≤ A / B) :
    -(_root_.GD.N0232.N0720.N1377.d002852 3 Amin (Bmax * cutoff) / (2 * Bmin)) ≤
      _root_.GD.N0232.N0720.N1385.d002940 A B level kappa := by
  have hApos : 0 < A := hAmin.trans_le hA
  have hB : 0 < B := hBmin.trans_le hBlower
  have hlinear : B * kappa ≤ Bmax * cutoff :=
    (mul_le_mul_of_nonneg_left hkappa hB.le).trans
      (mul_le_mul_of_nonneg_right hBupper hcutoff)
  have hmoment := _root_.GD.N0232.N0720.N1380.d002920 3 hAmin hApos hA hlinear
  have hquot : _root_.GD.N0232.N0720.N1377.d002852 3 A (B * kappa) / (2 * B) ≤
      _root_.GD.N0232.N0720.N1377.d002852 3 Amin (Bmax * cutoff) / (2 * Bmin) := by
    apply div_le_div₀ (_root_.GD.N0232.N0720.N1377.d002861 3 hAmin (Bmax * cutoff)).le hmoment
    · positivity
    · linarith
  rw [_root_.GD.N0232.N0720.N1385.d002941 hApos hB.ne']
  have hpositive : 0 ≤ (A / B - level) * _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hgeometry)
      (_root_.GD.N0232.N0720.N1377.d002861 5 hApos _).le) (by norm_num)
  linarith

variable {I : Type*} [Fintype I]



theorem d002943 (weight K L envelope : I → ℝ)
    {level C : ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (hprobability : ∑ i, weight i = 1)
    (hdenominator : 0 < ∑ i, weight i * K i)
    (hposterior : (∑ i, weight i * L i) / (∑ i, weight i * K i) ≤ level)
    (henvelope : ∀ i, envelope i ≤ L i - level * K i + C) :
    ∑ i, weight i * envelope i ≤ C := by
  have hdeficit : (∑ i, weight i * L i) -
      level * (∑ i, weight i * K i) ≤ 0 := by
    have h := (div_le_iff₀ hdenominator).1 hposterior
    linarith
  calc
    ∑ i, weight i * envelope i ≤
        ∑ i, weight i * (L i - level * K i + C) :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (henvelope i) (hweight i))
    _ = (∑ i, weight i * L i) - level * (∑ i, weight i * K i) + C := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [show ∀ i, weight i * (level * K i) = level * (weight i * K i) by
        intro i; ring]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hprobability, one_mul]
    _ ≤ C := by linarith



theorem d002944
    (weight A B kappa : I → ℝ)
    {Amin Amax Bmin Bmax level delta beta cutoff : ℝ}
    (hAmin : 0 < Amin) (hA : ∀ i, Amin ≤ A i)
    (hAupper : ∀ i, A i ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : ∀ i, Bmin ≤ B i)
    (hBupper : ∀ i, B i ≤ Bmax)
    (hdelta : 0 ≤ delta) (hcutoff : 1 ≤ cutoff)
    (hgeometry : ∀ i, level + delta ≤ A i / B i)
    (hrate : ∀ i, beta ≤ B i ^ 2 / (2 * A i))
    (hthreshold : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * cutoff ^ 2)
    (hweight : ∀ i, 0 ≤ weight i) (hprobability : ∑ i, weight i = 1)
    (hdenominator : 0 < ∑ i, weight i * (_root_.GD.N0232.N0720.N1377.d002852 5 (A i) (B i * kappa i) / 8))
    (hposterior :
      (∑ i, weight i * (kappa i * _root_.GD.N0232.N0720.N1377.d002852 4 (A i) (B i * kappa i) / 8)) /
        (∑ i, weight i * (_root_.GD.N0232.N0720.N1377.d002852 5 (A i) (B i * kappa i) / 8)) ≤ level) :
    (∑ i, weight i * (if cutoff ≤ kappa i then
      (delta / 2 * _root_.GD.N0232.N0720.N1375.d002935 Amax Bmin) * Real.exp (beta * kappa i ^ 2)
      else 0)) ≤ _root_.GD.N0232.N0720.N1377.d002852 3 Amin (Bmax * cutoff) / (2 * Bmin) := by
  classical
  apply _root_.GD.N0232.N0720.N1385.d002943 weight
    (fun i ↦ _root_.GD.N0232.N0720.N1377.d002852 5 (A i) (B i * kappa i) / 8)
    (fun i ↦ kappa i * _root_.GD.N0232.N0720.N1377.d002852 4 (A i) (B i * kappa i) / 8)
    _ hweight hprobability hdenominator hposterior
  intro i
  have hApos : 0 < A i := hAmin.trans_le (hA i)
  have hC : 0 ≤ _root_.GD.N0232.N0720.N1377.d002852 3 Amin (Bmax * cutoff) / (2 * Bmin) := by
    exact div_nonneg (_root_.GD.N0232.N0720.N1377.d002861 3 hAmin _).le (by positivity)
  split_ifs with hi
  · have hsq : cutoff ^ 2 ≤ kappa i ^ 2 :=
      (sq_le_sq₀ (le_trans zero_le_one hcutoff)
        (le_trans (le_trans zero_le_one hcutoff) hi)).2 hi
    have ht : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa i ^ 2 :=
      hthreshold.trans (mul_le_mul_of_nonneg_left hsq
        (mul_nonneg hdelta (pow_nonneg hBmin.le _)))
    have hl := _root_.GD.N0232.N0720.N1375.d002938 hApos (hAupper i) hBmin
      (hBlower i) (hcutoff.trans hi) hdelta (hrate i) (hgeometry i) ht
    linarith
  · have hl := _root_.GD.N0232.N0720.N1385.d002942 hAmin (hA i) hBmin (hBlower i)
      (hBupper i) (le_trans zero_le_one hcutoff) (le_of_not_ge hi)
      (by linarith [hgeometry i] : level ≤ A i / B i)
    unfold _root_.GD.N0232.N0720.N1385.d002940 at hl
    linarith

end
end GD.N0232.N0720.N1385
