import GD.Module0165
import Mathlib.Tactic
















namespace GD
namespace N0232
namespace N0720
namespace N1284

noncomputable section

open _root_.GD.N0232.N0720.N1203





theorem d002666 (epsilon : ℝ) :
    2 * (1 - epsilon) - (1 - 2 * epsilon) = 1 := by ring



theorem d002667
    (epsilon M c1 c2 : ℝ)
    (hweighted :
      (1 - epsilon) * c1 + (1 - 2 * epsilon) * c2 = M + 1) :
    (1 - epsilon) * (c1 - 2) +
        (1 - 2 * epsilon) * (c2 + 1) = M := by
  linarith



theorem d002668
    {epsilon M s1 s2 alpha beta c1 c2 : ℝ}
    (hs1 : s1 = 1 - epsilon) (hs2 : s2 = 1 - 2 * epsilon)
    (halpha : alpha = M + 1 - epsilon) (hbeta : beta = epsilon)
    (hc1 : s1 * c1 = alpha) (hc2 : s2 * c2 = beta) :
    s1 * c1 + s2 * c2 = M + 1 := by
  rw [hc1, hc2, halpha, hbeta]
  ring




theorem d002669
    {epsilon v0 V x p h k1 k2 c1 c2 : ℝ} (hV : V ≠ 0) :
    x * (p + k1 * (c1 * h - 2 * p) + k2 * (c2 * h + p))
        - k1 * x *
            (c1 * (1 - (1 - epsilon) * v0 / V) * h - 2 * epsilon * p)
        - k2 * x *
            (c2 * (1 - (1 - 2 * epsilon) * v0 / V) * h +
              2 * epsilon * p) =
      x *
        ((1 - 2 * (1 - epsilon) * k1 +
            (1 - 2 * epsilon) * k2) * p +
          (v0 / V) *
            ((1 - epsilon) * c1 * k1 +
              (1 - 2 * epsilon) * c2 * k2) * h) := by
  field_simp [hV]
  ring




def d002670 (variance x : ℝ) : ℝ :=
  (Real.sqrt variance)⁻¹ *
    Real.exp (-(x ^ 2) / (2 * variance))

theorem d002671 (variance x : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1284.d002670 variance x := by
  unfold _root_.GD.N0232.N0720.N1284.d002670
  positivity







theorem d002672
    {c w x : ℝ} (hc : 2 ≤ c) (hw : 0 < w) :
    2 * _root_.GD.N0232.N0720.N1284.d002670 w x ≤
      c * _root_.GD.N0232.N0720.N1284.d002670 ((c / 2) ^ 2 * w) x := by
  have hc0 : 0 < c / 2 := by linarith
  have hscale : 1 ≤ c / 2 := by linarith
  have hsqrtw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hsqrtScale :
      Real.sqrt ((c / 2) ^ 2 * w) = (c / 2) * Real.sqrt w := by
    rw [Real.sqrt_mul (sq_nonneg (c / 2)), Real.sqrt_sq_eq_abs,
      abs_of_pos hc0]
  have hexponent :
      Real.exp (-(x ^ 2) / (2 * w)) ≤
        Real.exp (-(x ^ 2) / (2 * ((c / 2) ^ 2 * w))) := by
    apply Real.exp_le_exp.mpr
    have hden0 : 0 < 2 * w := by positivity
    have hden1 : 0 < 2 * ((c / 2) ^ 2 * w) := by positivity
    rw [div_le_div_iff₀ hden0 hden1]
    have hs2 : 1 ≤ (c / 2) ^ 2 := by
      nlinarith [sq_nonneg (c / 2 - 1)]
    have hwscale : 2 * w ≤ 2 * ((c / 2) ^ 2 * w) := by
      nlinarith [mul_le_mul_of_nonneg_right hs2 hw.le]
    exact mul_le_mul_of_nonpos_left hwscale
      (neg_nonpos.mpr (sq_nonneg x))
  unfold _root_.GD.N0232.N0720.N1284.d002670
  rw [hsqrtScale]
  have hnorm : c * ((c / 2) * Real.sqrt w)⁻¹ =
      2 * (Real.sqrt w)⁻¹ := by
    field_simp [hc0.ne', hsqrtw.ne']
  rw [show c * (((c / 2) * Real.sqrt w)⁻¹ *
      Real.exp (-(x ^ 2) / (2 * ((c / 2) ^ 2 * w)))) =
      (c * ((c / 2) * Real.sqrt w)⁻¹) *
        Real.exp (-(x ^ 2) / (2 * ((c / 2) ^ 2 * w))) by ring,
    hnorm]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hexponent
      (show 0 ≤ 2 * (Real.sqrt w)⁻¹ by positivity)


theorem d002673
    {c w x : ℝ} (hc : 2 ≤ c) (hw : 0 < w) :
    0 ≤ c * _root_.GD.N0232.N0720.N1284.d002670 ((c / 2) ^ 2 * w) x -
      2 * _root_.GD.N0232.N0720.N1284.d002670 w x := by
  exact sub_nonneg.mpr (_root_.GD.N0232.N0720.N1284.d002672 hc hw)



theorem d002674
    {c U w x : ℝ} (hc : 0 ≤ c) :
    0 ≤ c * _root_.GD.N0232.N0720.N1284.d002670 U x + _root_.GD.N0232.N0720.N1284.d002670 w x := by
  exact add_nonneg
    (mul_nonneg hc (_root_.GD.N0232.N0720.N1284.d002671 U x))
    (_root_.GD.N0232.N0720.N1284.d002671 w x)




theorem d002675
    {p h k1 k2 q1 q2 gamma : ℝ}
    (hp : 0 ≤ p) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2)
    (hq1 : gamma * h ≤ q1) (hq2 : 0 ≤ q2) :
    gamma * k1 * h ≤ p + k1 * q1 + k2 * q2 := by
  have hfirst : gamma * k1 * h ≤ k1 * q1 := by
    calc
      gamma * k1 * h = k1 * (gamma * h) := by ring
      _ ≤ k1 * q1 := mul_le_mul_of_nonneg_left hq1 hk1
  have hsecond : 0 ≤ k2 * q2 := mul_nonneg hk2 hq2
  linarith


theorem d002676 (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]



theorem d002677
    {M epsilon alpha beta reciprocal K : ℝ}
    (hM : 3 ≤ M) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (halpha : alpha = M + 1 - epsilon) (hbeta : beta = epsilon)
    (hreciprocal : reciprocal ≤ 2)
    (hK : K = alpha ^ 2 + 2 * alpha * beta + beta ^ 2 * reciprocal) :
    K ≤ 2 * M ^ 2 := by
  have hab : alpha + beta = M + 1 := by
    rw [halpha, hbeta]
    ring
  have hbeta0 : 0 ≤ beta := by rw [hbeta]; exact he0
  have hbeta1 : beta ≤ 1 := by rw [hbeta]; exact he1
  have hbetaSq : beta ^ 2 ≤ 1 := by nlinarith [sq_nonneg beta]
  have hKle : K ≤ (alpha + beta) ^ 2 + beta ^ 2 := by
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hreciprocal (sq_nonneg beta)]
  rw [hab] at hKle
  nlinarith [sq_nonneg (M - 3)]











theorem d002678
    {N M epsilon c gamma H I K varianceRatio Phi : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hepsilon : 0 < epsilon)
    (hcM : M ≤ c) (hgamma : c / 3 ≤ gamma)
    (hH0 : 0 ≤ H) (hI0 : 0 ≤ I) (hK0 : 0 ≤ K)
    (hvariance0 : 0 ≤ varianceRatio)
    (hH : H ≤ 18 / N ^ 8)
    (hI : I ≤ c / (4 * N))
    (hK : K ≤ 2 * M ^ 2)
    (hvariance : varianceRatio ≤ 1 / (c ^ 2 * epsilon))
    (hMscale : M = N ^ 11) (hescale : epsilon = 1 / N ^ 2)
    (hPhi : Phi ≤ 2 / gamma * (H * I + varianceRatio * K)) :
    Phi ≤ 48 / N ^ 9 := by
  have hc : 0 < c := hM.trans_le hcM
  have hgamma0 : 0 < gamma := lt_of_lt_of_le (by positivity) hgamma
  have htwoGamma : 2 / gamma ≤ 6 / c := by
    apply (div_le_div_iff₀ hgamma0 hc).2
    nlinarith
  have hnarrow : H * I ≤ (9 * c) / (2 * N ^ 9) := by
    calc
      H * I ≤ (18 / N ^ 8) * I :=
        mul_le_mul_of_nonneg_right hH hI0
      _ ≤ (18 / N ^ 8) * (c / (4 * N)) := by
        apply mul_le_mul_of_nonneg_left hI
        positivity
      _ = (9 * c) / (2 * N ^ 9) := by
        field_simp [hN.ne']
        ring
  have hbroad : varianceRatio * K ≤ 2 * M ^ 2 / (c ^ 2 * epsilon) := by
    calc
      varianceRatio * K ≤ (1 / (c ^ 2 * epsilon)) * K :=
        mul_le_mul_of_nonneg_right hvariance hK0
      _ ≤ (1 / (c ^ 2 * epsilon)) * (2 * M ^ 2) := by
        apply mul_le_mul_of_nonneg_left hK
        positivity
      _ = 2 * M ^ 2 / (c ^ 2 * epsilon) := by ring
  have hinside0 : 0 ≤ H * I + varianceRatio * K := by positivity
  have hsplit :
      Phi ≤ (6 / c) *
        ((9 * c) / (2 * N ^ 9) +
          2 * M ^ 2 / (c ^ 2 * epsilon)) := by
    calc
      Phi ≤ 2 / gamma * (H * I + varianceRatio * K) := hPhi
      _ ≤ (6 / c) * (H * I + varianceRatio * K) :=
        mul_le_mul_of_nonneg_right htwoGamma hinside0
      _ ≤ (6 / c) *
          ((9 * c) / (2 * N ^ 9) +
            2 * M ^ 2 / (c ^ 2 * epsilon)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hnarrow hbroad
  have hcCube : M ^ 3 ≤ c ^ 3 := by
    exact pow_le_pow_left₀ hM.le hcM 3
  have hbroadScheduled :
      (6 / c) * (2 * M ^ 2 / (c ^ 2 * epsilon)) ≤ 12 / N ^ 9 := by
    have hratio : M ^ 2 / c ^ 3 ≤ 1 / M := by
      apply (div_le_div_iff₀ (pow_pos hc 3) hM).2
      nlinarith
    calc
      (6 / c) * (2 * M ^ 2 / (c ^ 2 * epsilon)) =
          12 * (M ^ 2 / c ^ 3) / epsilon := by
        field_simp [hc.ne', hepsilon.ne']
        ring
      _ ≤ 12 * (1 / M) / epsilon := by
        apply div_le_div_of_nonneg_right _ hepsilon.le
        exact mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 12 / N ^ 9 := by
        rw [hMscale, hescale]
        field_simp [hN.ne']
  have hnarrowScheduled :
      (6 / c) * ((9 * c) / (2 * N ^ 9)) = 27 / N ^ 9 := by
    field_simp [hc.ne']
    ring
  calc
    Phi ≤ (6 / c) *
        ((9 * c) / (2 * N ^ 9) +
          2 * M ^ 2 / (c ^ 2 * epsilon)) := hsplit
    _ = (6 / c) * ((9 * c) / (2 * N ^ 9)) +
        (6 / c) * (2 * M ^ 2 / (c ^ 2 * epsilon)) := by ring
    _ ≤ 27 / N ^ 9 + 12 / N ^ 9 := by
      rw [hnarrowScheduled]
      simpa only [add_comm] using
        add_le_add_left hbroadScheduled (27 / N ^ 9)
    _ = 39 / N ^ 9 := by ring
    _ ≤ 48 / N ^ 9 := by
      have hN9 : 0 < N ^ 9 := pow_pos hN 9
      exact div_le_div_of_nonneg_right (by norm_num) hN9.le

end

end N1284
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1284.d002667
#print axioms _root_.GD.N0232.N0720.N1284.d002669
#print axioms _root_.GD.N0232.N0720.N1284.d002672
#print axioms _root_.GD.N0232.N0720.N1284.d002677
#print axioms _root_.GD.N0232.N0720.N1284.d002678
