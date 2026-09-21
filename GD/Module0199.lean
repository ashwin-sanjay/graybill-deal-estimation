import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real









open scoped Topology

namespace GD.N0232.N0720.N1350

noncomputable section


noncomputable def d002722
    (rho beta x : ℝ) (s : ℤ) : ℝ :=
  rho ^ (beta * (s : ℝ)) /
    (x + rho ^ (s : ℝ)) ^ (5 / 2 : ℝ)

theorem d002723
    {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (beta : ℝ) (s : ℤ) :
    0 < _root_.GD.N0232.N0720.N1350.d002722 rho beta x s := by
  unfold _root_.GD.N0232.N0720.N1350.d002722
  positivity


theorem d002724
    {rho x y : ℝ} (hrho : 0 < rho) (hx : 0 < x) (hxy : x ≤ y)
    (beta : ℝ) (s : ℤ) :
    _root_.GD.N0232.N0720.N1350.d002722 rho beta y s ≤
      _root_.GD.N0232.N0720.N1350.d002722 rho beta x s := by
  unfold _root_.GD.N0232.N0720.N1350.d002722
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hrho.le _)
  · positivity
  · apply Real.rpow_le_rpow
    · positivity
    · linarith
    · norm_num



theorem d002725
    {rho beta x : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (n : ℕ) :
    _root_.GD.N0232.N0720.N1350.d002722 rho beta x (n : ℤ) ≤
      (1 / x ^ (5 / 2 : ℝ)) * (rho ^ beta) ^ n := by
  have hbase :
      x ^ (5 / 2 : ℝ) ≤
        (x + rho ^ (n : ℝ)) ^ (5 / 2 : ℝ) := by
    apply Real.rpow_le_rpow hx.le
    · exact le_add_of_nonneg_right (Real.rpow_nonneg hrho.le _)
    · norm_num
  have hnum : 0 ≤ rho ^ (beta * (n : ℝ)) :=
    Real.rpow_nonneg hrho.le _
  have hden : 0 < x ^ (5 / 2 : ℝ) := by positivity
  unfold _root_.GD.N0232.N0720.N1350.d002722
  simp only [Int.cast_natCast]
  calc
    rho ^ (beta * (n : ℝ)) /
          (x + rho ^ (n : ℝ)) ^ (5 / 2 : ℝ) ≤
        rho ^ (beta * (n : ℝ)) / x ^ (5 / 2 : ℝ) :=
      div_le_div_of_nonneg_left hnum hden hbase
    _ = (1 / x ^ (5 / 2 : ℝ)) * (rho ^ beta) ^ n := by
      rw [Real.rpow_mul hrho.le, Real.rpow_natCast]
      ring



theorem d002726
    {rho beta x : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (n : ℕ) :
    _root_.GD.N0232.N0720.N1350.d002722 rho beta x (-(n : ℤ)) ≤
      (rho ^ (5 / 2 - beta : ℝ)) ^ n := by
  have hsmall :
      rho ^ (-(n : ℝ)) ≤ x + rho ^ (-(n : ℝ)) := by
    linarith
  have hbase :
      (rho ^ (-(n : ℝ))) ^ (5 / 2 : ℝ) ≤
        (x + rho ^ (-(n : ℝ))) ^ (5 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (Real.rpow_nonneg hrho.le _)
    · exact hsmall
    · norm_num
  have hnum : 0 ≤ rho ^ (beta * (-(n : ℝ))) :=
    Real.rpow_nonneg hrho.le _
  have hden : 0 < (rho ^ (-(n : ℝ))) ^ (5 / 2 : ℝ) := by
    positivity
  unfold _root_.GD.N0232.N0720.N1350.d002722
  simp only [Int.cast_neg, Int.cast_natCast]
  calc
    rho ^ (beta * -(n : ℝ)) /
          (x + rho ^ (-(n : ℝ))) ^ (5 / 2 : ℝ) ≤
        rho ^ (beta * -(n : ℝ)) /
          (rho ^ (-(n : ℝ))) ^ (5 / 2 : ℝ) :=
      div_le_div_of_nonneg_left hnum hden hbase
    _ = (rho ^ (5 / 2 - beta : ℝ)) ^ n := by
      rw [← Real.rpow_mul hrho.le, ← Real.rpow_sub hrho]
      rw [show beta * -(n : ℝ) - -(n : ℝ) * (5 / 2 : ℝ) =
          (5 / 2 - beta : ℝ) * n by ring]
      rw [Real.rpow_mul hrho.le, Real.rpow_natCast]



theorem d002727
    {rho beta x : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2) (hx : 0 < x) :
    Summable (_root_.GD.N0232.N0720.N1350.d002722 rho beta x) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply Summable.of_nonneg_of_le
    · intro n
      exact (_root_.GD.N0232.N0720.N1350.d002723 hrho hx beta (n : ℤ)).le
    · exact _root_.GD.N0232.N0720.N1350.d002725 hrho hx
    · exact (summable_geometric_of_lt_one
        (Real.rpow_nonneg hrho.le beta)
        (Real.rpow_lt_one hrho.le hrhoOne hbeta)).mul_left
          (1 / x ^ (5 / 2 : ℝ))
  · apply Summable.of_nonneg_of_le
    · intro n
      exact (_root_.GD.N0232.N0720.N1350.d002723 hrho hx beta (-(n : ℤ))).le
    · exact _root_.GD.N0232.N0720.N1350.d002726 hrho hx
    · exact summable_geometric_of_lt_one
        (Real.rpow_nonneg hrho.le (5 / 2 - beta : ℝ))
        (Real.rpow_lt_one hrho.le hrhoOne (by linarith))



theorem d002728
    {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x) (beta : ℝ) (s : ℤ) :
    _root_.GD.N0232.N0720.N1350.d002722 rho beta (rho * x) s =
      rho ^ (beta - 5 / 2 : ℝ) *
        _root_.GD.N0232.N0720.N1350.d002722 rho beta x (s - 1) := by
  have hpow :
      rho ^ (s : ℝ) = rho * rho ^ ((s : ℝ) - 1) := by
    calc
      rho ^ (s : ℝ) = rho ^ (((s : ℝ) - 1) + 1) := by ring_nf
      _ = rho ^ ((s : ℝ) - 1) * rho ^ (1 : ℝ) :=
        Real.rpow_add hrho _ _
      _ = rho * rho ^ ((s : ℝ) - 1) := by
        rw [Real.rpow_one]
        ring
  have hbase :
      rho * x + rho ^ (s : ℝ) =
        rho * (x + rho ^ ((s : ℝ) - 1)) := by
    rw [hpow]
    ring
  have hden :
      (rho * x + rho ^ (s : ℝ)) ^ (5 / 2 : ℝ) =
        rho ^ (5 / 2 : ℝ) *
          (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ) := by
    rw [hbase, Real.mul_rpow hrho.le]
    positivity
  have hcast : ((s - 1 : ℤ) : ℝ) = (s : ℝ) - 1 := by norm_num
  have hcoef :
      rho ^ (beta * (s : ℝ)) / rho ^ (5 / 2 : ℝ) =
        rho ^ (beta - 5 / 2 : ℝ) *
          rho ^ (beta * ((s : ℝ) - 1)) := by
    rw [← Real.rpow_sub hrho, ← Real.rpow_add hrho]
    congr 1
    ring
  unfold _root_.GD.N0232.N0720.N1350.d002722
  rw [hcast, hden]
  have hR : rho ^ (5 / 2 : ℝ) ≠ 0 := by positivity
  have hD :
      (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ) ≠ 0 := by
    positivity
  calc
    rho ^ (beta * (s : ℝ)) /
          (rho ^ (5 / 2 : ℝ) *
            (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ)) =
        (rho ^ (beta * (s : ℝ)) / rho ^ (5 / 2 : ℝ)) /
          (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ) := by
            field_simp
    _ = (rho ^ (beta - 5 / 2 : ℝ) *
          rho ^ (beta * ((s : ℝ) - 1))) /
          (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ) := by rw [hcoef]
    _ = rho ^ (beta - 5 / 2 : ℝ) *
          (rho ^ (beta * ((s : ℝ) - 1)) /
            (x + rho ^ ((s : ℝ) - 1)) ^ (5 / 2 : ℝ)) := by ring


noncomputable def d002729 (rho beta x : ℝ) : ℝ :=
  ∑' s : ℤ, _root_.GD.N0232.N0720.N1350.d002722 rho beta x s




theorem d002730
    {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x) (beta : ℝ) :
    _root_.GD.N0232.N0720.N1350.d002729 rho beta (rho * x) =
      rho ^ (beta - 5 / 2 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 rho beta x := by
  unfold _root_.GD.N0232.N0720.N1350.d002729
  rw [show (fun s : ℤ ↦ _root_.GD.N0232.N0720.N1350.d002722 rho beta (rho * x) s) =
      (fun s : ℤ ↦ rho ^ (beta - 5 / 2 : ℝ) *
        _root_.GD.N0232.N0720.N1350.d002722 rho beta x (s - 1)) by
      funext s
      exact _root_.GD.N0232.N0720.N1350.d002728 hrho hx beta s]
  rw [tsum_mul_left]
  exact congrArg (rho ^ (beta - 5 / 2 : ℝ) * ·)
    ((Equiv.subRight (1 : ℤ)).tsum_eq
      (fun s : ℤ ↦ _root_.GD.N0232.N0720.N1350.d002722 rho beta x s))


theorem d002731
    {rho beta x : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2) (hx : 0 < x) :
    0 < _root_.GD.N0232.N0720.N1350.d002729 rho beta x := by
  exact (_root_.GD.N0232.N0720.N1350.d002727 hrho hrhoOne hbeta hbetaTop hx).tsum_pos
    (fun s ↦ (_root_.GD.N0232.N0720.N1350.d002723 hrho hx beta s).le)
    0 (_root_.GD.N0232.N0720.N1350.d002723 hrho hx beta 0)


noncomputable def d002732
    (rho beta theta e T : ℝ) : ℝ :=
  let left := _root_.GD.N0232.N0720.N1350.d002729 rho beta ((1 - e) * theta / T)
  let right := _root_.GD.N0232.N0720.N1350.d002729 rho beta (e * theta / T)
  left / (right + left)


theorem d002733
    {rho beta theta e T : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (htheta : 0 < theta) (he : 0 < e) (heOne : e < 1) (hT : 0 < T) :
    _root_.GD.N0232.N0720.N1350.d002732 rho beta theta (1 - e) T =
      1 - _root_.GD.N0232.N0720.N1350.d002732 rho beta theta e T := by
  have hxL : 0 < (1 - e) * theta / T := by positivity
  have hxR : 0 < e * theta / T := by positivity
  have hL := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hxL
  have hR := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hxR
  unfold _root_.GD.N0232.N0720.N1350.d002732
  have hsub : 1 - (1 - e) = e := by ring
  rw [hsub]
  dsimp only
  have hL' : 0 < _root_.GD.N0232.N0720.N1350.d002729 rho beta (theta * (1 - e) / T) := by
    convert hL using 1 <;> ring_nf
  field_simp [ne_of_gt (add_pos hL' hR), ne_of_gt (add_pos hR hL')]
  ring


theorem d002734
    {rho beta theta e T : ℝ} (htheta : 0 < theta) :
    _root_.GD.N0232.N0720.N1350.d002732 rho beta theta e T =
      _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e (T / theta) := by
  have hargL :
      (1 - e) * theta / T = (1 - e) * 1 / (T / theta) := by
    field_simp [htheta.ne']
  have hargR : e * theta / T = e * 1 / (T / theta) := by
    field_simp [htheta.ne']
  unfold _root_.GD.N0232.N0720.N1350.d002732
  rw [hargL, hargR]


theorem d002735
    {rho beta theta e T : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (htheta : 0 < theta) (he : 0 < e) (heOne : e < 1) (hT : 0 < T) :
    _root_.GD.N0232.N0720.N1350.d002732 rho beta theta e (T / rho) =
      _root_.GD.N0232.N0720.N1350.d002732 rho beta theta e T := by
  have hxL : 0 < (1 - e) * theta / T := by positivity
  have hxR : 0 < e * theta / T := by positivity
  have hargL :
      (1 - e) * theta / (T / rho) =
        rho * ((1 - e) * theta / T) := by field_simp
  have hargR :
      e * theta / (T / rho) = rho * (e * theta / T) := by
    field_simp
  have hL := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hxL
  have hR := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hxR
  have hc : 0 < rho ^ (beta - 5 / 2 : ℝ) := by positivity
  unfold _root_.GD.N0232.N0720.N1350.d002732
  rw [hargL, hargR,
    _root_.GD.N0232.N0720.N1350.d002730 hrho hxL beta,
    _root_.GD.N0232.N0720.N1350.d002730 hrho hxR beta]
  field_simp




theorem d002736
    {rho beta x : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1350.d002729 rho beta (rho * x) ≠
      _root_.GD.N0232.N0720.N1350.d002729 rho beta x / rho := by
  intro heq
  have hD := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hx
  rw [_root_.GD.N0232.N0720.N1350.d002730 hrho hx beta] at heq
  have hprod :
      rho ^ (beta - 5 / 2 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 rho beta x =
        rho ^ (-1 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 rho beta x := by
    calc
      rho ^ (beta - 5 / 2 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 rho beta x =
          _root_.GD.N0232.N0720.N1350.d002729 rho beta x / rho := heq
      _ = rho ^ (-1 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 rho beta x := by
        rw [Real.rpow_neg_one]
        field_simp
  have hchar :
      rho ^ (beta - 5 / 2 : ℝ) = rho ^ (-1 : ℝ) :=
    mul_right_cancel₀ hD.ne' hprod
  have hexponent : beta - 5 / 2 = (-1 : ℝ) :=
    (Real.strictAnti_rpow_of_base_lt_one hrho hrhoOne).injective hchar
  apply hbetaNe
  linarith




theorem d002737
    {rho beta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) :
    _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 (1 / (1 + rho)) (1 / (1 + rho)) ≠
      1 / (1 + rho) := by
  have hone : (0 : ℝ) < 1 := zero_lt_one
  have hrhoOnePos : 0 < 1 + rho := by linarith
  have he : 0 < 1 / (1 + rho) := by positivity
  have heOne : 1 / (1 + rho) < 1 := by
    rw [div_lt_one hrhoOnePos]
    linarith
  have hD1 := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hone
  have hDrho := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hrho
  intro htrace
  have hargL :
      (1 - 1 / (1 + rho)) * 1 / (1 / (1 + rho)) = rho := by
    field_simp
    ring
  have hargR :
      (1 / (1 + rho)) * 1 / (1 / (1 + rho)) = 1 := by
    field_simp
  unfold _root_.GD.N0232.N0720.N1350.d002732 at htrace
  dsimp only at htrace
  rw [hargL, hargR] at htrace
  have hinverse :
      _root_.GD.N0232.N0720.N1350.d002729 rho beta rho = _root_.GD.N0232.N0720.N1350.d002729 rho beta 1 / rho := by
    field_simp [ne_of_gt hD1, ne_of_gt hDrho] at htrace ⊢
    nlinarith
  apply _root_.GD.N0232.N0720.N1350.d002736
    hrho hrhoOne hbeta hbetaTop hbetaNe hone
  simpa using hinverse



theorem d002738
    {rho beta T : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) (hT : 0 < T) :
    _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 (1 / (1 + rho)) T ≠
      1 / (1 + rho) := by
  let x : ℝ := (1 / (1 + rho)) / T
  have hrhoOnePos : 0 < 1 + rho := by linarith
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hargR : (1 / (1 + rho)) * 1 / T = x := by
    simp only [x]
    ring
  have hargL :
      (1 - 1 / (1 + rho)) * 1 / T = rho * x := by
    dsimp [x]
    field_simp
    ring
  have hDx := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop hx
  have hDrx := _root_.GD.N0232.N0720.N1350.d002731 hrho hrhoOne hbeta hbetaTop
    (mul_pos hrho hx)
  intro htrace
  unfold _root_.GD.N0232.N0720.N1350.d002732 at htrace
  dsimp only at htrace
  rw [hargL, hargR] at htrace
  have hinverse :
      _root_.GD.N0232.N0720.N1350.d002729 rho beta (rho * x) =
        _root_.GD.N0232.N0720.N1350.d002729 rho beta x / rho := by
    field_simp [ne_of_gt hDx, ne_of_gt hDrx] at htrace ⊢
    nlinarith
  exact _root_.GD.N0232.N0720.N1350.d002736
    hrho hrhoOne hbeta hbetaTop hbetaNe hx hinverse

end

end GD.N0232.N0720.N1350

#print axioms _root_.GD.N0232.N0720.N1350.d002727
#print axioms _root_.GD.N0232.N0720.N1350.d002730
#print axioms _root_.GD.N0232.N0720.N1350.d002735
#print axioms _root_.GD.N0232.N0720.N1350.d002738

