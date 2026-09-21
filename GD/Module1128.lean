import GD.Module0791
import GD.Module1034
import GD.Module1122
import GD.Module1025






















open Filter MeasureTheory Set
open scoped ENNReal BigOperators NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1154

noncomputable section

open _root_.GD.N0232.N0719.N0832
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1144
open _root_.GD.N0232.N0720.N1145
open _root_.GD.N0107
open _root_.GD.N0116
open _root_.GD.N0120
open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1501





theorem d018162
    (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    z ^ N * Real.exp (-z) ≤ (N.factorial : ℝ) := by
  have hseries := Real.pow_div_factorial_le_exp z hz N
  have hfactorial : 0 < (N.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hfactorial] at hseries
  calc
    z ^ N * Real.exp (-z) ≤
        (Real.exp z * (N.factorial : ℝ)) * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right hseries (Real.exp_pos _).le
    _ = (N.factorial : ℝ) := by
      calc
        (Real.exp z * (N.factorial : ℝ)) * Real.exp (-z) =
            (N.factorial : ℝ) * (Real.exp z * Real.exp (-z)) := by ring
        _ = (N.factorial : ℝ) := by rw [← Real.exp_add]; simp


theorem d018163
    (N : ℕ) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (t ^ 2)⁻¹ ^ N * Real.exp (-(R / t ^ 2)) ≤
      (R ^ N)⁻¹ * (N.factorial : ℝ) := by
  let z : ℝ := R / t ^ 2
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hbound := _root_.GD.N0232.N0720.N1154.d018162 N hz
  have hidentity :
      (t ^ 2)⁻¹ ^ N * Real.exp (-(R / t ^ 2)) =
        (R ^ N)⁻¹ * (z ^ N * Real.exp (-z)) := by
    dsimp [z]
    rw [div_pow, inv_pow]
    have htPow : (t ^ 2) ^ N ≠ 0 :=
      pow_ne_zero N (sq_pos_of_pos ht).ne'
    have hRpow : R ^ N ≠ 0 := pow_ne_zero N hR.ne'
    field_simp [htPow, hRpow]
  rw [hidentity]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_nonneg hR.le N))




theorem d018164
    (M : ℕ) {R k d t : ℝ}
    (hR : 0 < R) (hk : 0 < k) (ht : 0 < t) :
    d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
        Real.exp (-((R + k * d ^ 2) / t ^ 2)) ≤
      k⁻¹ * Real.exp (-1) *
        ((R ^ M)⁻¹ * (M.factorial : ℝ)) := by
  let x : ℝ := k * d ^ 2 / t ^ 2
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxBound : x * Real.exp (-x) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one x
  have hRBound := _root_.GD.N0232.N0720.N1154.d018163 M hR ht
  have hidentity :
      d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
          Real.exp (-((R + k * d ^ 2) / t ^ 2)) =
        k⁻¹ * (x * Real.exp (-x)) *
          ((t ^ 2)⁻¹ ^ M * Real.exp (-(R / t ^ 2))) := by
    have hexponent :
        -(x) + -(R / t ^ 2) = -((R + k * d ^ 2) / t ^ 2) := by
      dsimp [x]
      field_simp [ht.ne']
      ring
    have hexp :
        Real.exp (-((R + k * d ^ 2) / t ^ 2)) =
          Real.exp (-x) * Real.exp (-(R / t ^ 2)) := by
      rw [← Real.exp_add, hexponent]
    rw [hexp, pow_succ, inv_pow]
    dsimp [x]
    field_simp [hk.ne', ht.ne']
    have htCancel : t ^ (M * 2) * t⁻¹ ^ (M * 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
    calc
      d ^ 2 * t ^ 2 = d ^ 2 * t ^ 2 * 1 := by ring
      _ = d ^ 2 * t ^ 2 * (t ^ (M * 2) * t⁻¹ ^ (M * 2)) := by
        rw [htCancel]
      _ = _ := by ring
  rw [hidentity]
  have hkInv : 0 ≤ k⁻¹ := inv_nonneg.mpr hk.le
  have hleftNonneg : 0 ≤ x * Real.exp (-x) :=
    mul_nonneg hx (Real.exp_pos _).le
  have hrightNonneg :
      0 ≤ (t ^ 2)⁻¹ ^ M * Real.exp (-(R / t ^ 2)) := by positivity
  calc
    k⁻¹ * (x * Real.exp (-x)) *
        ((t ^ 2)⁻¹ ^ M * Real.exp (-(R / t ^ 2))) ≤
      k⁻¹ * Real.exp (-1) *
        ((t ^ 2)⁻¹ ^ M * Real.exp (-(R / t ^ 2))) := by
          gcongr
    _ ≤ k⁻¹ * Real.exp (-1) *
        ((R ^ M)⁻¹ * (M.factorial : ℝ)) := by
          gcongr




theorem d018165
    (M : ℕ) {R k c mu t : ℝ}
    (hR : 0 < R) (hk : 0 < k) (ht : 0 < t) :
    mu ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
        Real.exp (-((R + k * (c - mu) ^ 2) / t ^ 2)) ≤
      2 * c ^ 2 * ((R ^ (M + 1))⁻¹ * ((M + 1).factorial : ℝ)) +
        2 * (k⁻¹ * Real.exp (-1) *
          ((R ^ M)⁻¹ * (M.factorial : ℝ))) := by
  let d : ℝ := mu - c
  have hmu : mu ^ 2 ≤ 2 * c ^ 2 + 2 * d ^ 2 := by
    dsimp [d]
    nlinarith [sq_nonneg (mu - 2 * c)]
  have hbarrier :
      Real.exp (-((R + k * (c - mu) ^ 2) / t ^ 2)) ≤
        Real.exp (-(R / t ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
    have hkSq : 0 ≤ k * (c - mu) ^ 2 := mul_nonneg hk.le (sq_nonneg _)
    apply neg_le_neg
    exact (div_le_div_iff_of_pos_right htSq).2 (le_add_of_nonneg_right hkSq)
  have hfactorNonneg :
      0 ≤ (t ^ 2)⁻¹ ^ (M + 1) *
        Real.exp (-((R + k * (c - mu) ^ 2) / t ^ 2)) := by positivity
  have hsplit :
      mu ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
          Real.exp (-((R + k * (c - mu) ^ 2) / t ^ 2)) ≤
        2 * c ^ 2 *
            ((t ^ 2)⁻¹ ^ (M + 1) * Real.exp (-(R / t ^ 2))) +
          2 * d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
            Real.exp (-((R + k * d ^ 2) / t ^ 2)) := by
    have hdEq : (c - mu) ^ 2 = d ^ 2 := by
      dsimp [d]
      ring
    have hbarrierD :
        Real.exp (-((R + k * d ^ 2) / t ^ 2)) ≤
          Real.exp (-(R / t ^ 2)) := by
      rw [← hdEq]
      exact hbarrier
    rw [hdEq]
    have hconstantTerm :
        2 * c ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
            Real.exp (-((R + k * d ^ 2) / t ^ 2)) ≤
          2 * c ^ 2 *
            ((t ^ 2)⁻¹ ^ (M + 1) * Real.exp (-(R / t ^ 2))) := by
      calc
        2 * c ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
            Real.exp (-((R + k * d ^ 2) / t ^ 2)) =
          (2 * c ^ 2 * (t ^ 2)⁻¹ ^ (M + 1)) *
            Real.exp (-((R + k * d ^ 2) / t ^ 2)) := by ring
        _ ≤ (2 * c ^ 2 * (t ^ 2)⁻¹ ^ (M + 1)) *
            Real.exp (-(R / t ^ 2)) :=
          mul_le_mul_of_nonneg_left hbarrierD (by positivity)
        _ = _ := by ring
    calc
      mu ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
          Real.exp (-((R + k * d ^ 2) / t ^ 2)) ≤
        (2 * c ^ 2 + 2 * d ^ 2) * (t ^ 2)⁻¹ ^ (M + 1) *
          Real.exp (-((R + k * d ^ 2) / t ^ 2)) := by
            gcongr
      _ ≤ 2 * c ^ 2 *
            ((t ^ 2)⁻¹ ^ (M + 1) * Real.exp (-(R / t ^ 2))) +
          2 * d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
            Real.exp (-((R + k * d ^ 2) / t ^ 2)) := by
              calc
                _ = 2 * c ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
                      Real.exp (-((R + k * d ^ 2) / t ^ 2)) +
                    2 * d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
                      Real.exp (-((R + k * d ^ 2) / t ^ 2)) := by ring
                _ ≤ _ := add_le_add hconstantTerm le_rfl
  have hconstant := _root_.GD.N0232.N0720.N1154.d018163 (M + 1) hR ht
  have hcentered :
      d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
          Real.exp (-((R + k * d ^ 2) / t ^ 2)) ≤
        k⁻¹ * Real.exp (-1) *
          ((R ^ M)⁻¹ * (M.factorial : ℝ)) :=
    _root_.GD.N0232.N0720.N1154.d018164 M (d := d) hR hk ht
  calc
    mu ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
        Real.exp (-((R + k * (c - mu) ^ 2) / t ^ 2)) ≤ _ := hsplit
    _ ≤ 2 * c ^ 2 * ((R ^ (M + 1))⁻¹ *
          ((M + 1).factorial : ℝ)) +
        2 * (k⁻¹ * Real.exp (-1) *
          ((R ^ M)⁻¹ * (M.factorial : ℝ))) := by
      have hc :
          2 * c ^ 2 *
              ((t ^ 2)⁻¹ ^ (M + 1) * Real.exp (-(R / t ^ 2))) ≤
            2 * c ^ 2 *
              ((R ^ (M + 1))⁻¹ * ((M + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hconstant (by positivity)
      have hd :
          2 * (d ^ 2 * (t ^ 2)⁻¹ ^ (M + 1) *
              Real.exp (-((R + k * d ^ 2) / t ^ 2))) ≤
            2 * (k⁻¹ * Real.exp (-1) *
              ((R ^ M)⁻¹ * (M.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left hcentered (by norm_num)
      simpa only [mul_assoc] using add_le_add hc hd





theorem d018166
    (N : ℕ) (hN : 2 ≤ N) (location scale : ℝ)
    (hscale : 0 < scale) (x : _root_.GD.N0137.d008894 N) :
    _root_.GD.N0232.N0719.N0932.d009213 N location scale x =
      scale⁻¹ ^ N * Real.exp
        ((_root_.GD.N0126.d006422 x +
              (N : ℝ) * _root_.GD.N0107.d009084 x ^ 2) / 2 -
          (_root_.GD.N0126.d006422 x +
              (N : ℝ) * (_root_.GD.N0107.d009084 x - location) ^ 2) /
            (2 * scale ^ 2)) := by
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp_rw [_root_.GD.N0232.N0720.N1124.d016497
    location scale _ hscale]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  congr 2
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.sum_div]
  rw [_root_.GD.N0126.d006428]
  rw [_root_.GD.N0126.d006427]
  simp only [_root_.GD.N0126.d006419, Fintype.card_fin,
    _root_.GD.N0107.d009084]


theorem d018167
    (N : ℕ) (hN : 2 ≤ N) (location scale : ℝ)
    (hscale : 0 < scale) (x : _root_.GD.N0137.d008894 N) :
    _root_.GD.N0232.N0719.N0932.d009213 N location scale x ^ 2 =
      (scale ^ 2)⁻¹ ^ N * Real.exp
        (_root_.GD.N0126.d006422 x +
            (N : ℝ) * _root_.GD.N0107.d009084 x ^ 2 -
          (_root_.GD.N0126.d006422 x +
              (N : ℝ) * (_root_.GD.N0107.d009084 x - location) ^ 2) /
            scale ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1154.d018166
    N hN location scale hscale x]
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 1
  · calc
      (scale⁻¹ ^ N) ^ 2 = ((scale ^ N) ^ 2)⁻¹ := by
        rw [inv_pow, inv_pow]
      _ = (scale ^ (N * 2))⁻¹ := by rw [pow_mul]
      _ = (scale ^ (2 * N))⁻¹ := by rw [Nat.mul_comm]
      _ = ((scale ^ 2) ^ N)⁻¹ := by rw [pow_mul]
      _ = (scale ^ 2)⁻¹ ^ N := (inv_pow _ _).symm
  · ring



theorem d018168 {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (x ^ ((N : ℝ) / 2)) ^ 2 = x ^ N := by
  calc
    (x ^ ((N : ℝ) / 2)) ^ 2 =
        (x ^ ((N : ℝ) / 2)) ^ (2 : ℝ) := by
          exact (Real.rpow_two _).symm
    _ = x ^ (((N : ℝ) / 2) * 2) := by
          exact (Real.rpow_mul hx.le _ _).symm
    _ = x ^ (N : ℝ) := by ring_nf
    _ = x ^ N := Real.rpow_natCast x N



theorem d018169
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau ^ 2 =
      _root_.GD.N0107.d009045 m n sigma tau ^ 2 *
        _root_.GD.N0116.d006507
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) ^ 2 *
        _root_.GD.N0107.d009046 m n sigma tau ^ (m + 2) *
        (1 - _root_.GD.N0107.d009046 m n sigma tau) ^ (n + 2) *
        _root_.GD.N0232.N0720.d014160 U ^ 2 := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let alpha : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let beta : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have he1 : 0 < 1 - e :=
    sub_pos.mpr
      (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau)
  have halpha :
      (alpha + (3 : ℝ) / 2) * 2 = ((m + 2 : ℕ) : ℝ) := by
    dsimp only [alpha]
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  have hbeta :
      (beta + (3 : ℝ) / 2) * 2 = ((n + 2 : ℕ) : ℝ) := by
    dsimp only [beta]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hepow :
      (e ^ (alpha + (3 : ℝ) / 2)) ^ 2 = e ^ (m + 2) := by
    calc
      (e ^ (alpha + (3 : ℝ) / 2)) ^ 2 =
          (e ^ (alpha + (3 : ℝ) / 2)) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = e ^ ((alpha + (3 : ℝ) / 2) * 2) :=
        (Real.rpow_mul he0.le _ _).symm
      _ = e ^ (((m + 2 : ℕ) : ℝ)) := by rw [halpha]
      _ = e ^ (m + 2) := Real.rpow_natCast _ _
  have h1epow :
      ((1 - e) ^ (beta + (3 : ℝ) / 2)) ^ 2 =
        (1 - e) ^ (n + 2) := by
    calc
      ((1 - e) ^ (beta + (3 : ℝ) / 2)) ^ 2 =
          ((1 - e) ^ (beta + (3 : ℝ) / 2)) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = (1 - e) ^ ((beta + (3 : ℝ) / 2) * 2) :=
        (Real.rpow_mul he1.le _ _).symm
      _ = (1 - e) ^ (((n + 2 : ℕ) : ℝ)) := by rw [hbeta]
      _ = (1 - e) ^ (n + 2) := Real.rpow_natCast _ _
  change
    (_root_.GD.N0107.d009045 m n sigma tau *
      (_root_.GD.N0116.d006507 alpha beta *
        (e ^ (alpha + (3 : ℝ) / 2) *
          (1 - e) ^ (beta + (3 : ℝ) / 2))) *
      _root_.GD.N0232.N0720.d014160 U) ^ 2 = _
  calc
    _ = _root_.GD.N0107.d009045 m n sigma tau ^ 2 *
        _root_.GD.N0116.d006507 alpha beta ^ 2 *
        (e ^ (alpha + (3 : ℝ) / 2)) ^ 2 *
        ((1 - e) ^ (beta + (3 : ℝ) / 2)) ^ 2 *
        _root_.GD.N0232.N0720.d014160 U ^ 2 := by ring
    _ = _ := by rw [hepow, h1epow]


theorem d018170
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau ^ 2 =
      (_root_.GD.N0116.d006507
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) * _root_.GD.N0232.N0720.d014160 U) ^ 2 *
        ((tau ^ 2 / (n : ℝ)) ^ (m + 2) *
          (sigma ^ 2 / (m : ℝ)) ^ (n + 2)) /
        (sigma ^ 2 / (m : ℝ) + tau ^ 2 / (n : ℝ)) ^
          (m + n + 2) := by
  rw [_root_.GD.N0232.N0720.N1154.d018169
    m n hm hn U sigma tau hsigma htau]
  simp only [_root_.GD.N0107.d009045, _root_.GD.N0107.d009043, _root_.GD.N0107.d009044,
    _root_.GD.N0107.d009046]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hQ : sigma ^ 2 / (m : ℝ) + tau ^ 2 / (n : ℝ) ≠ 0 := by
    positivity
  have hOneMinus :
      1 - tau ^ 2 / (n : ℝ) /
          (sigma ^ 2 / (m : ℝ) + tau ^ 2 / (n : ℝ)) =
        (sigma ^ 2 / (m : ℝ)) /
          (sigma ^ 2 / (m : ℝ) + tau ^ 2 / (n : ℝ)) := by
    field_simp [hm0, hn0, hQ]
    ring
  rw [hOneMinus]
  have hprojective (a b K g : ℝ) (hab : a + b ≠ 0) :
      (a + b) ^ 2 * K ^ 2 * (b / (a + b)) ^ (m + 2) *
          (a / (a + b)) ^ (n + 2) * g ^ 2 =
        (K * g) ^ 2 * (b ^ (m + 2) * a ^ (n + 2)) /
          (a + b) ^ (m + n + 2) := by
    have hpw :
        (a + b) ^ 2 * (a + b) ^ (m + n + 2) =
          (a + b) ^ (m + 2) * (a + b) ^ (n + 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [div_pow, div_pow]
    field_simp [hab]
    calc
      _ = K ^ 2 * b ^ (m + 2) * a ^ (n + 2) * g ^ 2 *
          ((a + b) ^ 2 * (a + b) ^ (m + n + 2)) := by ring
      _ = K ^ 2 * b ^ (m + 2) * a ^ (n + 2) * g ^ 2 *
          ((a + b) ^ (m + 2) * (a + b) ^ (n + 2)) := by rw [hpw]
      _ = _ := by ring
  exact hprojective
    (sigma ^ 2 / (m : ℝ)) (tau ^ 2 / (n : ℝ))
    (_root_.GD.N0116.d006507 (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)) (_root_.GD.N0232.N0720.d014160 U) hQ


theorem d018171
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n theta omega ^ 2 =
      (theta.scale₁ ^ 2)⁻¹ ^ m * (theta.scale₂ ^ 2)⁻¹ ^ n *
        Real.exp
          (_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
            (_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2) -
            (_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) *
                  (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
              theta.scale₁ ^ 2 -
            (_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) *
                  (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
              theta.scale₂ ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1499.d015001
  rw [mul_pow,
    _root_.GD.N0232.N0720.N1154.d018167
      m hm theta.location theta.scale₁ theta.scale₁_pos omega.1,
    _root_.GD.N0232.N0720.N1154.d018167
      n hn theta.location theta.scale₂ theta.scale₂_pos omega.2]
  calc
    (theta.scale₁ ^ 2)⁻¹ ^ m * Real.exp
          (_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 -
            (_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) * (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
              theta.scale₁ ^ 2) *
        ((theta.scale₂ ^ 2)⁻¹ ^ n * Real.exp
          (_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2 -
            (_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) * (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
              theta.scale₂ ^ 2)) =
      (theta.scale₁ ^ 2)⁻¹ ^ m * (theta.scale₂ ^ 2)⁻¹ ^ n *
        (Real.exp
          (_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 -
            (_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) * (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
              theta.scale₁ ^ 2) *
        Real.exp
          (_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2 -
            (_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) * (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
              theta.scale₂ ^ 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring


theorem d018172
    (m n : ℕ) {sigma tau : ℝ}
    (hm0 : 0 < (m : ℝ)) (hn0 : 0 < (n : ℝ))
    (hsigma : 0 < sigma) (htau : 0 < tau) :
    (sigma ^ 2)⁻¹ ^ m * (tau ^ 2)⁻¹ ^ n *
        (sigma ^ 2 / (m : ℝ) + tau ^ 2 / (n : ℝ)) ^
          (m + n + 2) /
      ((tau ^ 2 / (n : ℝ)) ^ (m + 2) *
        (sigma ^ 2 / (m : ℝ)) ^ (n + 2)) =
    (m : ℝ) ^ (n + 2) * (n : ℝ) ^ (m + 2) *
      (1 / ((m : ℝ) * tau ^ 2) +
        1 / ((n : ℝ) * sigma ^ 2)) ^ (m + n + 2) := by
  let a : ℝ := sigma ^ 2
  let b : ℝ := tau ^ 2
  let M : ℝ := m
  let N : ℝ := n
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hb : b ≠ 0 := by
    dsimp [b]
    positivity
  have hM : M ≠ 0 := by
    dsimp [M]
    positivity
  have hN : N ≠ 0 := by
    dsimp [N]
    positivity
  change
    a⁻¹ ^ m * b⁻¹ ^ n * (a / M + b / N) ^ (m + n + 2) /
        ((b / N) ^ (m + 2) * (a / M) ^ (n + 2)) =
      M ^ (n + 2) * N ^ (m + 2) *
        (1 / (M * b) + 1 / (N * a)) ^ (m + n + 2)
  have hbase :
      1 / (M * b) + 1 / (N * a) =
        (a / M + b / N) / (a * b) := by
    field_simp [ha, hb, hM, hN]
  rw [hbase, div_pow, div_pow, div_pow, inv_pow, inv_pow]
  field_simp [ha, hb, hM, hN]
  ring




theorem d018173
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (|_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| /
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) ^ 2 =
      (Real.exp
          (_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
            (_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2)) *
        (m : ℝ) ^ (n + 2) * (n : ℝ) ^ (m + 2) /
        (_root_.GD.N0116.d006507
            (((m - 1 : ℕ) : ℝ) / 2)
            (((n - 1 : ℕ) : ℝ) / 2) * _root_.GD.N0232.N0720.d014160 U) ^ 2) *
      (theta.location ^ 2 *
        (1 / ((m : ℝ) * theta.scale₂ ^ 2) +
          1 / ((n : ℝ) * theta.scale₁ ^ 2)) ^ (m + n + 2) *
        Real.exp
          (-((_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) *
                  (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
              theta.scale₁ ^ 2) -
            ((_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) *
                  (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
              theta.scale₂ ^ 2))) := by
  have hm0 : 0 < (m : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  let K : ℝ := _root_.GD.N0116.d006507
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2) * _root_.GD.N0232.N0720.d014160 U
  let P : ℝ :=
    (theta.scale₂ ^ 2 / (n : ℝ)) ^ (m + 2) *
      (theta.scale₁ ^ 2 / (m : ℝ)) ^ (n + 2)
  let Qp : ℝ :=
    (theta.scale₁ ^ 2 / (m : ℝ) +
      theta.scale₂ ^ 2 / (n : ℝ)) ^ (m + n + 2)
  let AScale : ℝ :=
    (theta.scale₁ ^ 2)⁻¹ ^ m * (theta.scale₂ ^ 2)⁻¹ ^ n
  let base : ℝ :=
    1 / ((m : ℝ) * theta.scale₂ ^ 2) +
      1 / ((n : ℝ) * theta.scale₁ ^ 2)
  let scaleConstant : ℝ :=
    (m : ℝ) ^ (n + 2) * (n : ℝ) ^ (m + 2)
  have hKPos : 0 < K := by
    dsimp [K]
    have halpha : 0 < (((m - 1 : ℕ) : ℝ) / 2) := by
      have : 0 < (m - 1 : ℕ) := by omega
      positivity
    have hbeta : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
      have : 0 < (n - 1 : ℕ) := by omega
      positivity
    exact mul_pos
      (_root_.GD.N0120.d008821 halpha hbeta)
      (_root_.GD.N0232.N0720.d014165 U)
  have hPPos : 0 < P := by
    dsimp [P]
    exact mul_pos
      (pow_pos (div_pos (sq_pos_of_pos theta.scale₂_pos) hn0) _)
      (pow_pos (div_pos (sq_pos_of_pos theta.scale₁_pos) hm0) _)
  have hQpPos : 0 < Qp := by
    dsimp [Qp]
    exact pow_pos (add_pos
      (div_pos (sq_pos_of_pos theta.scale₁_pos) hm0)
      (div_pos (sq_pos_of_pos theta.scale₂_pos) hn0)) _
  have hscale :
      AScale * Qp / P = scaleConstant * base ^ (m + n + 2) := by
    simpa only [AScale, Qp, P, scaleConstant, base] using
      (_root_.GD.N0232.N0720.N1154.d018172 m n hm0 hn0
        theta.scale₁_pos theta.scale₂_pos)
  have hnormalize :
      AScale / (K ^ 2 * P / Qp) =
        scaleConstant * base ^ (m + n + 2) / K ^ 2 := by
    calc
      AScale / (K ^ 2 * P / Qp) =
          (AScale * Qp / P) / K ^ 2 := by
            field_simp [hKPos.ne', hPPos.ne', hQpPos.ne']
      _ = scaleConstant * base ^ (m + n + 2) / K ^ 2 := by rw [hscale]
  rw [div_pow, sq_abs, mul_pow]
  rw [_root_.GD.N0232.N0720.N1154.d018171 m n hm hn]
  rw [_root_.GD.N0232.N0720.N1154.d018170
    m n hm hn U theta.scale₁_pos theta.scale₂_pos]
  change (AScale * Real.exp _ * theta.location ^ 2) /
      (K ^ 2 * P / Qp) = _
  rw [show Real.exp
      (_root_.GD.N0126.d006422 omega.1 +
          (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
        (_root_.GD.N0126.d006422 omega.2 +
          (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2) -
        (_root_.GD.N0126.d006422 omega.1 +
            (m : ℝ) *
              (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
          theta.scale₁ ^ 2 -
        (_root_.GD.N0126.d006422 omega.2 +
            (n : ℝ) *
              (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
          theta.scale₂ ^ 2) =
      Real.exp
        (_root_.GD.N0126.d006422 omega.1 +
            (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
          (_root_.GD.N0126.d006422 omega.2 +
            (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2)) *
      Real.exp
        (-((_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) *
                (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
            theta.scale₁ ^ 2) -
          ((_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) *
                (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
            theta.scale₂ ^ 2)) by
        rw [← Real.exp_add]
        congr 1
        ring]
  calc
    (AScale *
        (Real.exp
            (_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
              (_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2)) *
          Real.exp
            (-((_root_.GD.N0126.d006422 omega.1 +
                  (m : ℝ) *
                    (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
                theta.scale₁ ^ 2) -
              ((_root_.GD.N0126.d006422 omega.2 +
                  (n : ℝ) *
                    (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
                theta.scale₂ ^ 2))) * theta.location ^ 2) /
          (K ^ 2 * P / Qp) =
      (AScale / (K ^ 2 * P / Qp)) *
        (Real.exp
            (_root_.GD.N0126.d006422 omega.1 +
                (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
              (_root_.GD.N0126.d006422 omega.2 +
                (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2) * 1) *
          theta.location ^ 2 *
          Real.exp
            (-((_root_.GD.N0126.d006422 omega.1 +
                  (m : ℝ) *
                    (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
                theta.scale₁ ^ 2) -
              ((_root_.GD.N0126.d006422 omega.2 +
                  (n : ℝ) *
                    (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
                theta.scale₂ ^ 2))) := by ring
    _ = _ := by
      rw [hnormalize]
      dsimp [scaleConstant, base, K]
      ring





theorem d018174
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hx : 0 < _root_.GD.N0126.d006422 omega.1)
    (hy : 0 < _root_.GD.N0126.d006422 omega.2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      theta.location ^ 2 *
          (1 / ((m : ℝ) * theta.scale₂ ^ 2) +
            1 / ((n : ℝ) * theta.scale₁ ^ 2)) ^ (m + n + 2) *
          Real.exp
            (-((_root_.GD.N0126.d006422 omega.1 +
                  (m : ℝ) *
                    (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
                theta.scale₁ ^ 2) -
              ((_root_.GD.N0126.d006422 omega.2 +
                  (n : ℝ) *
                    (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
                theta.scale₂ ^ 2)) ≤ B := by
  let M : ℕ := m + n + 1
  let Bx : ℝ :=
    2 * _root_.GD.N0107.d009084 omega.1 ^ 2 *
        ((_root_.GD.N0126.d006422 omega.1 ^ (M + 1))⁻¹ *
          ((M + 1).factorial : ℝ)) +
      2 * (((m : ℝ))⁻¹ * Real.exp (-1) *
        ((_root_.GD.N0126.d006422 omega.1 ^ M)⁻¹ *
          (M.factorial : ℝ)))
  let By : ℝ :=
    2 * _root_.GD.N0107.d009084 omega.2 ^ 2 *
        ((_root_.GD.N0126.d006422 omega.2 ^ (M + 1))⁻¹ *
          ((M + 1).factorial : ℝ)) +
      2 * (((n : ℝ))⁻¹ * Real.exp (-1) *
        ((_root_.GD.N0126.d006422 omega.2 ^ M)⁻¹ *
          (M.factorial : ℝ)))
  let B : ℝ :=
    2 ^ ((m + n + 2) - 1) *
      (((m : ℝ))⁻¹ ^ (m + n + 2) * By +
        ((n : ℝ))⁻¹ ^ (m + n + 2) * Bx)
  have hm0 : 0 < (m : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hBx : 0 ≤ Bx := by
    dsimp [Bx]
    positivity
  have hBy : 0 ≤ By := by
    dsimp [By]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro theta
  let u : ℝ := 1 / ((m : ℝ) * theta.scale₂ ^ 2)
  let v : ℝ := 1 / ((n : ℝ) * theta.scale₁ ^ 2)
  let X : ℝ := _root_.GD.N0126.d006422 omega.1 +
    (m : ℝ) * (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2
  let Y : ℝ := _root_.GD.N0126.d006422 omega.2 +
    (n : ℝ) * (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hpow := add_pow_le hu hv (m + n + 2)
  have hExpDropX :
      Real.exp (-(X / theta.scale₁ ^ 2) -
          Y / theta.scale₂ ^ 2) ≤
        Real.exp (-(X / theta.scale₁ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Y / theta.scale₂ ^ 2 := by positivity
    linarith
  have hExpDropY :
      Real.exp (-(X / theta.scale₁ ^ 2) -
          Y / theta.scale₂ ^ 2) ≤
        Real.exp (-(Y / theta.scale₂ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ X / theta.scale₁ ^ 2 := by positivity
    linarith
  have hlocX := _root_.GD.N0232.N0720.N1154.d018165 M hx hm0
    theta.scale₁_pos
    (c := _root_.GD.N0107.d009084 omega.1) (mu := theta.location)
  have hlocY := _root_.GD.N0232.N0720.N1154.d018165 M hy hn0
    theta.scale₂_pos
    (c := _root_.GD.N0107.d009084 omega.2) (mu := theta.location)
  have hlocX' :
      theta.location ^ 2 * (theta.scale₁ ^ 2)⁻¹ ^ (m + n + 2) *
          Real.exp (-(X / theta.scale₁ ^ 2)) ≤ Bx := by
    simpa only [M, X, Bx, Nat.add_assoc] using hlocX
  have hlocY' :
      theta.location ^ 2 * (theta.scale₂ ^ 2)⁻¹ ^ (m + n + 2) *
          Real.exp (-(Y / theta.scale₂ ^ 2)) ≤ By := by
    simpa only [M, Y, By, Nat.add_assoc] using hlocY
  have huPow :
      u ^ (m + n + 2) =
        ((m : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.scale₂ ^ 2)⁻¹ ^ (m + n + 2) := by
    dsimp [u]
    rw [one_div, mul_inv, mul_pow]
  have hvPow :
      v ^ (m + n + 2) =
        ((n : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.scale₁ ^ 2)⁻¹ ^ (m + n + 2) := by
    dsimp [v]
    rw [one_div, mul_inv, mul_pow]
  have huTerm :
      theta.location ^ 2 * u ^ (m + n + 2) *
          Real.exp (-(X / theta.scale₁ ^ 2) -
            Y / theta.scale₂ ^ 2) ≤
        ((m : ℝ))⁻¹ ^ (m + n + 2) * By := by
    rw [huPow]
    calc
      theta.location ^ 2 *
          (((m : ℝ))⁻¹ ^ (m + n + 2) *
            (theta.scale₂ ^ 2)⁻¹ ^ (m + n + 2)) *
          Real.exp (-(X / theta.scale₁ ^ 2) -
            Y / theta.scale₂ ^ 2) =
        ((m : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.location ^ 2 *
            (theta.scale₂ ^ 2)⁻¹ ^ (m + n + 2) *
            Real.exp (-(X / theta.scale₁ ^ 2) -
              Y / theta.scale₂ ^ 2)) := by ring
      _ ≤ ((m : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.location ^ 2 *
            (theta.scale₂ ^ 2)⁻¹ ^ (m + n + 2) *
            Real.exp (-(Y / theta.scale₂ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hExpDropY
        positivity
      _ ≤ ((m : ℝ))⁻¹ ^ (m + n + 2) * By :=
        mul_le_mul_of_nonneg_left hlocY' (by positivity)
  have hvTerm :
      theta.location ^ 2 * v ^ (m + n + 2) *
          Real.exp (-(X / theta.scale₁ ^ 2) -
            Y / theta.scale₂ ^ 2) ≤
        ((n : ℝ))⁻¹ ^ (m + n + 2) * Bx := by
    rw [hvPow]
    calc
      theta.location ^ 2 *
          (((n : ℝ))⁻¹ ^ (m + n + 2) *
            (theta.scale₁ ^ 2)⁻¹ ^ (m + n + 2)) *
          Real.exp (-(X / theta.scale₁ ^ 2) -
            Y / theta.scale₂ ^ 2) =
        ((n : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.location ^ 2 *
            (theta.scale₁ ^ 2)⁻¹ ^ (m + n + 2) *
            Real.exp (-(X / theta.scale₁ ^ 2) -
              Y / theta.scale₂ ^ 2)) := by ring
      _ ≤ ((n : ℝ))⁻¹ ^ (m + n + 2) *
          (theta.location ^ 2 *
            (theta.scale₁ ^ 2)⁻¹ ^ (m + n + 2) *
            Real.exp (-(X / theta.scale₁ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hExpDropX
        positivity
      _ ≤ ((n : ℝ))⁻¹ ^ (m + n + 2) * Bx :=
        mul_le_mul_of_nonneg_left hlocX' (by positivity)
  change theta.location ^ 2 * (u + v) ^ (m + n + 2) *
      Real.exp (-(X / theta.scale₁ ^ 2) -
        Y / theta.scale₂ ^ 2) ≤ B
  calc
    theta.location ^ 2 * (u + v) ^ (m + n + 2) *
        Real.exp (-(X / theta.scale₁ ^ 2) -
          Y / theta.scale₂ ^ 2) ≤
      theta.location ^ 2 *
          (2 ^ ((m + n + 2) - 1) *
            (u ^ (m + n + 2) + v ^ (m + n + 2))) *
        Real.exp (-(X / theta.scale₁ ^ 2) -
          Y / theta.scale₂ ^ 2) := by
            gcongr
    _ = 2 ^ ((m + n + 2) - 1) *
        (theta.location ^ 2 * u ^ (m + n + 2) *
            Real.exp (-(X / theta.scale₁ ^ 2) -
              Y / theta.scale₂ ^ 2) +
          theta.location ^ 2 * v ^ (m + n + 2) *
            Real.exp (-(X / theta.scale₁ ^ 2) -
              Y / theta.scale₂ ^ 2)) := by ring
    _ ≤ 2 ^ ((m + n + 2) - 1) *
        (((m : ℝ))⁻¹ ^ (m + n + 2) * By +
          ((n : ℝ))⁻¹ ^ (m + n + 2) * Bx) := by
      exact mul_le_mul_of_nonneg_left (add_le_add huTerm hvTerm) (by positivity)
    _ = B := by rfl



theorem d018175
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hx : 0 < _root_.GD.N0126.d006422 omega.1)
    (hy : 0 < _root_.GD.N0126.d006422 omega.2) :
    _root_.GD.N0232.N0720.N1145.d018022 m n hm hn U omega := by
  obtain ⟨B, hB, hnormalized⟩ :=
    _root_.GD.N0232.N0720.N1154.d018174 m n hm hn omega hx hy
  let D : ℝ :=
    Real.exp
        (_root_.GD.N0126.d006422 omega.1 +
            (m : ℝ) * _root_.GD.N0107.d009084 omega.1 ^ 2 +
          (_root_.GD.N0126.d006422 omega.2 +
            (n : ℝ) * _root_.GD.N0107.d009084 omega.2 ^ 2)) *
      (m : ℝ) ^ (n + 2) * (n : ℝ) ^ (m + 2) /
      (_root_.GD.N0116.d006507
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) * _root_.GD.N0232.N0720.d014160 U) ^ 2
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  let C : ℝ := 16 * Real.sqrt (D * B)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro theta
  have hgap := _root_.GD.N0232.N0720.N1082.d015391 m n hm hn U
    theta.scale₁_pos theta.scale₂_pos
  let F : ℝ :=
    theta.location ^ 2 *
      (1 / ((m : ℝ) * theta.scale₂ ^ 2) +
        1 / ((n : ℝ) * theta.scale₁ ^ 2)) ^ (m + n + 2) *
      Real.exp
        (-((_root_.GD.N0126.d006422 omega.1 +
              (m : ℝ) *
                (_root_.GD.N0107.d009084 omega.1 - theta.location) ^ 2) /
            theta.scale₁ ^ 2) -
          ((_root_.GD.N0126.d006422 omega.2 +
              (n : ℝ) *
                (_root_.GD.N0107.d009084 omega.2 - theta.location) ^ 2) /
            theta.scale₂ ^ 2))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFB : F ≤ B := by
    simpa only [F] using hnormalized theta
  have hratioSq :
      (|_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| /
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) ^ 2 ≤
        D * B := by
    rw [_root_.GD.N0232.N0720.N1154.d018173
      m n hm hn U omega theta]
    change D * F ≤ D * B
    exact mul_le_mul_of_nonneg_left hFB hD
  have hDB : 0 ≤ D * B := mul_nonneg hD hB
  have hratioNonneg :
      0 ≤ |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| /
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    positivity
  have hratio :
      |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| /
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ ≤
        Real.sqrt (D * B) := by
    apply (sq_le_sq₀ hratioNonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hDB]
    exact hratioSq
  have habs :
      |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| ≤
        Real.sqrt (D * B) *
          _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    exact (div_le_iff₀ hgap).mp hratio
  simpa only [C] using (show
    |_root_.GD.N0232.N0720.N1499.d015001 m n theta omega * theta.location| ≤
      (16 * Real.sqrt (D * B)) *
        (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ / 16) by
      convert habs using 1
      all_goals ring)



theorem d018176
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      0 < _root_.GD.N0126.d006422 omega.1 ∧
        0 < _root_.GD.N0126.d006422 omega.2 := by
  have href :
      _root_.GD.N0232.N0720.N1080.d014172 m n =
        (_root_.GD.N0137.d008895 m).prod (_root_.GD.N0137.d008895 n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
      _root_.GD.N0137.d008914 _root_.GD.N0232.N0720.N1080.d014169
      _root_.GD.N0107.d009024
      _root_.GD.N0107.d009018
    simp
  rw [href]
  have hx :=
    (measurePreserving_fst
      (μ := _root_.GD.N0137.d008895 m)
      (ν := _root_.GD.N0137.d008895 n)).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0832.d012009 m hm)
  have hy :=
    (measurePreserving_snd
      (μ := _root_.GD.N0137.d008895 m)
      (ν := _root_.GD.N0137.d008895 n)).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0832.d012009 n hn)
  exact hx.and hy



theorem d018177
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1145.d018023 m n hm hn U := by
  filter_upwards [_root_.GD.N0232.N0720.N1154.d018176 m n hm hn] with
      omega homega
  exact _root_.GD.N0232.N0720.N1154.d018175
    m n hm hn U omega homega.1 homega.2




theorem d018178
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {Irow : ℕ → Type*}
    [∀ j, Fintype (Irow j)] [∀ j, DecidableEq (Irow j)]
    (packet : ∀ j, Irow j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Irow j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) :
    ¬ Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          (packet j) (weight j)) atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1145.d018026
    U (_root_.GD.N0232.N0720.N1154.d018177 m n hm hn U)
      packet weight hweight





theorem d018179
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ (k : ℕ) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (weight : Fin k → ℝ),
        (∀ i, 0 ≤ weight i) →
        eta ≤ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
            packet weight := by
  classical
  by_contra hfloor
  push Not at hfloor
  have hchoose : ∀ j : ℕ,
      ∃ (k : ℕ) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (weight : Fin k → ℝ),
        (∀ i, 0 ≤ weight i) ∧
          ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
              packet weight < 1 / ((j : ℝ) + 1) := by
    intro j
    exact hfloor (1 / ((j : ℝ) + 1)) (by positivity)
  choose width packet weight hweight hbound using hchoose
  have htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          (packet j) (weight j)) atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ (_root_.GD.N0232.N0720.N1144.d018007 U
        (packet j) (weight j) (hweight j)).le)
      (fun j ↦ (hbound j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact (_root_.GD.N0232.N0720.N1154.d018178
    (Irow := fun j ↦ Fin (width j)) U packet weight hweight) htight

end

end N1154
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1154.d018173
#print axioms _root_.GD.N0232.N0720.N1154.d018177
#print axioms _root_.GD.N0232.N0720.N1154.d018178
#print axioms _root_.GD.N0232.N0720.N1154.d018179
