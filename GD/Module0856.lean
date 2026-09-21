import GD.Module0855
import Mathlib.MeasureTheory.Integral.DominatedConvergence





















open MeasureTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1428

noncomputable section

open _root_.GD.N0232.N0720.N1421




def d013133 (beta : ℝ) : ℝ :=
  4 * (beta + 1) / beta

theorem d013134
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1428.d013133 beta := by
  unfold _root_.GD.N0232.N0720.N1428.d013133
  positivity



noncomputable def d013135 (beta X : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1428.d013133 beta * X *
    (beta / (beta + 2 * X)) ^ (beta + 2)



def d013136 (t X : ℝ) : ℝ :=
  (1 - t) * (1 - X) / ((1 - t) * X + t)


noncomputable def d013137 (t u : ℝ) : ℝ :=
  (1 - t) / (1 - t + t ^ u)


noncomputable def d013138 (t u : ℝ) : ℝ :=
  1 - _root_.GD.N0232.N0720.N1421.d013128 t u


noncomputable def d013139 (beta t u : ℝ) : ℝ :=
  (beta / (beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 t u)) ^ (beta + 2)


noncomputable def d013140 (beta t u : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1428.d013137 t u ^ 2 *
    _root_.GD.N0232.N0720.N1428.d013138 t u ^ 2 *
      _root_.GD.N0232.N0720.N1428.d013139 beta t u

theorem d013141 (beta t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1428.d013140 beta t) := by
  unfold _root_.GD.N0232.N0720.N1428.d013140 _root_.GD.N0232.N0720.N1428.d013137 _root_.GD.N0232.N0720.N1428.d013138
    _root_.GD.N0232.N0720.N1428.d013139 _root_.GD.N0232.N0720.N1421.d013128 _root_.GD.N0232.N0720.N1421.d013126
  fun_prop




theorem d013142
    {t u : ℝ} (ht : 0 < t) :
    _root_.GD.N0232.N0720.N1421.d013128 t u * t ^ u = t := by
  unfold _root_.GD.N0232.N0720.N1421.d013128
  rw [_root_.GD.N0232.N0720.N1421.d013127]
  calc
    t ^ (1 - u) * t ^ u = t ^ ((1 - u) + u) :=
      (Real.rpow_add ht (1 - u) u).symm
    _ = t := by simp



theorem d013143
    {t u : ℝ} (ht : 0 < t) :
    (1 - t) * _root_.GD.N0232.N0720.N1421.d013128 t u + t =
      _root_.GD.N0232.N0720.N1421.d013128 t u * (1 - t + t ^ u) := by
  rw [mul_add]
  rw [_root_.GD.N0232.N0720.N1428.d013142 ht]
  ring


theorem d013144
    {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1428.d013136 t (_root_.GD.N0232.N0720.N1421.d013128 t u) =
      _root_.GD.N0232.N0720.N1428.d013137 t u * _root_.GD.N0232.N0720.N1428.d013138 t u /
        _root_.GD.N0232.N0720.N1421.d013128 t u := by
  have hx : 0 < _root_.GD.N0232.N0720.N1421.d013128 t u :=
    Real.rpow_pos_of_pos ht0 _
  have hstable : 0 < 1 - t + t ^ u := by
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht1)
      (Real.rpow_nonneg ht0.le _)
  unfold _root_.GD.N0232.N0720.N1428.d013136 _root_.GD.N0232.N0720.N1428.d013137
    _root_.GD.N0232.N0720.N1428.d013138
  rw [_root_.GD.N0232.N0720.N1428.d013143 ht0]
  field_simp [hx.ne', hstable.ne']



theorem d013145
    {beta t u : ℝ}
    (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1428.d013135 beta (_root_.GD.N0232.N0720.N1421.d013128 t u) *
        _root_.GD.N0232.N0720.N1428.d013136 t (_root_.GD.N0232.N0720.N1421.d013128 t u) ^ 2 *
          _root_.GD.N0232.N0720.N1421.d013128 t u =
      _root_.GD.N0232.N0720.N1428.d013133 beta * _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
  have hx : _root_.GD.N0232.N0720.N1421.d013128 t u ≠ 0 :=
    (Real.rpow_pos_of_pos ht0 _).ne'
  rw [_root_.GD.N0232.N0720.N1428.d013144 ht0 ht1]
  unfold _root_.GD.N0232.N0720.N1428.d013135 _root_.GD.N0232.N0720.N1428.d013140 _root_.GD.N0232.N0720.N1428.d013139
  field_simp [hx]



theorem d013146
    {beta t u : ℝ}
    (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1428.d013135 beta (_root_.GD.N0232.N0720.N1421.d013128 t u) *
        _root_.GD.N0232.N0720.N1428.d013136 t (_root_.GD.N0232.N0720.N1421.d013128 t u) ^ 2 *
          |(-Real.log t) * _root_.GD.N0232.N0720.N1421.d013128 t u| =
      _root_.GD.N0232.N0720.N1428.d013133 beta * Real.log (1 / t) *
        _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
  rw [_root_.GD.N0232.N0720.N1421.d013132 ht0 ht1]
  calc
    _ = Real.log (1 / t) *
        (_root_.GD.N0232.N0720.N1428.d013135 beta (_root_.GD.N0232.N0720.N1421.d013128 t u) *
          _root_.GD.N0232.N0720.N1428.d013136 t (_root_.GD.N0232.N0720.N1421.d013128 t u) ^ 2 *
            _root_.GD.N0232.N0720.N1421.d013128 t u) := by ring
    _ = Real.log (1 / t) *
        (_root_.GD.N0232.N0720.N1428.d013133 beta *
          _root_.GD.N0232.N0720.N1428.d013140 beta t u) := by
      rw [_root_.GD.N0232.N0720.N1428.d013145 hbeta ht0 ht1]
    _ = _ := by ring



theorem d013147
    {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1421.d013128 t u ∈ Icc (0 : ℝ) 1 := by
  have hexp : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  exact ⟨(Real.rpow_pos_of_pos ht0 _).le,
    Real.rpow_le_one ht0.le ht1.le hexp⟩

theorem d013148
    {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1428.d013137 t u ∈ Icc (0 : ℝ) 1 := by
  have hnum : 0 < 1 - t := sub_pos.mpr ht1
  have hpow : 0 ≤ t ^ u := Real.rpow_nonneg ht0.le _
  have hden : 0 < 1 - t + t ^ u := add_pos_of_pos_of_nonneg hnum hpow
  unfold _root_.GD.N0232.N0720.N1428.d013137
  exact ⟨div_nonneg hnum.le hden.le,
    (div_le_one hden).2 (le_add_of_nonneg_right hpow)⟩

theorem d013149
    {t u : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1428.d013138 t u ∈ Icc (0 : ℝ) 1 := by
  have hx := _root_.GD.N0232.N0720.N1428.d013147 ht0 ht1 hu
  have hx0 : 0 ≤ _root_.GD.N0232.N0720.N1421.d013128 t u := hx.1
  have hx1 : _root_.GD.N0232.N0720.N1421.d013128 t u ≤ 1 := hx.2
  unfold _root_.GD.N0232.N0720.N1428.d013138
  constructor <;> linarith

theorem d013150
    {beta t u : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) :
    _root_.GD.N0232.N0720.N1428.d013139 beta t u ∈ Icc (0 : ℝ) 1 := by
  have hx : 0 ≤ _root_.GD.N0232.N0720.N1421.d013128 t u :=
    Real.rpow_nonneg ht0.le _
  have hden : 0 < beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 t u := by positivity
  have hbase0 : 0 ≤ beta / (beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 t u) :=
    div_nonneg hbeta.le hden.le
  have hbase1 : beta / (beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 t u) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have hexp : 0 ≤ beta + 2 := by linarith
  unfold _root_.GD.N0232.N0720.N1428.d013139
  exact ⟨Real.rpow_nonneg hbase0 _, Real.rpow_le_one hbase0 hbase1 hexp⟩


theorem d013151
    {beta t u : ℝ}
    (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1428.d013140 beta t u ∈ Icc (0 : ℝ) 1 := by
  have hA := _root_.GD.N0232.N0720.N1428.d013148 (u := u) ht0 ht1
  have hB := _root_.GD.N0232.N0720.N1428.d013149 ht0 ht1 hu
  have hC := _root_.GD.N0232.N0720.N1428.d013150 (beta := beta) (u := u) hbeta ht0
  have hA2 : _root_.GD.N0232.N0720.N1428.d013137 t u ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hA.1 zero_le_one).2 hA.2
  have hB2 : _root_.GD.N0232.N0720.N1428.d013138 t u ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hB.1 zero_le_one).2 hB.2
  have hAB0 : 0 ≤ _root_.GD.N0232.N0720.N1428.d013137 t u ^ 2 *
      _root_.GD.N0232.N0720.N1428.d013138 t u ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hAB1 : _root_.GD.N0232.N0720.N1428.d013137 t u ^ 2 *
      _root_.GD.N0232.N0720.N1428.d013138 t u ^ 2 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hA2 hB2 (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  unfold _root_.GD.N0232.N0720.N1428.d013140
  constructor
  · exact mul_nonneg hAB0 hC.1
  · calc
      _ ≤ 1 * 1 := mul_le_mul hAB1 hC.2 hC.1 zero_le_one
      _ = 1 := by ring



theorem d013152
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => p n ^ a) atTop (nhds 0) := by
  have hcontinuous := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h := hcontinuous.tendsto.comp hp
  have hzero : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha.ne'
  rw [hzero] at h
  exact h.congr' (Eventually.of_forall fun _ => rfl)



theorem d013153
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => _root_.GD.N0232.N0720.N1428.d013140 beta (p n) u)
      atTop (nhds 1) := by
  have hx : Tendsto (fun n => _root_.GD.N0232.N0720.N1421.d013128 (p n) u)
      atTop (nhds 0) := by
    unfold _root_.GD.N0232.N0720.N1421.d013128
    rw [show _root_.GD.N0232.N0720.N1421.d013126 u = 1 - u by
      exact _root_.GD.N0232.N0720.N1421.d013127 u]
    exact _root_.GD.N0232.N0720.N1428.d013152 hp (sub_pos.mpr hu.2)
  have hpu : Tendsto (fun n => p n ^ u) atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1428.d013152 hp hu.1
  have honeSub : Tendsto (fun n => 1 - p n) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hp using 1 <;> ring
  have htransport : Tendsto
      (fun n => _root_.GD.N0232.N0720.N1428.d013137 (p n) u) atTop (nhds 1) := by
    have h := honeSub.div (honeSub.add hpu)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simp only [add_zero, div_one] at h
    exact h.congr' (Eventually.of_forall fun _ => rfl)
  have hendpoint : Tendsto
      (fun n => _root_.GD.N0232.N0720.N1428.d013138 (p n) u) atTop (nhds 1) := by
    unfold _root_.GD.N0232.N0720.N1428.d013138
    convert tendsto_const_nhds.sub hx using 1 <;> ring
  have hbase : Tendsto
      (fun n => beta / (beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 (p n) u))
      atTop (nhds 1) := by
    have hden : Tendsto
        (fun n => beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 (p n) u)
        atTop (nhds beta) := by
      convert tendsto_const_nhds.add (hx.const_mul 2) using 1 <;> ring
    have hnum : Tendsto (fun _ : ℕ => beta) atTop (nhds beta) :=
      tendsto_const_nhds
    have hratio := hnum.div hden hbeta.ne'
    have hratio' : Tendsto
        (fun n => beta / (beta + 2 * _root_.GD.N0232.N0720.N1421.d013128 (p n) u))
        atTop (nhds (beta / beta)) :=
      hratio.congr' (Eventually.of_forall fun _ => rfl)
    convert hratio' using 1 <;> field_simp [hbeta.ne']
  have hdensity : Tendsto
      (fun n => _root_.GD.N0232.N0720.N1428.d013139 beta (p n) u)
      atTop (nhds 1) := by
    unfold _root_.GD.N0232.N0720.N1428.d013139
    have hcontinuous :=
      Real.continuousAt_rpow_const 1 (beta + 2) (Or.inl one_ne_zero)
    have h := hcontinuous.tendsto.comp hbase
    rw [Real.one_rpow] at h
    exact h.congr' (Eventually.of_forall fun _ => rfl)
  unfold _root_.GD.N0232.N0720.N1428.d013140
  convert (htransport.pow 2).mul ((hendpoint.pow 2).mul hdensity) using 1 <;>
    ring



theorem d013154
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => ∫ u in Ioo (0 : ℝ) 1,
        _root_.GD.N0232.N0720.N1428.d013140 beta (p n) u)
      atTop (nhds 1) := by
  have hdc : Tendsto
      (fun n => ∫ u, _root_.GD.N0232.N0720.N1428.d013140 beta (p n) u
        ∂volume.restrict (Ioo (0 : ℝ) 1))
      atTop
      (nhds (∫ _ : ℝ, 1 ∂volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => 1)
    · exact Filter.Eventually.of_forall fun n =>
        (_root_.GD.N0232.N0720.N1428.d013141 beta (p n)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hw := _root_.GD.N0232.N0720.N1428.d013151 hbeta (hp0 n) (hp1 n)
          ⟨hu.1.le, hu.2.le⟩
        rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
        exact hw.2
    · exact integrableOn_const (by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact _root_.GD.N0232.N0720.N1428.d013153 hbeta hp hp0 hp1 hu
  simpa [Real.volume_Ioo] using hdc

end

end N1428
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1428.d013146
#print axioms _root_.GD.N0232.N0720.N1428.d013151
#print axioms _root_.GD.N0232.N0720.N1428.d013153
#print axioms _root_.GD.N0232.N0720.N1428.d013154
