import GD.Module1366
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Ring
import GD.Module0757
import GD.Module1260
import GD.Module0664
import GD.Module1261
import GD.Module1262
import GD.Module1270










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace GD.N0213.N0498

open _root_.GD.N0213.N0497

noncomputable section

variable {K : Type*} [MetricSpace K]

def d022018 (M a : ℝ) : ℝ := max (-M) (min M a)

theorem d022019 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) : |_root_.GD.N0213.N0498.d022018 M a| ≤ M := by
  apply abs_le.2
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem d022020 {M a : ℝ} (ha : |a| ≤ M) : _root_.GD.N0213.N0498.d022018 M a = a := by
  rcases abs_le.1 ha with ⟨hl, hu⟩
  simp only [_root_.GD.N0213.N0498.d022018, min_eq_right hu, max_eq_right hl]

theorem d022021 {M : ℝ} (hM : 0 ≤ M) (a : ℝ) :
    |a - _root_.GD.N0213.N0498.d022018 M a| ≤ |a| := by
  by_cases hl : a < -M
  · have ha : a < 0 := by linarith
    have ham : a ≤ M := by linarith
    rw [_root_.GD.N0213.N0498.d022018, min_eq_right ham, max_eq_left hl.le,
      abs_of_nonpos (by linarith : a - -M ≤ 0), abs_of_neg ha]
    linarith
  · by_cases hu : M < a
    · have ha : 0 < a := by linarith
      rw [_root_.GD.N0213.N0498.d022018, min_eq_left hu.le, max_eq_right (by linarith : -M ≤ M),
        abs_of_nonneg (by linarith : 0 ≤ a - M), abs_of_pos ha]
      linarith
    · rw [_root_.GD.N0213.N0498.d022020 (abs_le.2 ⟨le_of_not_gt hl, le_of_not_gt hu⟩), sub_self, abs_zero]
      exact abs_nonneg a

def d022022 (f : (ℝ × K) → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : 0 ≤ M) : (ℝ × K) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p ↦ _root_.GD.N0213.N0498.d022018 M (f p))
    (continuous_const.max (continuous_const.min hf)) M
    (fun p ↦ by simpa only [Real.norm_eq_abs] using _root_.GD.N0213.N0498.d022019 hM (f p))



theorem d022023
    {f : (ℝ × K) → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0213.N0497.d022004 α p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : (ℝ × K) →ᵇ ℝ, ∀ p,
      ‖f p - b p‖ ≤ ε * _root_.GD.N0213.N0497.d022004 β p := by
  have hdecay : Tendsto (fun T : ℝ ↦ C * Real.exp ((α - β) * T))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun T : ℝ ↦ (α - β) * T) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (sub_neg.2 hαβ)).2 tendsto_id
    simpa only [mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  obtain ⟨T, hTsmall⟩ := (hdecay.eventually (Iio_mem_nhds hε)).exists
  let M : ℝ := C * Real.exp (α * T)
  have hM : 0 ≤ M := mul_nonneg hC (Real.exp_pos _).le
  refine ⟨_root_.GD.N0213.N0498.d022022 f hf M hM, ?_⟩
  intro p
  change ‖f p - _root_.GD.N0213.N0498.d022018 M (f p)‖ ≤ ε * _root_.GD.N0213.N0497.d022004 β p
  by_cases hp : p.1 ^ 2 ≤ T
  · have hfp : |f p| ≤ M := by
      apply (hbound p).trans
      dsimp [_root_.GD.N0213.N0497.d022004, M]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp hα)) hC
    rw [_root_.GD.N0213.N0498.d022020 hfp, sub_self, norm_zero]
    exact mul_nonneg hε.le (_root_.GD.N0213.N0497.d022006 β p).le
  · have htail : C * Real.exp ((α - β) * p.1 ^ 2) ≤ ε := by
      apply le_trans _ hTsmall.le
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (le_of_not_ge hp)
          (sub_nonpos.2 hαβ.le))) hC
    calc
      ‖f p - _root_.GD.N0213.N0498.d022018 M (f p)‖ ≤ ‖f p‖ := _root_.GD.N0213.N0498.d022021 hM (f p)
      _ ≤ C * _root_.GD.N0213.N0497.d022004 α p := hbound p
      _ = (C * Real.exp ((α - β) * p.1 ^ 2)) * _root_.GD.N0213.N0497.d022004 β p := by
        dsimp [_root_.GD.N0213.N0497.d022004]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ ε * _root_.GD.N0213.N0497.d022004 β p :=
        mul_le_mul_of_nonneg_right htail (_root_.GD.N0213.N0497.d022006 β p).le

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem d022024 {μ : ProbabilityMeasure (ℝ × K)}
    {f : (ℝ × K) → ℝ} (hf : Continuous f) {C α β : ℝ}
    (hC : 0 ≤ C) (hαβ : α ≤ β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0213.N0497.d022004 α p)
    (hi : Integrable (_root_.GD.N0213.N0497.d022004 β) (μ : Measure (ℝ × K))) :
    Integrable f (μ : Measure (ℝ × K)) := by
  apply (hi.const_mul C).mono' hf.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  apply (hbound p).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (sq_nonneg p.1))

private theorem d022025
    {μ : ProbabilityMeasure (ℝ × K)} {f : (ℝ × K) → ℝ}
    (hfi : Integrable f (μ : Measure (ℝ × K))) (b : (ℝ × K) →ᵇ ℝ)
    {ε β B : ℝ} (hε : 0 ≤ ε)
    (hi : Integrable (_root_.GD.N0213.N0497.d022004 β) (μ : Measure (ℝ × K)))
    (hb : (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K))) ≤ B)
    (herr : ∀ p, ‖f p - b p‖ ≤ ε * _root_.GD.N0213.N0497.d022004 β p) :
    dist (∫ p, f p ∂(μ : Measure (ℝ × K)))
      (∫ p, b p ∂(μ : Measure (ℝ × K))) ≤ ε * B := by
  rw [dist_eq_norm, ← integral_sub hfi
    (BoundedContinuousFunction.integrable (μ : Measure (ℝ × K)) b)]
  calc
    ‖∫ p, f p - b p ∂(μ : Measure (ℝ × K))‖
      ≤ ∫ p, ε * _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K)) :=
        norm_integral_le_of_norm_le (hi.const_mul ε) (Eventually.of_forall herr)
    _ = ε * ∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K)) :=
      integral_const_mul ε _
    _ ≤ ε * B := mul_le_mul_of_nonneg_left hb hε



theorem d022026
    {ν : ℕ → ProbabilityMeasure (ℝ × K)} {μ : ProbabilityMeasure (ℝ × K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (hmoment : _root_.GD.N0213.N0497.d022007 ν β B)
    {f : (ℝ × K) → ℝ} (hf : Continuous f) {C α : ℝ}
    (hC : 0 ≤ C) (hβ : 0 < β) (hαβ : α < β)
    (hbound : ∀ p, ‖f p‖ ≤ C * _root_.GD.N0213.N0497.d022004 α p) :
    Tendsto (fun n ↦ ∫ p, f p ∂(ν n : Measure (ℝ × K))) atTop
      (𝓝 (∫ p, f p ∂(μ : Measure (ℝ × K)))) := by
  have hlimitMoment := _root_.GD.N0213.N0497.d022013 hlim hmoment
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0213.N0497.d022006 β p).le).trans (hmoment 0).2
  have hfi (n : ℕ) : Integrable f (ν n : Measure (ℝ × K)) :=
    _root_.GD.N0213.N0498.d022024 hf hC hαβ.le hbound (hmoment n).1
  have hfμ : Integrable f (μ : Measure (ℝ × K)) :=
    _root_.GD.N0213.N0498.d022024 hf hC hαβ.le hbound hlimitMoment.1
  have hbound' (p : (ℝ × K)) : ‖f p‖ ≤ C * _root_.GD.N0213.N0497.d022004 (max α 0) p := by
    apply (hbound p).trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left α 0) (sq_nonneg p.1))) hC
  apply Metric.tendsto_atTop.2
  intro δ hδ
  let ε : ℝ := δ / (3 * (B + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεB : ε * B ≤ δ / 3 := by
    have he : ε * (B + 1) = δ / 3 := by
      dsimp [ε]
      field_simp [show B + 1 ≠ 0 by linarith]
    have hm := mul_le_mul_of_nonneg_left (show B ≤ B + 1 by linarith) hε.le
    rwa [he] at hm
  obtain ⟨b, hb⟩ := _root_.GD.N0213.N0498.d022023 hf hC (le_max_right α 0)
    (max_lt hαβ hβ) hbound' hε
  have hbLimit : Tendsto (fun n ↦ ∫ p, b p ∂(ν n : Measure (ℝ × K))) atTop
      (𝓝 (∫ p, b p ∂(μ : Measure (ℝ × K)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction b).tendsto μ |>.comp hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbLimit (δ / 3) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  have hleft := _root_.GD.N0213.N0498.d022025 (hfi n) b hε.le (hmoment n).1 (hmoment n).2 hb
  have hright := _root_.GD.N0213.N0498.d022025 hfμ b hε.le hlimitMoment.1 hlimitMoment.2 hb
  have htri := dist_triangle
    (∫ p, f p ∂(ν n : Measure (ℝ × K)))
    (∫ p, b p ∂(ν n : Measure (ℝ × K)))
    (∫ p, f p ∂(μ : Measure (ℝ × K)))
  have htri' := dist_triangle
    (∫ p, b p ∂(ν n : Measure (ℝ × K)))
    (∫ p, b p ∂(μ : Measure (ℝ × K)))
    (∫ p, f p ∂(μ : Measure (ℝ × K)))
  rw [dist_comm (∫ p, b p ∂(μ : Measure (ℝ × K)))] at htri'
  have hmiddle := hN n hn
  linarith

end

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0994 _root_.GD.N0232.N0719.N0989
open _root_.GD.N0232.N0719.N0983 (d009709)
open _root_.GD.N0232.N0720.N1382
  (d004663 d004664 d004665)

theorem d022027
    {k : ℕ} {nu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)} {mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)}
    (hlim : Tendsto nu atTop (𝓝 mu))
    (hmom : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 nu beta B)
    (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ} (hphi : Continuous phi)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Tendsto (fun j => ∫ p, _root_.GD.N0232.N0719.N0994.d011381 n m phi x p ∂(nu j : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)))
      atTop (𝓝 (∫ p, _root_.GD.N0232.N0719.N0994.d011381 n m phi x p ∂(mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)))) := by
  obtain ⟨delta, R, hd, hR, hbox⟩ := _root_.GD.N0232.N0719.N0994.d011380 hx
  let alpha := (_root_.GD.N0232.N0720.N1382.d004663 delta R + 1 / 2) / 2
  let beta := (alpha + 1 / 2) / 2
  have hr0 := _root_.GD.N0232.N0720.N1382.d004664 hd hR
  have hr1 := _root_.GD.N0232.N0720.N1382.d004665 hd (R := R)
  have ha0 : 0 < alpha := by dsimp [alpha]; linarith
  have ha1 : alpha < 1 / 2 := by dsimp [alpha]; linarith
  have hra : _root_.GD.N0232.N0720.N1382.d004663 delta R < alpha := by dsimp [alpha]; linarith
  have hb0 : 0 < beta := by dsimp [beta]; linarith
  have hb1 : beta < 1 / 2 := by dsimp [beta]; linarith
  have hab : alpha < beta := by dsimp [beta]; linarith
  obtain ⟨B, hB⟩ := hmom beta hb0 hb1
  obtain ⟨C, hC, hbound⟩ := _root_.GD.N0232.N0719.N0994.d011383 n m hphi hd hR hra
  exact _root_.GD.N0213.N0498.d022026 hlim hB
    (_root_.GD.N0232.N0719.N0994.d011382 n m hphi hx) hC.le hb0 hab
    (hbound x (mem_of_mem_nhds hbox))

end GD.N0213.N0498

#print axioms _root_.GD.N0213.N0498.d022023
#print axioms _root_.GD.N0213.N0498.d022026
#print axioms _root_.GD.N0213.N0498.d022027

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set
open scoped Topology BigOperators ContDiff

namespace GD.N0232.N0719.N0993

open _root_.GD.N0232.N0719.N0873
open _root_.GD.N0232.N0719.N0989 (d011338 d011346 d011361 d011345)
open _root_.GD.N0232.N0719.N0994 _root_.GD.N0232.N0719.N0995
open _root_.GD.N0232.N0719.N0983 (d009709)
open _root_.GD.N0232.N0720.N1377 (d002861)

noncomputable section
variable {k : ℕ}

def d020540 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu x

def d020541 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0995.d011389 n 1 (fun _ => 1) nu x

theorem d020542 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) [IsProbabilityMeasure nu]
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    0 < _root_.GD.N0232.N0719.N0993.d020540 n nu x := by
  have hp (p : _root_.GD.N0232.N0719.N0994.d011371 k) : 0 < _root_.GD.N0232.N0719.N0994.d011381 (n + 1) 0 (fun _ => 1) x p := by
    simpa only [_root_.GD.N0232.N0719.N0994.d011381, pow_zero, mul_one, one_mul, _root_.GD.N0232.N0719.N0989.d011346] using
      _root_.GD.N0232.N0720.N1377.d002861 (n + 1)
        (_root_.GD.N0232.N0719.N0989.d011345 _ (_root_.GD.N0232.N0719.N0994.d011373 p.2) (_root_.GD.N0232.N0719.N0994.d011374 p.2) hx) _
  have hi := _root_.GD.N0232.N0719.N0994.d011384 (n + 1) 0 (phi := fun _ => 1)
    continuous_const nu hnu hx
  have hs : Function.support (_root_.GD.N0232.N0719.N0994.d011381 (n + 1) 0 (fun _ => 1) x) = univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp p).ne'
  apply (integral_pos_iff_support_of_nonneg (fun p => (hp p).le) hi).2
  rw [hs, measure_univ]
  exact zero_lt_one

theorem d020543 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) (i : Fin k) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020541 n nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
      x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020540 n nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
        fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020540 n nu) x (_root_.GD.N0232.N0719.N0873.d011296 i) := by
  change fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 n 1 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
    x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
      fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011296 i)
  rw [(_root_.GD.N0232.N0719.N0995.d011395 n 1 (phi := fun _ => 1) continuous_const nu hnu hx).fderiv,
    (_root_.GD.N0232.N0719.N0995.d011395 (n + 1) 0 (phi := fun _ => 1) continuous_const nu hnu hx).fderiv]
  simp [_root_.GD.N0232.N0719.N0995.d011390, _root_.GD.N0232.N0719.N0995.d011387, _root_.GD.N0232.N0719.N0873.d011296, _root_.GD.N0232.N0719.N0873.d011297, _root_.GD.N0232.N0719.N0873.d011298, _root_.GD.N0232.N0719.N0873.d011299,
    Pi.single_apply, smul_eq_mul, Nat.add_assoc, Finset.sum_add_distrib]
  ring

theorem d020544 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0994.d011371 k) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0719.N0994.d011381 n m phi (_root_.GD.N0232.N0719.N0982.d020345 x a) p =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0994.d011381 n m phi x p := by
  change p.1 ^ m * phi p.2 * _root_.GD.N0232.N0719.N0989.d011346 n p.1 (_root_.GD.N0232.N0719.N0994.d011372 p.2)
    (_root_.GD.N0232.N0719.N0989.d011358 a x) = _
  rw [_root_.GD.N0232.N0719.N0989.d011361 _ _ _ ha]
  unfold _root_.GD.N0232.N0719.N0994.d011381
  ring

theorem d020545 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0719.N0995.d011389 n m phi nu (_root_.GD.N0232.N0719.N0982.d020345 x a) =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0995.d011389 n m phi nu x := by
  unfold _root_.GD.N0232.N0719.N0995.d011389
  simp_rw [_root_.GD.N0232.N0719.N0993.d020544 n m phi x _ ha]
  exact integral_const_mul _ _



def d020546 (n : ℕ) (nu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))) :
    _root_.GD.N0232.N0719.N0982.d020351 (n + 2)
      (fun x => _root_.GD.N0232.N0719.N0993.d020541 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
        _root_.GD.N0232.N0719.N0993.d020540 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x) where
  M := _root_.GD.N0232.N0719.N0993.d020540 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
  N := _root_.GD.N0232.N0719.N0993.d020541 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
  smooth_M := _root_.GD.N0232.N0719.N0995.d011396 (n + 1) 0 continuous_const _ hnu
  smooth_N := _root_.GD.N0232.N0719.N0995.d011396 n 1 continuous_const _ hnu
  positive_M := fun _ hx => _root_.GD.N0232.N0719.N0993.d020542 n _ hnu hx
  numerator := fun _ hx => (div_mul_cancel₀ _ (_root_.GD.N0232.N0719.N0993.d020542 n _ hnu hx).ne').symm
  pde := fun _ hx i => _root_.GD.N0232.N0719.N0993.d020543 n _ hnu hx i
  homogeneous := by
    intro x hx a ha
    change a ^ (n + 2) * _root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1)
      (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (_root_.GD.N0232.N0719.N0982.d020345 x a) = _
    rw [_root_.GD.N0232.N0719.N0993.d020545 _ _ _ _ _ ha]
    simp only [Nat.add_assoc]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero (n + 2) ha.ne'), one_mul]
    rfl

end
end GD.N0232.N0719.N0993

#print axioms _root_.GD.N0232.N0719.N0993.d020543
#print axioms _root_.GD.N0232.N0719.N0993.d020546

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0213.N0483

noncomputable section

open _root_.GD.N0232.N0719.N0983

variable {k : ℕ}

theorem d022028 (c a : ℝ) (y : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009713 (fun i => c + a * y i) p = c + a * _root_.GD.N0232.N0719.N0983.d009713 y p := by
  unfold _root_.GD.N0232.N0719.N0983.d009713
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, _root_.GD.N0232.N0719.N0983.d009712, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d022029 (c a : ℝ) (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
      a ^ 2 * _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009714
  rw [_root_.GD.N0213.N0483.d022028]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem d022030 (q c a : ℝ) (y r : Fin k → ℝ)
    (hr : ∀ i, 0 < r i) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009720 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
      (a ^ 2) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009720
  rw [_root_.GD.N0213.N0483.d022029, Real.mul_rpow (sq_nonneg a) (_root_.GD.N0232.N0719.N0983.d009718 y r hr p).le]

theorem d022031 (q c a : ℝ) (ha : a ≠ 0)
    (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (i : Fin k) :
    _root_.GD.N0232.N0719.N0983.d009725 q (fun j => c + a * y j) (fun j => a ^ 2 * r j) mu i =
      _root_.GD.N0232.N0719.N0983.d009725 q y r mu i := by
  have hc : (a ^ 2) ^ (-q) ≠ 0 :=
    (Real.rpow_pos_of_pos (sq_pos_of_ne_zero ha) _).ne'
  unfold _root_.GD.N0232.N0719.N0983.d009725 _root_.GD.N0232.N0719.N0983.d009723
  simp_rw [_root_.GD.N0213.N0483.d022030 q c a y r hr]
  simp_rw [mul_left_comm (_root_.GD.N0232.N0719.N0983.d009710 i _ : ℝ) ((a ^ 2) ^ (-q))]
  rw [integral_const_mul, integral_const_mul]
  exact mul_div_mul_left _ _ hc

theorem d022032 (q c a : ℝ) (ha : a ≠ 0)
    (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0719.N0983.d009724 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) mu =
      c + a * _root_.GD.N0232.N0719.N0983.d009724 q y r mu := by
  rw [_root_.GD.N0232.N0719.N0983.d009730 q _ _ (fun i => mul_pos (sq_pos_of_ne_zero ha) (hr i)) mu]
  simp_rw [_root_.GD.N0213.N0483.d022031 q c a ha y r hr mu]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, _root_.GD.N0232.N0719.N0983.d009729 q y r hr mu, one_mul,
    _root_.GD.N0232.N0719.N0983.d009730 q y r hr mu, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end GD.N0213.N0483

#print axioms _root_.GD.N0213.N0483.d022029
#print axioms _root_.GD.N0213.N0483.d022031
#print axioms _root_.GD.N0213.N0483.d022032

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0213.N0484

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0982 (d020351)
open _root_.GD.N0232.N0719.N0862

variable {k : ℕ}

theorem d022033 (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 y r p = _root_.GD.N0232.N0719.N0987.d020295
      (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)) y r := by
  have hvar : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2) =
      (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i ^ 2) - (_root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2 := by
    calc
      _ = (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i ^ 2) -
          2 * _root_.GD.N0232.N0719.N0983.d009713 y p * (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i) +
          (_root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2 * (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [_root_.GD.N0232.N0719.N0983.d009712]; unfold _root_.GD.N0232.N0719.N0983.d009713; ring
  unfold _root_.GD.N0232.N0719.N0983.d009714 _root_.GD.N0232.N0719.N0987.d020295
  rw [hvar]
  unfold _root_.GD.N0232.N0719.N0983.d009713
  ring

theorem d022034 (q : ℝ) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0232.N0719.N0983.d009724 q x.1 x.2 mu = _root_.GD.N0232.N0719.N0987.d020298 q mu _root_.GD.N0232.N0719.N0983.d009710 x := by
  unfold _root_.GD.N0232.N0719.N0983.d009724 _root_.GD.N0232.N0719.N0983.d009723 _root_.GD.N0232.N0719.N0983.d009720 _root_.GD.N0232.N0719.N0987.d020298
  simp only [_root_.GD.N0213.N0484.d022033, _root_.GD.N0232.N0719.N0983.d009713]

set_option maxHeartbeats 800000 in
theorem d022035 (q : ℝ) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    [IsProbabilityMeasure mu] :
    ContinuousOn (fun x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) =>
      _root_.GD.N0232.N0719.N0983.d009724 q x.1 x.2 mu) _root_.GD.N0232.N0719.N0982.d020342 := by
  have hp (i : Fin k) : Continuous
      (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k =>
        (_root_.GD.N0232.N0719.N0983.d009710 i z.2 : ℝ)) :=
    (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).comp continuous_snd
  have hy (i : Fin k) : Continuous
      (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k => z.1.1 i) :=
    (continuous_apply i).comp (continuous_fst.comp continuous_fst)
  have hr (i : Fin k) : Continuous
      (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k => z.1.2 i) :=
    (continuous_apply i).comp (continuous_snd.comp continuous_fst)
  have hb : Continuous (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k =>
      _root_.GD.N0232.N0719.N0983.d009713 z.1.1 z.2) :=
    continuous_finsetSum _ (fun i _ => (hp i).mul (hy i))
  have he : Continuous (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k =>
      _root_.GD.N0232.N0719.N0983.d009714 z.1.1 z.1.2 z.2) := by
    exact (continuous_finsetSum _ (fun i _ => (hp i).mul (hr i))).add
      (continuous_const.mul (continuous_finsetSum _
        (fun i _ => (hp i).mul (((hy i).sub hb).pow 2))))
  have hk : ContinuousOn (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k =>
      _root_.GD.N0232.N0719.N0983.d009720 q z.1.1 z.1.2 z.2) (_root_.GD.N0232.N0719.N0982.d020342 ×ˢ univ) := by
    exact he.continuousOn.rpow_const (fun z hz =>
      Or.inl (_root_.GD.N0232.N0719.N0983.d009718 z.1.1 z.1.2 hz.1 z.2).ne')
  have hn : ContinuousOn (fun z : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) × _root_.GD.N0232.N0719.N0983.d009709 k =>
      _root_.GD.N0232.N0719.N0983.d009713 z.1.1 z.2 * _root_.GD.N0232.N0719.N0983.d009720 q z.1.1 z.1.2 z.2)
        (_root_.GD.N0232.N0719.N0982.d020342 ×ˢ univ) := hb.continuousOn.mul hk
  have hnum := continuousOn_integral_of_compact_support (μ := mu)
    (f := fun (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0983.d009709 k) =>
      _root_.GD.N0232.N0719.N0983.d009713 x.1 p * _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p)
    (k := (univ : Set (_root_.GD.N0232.N0719.N0983.d009709 k)))
    (s := _root_.GD.N0232.N0719.N0982.d020342) isCompact_univ hn
    (fun _ _ _ h => False.elim (h (mem_univ _)))
  have hden := continuousOn_integral_of_compact_support (μ := mu)
    (f := fun (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0983.d009709 k) =>
      _root_.GD.N0232.N0719.N0983.d009720 q x.1 x.2 p)
    (k := (univ : Set (_root_.GD.N0232.N0719.N0983.d009709 k)))
    (s := _root_.GD.N0232.N0719.N0982.d020342) isCompact_univ hk
    (fun _ _ _ h => False.elim (h (mem_univ _)))
  exact hnum.div hden (fun x hx => (_root_.GD.N0232.N0719.N0983.d009728 q x.1 x.2 hx mu).ne')



theorem d022036
    (sizes : Fin k → ℕ) (q : ℝ) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu]
    (hr : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i) :
    _root_.GD.N0232.N0719.N0862.d013365 sizes mu _root_.GD.N0232.N0719.N0983.d009710
      (fun z => _root_.GD.N0232.N0719.N0983.d009720 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)) := by
  filter_upwards [hr] with z hz
  exact ⟨_root_.GD.N0232.N0719.N0983.d009726 q _ _ hz mu, _root_.GD.N0232.N0719.N0983.d009728 q _ _ hz mu,
    ae_of_all _ (fun p => (_root_.GD.N0232.N0719.N0983.d009722 q _ _ hz p).le),
    fun i => _root_.GD.N0232.N0719.N0983.d009727 q _ _ hz mu i⟩

theorem d022037
    (hk : 3 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (D : ℕ) (hD : 3 ≤ D)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu]
    (hr : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    (hcap : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ z, f z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ z, _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s)
    (hrep : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f z = _root_.GD.N0232.N0719.N0983.d009724 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) mu) :
    ¬ Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (D + 1) (fun x => _root_.GD.N0232.N0719.N0983.d009724 ((D : ℝ) / 2) x.1 x.2 mu)) := by
  have hweight : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f z = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu _root_.GD.N0232.N0719.N0983.d009710
        (_root_.GD.N0232.N0719.N0983.d009720 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)) i *
          _root_.GD.N0232.N0719.N0900.d009102 k sizes z i := by
    filter_upwards [hr, hrep] with z hz hrepz
    rw [hrepz, _root_.GD.N0232.N0719.N0983.d009730 _ _ _ hz mu]
    simp only [_root_.GD.N0232.N0719.N0986.d020363, _root_.GD.N0232.N0719.N0983.d009725, _root_.GD.N0232.N0719.N0862.d013361, _root_.GD.N0232.N0719.N0983.d009723]
  have h := _root_.GD.N0232.N0719.N0979.d020358
    hk sizes hn D hD mu _root_.GD.N0232.N0719.N0983.d009710 (fun i => (_root_.GD.N0232.N0719.N0983.d009711 i).measurable)
    (fun z => _root_.GD.N0232.N0719.N0983.d009720 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z))
    (_root_.GD.N0213.N0484.d022036 sizes _ mu hr)
    (ae_of_all _ _root_.GD.N0232.N0719.N0983.d009712) f hfm hf hcap hweight
  simpa only [_root_.GD.N0213.N0484.d022034] using h

end
end GD.N0213.N0484

#print axioms _root_.GD.N0213.N0484.d022033
#print axioms _root_.GD.N0213.N0484.d022034
#print axioms _root_.GD.N0213.N0484.d022035
#print axioms _root_.GD.N0213.N0484.d022036
#print axioms _root_.GD.N0213.N0484.d022037

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0213.N0499

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0994 _root_.GD.N0232.N0719.N0995 _root_.GD.N0232.N0719.N0993
open _root_.GD.N0232.N0719.N0989 (d011338)
open _root_.GD.N0232.N0719.N0990 _root_.GD.N0232.N0719.N0991
open _root_.GD.N0213.N0497 _root_.GD.N0213.N0498

variable {k : ℕ}

theorem d022038
    {nu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)} {mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)}
    (hlim : Tendsto nu atTop (𝓝 mu))
    (hmom : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 nu beta B) :
    _root_.GD.N0232.N0719.N0994.d011375 (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) := by
  intro beta hb hh
  obtain ⟨B, hB⟩ := hmom beta hb hh
  exact (_root_.GD.N0213.N0497.d022013 hlim hB).1

theorem d022039
    {nu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)} {mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k)}
    (hlim : Tendsto nu atTop (𝓝 mu))
    (hmom : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 nu beta B)
    (n : ℕ) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Tendsto (fun j => _root_.GD.N0232.N0719.N0993.d020541 n (nu j : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
      _root_.GD.N0232.N0719.N0993.d020540 n (nu j : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x) atTop
      (𝓝 (_root_.GD.N0232.N0719.N0993.d020541 n (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
        _root_.GD.N0232.N0719.N0993.d020540 n (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x)) := by
  have hN := _root_.GD.N0213.N0498.d022027 hlim hmom n 1
    (phi := fun _ => 1) continuous_const hx
  have hM := _root_.GD.N0213.N0498.d022027 hlim hmom (n + 1) 0
    (phi := fun _ => 1) continuous_const hx
  exact hN.div hM (_root_.GD.N0232.N0719.N0993.d020542 n _
    (_root_.GD.N0213.N0499.d022038 hlim hmom) hx).ne'

theorem d022040
    {d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0719.N0991.d020538 sizes hdim nu x =
      _root_.GD.N0232.N0719.N0993.d020541 (d + 1) nu (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) /
        _root_.GD.N0232.N0719.N0993.d020540 (d + 1) nu (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
  simp only [_root_.GD.N0232.N0719.N0991.d020538, _root_.GD.N0232.N0719.N0993.d020541, _root_.GD.N0232.N0719.N0993.d020540, _root_.GD.N0232.N0719.N0995.d011389, _root_.GD.N0232.N0719.N0994.d011381,
    _root_.GD.N0232.N0719.N0990.d020511, _root_.GD.N0232.N0719.N0990.d020510, pow_one, pow_zero, mul_one, one_mul,
    Nat.add_assoc]
  rfl




theorem d022041
    {d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (nu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hmom : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 nu beta B)
    (g : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hraw : ∀ᵐ x ∂(volume : Measure
        (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (nu j : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x)
        atTop (𝓝 (g x))) :
    ∃ mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k),
      _root_.GD.N0232.N0719.N0994.d011375 (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) ∧
      Nonempty (_root_.GD.N0232.N0719.N0982.d020351 ((d + 1) + 2)
        (fun x => _root_.GD.N0232.N0719.N0993.d020541 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
          _root_.GD.N0232.N0719.N0993.d020540 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x)) ∧
      (∀ᵐ x ∂(volume : Measure
          (_root_.GD.N0232.N0720.N1341.d004414 d)),
        _root_.GD.N0232.N0719.N0990.d020512 sizes hdim x ∈ _root_.GD.N0232.N0719.N0989.d011338 →
          g x = _root_.GD.N0232.N0719.N0993.d020541 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
              (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) /
            _root_.GD.N0232.N0719.N0993.d020540 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
              (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) := by
  obtain ⟨mu, phi, hphi, hlim, hmu, _⟩ := _root_.GD.N0213.N0497.d022017 k nu hmom
  have hsub : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 (nu ∘ phi) beta B := by
    intro beta hb hh
    obtain ⟨B, hB⟩ := hmom beta hb hh
    exact ⟨B, fun j => hB (phi j)⟩
  refine ⟨mu, hmu, ⟨_root_.GD.N0232.N0719.N0993.d020546 (d + 1) mu hmu⟩, ?_⟩
  filter_upwards [hraw] with x hx
  intro hxpos
  have hfirst := hx.comp hphi.tendsto_atTop
  have hsecond := _root_.GD.N0213.N0499.d022039 hlim hsub (d + 1) hxpos
  apply tendsto_nhds_unique hfirst
  simpa only [Function.comp_def, _root_.GD.N0213.N0499.d022040] using hsecond

theorem d022042
    {d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i)
    (nu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hmom : ∀ beta : ℝ, 0 < beta → beta < (1 / 2 : ℝ) →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 nu beta B)
    (g : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hraw : ∀ᵐ x ∂(volume : Measure
        (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (nu j : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x)
        atTop (𝓝 (g x)))
    (F : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ)
    (hF : ContinuousOn F _root_.GD.N0232.N0719.N0982.d020342)
    (hrep : ∀ᵐ x ∂(volume : Measure
        (_root_.GD.N0232.N0720.N1341.d004414 d)),
      _root_.GD.N0232.N0719.N0990.d020512 sizes hdim x ∈ _root_.GD.N0232.N0719.N0989.d011338 → g x = F (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) :
    Nonempty (_root_.GD.N0232.N0719.N0982.d020351 ((d + 1) + 2) F) := by
  obtain ⟨mu, hmu, ⟨m⟩, hlimit⟩ :=
    _root_.GD.N0213.N0499.d022041 sizes hdim nu hmom g hraw
  let G := fun x => _root_.GD.N0232.N0719.N0993.d020541 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
    _root_.GD.N0232.N0719.N0993.d020540 (d + 1) (mu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x
  have hG : ContinuousOn G _root_.GD.N0232.N0719.N0982.d020342 :=
    (_root_.GD.N0232.N0719.N0995.d011396 (d + 1) 1 (phi := fun _ => 1)
      continuous_const _ hmu).continuousOn.div
      (_root_.GD.N0232.N0719.N0995.d011396 ((d + 1) + 1) 0 (phi := fun _ => 1)
        continuous_const _ hmu).continuousOn
      (fun x hx => (_root_.GD.N0232.N0719.N0993.d020542 (d + 1) _ hmu hx).ne')
  have hrawEq : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈
          _root_.GD.N0232.N0719.N0982.d020342 →
        F (_root_.GD.N0232.N0719.N0986.d020362 sizes z) =
          G (_root_.GD.N0232.N0719.N0986.d020362 sizes z) := by
    have he := (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim).quasiMeasurePreserving.ae
      (hrep.and hlimit)
    filter_upwards [he] with z hz
    simpa only [_root_.GD.N0232.N0719.N0990.d020512, MeasurableEquiv.symm_apply_apply, G,
      _root_.GD.N0232.N0719.N0989.d011338, _root_.GD.N0232.N0719.N0982.d020342] using
      (fun hx => (hz.1 hx).symm.trans (hz.2 hx))
  have heq := _root_.GD.N0232.N0719.N0986.d020376
    sizes hn hF hG hrawEq
  refine ⟨{ m with numerator := ?_ }⟩
  intro x hx
  exact (m.numerator x hx).trans (congrArg (fun y => y * m.M x) (heq hx).symm)

end
end GD.N0213.N0499

#print axioms _root_.GD.N0213.N0499.d022038
#print axioms _root_.GD.N0213.N0499.d022039
#print axioms _root_.GD.N0213.N0499.d022040
#print axioms _root_.GD.N0213.N0499.d022041
#print axioms _root_.GD.N0213.N0499.d022042
