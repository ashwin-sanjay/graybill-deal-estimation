import GD.Module0359
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic






















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral Filter Topology
open scoped Interval

namespace GD.N0106.N0428.N0765.N1547
open _root_.GD.N0106.N0428.N0765.N1534
noncomputable section



section Chebyshev
variable {w f g : ℝ → ℝ}



theorem d005448
    (hw : ContinuousOn w (Icc 0 1)) (hwnn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < w x)
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfm : StrictMonoOn f (Icc 0 1)) (hgm : StrictMonoOn g (Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, f x * w x) * (∫ x in (0 : ℝ)..1, g x * w x)
      < (∫ x in (0 : ℝ)..1, w x) * ∫ x in (0 : ℝ)..1, f x * g x * w x := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hwi : IntervalIntegrable w volume 0 1 := hw.intervalIntegrable_of_Icc zero_le_one
  have hfwi : IntervalIntegrable (fun x => f x * w x) volume 0 1 :=
    (hf.mul hw).intervalIntegrable_of_Icc zero_le_one
  have hgwi : IntervalIntegrable (fun x => g x * w x) volume 0 1 :=
    (hg.mul hw).intervalIntegrable_of_Icc zero_le_one
  have hfgwi : IntervalIntegrable (fun x => f x * g x * w x) volume 0 1 :=
    ((hf.mul hg).mul hw).intervalIntegrable_of_Icc zero_le_one
  set W := ∫ x in (0 : ℝ)..1, w x with hWdef
  have hW : 0 < W :=
    intervalIntegral_pos_of_pos_on hwi (fun x hx => hwpos x hx) zero_lt_one
  set m := (∫ x in (0 : ℝ)..1, f x * w x) / W with hmdef
  have hmW : (∫ x in (0 : ℝ)..1, f x * w x) = m * W := by
    rw [hmdef, div_mul_cancel₀ _ hW.ne']

  have hlo : f 0 * W ≤ ∫ x in (0 : ℝ)..1, f x * w x := by
    rw [hWdef, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on zero_le_one (hwi.const_mul _) hfwi
    intro x hx
    exact mul_le_mul_of_nonneg_right (hfm.monotoneOn h0 hx hx.1) (hwnn x hx)
  have hhi : (∫ x in (0 : ℝ)..1, f x * w x) ≤ f 1 * W := by
    rw [hWdef, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on zero_le_one hfwi (hwi.const_mul _)
    intro x hx
    exact mul_le_mul_of_nonneg_right (hfm.monotoneOn hx h1 hx.2) (hwnn x hx)
  have hm0 : f 0 ≤ m := by
    rw [hmdef, le_div_iff₀ hW]; exact hlo
  have hm1 : m ≤ f 1 := by
    rw [hmdef, div_le_iff₀ hW]; exact hhi
  obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_Icc zero_le_one hf ⟨hm0, hm1⟩

  set h : ℝ → ℝ := fun x => (f x - m) * (g x - g t₀) * w x with hhdef
  have hh_nonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ h x := by
    intro x hx
    have hw0 := hwnn x hx
    rcases le_total x t₀ with hxt | hxt
    · have hf' : f x ≤ m := hft₀ ▸ hfm.monotoneOn hx ht₀ hxt
      have hg' : g x ≤ g t₀ := hgm.monotoneOn hx ht₀ hxt
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hw0
    · have hf' : m ≤ f x := hft₀ ▸ hfm.monotoneOn ht₀ hx hxt
      have hg' : g t₀ ≤ g x := hgm.monotoneOn ht₀ hx hxt
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hw0
  have hh_cont : ContinuousOn h (Icc 0 1) :=
    ((hf.sub continuousOn_const).mul (hg.sub continuousOn_const)).mul hw
  have hh_pos : ∃ c ∈ Icc (0 : ℝ) 1, 0 < h c := by
    rcases lt_or_eq_of_le ht₀.2 with hlt | heq
    · have hcI : (t₀ + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht₀.1], by linarith⟩
      have hcIcc : (t₀ + 1) / 2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hcI
      refine ⟨(t₀ + 1) / 2, hcIcc, ?_⟩
      have htc : t₀ < (t₀ + 1) / 2 := by linarith
      have hf' : m < f ((t₀ + 1) / 2) := hft₀ ▸ hfm ht₀ hcIcc htc
      have hg' : g t₀ < g ((t₀ + 1) / 2) := hgm ht₀ hcIcc htc
      exact mul_pos (mul_pos (by linarith) (by linarith)) (hwpos _ hcI)
    · have hcI : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hcIcc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hcI
      refine ⟨1 / 2, hcIcc, ?_⟩
      have hct : (1 / 2 : ℝ) < t₀ := by rw [heq]; norm_num
      have hf' : f (1 / 2) < m := hft₀ ▸ hfm hcIcc ht₀ hct
      have hg' : g (1 / 2) < g t₀ := hgm hcIcc ht₀ hct
      exact mul_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (hwpos _ hcI)
  have hint : 0 < ∫ x in (0 : ℝ)..1, h x := by
    have := integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one
      continuousOn_const hh_cont (fun x hx => hh_nonneg x (Ioc_subset_Icc_self hx)) hh_pos
    simpa using this

  have hexp : (∫ x in (0 : ℝ)..1, h x)
      = (∫ x in (0 : ℝ)..1, f x * g x * w x) - g t₀ * (∫ x in (0 : ℝ)..1, f x * w x)
        - m * (∫ x in (0 : ℝ)..1, g x * w x) + m * g t₀ * W := by
    have e : h = fun x => ((f x * g x * w x - g t₀ * (f x * w x)) - m * (g x * w x))
        + m * g t₀ * w x := by
      funext x
      simp only [hhdef]
      ring
    rw [e, integral_add ((hfgwi.sub (hfwi.const_mul _)).sub (hgwi.const_mul _)) (hwi.const_mul _),
      integral_sub (hfgwi.sub (hfwi.const_mul _)) (hgwi.const_mul _),
      integral_sub hfgwi (hfwi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hexp, hmW] at hint
  rw [hmW]
  nlinarith [hint, hW]

end Chebyshev




def d005449 (s l : ℝ) : ℝ :=
  (l * (1 - l)) ^ ((9 : ℝ) / 2) * (1 + (s - 1) * l) ^ (-((21 : ℝ) / 2))


def d005450 (s : ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) / ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l


def d005451 (s l : ℝ) : ℝ := l / (1 + (s - 1) * l)


def d005452 (s : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, φ l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) / ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l


def d005453 (s : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1547.d005452 s (fun l => l * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l) - _root_.GD.N0106.N0428.N0765.N1547.d005452 s (fun l => l) * _root_.GD.N0106.N0428.N0765.N1547.d005452 s (_root_.GD.N0106.N0428.N0765.N1547.d005451 s)

theorem d005454 (s l : ℝ) : _root_.GD.N0106.N0428.N0765.N1547.d005449 s l = _root_.GD.N0106.N0428.N0765.N1534.d005329 s 0 1 1 l := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005449 _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1534.d005328
  rw [show (1 : ℝ) * (1 - l) + s * 1 * l + (1 + s) * 0 * l * (1 - l) = 1 + (s - 1) * l by ring]

theorem d005455 (s : ℝ) : _root_.GD.N0106.N0428.N0765.N1547.d005450 s = _root_.GD.N0106.N0428.N0765.N1534.d005330 s 0 1 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005450 _root_.GD.N0106.N0428.N0765.N1534.d005330
  simp_rw [_root_.GD.N0106.N0428.N0765.N1547.d005454]


theorem d005456 {η v w : ℝ} (hη : 0 < η) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 η 0 v w = _root_.GD.N0106.N0428.N0765.N1547.d005450 (η * w / v) := by
  rw [_root_.GD.N0106.N0428.N0765.N1547.d005455, _root_.GD.N0106.N0428.N0765.N1534.d005344 hη le_rfl,
    _root_.GD.N0106.N0428.N0765.N1534.d005344 (by positivity) le_rfl]
  simp only [mul_zero, zero_div, Real.sqrt_zero, mul_one]
  have h := _root_.GD.N0106.N0428.N0765.N1534.d005327 (U₁ := 1) (U₂ := η * w / v) (Δ := 0) (Δ' := 0) (c := v) one_pos
    (by positivity) hv (by simp)
  rw [mul_one, show v * (η * w / v) = η * w by field_simp] at h
  exact h

section Analysis
variable {s : ℝ}

theorem d005457 (hs : 0 < s) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : 0 < 1 + (s - 1) * l := by
  rcases eq_or_lt_of_le hl.2 with h | h
  · rw [h]
    simpa using hs
  · nlinarith [mul_nonneg hs.le hl.1]

theorem d005458 (hs : 0 < s) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : min 1 s ≤ 1 + (s - 1) * l := by
  have h1 : min 1 s ≤ 1 := min_le_left _ _
  have h2 : min 1 s ≤ s := min_le_right _ _
  nlinarith [hl.1, hl.2, mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hl.2),
    mul_le_mul_of_nonneg_left h2 hl.1]

theorem d005459 (hs : 0 < s) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1547.d005449 s) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005449
  apply ContinuousOn.mul
  · exact ((Real.continuous_rpow_const (by norm_num)).comp
      (by fun_prop : Continuous fun l : ℝ => l * (1 - l))).continuousOn
  · exact ContinuousOn.rpow_const (by fun_prop) (fun l hl => Or.inl (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl).ne')

theorem d005460 (hs : 0 < s) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (hl' : l ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1547.d005449 s l :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hl'.1 (sub_pos.mpr hl'.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl) _)

theorem d005461 (hs : 0 < s) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1547.d005449 s l :=
  _root_.GD.N0106.N0428.N0765.N1547.d005460 hs (Ioo_subset_Icc_self hl) hl

theorem d005462 (hs : 0 < s) : 0 < ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l :=
  intervalIntegral_pos_of_pos_on ((_root_.GD.N0106.N0428.N0765.N1547.d005459 hs).intervalIntegrable_of_Icc zero_le_one)
    (fun _ hl => _root_.GD.N0106.N0428.N0765.N1547.d005461 hs hl) zero_lt_one

theorem d005463 (hs : 0 < s) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1547.d005451 s) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005451
  exact continuousOn_id.div (by fun_prop) (fun l hl => (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl).ne')

theorem d005464 (hs : 0 < s) : StrictMonoOn (_root_.GD.N0106.N0428.N0765.N1547.d005451 s) (Icc 0 1) := by
  intro x hx y hy hxy
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005451
  rw [div_lt_div_iff₀ (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hx) (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hy)]
  nlinarith [hxy]

theorem d005465 (s : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1547.d005449 s) := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005449
  fun_prop

theorem d005466 (s : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1547.d005451 s) := by
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005451
  fun_prop


theorem d005467 (hs : 0 < s) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) s := by
  have hb := _root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl
  have hbase : HasDerivAt (fun s : ℝ => 1 + (s - 1) * l) l s := by
    have h := (((hasDerivAt_id s).sub_const 1).mul_const l).const_add 1
    simpa using h
  have hpow := hbase.rpow_const (p := -((21 : ℝ) / 2)) (Or.inl hb.ne')
  have h := hpow.const_mul ((l * (1 - l)) ^ ((9 : ℝ) / 2))
  refine h.congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005451 _root_.GD.N0106.N0428.N0765.N1547.d005449
  rw [Real.rpow_sub_one hb.ne']
  field_simp


theorem d005468 (hs : 0 < s) :
    HasDerivAt (fun s => ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
      (∫ l in (0 : ℝ)..1, -((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) s ∧
    HasDerivAt (fun s => ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
      (∫ l in (0 : ℝ)..1, l * (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)) s := by
  set m₀ := min 1 (s / 2) with hm₀
  have hm₀pos : 0 < m₀ := lt_min one_pos (by positivity)
  have hS : Ioi (s / 2) ∈ 𝓝 s := Ioi_mem_nhds (by linarith)

  have hbound : ∀ l ∈ Ι (0 : ℝ) 1, ∀ x ∈ Ioi (s / 2),
      ‖-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l‖ ≤ (21 / 2) * m₀⁻¹ * m₀ ^ (-((21 : ℝ) / 2)) := by
    intro l hl x hx
    rw [uIoc_of_le zero_le_one] at hl
    have hlI : l ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hl
    have hx0 : 0 < x := lt_trans (by positivity) hx
    have hb := _root_.GD.N0106.N0428.N0765.N1547.d005457 hx0 hlI
    have hbge : m₀ ≤ 1 + (x - 1) * l := by
      have := _root_.GD.N0106.N0428.N0765.N1547.d005458 hx0 hlI
      have hmin : m₀ ≤ min 1 x := le_min (min_le_left _ _)
        ((min_le_right _ _).trans (le_of_lt hx))
      exact hmin.trans this
    have ht0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1547.d005451 x l := div_nonneg hlI.1 hb.le
    have ht : _root_.GD.N0106.N0428.N0765.N1547.d005451 x l ≤ m₀⁻¹ := by
      unfold _root_.GD.N0106.N0428.N0765.N1547.d005451
      rw [div_le_iff₀ hb]
      calc l ≤ 1 := hlI.2
        _ = m₀⁻¹ * m₀ := (inv_mul_cancel₀ hm₀pos.ne').symm
        _ ≤ m₀⁻¹ * (1 + (x - 1) * l) := by gcongr
    have hk0 : 0 ≤ _root_.GD.N0106.N0428.N0765.N1547.d005449 x l := by
      unfold _root_.GD.N0106.N0428.N0765.N1547.d005449
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg hlI.1 (sub_nonneg.mpr hlI.2)) _)
        (Real.rpow_nonneg hb.le _)
    have hk : _root_.GD.N0106.N0428.N0765.N1547.d005449 x l ≤ m₀ ^ (-((21 : ℝ) / 2)) := by
      unfold _root_.GD.N0106.N0428.N0765.N1547.d005449
      have h1 : (l * (1 - l)) ^ ((9 : ℝ) / 2) ≤ 1 := by
        apply Real.rpow_le_one (mul_nonneg hlI.1 (sub_nonneg.mpr hlI.2)) _ (by norm_num)
        have := mul_le_mul hlI.2 (by linarith [hlI.1] : 1 - l ≤ 1) (by linarith [hlI.2])
          zero_le_one
        simpa using this
      have h2 : (1 + (x - 1) * l) ^ (-((21 : ℝ) / 2)) ≤ m₀ ^ (-((21 : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_nonpos hm₀pos hbge (by norm_num)
      exact (mul_le_mul h1 h2 (Real.rpow_nonneg hb.le _) zero_le_one).trans (le_of_eq (one_mul _))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 21 / 2),
      abs_of_nonneg ht0, abs_of_nonneg hk0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hk hk0 (by positivity)
  have hmeasF : ∀ x : ℝ, AEStronglyMeasurable (fun l => _root_.GD.N0106.N0428.N0765.N1547.d005449 x l) (volume.restrict (Ι (0 : ℝ) 1)) :=
    fun x => (_root_.GD.N0106.N0428.N0765.N1547.d005465 x).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun l => -((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    ((measurable_const.mul (_root_.GD.N0106.N0428.N0765.N1547.d005466 s)).mul (_root_.GD.N0106.N0428.N0765.N1547.d005465 s)).aestronglyMeasurable
  have hdiff : ∀ l ∈ Ι (0 : ℝ) 1, ∀ x ∈ Ioi (s / 2),
      HasDerivAt (fun x => _root_.GD.N0106.N0428.N0765.N1547.d005449 x l) (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l) x := by
    intro l hl x hx
    rw [uIoc_of_le zero_le_one] at hl
    exact _root_.GD.N0106.N0428.N0765.N1547.d005467 (lt_trans (by positivity) hx) (Ioc_subset_Icc_self hl)
  constructor
  · exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x l => _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)
      (F' := fun x l => -((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)
      (bound := fun _ => (21 / 2) * m₀⁻¹ * m₀ ^ (-((21 : ℝ) / 2))) hS
      (Eventually.of_forall hmeasF)
      ((_root_.GD.N0106.N0428.N0765.N1547.d005459 hs).intervalIntegrable_of_Icc zero_le_one)
      hmeasF' (Eventually.of_forall hbound) intervalIntegrable_const
      (Eventually.of_forall hdiff)).2
  · have hbound' : ∀ l ∈ Ι (0 : ℝ) 1, ∀ x ∈ Ioi (s / 2),
        ‖l * (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)‖
          ≤ (21 / 2) * m₀⁻¹ * m₀ ^ (-((21 : ℝ) / 2)) := by
      intro l hl x hx
      have h := hbound l hl x hx
      have hl' := hl
      rw [uIoc_of_le zero_le_one] at hl'
      rw [norm_mul, Real.norm_eq_abs l, abs_of_nonneg hl'.1.le]
      exact le_trans (mul_le_mul_of_nonneg_right hl'.2 (norm_nonneg _)) (by rw [one_mul]; exact h)
    have hdiff' : ∀ l ∈ Ι (0 : ℝ) 1, ∀ x ∈ Ioi (s / 2),
        HasDerivAt (fun x => l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)
          (l * (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)) x :=
      fun l hl x hx => (hdiff l hl x hx).const_mul l
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x l => l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l)
      (F' := fun x l => l * (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 x l * _root_.GD.N0106.N0428.N0765.N1547.d005449 x l))
      (bound := fun _ => (21 / 2) * m₀⁻¹ * m₀ ^ (-((21 : ℝ) / 2))) hS
      (Eventually.of_forall fun x => (measurable_id.mul (_root_.GD.N0106.N0428.N0765.N1547.d005465 x)).aestronglyMeasurable)
      ((continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs)).intervalIntegrable_of_Icc zero_le_one)
      (measurable_id.mul ((measurable_const.mul (_root_.GD.N0106.N0428.N0765.N1547.d005466 s)).mul
        (_root_.GD.N0106.N0428.N0765.N1547.d005465 s))).aestronglyMeasurable
      (Eventually.of_forall hbound') intervalIntegrable_const
      (Eventually.of_forall hdiff')).2


theorem d005469 (hs : 0 < s) :
    HasDerivAt _root_.GD.N0106.N0428.N0765.N1547.d005450 (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005453 s) s := by
  obtain ⟨hD, hN⟩ := _root_.GD.N0106.N0428.N0765.N1547.d005468 hs
  have hDpos := _root_.GD.N0106.N0428.N0765.N1547.d005462 hs
  have h := hN.div hD hDpos.ne'
  refine h.congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005453 _root_.GD.N0106.N0428.N0765.N1547.d005452
  have e1 : (∫ l in (0 : ℝ)..1, l * (-((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l))
      = -((21 : ℝ) / 2) * ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext l
    ring
  have e2 : (∫ l in (0 : ℝ)..1, -((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
      = -((21 : ℝ) / 2) * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005451 s l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext l
    ring
  rw [e1, e2]
  field_simp
  ring



theorem d005470 (hs : 0 < s) : 0 < _root_.GD.N0106.N0428.N0765.N1547.d005453 s := by
  have hD := _root_.GD.N0106.N0428.N0765.N1547.d005462 hs
  have hcov := _root_.GD.N0106.N0428.N0765.N1547.d005448 (w := _root_.GD.N0106.N0428.N0765.N1547.d005449 s) (f := fun l => l) (g := _root_.GD.N0106.N0428.N0765.N1547.d005451 s)
    (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs)
    (fun l hl => by
      unfold _root_.GD.N0106.N0428.N0765.N1547.d005449
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg hl.1 (sub_nonneg.mpr hl.2)) _)
        (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl).le _))
    (fun l hl => _root_.GD.N0106.N0428.N0765.N1547.d005461 hs hl)
    continuousOn_id (_root_.GD.N0106.N0428.N0765.N1547.d005463 hs) (strictMono_id.strictMonoOn _) (_root_.GD.N0106.N0428.N0765.N1547.d005464 hs)
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005453 _root_.GD.N0106.N0428.N0765.N1547.d005452
  rw [div_mul_div_comm, div_sub_div _ _ hD.ne' (mul_ne_zero hD.ne' hD.ne')]
  apply div_pos
  · nlinarith [hcov, hD]
  · positivity


theorem d005471 (hs : 0 < s) : deriv _root_.GD.N0106.N0428.N0765.N1547.d005450 s < 0 := by
  rw [(_root_.GD.N0106.N0428.N0765.N1547.d005469 hs).deriv]
  have := _root_.GD.N0106.N0428.N0765.N1547.d005470 hs
  nlinarith


theorem d005472 : StrictAntiOn _root_.GD.N0106.N0428.N0765.N1547.d005450 (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (_root_.GD.N0106.N0428.N0765.N1547.d005469 hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact _root_.GD.N0106.N0428.N0765.N1547.d005471 hx

end Analysis

end
end GD.N0106.N0428.N0765.N1547

#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005448
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005456
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005467
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005468
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005469
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005470
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005471
#print axioms _root_.GD.N0106.N0428.N0765.N1547.d005472
