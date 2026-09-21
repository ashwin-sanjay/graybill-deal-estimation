import GD.Module1762
import GD.Module1766
import GD.Module1767
import GD.Module0383
import Mathlib.MeasureTheory.Integral.Prod











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory Set Filter Topology
open scoped FourierTransform BigOperators

namespace GD.N0106.N0428.N0765.N1513
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1512 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1550
open _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1602 _root_.GD.N0106.N0428.N0765.N1590 _root_.GD.N0106.N0428.N0765.N1601 _root_.GD.N0106.N0428.N0765.N1613
open _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1653

private theorem d029279 : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by
  simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos

theorem d029280 (r x : ℝ) : _root_.GD.N0106.N0428.N0765.N1587.d029254 r r x = Real.exp (-r * |x|) := by
  by_cases hx : x ≤ 0
  · simp only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx, abs_of_nonpos hx]
    congr 1
    ring
  · simp only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hx, abs_of_nonneg (lt_of_not_ge hx).le]

theorem d029281 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a b : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)‖ ≤
      _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a *
        _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1513.d029280] using _root_.GD.N0106.N0428.N0765.N1512.d029217 channel k heta hs (a, b)

theorem d029282 (channel : Bool) (k : ℕ) (eta : ℝ) {p : ℝ × ℝ}
    (hp : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 p.1 p.2 < Real.pi) :
    ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta q.1 q.2) p := by
  have hs := _root_.GD.N0106.N0428.N0765.N1537.d021535 hp
  have hA : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.1 / 2)) p := by fun_prop
  have hB : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.2 / 2)) p := by fun_prop
  have hS : ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1538.d021231 q.1 q.2) p := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021231 _root_.GD.N0106.N0428.N0765.N1538.d021192
    fun_prop
  have hDa := hA.rpow_const (p := -((23 : ℝ) / 2))
    (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.1).ne')
  have hDb := hB.rpow_const (p := -(10 : ℝ))
    (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne')
  have hg := hB.inv₀ (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne'
  have hK := hS.inv₀ (_root_.GD.N0106.N0428.N0765.N1538.d021232 hp).ne'
  cases channel <;> unfold _root_.GD.N0106.N0428.N0765.N1512.d029214 _root_.GD.N0106.N0428.N0765.N1512.d029213 _root_.GD.N0106.N0428.N0765.N1512.d029197 _root_.GD.N0106.N0428.N0765.N1512.d029143 _root_.GD.N0106.N0428.N0765.N1512.d029183 <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem d029283 (channel : Bool) (k : ℕ) {eta dA dB : ℝ}
    (heta : 1 ≤ eta) (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ α β : ℝ, |α| ≤ dA → |β| ≤ dB → ∀ a b : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)‖ ≤
        K * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b := by
  let S : Set (ℝ × ℝ) := Icc (-dA) dA ×ˢ Icc (-dB) dB
  have hsub : ∀ p ∈ S, ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 p.1 p.2 < Real.pi := by
    intro p hp
    have ha := abs_le.mpr hp.1
    have hb := abs_le.mpr hp.2
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021192
    nlinarith
  have hc : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta p.1 p.2) S :=
    fun p hp => (_root_.GD.N0106.N0428.N0765.N1513.d029282 channel k eta (hsub p hp)).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro α β hα hβ a b
  have hp : (α, β) ∈ S := ⟨abs_le.mp hα, abs_le.mp hβ⟩
  have hn : |_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK (α, β) hp
  have hcoef : _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β ≤ max K 1 :=
    (le_abs_self _).trans (hn.trans (le_max_left _ _))
  exact (_root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta (hsub _ hp) a b).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le)
      (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le)

theorem d029284 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (b : ℝ) :
    Integrable (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)) := by
  have hm : Measurable (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)) :=
    (_root_.GD.N0106.N0428.N0765.N1512.d029196 channel k eta α β).comp (measurable_id.prodMk measurable_const)
  exact Integrable.mono' (((_root_.GD.N0106.N0428.N0765.N1602.d029276 (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel)
    (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel)).const_mul (_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β)).mul_const (_root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b))
      hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => _root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta hs a b)

theorem d029285 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a : ℝ) :
    Integrable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)) := by
  have hm : Measurable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)) :=
    (_root_.GD.N0106.N0428.N0765.N1512.d029196 channel k eta α β).comp (measurable_const.prodMk measurable_id)
  exact Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (0 : ℝ) < 5)).const_mul
      (_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a))
        hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun b => _root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta hs a b)


theorem d029286 {f : ℂ → ℂ} {d y AL AR a b : ℝ}
    (hd : 0 ≤ d) (hy : |y| ≤ d)
    (hf : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ f z)
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0)) (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 → ‖f z‖ ≤ AL * Real.exp (a * z.re))
    (hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re → ‖f z‖ ≤ AR * Real.exp (-b * z.re))
    (xi : ℝ) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) 0 x) = ∫ x, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) y x := by
  apply _root_.GD.N0106.N0428.N0765.N1550.d005482
    (AL := Real.exp (2 * Real.pi * |xi| * d) * AL)
    (AR := Real.exp (2 * Real.pi * |xi| * d) * AR)
    hd hy (fun z hz => _root_.GD.N0106.N0428.N0765.N1550.d005486 xi (hf z hz))
    (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi h0) (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi hyint) ha hb
  · intro z hz hx
    exact (_root_.GD.N0106.N0428.N0765.N1550.d005485 xi hz).trans
      ((mul_le_mul_of_nonneg_left (hleft z hz hx) (Real.exp_nonneg _)).trans_eq (by ring))
  · intro z hz hx
    exact (_root_.GD.N0106.N0428.N0765.N1550.d005485 xi hz).trans
      ((mul_le_mul_of_nonneg_left (hright z hz hx) (Real.exp_nonneg _)).trans_eq (by ring))

theorem d029287 (channel : Bool) (k : ℕ) {eta dA dB α β : ℝ}
    (heta : 1 ≤ eta) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi)
    (hα : |α| ≤ dA) (hβ : |β| ≤ dB) (b xi : ℝ) :
    (∫ a, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β))) 0 a) =
      ∫ a, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β))) α a := by
  obtain ⟨K, _, hK⟩ := _root_.GD.N0106.N0428.N0765.N1513.d029283 channel k heta hd
  have hp : ∀ s, |s| ≤ dA → ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 s β < Real.pi := by
    intro s hs
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021192
    nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dA →
      DifferentiableAt ℂ (fun w => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta w (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1512.d029192 channel k (lt_of_lt_of_le zero_lt_one heta)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hp z.im hz)
  have ht : ∀ z : ℂ, |z.im| ≤ dA →
      ‖_root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ K *
        _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) z.re * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b := by
    intro z hz
    have h := hK z.im β hz hβ z.re b
    simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1550.d005473, Complex.re_add_im] using h
  apply _root_.GD.N0106.N0428.N0765.N1513.d029286 (AL := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b) (AR := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b)
    hdA hα hf (_root_.GD.N0106.N0428.N0765.N1513.d029284 channel k heta (hp 0 (by simpa using hdA)) b)
    (_root_.GD.N0106.N0428.N0765.N1513.d029284 channel k heta (hp α hα) b)
    (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) _ _ xi
  · intro z hz hx
    simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx, mul_assoc, mul_left_comm, mul_comm] using ht z hz
  · intro z hz hx
    have he : _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) z.re =
        Real.exp (-_root_.GD.N0106.N0428.N0765.N1512.d029209 channel * z.re) := by
      rw [_root_.GD.N0106.N0428.N0765.N1513.d029280, abs_of_nonneg hx]
    simpa only [he, mul_assoc, mul_left_comm, mul_comm] using ht z hz

theorem d029288 (channel : Bool) (k : ℕ) {eta dA dB α β : ℝ}
    (heta : 1 ≤ eta) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi)
    (hα : |α| ≤ dA) (hβ : |β| ≤ dB) (a nu : ℝ) :
    (∫ b, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 nu (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) z)) 0 b) =
      ∫ b, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 nu (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) z)) β b := by
  obtain ⟨K, _, hK⟩ := _root_.GD.N0106.N0428.N0765.N1513.d029283 channel k heta hd
  have hp : ∀ s, |s| ≤ dB → ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α s < Real.pi := by
    intro s hs
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021192
    nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dB →
      DifferentiableAt ℂ (fun w => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) w) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1512.d029193 channel k (lt_of_lt_of_le zero_lt_one heta)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hp z.im hz)
  have ht : ∀ z : ℂ, |z.im| ≤ dB →
      ‖_root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) z‖ ≤
        K * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 z.re := by
    intro z hz
    have h := hK α z.im hα hz a z.re
    simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1550.d005473, Complex.re_add_im] using h
  apply _root_.GD.N0106.N0428.N0765.N1513.d029286
    (AL := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a)
    (AR := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a)
    hdB hβ hf (_root_.GD.N0106.N0428.N0765.N1513.d029285 channel k heta (hp 0 (by simpa using hdB)) a)
    (_root_.GD.N0106.N0428.N0765.N1513.d029285 channel k heta (hp β hβ) a)
    (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5) _ _ nu
  · intro z hz hx
    simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx] using ht z hz
  · intro z hz hx
    simpa only [_root_.GD.N0106.N0428.N0765.N1513.d029280, abs_of_nonneg hx] using ht z hz

def d029289 (xi : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I))

def d029290 (channel : Bool) (k : ℕ) (eta α β xi nu : ℝ) (q : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1513.d029289 xi (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) * _root_.GD.N0106.N0428.N0765.N1513.d029289 nu (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) * _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q

theorem d029291 (xi a α : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1513.d029289 xi (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α)‖ = Real.exp (2 * Real.pi * xi * α) := by
  have h := _root_.GD.N0106.N0428.N0765.N1550.d005484 xi (fun _ => (1 : ℂ)) (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α)
  simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1513.d029289, mul_one, norm_one, _root_.GD.N0106.N0428.N0765.N1550.d005477] using h

theorem d029292 (channel : Bool) (k : ℕ) (eta α β xi nu : ℝ) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu q‖ =
      (Real.exp (2 * Real.pi * xi * α) * Real.exp (2 * Real.pi * nu * β)) *
        ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q‖ := by
  simp only [_root_.GD.N0106.N0428.N0765.N1513.d029290, norm_mul, _root_.GD.N0106.N0428.N0765.N1513.d029291]

theorem d029293 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (xi nu : ℝ) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu) := by
  have hm : Measurable (_root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu) := by
    have hF := _root_.GD.N0106.N0428.N0765.N1512.d029196 channel k eta α β
    unfold _root_.GD.N0106.N0428.N0765.N1513.d029290 _root_.GD.N0106.N0428.N0765.N1513.d029289 _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  exact Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1512.d029203 channel k heta hs).norm.const_mul
    (Real.exp (2 * Real.pi * xi * α) * Real.exp (2 * Real.pi * nu * β)))
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => (_root_.GD.N0106.N0428.N0765.N1513.d029292 channel k eta α β xi nu q).le)

theorem d029294 (f : ℝ → ℂ) (xi : ℝ) :
    𝓕 f xi = ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1513.d029289 xi (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) * f a := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with a
  simp only [_root_.GD.N0106.N0428.N0765.N1513.d029289, _root_.GD.N0106.N0428.N0765.N1550.d005478, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem d029295 (channel : Bool) (k : ℕ) (eta xi nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) xi nu =
      ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta 0 0 xi nu (a, b) := by
  unfold _root_.GD.N0106.N0428.N0765.N1652.d005817 _root_.GD.N0106.N0428.N0765.N1652.d005816
  rw [_root_.GD.N0106.N0428.N0765.N1513.d029294]
  simp_rw [_root_.GD.N0106.N0428.N0765.N1513.d029294, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with b
  unfold _root_.GD.N0106.N0428.N0765.N1513.d029290
  ring

theorem d029296 (channel : Bool) (k : ℕ) {eta dA dB α β : ℝ}
    (heta : 1 ≤ eta) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi)
    (hα : |α| ≤ dA) (hβ : |β| ≤ dB) (xi nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) xi nu =
      ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu p := by
  have hp0 : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; simp only [abs_zero]; nlinarith
  have hp : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hshiftB (a : ℝ) : (∫ b, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta 0 0 xi nu (a, b)) =
      ∫ b, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta 0 β xi nu (a, b) := by
    simp only [_root_.GD.N0106.N0428.N0765.N1513.d029290, _root_.GD.N0106.N0428.N0765.N1512.d029194, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    congr 1
    exact _root_.GD.N0106.N0428.N0765.N1513.d029288 channel k heta hdA hdB hd (by simpa using hdA) hβ a nu
  have hshiftA (b : ℝ) : (∫ a, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta 0 β xi nu (a, b)) =
      ∫ a, _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu (a, b) := by
    have h := _root_.GD.N0106.N0428.N0765.N1513.d029287 channel k heta hdA hdB hd hα hβ b xi
    have hmul := congrArg (fun v : ℂ => _root_.GD.N0106.N0428.N0765.N1513.d029289 nu (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β) * v) h
    simp only [← integral_const_mul, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1513.d029290, _root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1513.d029289] at hmul ⊢
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [_root_.GD.N0106.N0428.N0765.N1513.d029295]
  simp_rw [hshiftB]
  have hi0 := _root_.GD.N0106.N0428.N0765.N1513.d029293 channel k heta hp0 xi nu
  have hi := _root_.GD.N0106.N0428.N0765.N1513.d029293 channel k heta hp xi nu
  rw [Measure.volume_eq_prod] at hi0 hi
  rw [integral_integral_swap (f := fun a b => _root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta 0 β xi nu (a, b)) hi0]
  simp_rw [hshiftA]
  simpa only [Measure.volume_eq_prod] using (integral_prod_symm _ hi).symm

theorem d029297 (channel : Bool) (k : ℕ) (eta dA dB xi nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta (if 0 ≤ xi then -dA else dA) (if 0 ≤ nu then -dB else dB) =
      _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta dA dB := by
  split_ifs <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029199, _root_.GD.N0106.N0428.N0765.N1512.d029197, _root_.GD.N0106.N0428.N0765.N1512.d029183, _root_.GD.N0106.N0428.N0765.N1538.d021231, _root_.GD.N0106.N0428.N0765.N1538.d021192,
    abs_neg, neg_div, Real.cos_neg]

theorem d029298 (channel : Bool) (k : ℕ) {eta dA dB : ℝ}
    (heta : 1 ≤ eta) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) (xi nu : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) xi nu‖ ≤
      _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta dA dB * Real.exp (-2 * Real.pi * dA * |xi|) *
        Real.exp (-2 * Real.pi * dB * |nu|) := by
  let α : ℝ := if 0 ≤ xi then -dA else dA
  let β : ℝ := if 0 ≤ nu then -dB else dB
  have hα : |α| ≤ dA := by simp only [α]; split <;> simp [abs_of_nonneg hdA]
  have hβ : |β| ≤ dB := by simp only [β]; split <;> simp [abs_of_nonneg hdB]
  have hp : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have heA : 2 * Real.pi * xi * α = -2 * Real.pi * dA * |xi| := by
    unfold α
    split_ifs with hxi
    · rw [abs_of_nonneg hxi]; ring
    · rw [abs_of_neg (lt_of_not_ge hxi)]; ring
  have heB : 2 * Real.pi * nu * β = -2 * Real.pi * dB * |nu| := by
    unfold β
    split_ifs with hnu
    · rw [abs_of_nonneg hnu]; ring
    · rw [abs_of_neg (lt_of_not_ge hnu)]; ring
  rw [_root_.GD.N0106.N0428.N0765.N1513.d029296 channel k heta hdA hdB hd hα hβ]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1513.d029290 channel k eta α β xi nu p‖ := norm_integral_le_integral_norm _
    _ = (Real.exp (2 * Real.pi * xi * α) * Real.exp (2 * Real.pi * nu * β)) *
        ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β p‖ := by
      simp_rw [_root_.GD.N0106.N0428.N0765.N1513.d029292]
      exact integral_const_mul _ _
    _ ≤ (Real.exp (2 * Real.pi * xi * α) * Real.exp (2 * Real.pi * nu * β)) *
        _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta α β := mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1512.d029204 channel k heta hp) (by positivity)
    _ = _ := by
      rw [heA, heB, show _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta α β = _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta dA dB from
        _root_.GD.N0106.N0428.N0765.N1513.d029297 channel k eta dA dB xi nu]
      ring

theorem d029299 (channel : Bool) (k : ℕ) {eta dA dB α : ℝ}
    (heta : 1 ≤ eta) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) (hα : |α| ≤ dA) (a nu : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α 0) nu a‖ ≤
      Real.exp (-2 * Real.pi * dB * |nu|) *
        ∫ b : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α (if 0 ≤ nu then -dB else dB) (a, b)‖ := by
  let β : ℝ := if 0 ≤ nu then -dB else dB
  have hβ : |β| ≤ dB := by simp only [β]; split <;> simp [abs_of_nonneg hdB]
  have he : 2 * Real.pi * nu * β = -2 * Real.pi * dB * |nu| := by
    unfold β
    split_ifs with hnu
    · rw [abs_of_nonneg hnu]; ring
    · rw [abs_of_neg (lt_of_not_ge hnu)]; ring
  change ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) z) 0) nu‖ ≤ _
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005488, _root_.GD.N0106.N0428.N0765.N1513.d029288 channel k heta hdA hdB hd hα hβ a nu]
  calc
    _ ≤ ∫ b, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 nu (fun z => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) z)) β b‖ :=
      norm_integral_le_integral_norm _
    _ = Real.exp (2 * Real.pi * nu * β) * ∫ b, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β (a, b)‖ := by
      simp only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005484, _root_.GD.N0106.N0428.N0765.N1550.d005477, _root_.GD.N0106.N0428.N0765.N1512.d029194]
      exact integral_const_mul _ _
    _ = _ := by rw [he]

theorem d029300 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β := by
  have hC := _root_.GD.N0106.N0428.N0765.N1512.d029216 channel k heta hs
  have hA := ProbabilityTheory.beta_pos (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 10)
  have hB := ProbabilityTheory.beta_pos (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029214
  positivity

theorem d029301 (channel : Bool) (k : ℕ) {eta d : ℝ}
    (heta : 1 ≤ eta) (hd : 0 ≤ d) (hstrip : ((21 : ℝ) / 2) * d < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a nu : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) nu a‖ ≤
        C * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a *
          Real.exp (-2 * Real.pi * d * |nu|) := by
  have hs : ((21 : ℝ) / 2) * (0 + d) < Real.pi := by simpa only [zero_add] using hstrip
  obtain ⟨K, hKpos, hK⟩ := _root_.GD.N0106.N0428.N0765.N1513.d029283 channel k heta hs
  refine ⟨K * ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b,
    mul_nonneg hKpos.le (integral_nonneg fun b => (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ b).le), ?_⟩
  intro a nu
  let β : ℝ := if 0 ≤ nu then -d else d
  have hβ : |β| ≤ d := by simp only [β]; split <;> simp [abs_of_nonneg hd]
  have hp : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 0 β < Real.pi := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021192
    simp only [abs_zero]
    nlinarith
  have hb : (∫ b, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 β (a, b)‖) ≤
      (K * ∫ b, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b) * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a := by
    calc
      _ ≤ (∫ b : ℝ,
          (K * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a) * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b) := by
        apply integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1513.d029285 channel k heta hp a).norm
          ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)).const_mul _)
        exact Filter.Eventually.of_forall fun b => hK 0 β (by simp) hβ a b
      _ = _ := by rw [integral_const_mul]; ring
  exact (_root_.GD.N0106.N0428.N0765.N1513.d029299 channel k heta (le_refl (0 : ℝ)) hd hs (by simp) a nu).trans
    ((mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq (by ring))

theorem d029302 (channel : Bool) (k : ℕ) {eta : ℝ} (heta : 1 ≤ eta) (a : ℝ) :
    Continuous (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hd := _root_.GD.N0106.N0428.N0765.N1512.d029193 channel k (lt_of_lt_of_le zero_lt_one heta)
    (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (w := _root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)
    (by simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1513.d029279)
  exact ContinuousAt.comp (f := fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 t 0) (x := b)
    hd.continuousAt (by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop)

theorem d029303 (channel : Bool) (k : ℕ) {eta : ℝ}
    (heta : 1 ≤ eta) (nu : ℝ) : Continuous (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) nu) := by
  have hfun : _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) nu =
      fun a : ℝ => ∫ b, _root_.GD.N0106.N0428.N0765.N1513.d029289 nu (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0) * _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b) := by
    funext a
    exact _root_.GD.N0106.N0428.N0765.N1513.d029294 _ nu
  rw [hfun]
  have hC := _root_.GD.N0106.N0428.N0765.N1513.d029300 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279
  apply continuous_of_dominated
    (bound := fun b => _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0 * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b)
  · intro a
    have hF : Measurable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)) :=
      (_root_.GD.N0106.N0428.N0765.N1512.d029196 channel k eta 0 0).comp (measurable_const.prodMk measurable_id)
    have ho : Measurable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1513.d029289 nu (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) := by unfold _root_.GD.N0106.N0428.N0765.N1513.d029289 _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop
    exact (ho.mul hF).aestronglyMeasurable
  · intro a
    apply Filter.Eventually.of_forall
    intro b
    simp only [norm_mul, _root_.GD.N0106.N0428.N0765.N1513.d029291, mul_zero, Real.exp_zero, one_mul]
    have hdec : _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a ≤ 1 := by
      rw [_root_.GD.N0106.N0428.N0765.N1513.d029280, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel).le) (abs_nonneg a)
    exact (_root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279 a b).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec hC) (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le).trans_eq
        (by ring))
  · exact (_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)).const_mul _
  · apply Filter.Eventually.of_forall
    intro b
    have hcont : Continuous (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      have hd := _root_.GD.N0106.N0428.N0765.N1512.d029192 channel k (lt_of_lt_of_le zero_lt_one heta)
        (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (w := _root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)
        (by simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1513.d029279)
      exact ContinuousAt.comp (f := fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 t 0) (x := a)
        hd.continuousAt (by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop)
    exact hcont.const_mul _

theorem d029304 (channel : Bool) (k : ℕ) {eta : ℝ} (heta : 1 ≤ eta) (a nu : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) nu a‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0 * ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b) *
        _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a := by
  rw [_root_.GD.N0106.N0428.N0765.N1652.d005816, _root_.GD.N0106.N0428.N0765.N1513.d029294]
  calc
    _ ≤ ∫ b : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1513.d029289 nu (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0) * _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ b : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)‖ := by
      simp only [norm_mul, _root_.GD.N0106.N0428.N0765.N1513.d029291, mul_zero, Real.exp_zero, one_mul]
    _ ≤ ∫ b : ℝ, (_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0 *
        _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a) * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b := by
      apply integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1513.d029285 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279 a).norm
        ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)).const_mul _)
      exact Filter.Eventually.of_forall fun b => _root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279 a b
    _ = _ := by rw [integral_const_mul]; ring

theorem d029305 (channel : Bool) (k : ℕ) {eta d : ℝ} (heta : 1 ≤ eta)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * d < Real.pi) (a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (a, b)) := by
  obtain ⟨C, _, hC⟩ := _root_.GD.N0106.N0428.N0765.N1513.d029301 channel k heta hd.le hstrip
  refine ⟨_root_.GD.N0106.N0428.N0765.N1513.d029302 channel k heta a, 5, 5, 2 * Real.pi * d,
    _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0 * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a,
    C * _root_.GD.N0106.N0428.N0765.N1587.d029254 (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029209 channel) a,
    by norm_num, by norm_num, by positivity, ?_, ?_⟩
  · intro b
    exact _root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279 a b
  · intro nu
    simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005816, neg_mul] using hC a nu

theorem d029306 (channel : Bool) (k : ℕ) {eta d : ℝ} (heta : 1 ≤ eta)
    (hd : 0 < d) (hstrip : ((21 : ℝ) / 2) * (d + d) < Real.pi) (nu : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) nu) := by
  refine ⟨_root_.GD.N0106.N0428.N0765.N1513.d029303 channel k heta nu,
    _root_.GD.N0106.N0428.N0765.N1512.d029209 channel, _root_.GD.N0106.N0428.N0765.N1512.d029209 channel, 2 * Real.pi * d,
    _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0 * ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 5 b,
    _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta d d * Real.exp (-2 * Real.pi * d * |nu|),
    _root_.GD.N0106.N0428.N0765.N1512.d029210 channel, _root_.GD.N0106.N0428.N0765.N1512.d029210 channel, by positivity, ?_, ?_⟩
  · intro a
    exact _root_.GD.N0106.N0428.N0765.N1513.d029304 channel k heta a nu
  · intro xi
    rw [show -(2 * Real.pi * d) * |xi| = -2 * Real.pi * d * |xi| by ring]
    simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005817, mul_assoc, mul_left_comm, mul_comm] using
      _root_.GD.N0106.N0428.N0765.N1513.d029298 channel k heta hd.le hd.le hstrip xi nu

theorem d029307 (channel : Bool) (k : ℕ) {eta h d : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (hd : 0 < d)
    (hs : ((21 : ℝ) / 2) * d < Real.pi) (a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h (a, b)) :=
  _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029269 (_root_.GD.N0106.N0428.N0765.N1513.d029305 channel k heta hd hs (h * a)) hh)

theorem d029308 (channel : Bool) (k : ℕ) {eta h d : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (hd : 0 < d)
    (hs : ((21 : ℝ) / 2) * (d + d) < Real.pi) (n : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h) n) := by
  have heq : _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h) n =
      fun a : ℝ => h⁻¹ • _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) (n / h) (h * a) := by
    funext a
    exact _root_.GD.N0106.N0428.N0765.N1652.d005823 _ hh _ _
  rw [heq]
  exact _root_.GD.N0106.N0428.N0765.N1601.d029268 (_root_.GD.N0106.N0428.N0765.N1601.d029270
    (_root_.GD.N0106.N0428.N0765.N1601.d029269 (_root_.GD.N0106.N0428.N0765.N1513.d029306 channel k heta hd hs (n / h)) hh) h⁻¹)

theorem d029309 (channel : Bool) (k : ℕ) {eta h : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0 (x + h * p.1, y + h * p.2)) := by
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819
    ((_root_.GD.N0106.N0428.N0765.N1590.d029266 (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) hh x).mul_left
      (_root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta 0 0))
    (_root_.GD.N0106.N0428.N0765.N1590.d029266 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5) hh y)
  · intro n
    exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1513.d029300 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279) (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro n
    exact (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro p
    exact _root_.GD.N0106.N0428.N0765.N1513.d029281 channel k heta _root_.GD.N0106.N0428.N0765.N1513.d029279 _ _

private theorem d029310 {h : ℝ} (hh : 0 < h) (x n : ℝ) :
    h * (x / h + n) = x + h * n := by field_simp [hh.ne']

private theorem d029311 {h : ℝ} (hh : 0 < h) (d x : ℝ) :
    -2 * Real.pi * d * |x / h| = -(2 * Real.pi * d / h) * |x| := by
  rw [abs_div, abs_of_pos hh]
  ring

theorem d029312 (channel : Bool) (k : ℕ) {eta h : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (x y : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h (x / h + p.1, y / h + p.2)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005822, _root_.GD.N0106.N0428.N0765.N1513.d029310 hh] using _root_.GD.N0106.N0428.N0765.N1513.d029309 channel k heta hh x y

theorem d029313 (channel : Bool) (k : ℕ) {eta h d : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (hd : 0 < d)
    (hs : ((21 : ℝ) / 2) * d < Real.pi) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h) p.2 (x / h + p.1)) := by
  obtain ⟨C, hC, hbound⟩ := _root_.GD.N0106.N0428.N0765.N1513.d029301 channel k heta hd.le hs
  have hk : 0 < 2 * Real.pi * d / h := by positivity
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819
    ((_root_.GD.N0106.N0428.N0765.N1590.d029266 (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) (_root_.GD.N0106.N0428.N0765.N1512.d029210 channel) hh x).mul_left (h⁻¹ * C))
    (_root_.GD.N0106.N0428.N0765.N1590.d029265 hk)
  · intro n
    exact mul_nonneg (mul_nonneg (inv_pos.mpr hh).le hC) (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  · intro n
    exact (Real.exp_pos _).le
  · intro p
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005823 _ hh, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hh), _root_.GD.N0106.N0428.N0765.N1513.d029310 hh]
    have hb := mul_le_mul_of_nonneg_left (hbound (x + h * p.1) (p.2 / h)) (inv_pos.mpr hh).le
    rw [_root_.GD.N0106.N0428.N0765.N1513.d029311 hh d (p.2 : ℝ)] at hb
    simpa only [mul_assoc] using hb

theorem d029314 (channel : Bool) (k : ℕ) {eta h d : ℝ}
    (heta : 1 ≤ eta) (hh : 0 < h) (hd : 0 < d)
    (hs : ((21 : ℝ) / 2) * (d + d) < Real.pi) :
    Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta 0 0) h) p.1 p.2) := by
  have hk : 0 < 2 * Real.pi * d / h := by positivity
  let C : ℝ := |h⁻¹ * h⁻¹ * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta d d|
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819 ((_root_.GD.N0106.N0428.N0765.N1590.d029265 hk).mul_left C) (_root_.GD.N0106.N0428.N0765.N1590.d029265 hk)
  · intro n
    exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  · intro n
    exact (Real.exp_pos _).le
  · intro p
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005824 _ hh, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos (inv_pos.mpr hh) (inv_pos.mpr hh))]
    have hb := mul_le_mul_of_nonneg_left
      (_root_.GD.N0106.N0428.N0765.N1513.d029298 channel k heta hd.le hd.le hs (p.1 / h) (p.2 / h))
      (mul_pos (inv_pos.mpr hh) (inv_pos.mpr hh)).le
    rw [_root_.GD.N0106.N0428.N0765.N1513.d029311 hh d (p.1 : ℝ), _root_.GD.N0106.N0428.N0765.N1513.d029311 hh d (p.2 : ℝ)] at hb
    have hc : h⁻¹ * h⁻¹ * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta d d ≤ C := le_abs_self _
    calc _ ≤ (h⁻¹ * h⁻¹ * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta d d) *
        Real.exp (-(2 * Real.pi * d / h) * |(p.1 : ℝ)|) *
        Real.exp (-(2 * Real.pi * d / h) * |(p.2 : ℝ)|) := by simpa only [mul_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) (Real.exp_nonneg _)

def d029315 (channel : Bool) (k : Fin 5) (eta : ℝ) (q : ℝ × ℝ) : ℝ :=
  (1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q *
    _root_.GD.N0106.N0428.N0765.N1627.d021104 (k, if channel then 1 else 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q))

theorem d029316 (channel : Bool) (k : Fin 5) {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta q : ℂ) = _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k.val eta 0 0 q := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1550.d005478, _root_.GD.N0106.N0428.N0765.N1513.d029315] using (_root_.GD.N0106.N0428.N0765.N1512.d029205 channel k heta q).symm



theorem d029317 (channel : Bool) (k : Fin 5) (location : ℝ)
    {eta h d0 d1 : ℝ} (heta : 1 ≤ eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi) (x y : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0) -
      h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta (x + h * p.1, y + h * p.2))| ≤
      (2 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta d0 0 + 2 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta 0 d0) /
        (Real.exp (2 * Real.pi * d0 / h) - 1) +
      4 * _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k.val eta d1 d1 / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2 := by
  have he : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have heq : (fun p : ℝ × ℝ => (_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta p : ℂ)) = _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k.val eta 0 0 := by
    funext p
    exact _root_.GD.N0106.N0428.N0765.N1513.d029316 channel k he p
  have hre : _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta = fun p => (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k.val eta 0 0 p).re := by
    funext p
    rw [← _root_.GD.N0106.N0428.N0765.N1513.d029316 channel k he]
    rfl
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta) := by
    rw [hre]
    exact (_root_.GD.N0106.N0428.N0765.N1512.d029203 channel k.val heta _root_.GD.N0106.N0428.N0765.N1513.d029279).re
  have hint : (∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1513.d029315 channel k eta (a, b)) =
      _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0) := by
    rw [← integral_prod _ hi, ← Measure.volume_eq_prod]
    unfold _root_.GD.N0106.N0428.N0765.N1513.d029315
    rw [integral_const_mul, ← _root_.GD.N0106.N0428.N0765.N1512.d029180 location eta he]
  rw [← hint]
  have hsmall : ((21 : ℝ) / 2) * d1 < Real.pi := by nlinarith
  refine _root_.GD.N0106.N0428.N0765.N1653.d005827 hh hd0 hd1 ?_ ?_ x y ?_ ?_ ?_ ?_ ?_ ?_
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1513.d029307 channel k.val heta hh hd1 hsmall
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1513.d029308 channel k.val heta hh hd1 hmixed
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1513.d029312 channel k.val heta hh x y
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1513.d029313 channel k.val heta hh hd1 hsmall x
  · rw [heq]
    exact _root_.GD.N0106.N0428.N0765.N1513.d029314 channel k.val heta hh hd1 hmixed
  · intro m _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1513.d029298 channel k.val heta hd0.le (le_refl (0 : ℝ))
      (by simpa only [add_zero] using haxis) (m / h) 0
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1513.d029311 hh] using hb
  · intro n _
    rw [heq]
    have hb := _root_.GD.N0106.N0428.N0765.N1513.d029298 channel k.val heta (le_refl (0 : ℝ)) hd0.le
      (by simpa only [zero_add] using haxis) 0 (n / h)
    simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1513.d029311 hh] using hb
  · intro m n _ _
    rw [heq]
    simpa only [_root_.GD.N0106.N0428.N0765.N1513.d029311 hh] using _root_.GD.N0106.N0428.N0765.N1513.d029298 channel k.val heta hd1.le hd1.le hmixed (m / h) (n / h)

end
end GD.N0106.N0428.N0765.N1513

#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029296
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029298
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029303
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029307
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029308
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029313
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029314
#print axioms _root_.GD.N0106.N0428.N0765.N1513.d029317
