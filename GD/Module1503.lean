import GD.Module0542
import GD.Module0550
import GD.Module0549
import GD.Module1501
import GD.Module0749

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0225.N0540
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0072
open _root_.GD.N0225.N0539 _root_.GD.N0225.N0541 _root_.GD.N0225.N0538
open _root_.GD.N0225.N0542
open _root_.GD.N0213.N0495

variable {k : ℕ}

local instance d023472 : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := borel (_root_.GD.N0232.N0719.N0859.d010809 k)
local instance d023473 : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨rfl⟩

theorem d023474 {r : ℝ} (hr : 0 < r) (u v : ℝ) :
    ‖u * v‖ ≤ r⁻¹ * u ^ 2 + r * v ^ 2 := by
  rw [Real.norm_eq_abs, abs_mul]
  apply (mul_le_mul_iff_right₀ hr).mp
  have hcancel : r * (r⁻¹ * u ^ 2 + r * v ^ 2) = u ^ 2 + (r * |v|) ^ 2 := by
    rw [mul_pow, sq_abs]
    field_simp [hr.ne']
  rw [hcancel]
  nlinarith [sq_nonneg (|u| - r * |v|), sq_abs u,
    mul_nonneg (abs_nonneg u) (mul_nonneg hr.le (abs_nonneg v))]

theorem d023475 (α : Fin k → ℝ) (hsum : ∑ i, α i = 1) :
    ∀ᵐ β ∂_root_.GD.N0225.N0539.d008044 α, 0 < ∑ i, β i := by
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    simp at hsum
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  exact Finset.sum_pos (fun i _ => hβ i) ⟨⟨0, hk⟩, Finset.mem_univ _⟩

theorem d023476 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => _root_.GD.N0213.N0495.d007174 L (∑ i, β i) * _root_.GD.N0213.N0495.d007175 L (∑ i, β i)) (_root_.GD.N0225.N0539.d008044 α) := by
  have hi : Integrable (fun β => (∑ i, β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2) (_root_.GD.N0225.N0539.d008044 α) := by
    simpa only [Real.rpow_neg_one] using _root_.GD.N0225.N0539.d008057 α hα hsum hL (-1)
  apply (hi.add (_root_.GD.N0225.N0542.d008165 α hα hsum hL)).mono'
    (show AEStronglyMeasurable (fun β : Fin k → ℝ =>
      _root_.GD.N0213.N0495.d007174 L (∑ i, β i) * _root_.GD.N0213.N0495.d007175 L (∑ i, β i)) (_root_.GD.N0225.N0539.d008044 α) by
      apply Measurable.aestronglyMeasurable
      dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]
      fun_prop)
  exact (_root_.GD.N0225.N0540.d023475 α hsum).mono (fun β hβ => _root_.GD.N0225.N0540.d023474 hβ _ _)

theorem d023477 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => |_root_.GD.N0213.N0495.d007174 L (∑ i, β i) * _root_.GD.N0213.N0495.d007175 L (∑ i, β i)|) (_root_.GD.N0225.N0539.d008044 α) :=
  (_root_.GD.N0225.N0540.d023476 α hα hsum hL).abs


theorem d023478 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) (q : ℝ) :
    Integrable (fun β : Fin k → ℝ => (∑ i, β i) ^ q) (_root_.GD.N0225.N0539.d008058 α L) := by
  rw [_root_.GD.N0225.N0539.d008058, integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun β : Fin k → ℝ =>
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2)) by dsimp only [_root_.GD.N0213.N0495.d007174]; fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm] using
    _root_.GD.N0225.N0539.d008057 α hα hsum hL q

theorem d023479 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L)
    (g : (Fin k → ℝ) → ℝ) (hg : AEStronglyMeasurable g (_root_.GD.N0225.N0539.d008058 α L))
    (C q : ℝ) (hbound : ∀ β ∈ _root_.GD.N0225.N0541.d008076, ‖g β‖ ≤ C * (∑ i, β i) ^ q) :
    Integrable g (_root_.GD.N0225.N0539.d008058 α L) := by
  apply ((_root_.GD.N0225.N0540.d023478 α hα hsum hL q).const_mul C).mono' hg
  exact (_root_.GD.N0225.N0541.d008081 α L).mono (fun β hβ => hbound β hβ)

variable (sizes : Fin k → ℕ)

def d023480 (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (β : Fin k → ℝ) : ℝ :=
  (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal -
  (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes w)).toReal

theorem d023481
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    Measurable (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k => (_root_.GD.N0232.N0719.N0859.d010840 k sizes θ f).toReal) := by
  have h := (_root_.GD.N0232.N0719.N0865.d011222 k sizes
    (_root_.GD.N0232.N0719.N0970.d012312 k sizes f hf)).measurable.ennreal_toReal
  simpa only [_root_.GD.N0232.N0719.N0970.d012313 k sizes f hf] using h


theorem d023482
    (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    {L : ℝ} (hL : 0 < L)
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (C : ℝ) (hcap : ∀ β ∈ _root_.GD.N0225.N0541.d008076,
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) f).toReal ≤ C / (∑ i, β i)) :
    Integrable (fun β => (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) f).toReal) (_root_.GD.N0225.N0539.d008058 α L) := by
  apply _root_.GD.N0225.N0540.d023479 α hα hsum hL _
    ((_root_.GD.N0225.N0540.d023481 sizes f hf).comp hchart).aestronglyMeasurable C (-1)
  intro β hβ
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.rpow_neg_one, div_eq_mul_inv] using hcap β hβ

theorem d023483
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : _root_.GD.N0072.d023291 sizes p ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hw : _root_.GD.N0072.d023291 sizes w ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    Measurable (_root_.GD.N0225.N0540.d023480 sizes chart p w) :=
  ((_root_.GD.N0225.N0540.d023481 sizes _ hp).comp hchart).sub
    ((_root_.GD.N0225.N0540.d023481 sizes _ hw).comp hchart)


theorem d023484
    (α : Fin k → ℝ) (L : ℝ)
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : _root_.GD.N0072.d023291 sizes p ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hw : _root_.GD.N0072.d023291 sizes w ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (hint : Integrable (fun β =>
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal)
        (_root_.GD.N0225.N0539.d008058 α L)) :
    Integrable (_root_.GD.N0225.N0540.d023480 sizes chart p w) (_root_.GD.N0225.N0539.d008058 α L) := by
  apply hint.mono' (_root_.GD.N0225.N0540.d023483 sizes chart hchart p w hp hw).aestronglyMeasurable
  filter_upwards with β
  have hnn : 0 ≤ _root_.GD.N0225.N0540.d023480 sizes chart p w β :=
    sub_nonneg.mpr (ENNReal.toReal_mono (hp.2 (chart β)) (hweak (chart β)))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, _root_.GD.N0225.N0540.d023480]
  exact sub_le_self _ ENNReal.toReal_nonneg

theorem d023485
    (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    {L : ℝ} (hL : 0 < L)
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : _root_.GD.N0072.d023291 sizes p ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hw : _root_.GD.N0072.d023291 sizes w ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (C : ℝ) (hcap : ∀ β ∈ _root_.GD.N0225.N0541.d008076,
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal ≤
        C / (∑ i, β i)) :
    Integrable (_root_.GD.N0225.N0540.d023480 sizes chart p w) (_root_.GD.N0225.N0539.d008058 α L) := by
  apply _root_.GD.N0225.N0540.d023479 α hα hsum hL _
    (_root_.GD.N0225.N0540.d023483 sizes chart hchart p w hp hw).aestronglyMeasurable C (-1)
  intro β hβ
  have hle := ENNReal.toReal_mono (hp.2 (chart β)) (hweak (chart β))
  have hnn : 0 ≤ _root_.GD.N0225.N0540.d023480 sizes chart p w β := sub_nonneg.mpr hle
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, _root_.GD.N0225.N0540.d023480, Real.rpow_neg_one]
  calc
    _ ≤ (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal :=
      sub_le_self _ ENNReal.toReal_nonneg
    _ ≤ C / (∑ i, β i) := hcap β hβ
    _ = C * (∑ i, β i)⁻¹ := div_eq_mul_inv _ _

theorem d023486
    (hn : ∀ i, 2 ≤ sizes i)
    (α : Fin k → ℝ)
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (hbaseInt : ∀ n : ℕ, Integrable (fun β =>
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal)
        (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)))
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hregret : ∀ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w → (∀ t, ∑ i, w t i = 1) → (∀ t i, 0 ≤ w t i) →
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) →
      ∀ n : ℕ, (∫ β, _root_.GD.N0225.N0540.d023480 sizes chart p w β
        ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤ B n) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  rintro ⟨w, hw, hwunit, hweak, hstrict⟩
  let v := _root_.GD.N0072.d007614 ∘ w
  have hvm : Measurable v := _root_.GD.N0072.d007625.comp hw
  have hvunit : ∀ t, ∑ i, v t i = 1 := fun t => _root_.GD.N0072.d007617 (w t) (hwunit t)
  have hvnn : ∀ t i, 0 ≤ v t i := fun t i => _root_.GD.N0072.d007616 (w t) (hwunit t) i
  have hvweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := fun θ =>
    (_root_.GD.N0072.d023444 sizes hn w hw hwunit θ).trans (hweak θ)
  have hvstrict : ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := by
    obtain ⟨θ, hθ⟩ := hstrict
    exact ⟨θ, (_root_.GD.N0072.d023444 sizes hn w hw hwunit θ).trans_lt hθ⟩
  obtain ⟨hmidm, hmidunit, hmidnn, hmidstrict⟩ :=
    _root_.GD.N0225.N0538.d023465 sizes hn p v hp hvm hpunit hvunit hpnn hvnn hvweak hvstrict
  have hpf := _root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn
  have hmidf := _root_.GD.N0225.N0538.d023463 sizes hn _ hmidm hmidunit hmidnn
  have hmidweak := fun θ => (hmidstrict θ).le
  exact _root_.GD.N0101.N0408.d008172 α
    (_root_.GD.N0225.N0540.d023480 sizes chart p (_root_.GD.N0225.N0538.d023458 p v)) B
    (fun β _ => sub_pos.mpr
      ((ENNReal.toReal_lt_toReal (hmidf.2 (chart β)) (hpf.2 (chart β))).mpr
        (hmidstrict (chart β))))
    (fun n => _root_.GD.N0225.N0540.d023484 sizes α ((n : ℝ) + 1)
      chart hchart p _ hpf hmidf hmidweak (hbaseInt n))
    (hregret _ hmidm hmidunit hmidnn hmidweak) hB



theorem d023487
    (hn : ∀ i, 2 ≤ sizes i)
    (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    (chart : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d010809 k) (hchart : Measurable chart)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (C : ℝ) (hcap : ∀ β ∈ _root_.GD.N0225.N0541.d008076,
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes (chart β) (_root_.GD.N0072.d023291 sizes p)).toReal ≤
        C / (∑ i, β i))
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hregret : ∀ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w → (∀ t, ∑ i, w t i = 1) → (∀ t i, 0 ≤ w t i) →
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) →
      ∀ n : ℕ, (∫ β, _root_.GD.N0225.N0540.d023480 sizes chart p w β
        ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤ B n) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  apply _root_.GD.N0225.N0540.d023486 sizes hn α
    chart hchart p hp hpunit hpnn ?_ B hB hregret
  intro n
  exact _root_.GD.N0225.N0540.d023482 sizes α hα hsum (by positivity)
    chart hchart _ (_root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn) C hcap

end
end GD.N0225.N0540

#print axioms _root_.GD.N0225.N0540.d023478
#print axioms _root_.GD.N0225.N0540.d023479
#print axioms _root_.GD.N0225.N0540.d023481
#print axioms _root_.GD.N0225.N0540.d023483
#print axioms _root_.GD.N0225.N0540.d023485
#print axioms _root_.GD.N0225.N0540.d023487

#print axioms _root_.GD.N0225.N0540.d023482

#print axioms _root_.GD.N0225.N0540.d023484

#print axioms _root_.GD.N0225.N0540.d023486

#print axioms _root_.GD.N0225.N0540.d023474

#print axioms _root_.GD.N0225.N0540.d023475

#print axioms _root_.GD.N0225.N0540.d023476

#print axioms _root_.GD.N0225.N0540.d023477
