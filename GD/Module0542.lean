import GD.Module0539
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0225.N0541

noncomputable section

open _root_.GD.N0225.N0539
open _root_.GD.N0213.N0495

variable {k : ℕ}

def d008076 : Set (Fin k → ℝ) := {β | ∀ i, 0 < β i}

theorem d008077 : IsOpen (_root_.GD.N0225.N0541.d008076 (k := k)) := by
  simpa only [_root_.GD.N0225.N0541.d008076, Set.setOf_forall] using
    (isOpen_iInter_of_finite fun i : Fin k =>
      isOpen_lt continuous_const (continuous_apply i))

theorem d008078 (α β : Fin k → ℝ) :
    0 < _root_.GD.N0225.N0539.d008043 α β ↔ β ∈ _root_.GD.N0225.N0541.d008076 := by
  by_cases h : ∀ i, 0 < β i
  · constructor
    · intro _
      exact h
    · intro _
      simp only [_root_.GD.N0225.N0539.d008043, if_pos h]
      exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (h i) _)
  · simp [_root_.GD.N0225.N0539.d008043, h, _root_.GD.N0225.N0541.d008076]

theorem d008079 (α β : Fin k → ℝ) (hβ : β ∈ _root_.GD.N0225.N0541.d008076)
    {U : Set (Fin k → ℝ)} (hU : U ∈ 𝓝 β) :
    0 < _root_.GD.N0225.N0539.d008044 α U := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hz' := (withDensity_apply_eq_zero ((_root_.GD.N0225.N0539.d008046 α).ennreal_ofReal)).mp hz
  have heq : {x : Fin k → ℝ | ENNReal.ofReal (_root_.GD.N0225.N0539.d008043 α x) ≠ 0} = _root_.GD.N0225.N0541.d008076 := by
    ext x
    simp only [Set.mem_setOf_eq, ← pos_iff_ne_zero, ENNReal.ofReal_pos, _root_.GD.N0225.N0541.d008078]
  rw [heq] at hz'
  exact (Measure.measure_pos_of_mem_nhds (volume : Measure (Fin k → ℝ))
    (inter_mem (_root_.GD.N0225.N0541.d008077.mem_nhds hβ) hU)).ne' hz'

theorem d008080 (α : Fin k → ℝ) (L : ℝ) :
    _root_.GD.N0225.N0539.d008044 α ≪ _root_.GD.N0225.N0539.d008058 α L := by
  apply withDensity_absolutelyContinuous'
    (show Measurable (fun β : Fin k → ℝ =>
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2)) by dsimp only [_root_.GD.N0213.N0495.d007174]; fun_prop).aemeasurable
  filter_upwards with β
  exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (_root_.GD.N0213.N0495.d007176 _ _))).ne'

theorem d008081 (α : Fin k → ℝ) (L : ℝ) :
    ∀ᵐ β ∂_root_.GD.N0225.N0539.d008058 α L, β ∈ _root_.GD.N0225.N0541.d008076 :=
  (withDensity_absolutelyContinuous (_root_.GD.N0225.N0539.d008044 α) _).ae_le (_root_.GD.N0225.N0539.d008050 α)

theorem d008082 (α β : Fin k → ℝ) (L : ℝ)
    (hβ : β ∈ _root_.GD.N0225.N0541.d008076) {U : Set (Fin k → ℝ)} (hU : U ∈ 𝓝 β) :
    0 < _root_.GD.N0225.N0539.d008058 α L U := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (_root_.GD.N0225.N0541.d008079 α β hβ hU).ne'
    (_root_.GD.N0225.N0541.d008080 α L hz)

theorem d008083 {L M : ℝ} (hL : 0 < L) (hLM : L ≤ M) (r : ℝ) :
    _root_.GD.N0213.N0495.d007174 L r ≤ _root_.GD.N0213.N0495.d007174 M r := by
  have hM : 0 < M := hL.trans_le hLM
  apply Real.exp_le_exp.mpr
  simp only [div_pow]
  apply neg_le_neg
  exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hL)
    ((sq_le_sq₀ hL.le hM.le).mpr hLM)

theorem d008084 (α : Fin k → ℝ) {L M : ℝ}
    (hL : 0 < L) (hLM : L ≤ M) : _root_.GD.N0225.N0539.d008058 α L ≤ _root_.GD.N0225.N0539.d008058 α M := by
  apply withDensity_mono
  filter_upwards with β
  apply ENNReal.ofReal_le_ofReal
  exact (sq_le_sq₀ (_root_.GD.N0213.N0495.d007176 _ _).le (_root_.GD.N0213.N0495.d007176 _ _).le).mpr
    (_root_.GD.N0225.N0541.d008083 hL hLM _)

theorem d008085 (α β : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) (hβ : β ∈ _root_.GD.N0225.N0541.d008076)
    {U : Set (Fin k → ℝ)} (hU : U ∈ 𝓝 β) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c ≤ (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1) U).toReal := by
  have hfinite (L : ℝ) (hL : 0 < L) : _root_.GD.N0225.N0539.d008058 α L U ≠ ⊤ :=
    ne_top_of_le_ne_top (_root_.GD.N0225.N0539.d008059 α hα hsum hL) (measure_mono (subset_univ U))
  refine ⟨(_root_.GD.N0225.N0539.d008058 α 1 U).toReal,
    ENNReal.toReal_pos (_root_.GD.N0225.N0541.d008082 α β 1 hβ hU).ne'
      (hfinite 1 zero_lt_one), ?_⟩
  intro n
  apply ENNReal.toReal_mono (hfinite _ (by positivity))
  exact (_root_.GD.N0225.N0541.d008084 α zero_lt_one (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) U

theorem d008086
    (α β : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    (hβ : β ∈ _root_.GD.N0225.N0541.d008076) (g : (Fin k → ℝ) → ℝ)
    (hgm : Measurable g) (hg : ContinuousAt g β) (hgpos : 0 < g β) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ⊤ ∧ ∀ n : ℕ,
      δ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1) := by
  let ε : ℝ := g β / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let U : Set (Fin k → ℝ) := {x | ε < g x}
  have hU : MeasurableSet U := measurableSet_lt measurable_const hgm
  have hUnear : U ∈ 𝓝 β := hg (lt_mem_nhds (by dsimp [ε]; linarith : ε < g β))
  have hmass := _root_.GD.N0225.N0541.d008082 α β 1 hβ hUnear
  have hfinite : _root_.GD.N0225.N0539.d008058 α 1 U ≠ ⊤ :=
    ne_top_of_le_ne_top (_root_.GD.N0225.N0539.d008059 α hα hsum zero_lt_one) (measure_mono (subset_univ U))
  refine ⟨ENNReal.ofReal ε * _root_.GD.N0225.N0539.d008058 α 1 U,
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' hmass.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite, ?_⟩
  intro n
  apply le_trans ?_ (lintegral_mono' (_root_.GD.N0225.N0541.d008084 α zero_lt_one
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) le_rfl)
  calc
    ENNReal.ofReal ε * _root_.GD.N0225.N0539.d008058 α 1 U =
        ∫⁻ _x in U, ENNReal.ofReal ε ∂_root_.GD.N0225.N0539.d008058 α 1 := by rw [setLIntegral_const]
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (g x) ∂_root_.GD.N0225.N0539.d008058 α 1 :=
      setLIntegral_mono' hU (fun x hx => ENNReal.ofReal_le_ofReal hx.le)
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂_root_.GD.N0225.N0539.d008058 α 1 := setLIntegral_le_lintegral _ _

theorem d008087
    (α β : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    (hβ : β ∈ _root_.GD.N0225.N0541.d008076) (g : (Fin k → ℝ) → ℝ)
    (hgm : Measurable g) (hg : ContinuousAt g β) (hgpos : 0 < g β)
    (hnonneg : ∀ x ∈ _root_.GD.N0225.N0541.d008076, 0 ≤ g x)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ ∫ x, g x ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1) := by
  obtain ⟨δ, hδ, hδfin, hbound⟩ :=
    _root_.GD.N0225.N0541.d008086 α β hα hsum hβ g hgm hg hgpos
  refine ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' hδfin, ?_⟩
  intro n
  have hnn : ∀ᵐ x ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1), 0 ≤ g x :=
    (_root_.GD.N0225.N0541.d008081 α _).mono (fun x hx => hnonneg x hx)
  have hb := hbound n
  rw [← ofReal_integral_eq_lintegral_ofReal (hint n) hnn] at hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb


theorem d008088
    (α : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ)
    (hgpos : ∀ x ∈ _root_.GD.N0225.N0541.d008076, 0 < g x)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ ∫ x, g x ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1) := by
  have hnn (n : ℕ) : ∀ᵐ x ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1), 0 ≤ g x :=
    (_root_.GD.N0225.N0541.d008081 α _).mono (fun x hx => (hgpos x hx).le)
  have horth : 0 < _root_.GD.N0225.N0539.d008058 α 1 _root_.GD.N0225.N0541.d008076 :=
    _root_.GD.N0225.N0541.d008082 α (fun _ => 1) 1 (fun _ => zero_lt_one)
      (_root_.GD.N0225.N0541.d008077.mem_nhds (fun _ => zero_lt_one))
  have hsupp : 0 < _root_.GD.N0225.N0539.d008058 α 1 (Function.support g) :=
    horth.trans_le (measure_mono (fun x hx => (hgpos x hx).ne'))
  have hbase : 0 < ∫ x, g x ∂_root_.GD.N0225.N0539.d008058 α 1 :=
    (integral_pos_iff_support_of_nonneg_ae (f := g) (by
      change ∀ᵐ x ∂_root_.GD.N0225.N0539.d008058 α 1, 0 ≤ g x
      simpa only [Nat.cast_zero, zero_add] using hnn 0)
      (by simpa using hint 0)).mpr hsupp
  refine ⟨∫ x, g x ∂_root_.GD.N0225.N0539.d008058 α 1, hbase, ?_⟩
  intro n
  exact integral_mono_measure
    (_root_.GD.N0225.N0541.d008084 α zero_lt_one
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) (hnn n) (hint n)

end
end GD.N0225.N0541

#print axioms _root_.GD.N0225.N0541.d008079
#print axioms _root_.GD.N0225.N0541.d008080
#print axioms _root_.GD.N0225.N0541.d008081
#print axioms _root_.GD.N0225.N0541.d008082
#print axioms _root_.GD.N0225.N0541.d008083
#print axioms _root_.GD.N0225.N0541.d008084
#print axioms _root_.GD.N0225.N0541.d008085
#print axioms _root_.GD.N0225.N0541.d008086
#print axioms _root_.GD.N0225.N0541.d008087

#print axioms _root_.GD.N0225.N0541.d008088
