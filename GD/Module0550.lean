import GD.Module0542
import GD.Module0549

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0101.N0408

noncomputable section

open _root_.GD.N0225.N0539
open _root_.GD.N0225.N0541
open _root_.GD.N0225.N0542
open _root_.GD.N0213.N0495

variable {k : ℕ}



theorem d008170
    (α : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) (E : ℕ → ℝ)
    (hnonneg : ∀ β ∈ _root_.GD.N0225.N0541.d008076, 0 ≤ g β)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)))
    (hbound : ∀ n : ℕ, (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤ E n)
    (hE : Tendsto E atTop (𝓝 0)) :
    g =ᵐ[_root_.GD.N0225.N0539.d008044 α] 0 := by
  have hnn (n : ℕ) : 0 ≤ᵐ[_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)] g := by
    filter_upwards [_root_.GD.N0225.N0541.d008081 α ((n : ℝ) + 1)] with β hβ
    exact hnonneg β hβ
  have hnn₀ : 0 ≤ᵐ[_root_.GD.N0225.N0539.d008058 α 1] g := by
    simpa only [Nat.cast_zero, zero_add] using hnn 0
  have hint₀ : Integrable g (_root_.GD.N0225.N0539.d008058 α 1) := by
    simpa only [Nat.cast_zero, zero_add] using hint 0
  have hle (n : ℕ) : (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α 1) ≤ E n := by
    apply le_trans ?_ (hbound n)
    exact integral_mono_measure
      (_root_.GD.N0225.N0541.d008084 α zero_lt_one
        (le_add_of_nonneg_left (Nat.cast_nonneg n))) (hnn n) (hint n)
  have hz : (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α 1) = 0 :=
    le_antisymm (ge_of_tendsto' hE hle) (integral_nonneg_of_ae hnn₀)
  exact (_root_.GD.N0225.N0541.d008080 α 1).ae_le
    ((integral_eq_zero_iff_of_nonneg_ae hnn₀ hint₀).mp hz)



theorem d008171
    (α c : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    (g : (Fin k → ℝ) → ℝ)
    (hnonneg : ∀ β ∈ _root_.GD.N0225.N0541.d008076, 0 ≤ g β)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)))
    (hbound : ∀ n : ℕ,
      (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤
        ∫ β, ∑ i, c i * (β i *
          _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α) :
    g =ᵐ[_root_.GD.N0225.N0539.d008044 α] 0 :=
  _root_.GD.N0101.N0408.d008170 α g _ hnonneg hint hbound
    (_root_.GD.N0225.N0542.d008169 α c hα hsum)




theorem d008172
    (α : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) (E : ℕ → ℝ)
    (hpositive : ∀ β ∈ _root_.GD.N0225.N0541.d008076, 0 < g β)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)))
    (hbound : ∀ n : ℕ, (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤ E n)
    (hE : Tendsto E atTop (𝓝 0)) : False := by
  have hz := _root_.GD.N0101.N0408.d008170 α g E
    (fun β hβ => (hpositive β hβ).le) hint hbound hE
  have horth : 0 < _root_.GD.N0225.N0539.d008044 α _root_.GD.N0225.N0541.d008076 :=
    _root_.GD.N0225.N0541.d008079 α (fun _ => 1) (fun _ => zero_lt_one)
      (_root_.GD.N0225.N0541.d008077.mem_nhds (fun _ => zero_lt_one))
  have hzero : _root_.GD.N0225.N0539.d008044 α {β | g β ≠ 0} = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using hz
  exact horth.ne' (measure_mono_null
    (fun β hβ => (hpositive β hβ).ne') hzero)



theorem d008173
    (α c : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    (g : (Fin k → ℝ) → ℝ)
    (hpositive : ∀ β ∈ _root_.GD.N0225.N0541.d008076, 0 < g β)
    (hint : ∀ n : ℕ, Integrable g (_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)))
    (hbound : ∀ n : ℕ,
      (∫ β, g β ∂_root_.GD.N0225.N0539.d008058 α ((n : ℝ) + 1)) ≤
        ∫ β, ∑ i, c i * (β i *
          _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α) : False :=
  _root_.GD.N0101.N0408.d008172 α g _ hpositive hint hbound
    (_root_.GD.N0225.N0542.d008169 α c hα hsum)

end
end GD.N0101.N0408

#print axioms _root_.GD.N0101.N0408.d008170
#print axioms _root_.GD.N0101.N0408.d008171
#print axioms _root_.GD.N0101.N0408.d008172
#print axioms _root_.GD.N0101.N0408.d008173
