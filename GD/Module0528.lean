import GD.Module0525

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0276

noncomputable section

open _root_.GD.N0024.N0277

variable {Ω : Type*} [MeasurableSpace Ω]

def d007902 : _root_.GD.N0024.N0277.d007878 := ⟨1 / 2, by constructor <;> norm_num⟩

theorem d007903
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsProbabilityMeasure (Q t)]
    (hQ : ∀ t, Q t ≪ Q _root_.GD.N0024.N0276.d007902)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (V : ℝ) (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q g t ≤ V) : 0 < V := by
  by_contra hnot
  have hV : V ≤ 0 := not_lt.mp hnot
  have hmid := hcap _root_.GD.N0024.N0276.d007902
  have hint : _root_.GD.N0024.N0277.d007881 (Q _root_.GD.N0024.N0276.d007902) g _root_.GD.N0024.N0276.d007902.val ≤ 0 := by
    have h := (div_le_iff₀ (_root_.GD.N0024.N0277.d007880 _root_.GD.N0024.N0276.d007902)).mp hmid
    exact h.trans (mul_nonpos_of_nonpos_of_nonneg hV (_root_.GD.N0024.N0277.d007880 _root_.GD.N0024.N0276.d007902).le)
  have hzero : (∫ z, (g z - _root_.GD.N0024.N0276.d007902.val) ^ 2 ∂Q _root_.GD.N0024.N0276.d007902) = 0 :=
    le_antisymm hint (integral_nonneg fun _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    (_root_.GD.N0024.N0277.d007887 (Q _root_.GD.N0024.N0276.d007902) g hg hb _root_.GD.N0024.N0276.d007902)).mp hzero
  have hfloor : ∀ᵐ z ∂Q _root_.GD.N0024.N0276.d007902, (1 / 2 : ℝ) ≤ g z := by
    filter_upwards [hae] with z hz
    have heq : g z - _root_.GD.N0024.N0276.d007902.val = 0 := sq_eq_zero_iff.mp hz
    change g z - 1 / 2 = 0 at heq
    linarith
  exact _root_.GD.N0024.N0277.d007893 Q (Q _root_.GD.N0024.N0276.d007902) hQ g hg hb
    (1 / 2) V (by norm_num) hcap hfloor

end
end GD.N0024.N0276

#print axioms _root_.GD.N0024.N0276.d007903
