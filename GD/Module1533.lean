import GD.Module1425
import GD.Module1531
import GD.Module0724

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0069
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0051

variable {k : ℕ}

def d023850 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  θ.scale i ^ 2 / (sizes i : ℝ)

theorem d023851 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : 0 < _root_.GD.N0069.d023850 sizes θ i := by
  exact div_pos (sq_pos_of_pos (θ.scale_pos i))
    (Nat.cast_pos.mpr (by have := hn i; omega))

theorem d023852 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    Real.sqrt (_root_.GD.N0069.d023850 sizes θ i) = θ.scale i / Real.sqrt (sizes i : ℝ) := by
  rw [_root_.GD.N0069.d023850, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (θ.scale_pos i).le]



theorem d023853
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ).map (_root_.GD.N0069.d022759 sizes i j) =
      (_root_.GD.N0051.d023833 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j)).map
        (_root_.GD.N0051.d023834 θ.location (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812
  rw [(_root_.GD.N0069.d022761 sizes hn i j hij θ.location θ.scale).map_eq]
  unfold _root_.GD.N0232.N0719.N0933.d009288 _root_.GD.N0232.N0719.N0933.d009289
  rw [Measure.map_prod_map _ _ (_root_.GD.N0232.N0719.N0933.d009293 _ _ _) (_root_.GD.N0232.N0719.N0933.d009293 _ _ _),
    Measure.map_prod_map _ _ (_root_.GD.N0232.N0719.N0933.d009294 _ _) (_root_.GD.N0232.N0719.N0933.d009294 _ _),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  rcases u with ⟨⟨x, y⟩, ⟨s, t⟩⟩
  simp only [Prod.map_apply, _root_.GD.N0051.d023834, _root_.GD.N0069.d023852]
  rfl



def d023854 (sizes : Fin k → ℕ) (i j : Fin k) (f : _root_.GD.N0051.d023832 → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  f ∘ _root_.GD.N0069.d022759 sizes i j

theorem d023855 (sizes : Fin k → ℕ) (i j : Fin k)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f) :
    Measurable (_root_.GD.N0069.d023854 sizes i j f) := hf.comp (_root_.GD.N0069.d022760 sizes i j)



theorem d023856
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0069.d023854 sizes i j f) =
      ∫⁻ u, ENNReal.ofReal ((f (_root_.GD.N0051.d023834 θ.location
        (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j) u) - θ.location) ^ 2)
        ∂_root_.GD.N0051.d023833 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) := by
  have hl : Measurable (fun u : _root_.GD.N0051.d023832 => ENNReal.ofReal ((f u - θ.location) ^ 2)) := by
    fun_prop
  have hp : Measurable (_root_.GD.N0051.d023834 θ.location
      (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
    unfold _root_.GD.N0051.d023834
    fun_prop
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0069.d023854
  simp only [Function.comp_apply]
  rw [← lintegral_map hl (_root_.GD.N0069.d022760 sizes i j),
    _root_.GD.N0069.d023853 sizes hn i j hij θ, lintegral_map hl hp]



theorem d023857
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < _root_.GD.N0069.d022756 sizes i) (hpb : q / p < _root_.GD.N0069.d022756 sizes j) :
    Measurable (_root_.GD.N0069.d023854 sizes i j (_root_.GD.N0051.d023841 p q)) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0069.d023854 sizes i j (_root_.GD.N0051.d023841 p q)) ≤
        ENNReal.ofReal (_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) p q *
          min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
  have hf : Measurable (_root_.GD.N0051.d023841 p q) := _root_.GD.N0051.d022771 p q
  refine ⟨_root_.GD.N0069.d023855 sizes i j _ hf, ?_⟩
  intro θ
  rw [_root_.GD.N0069.d023856 sizes hn i j hij θ _ hf]
  have hb := _root_.GD.N0051.d023844 (m := θ.location)
    (_root_.GD.N0069.d022757 sizes hn i) (_root_.GD.N0069.d022757 sizes hn j) hp hq hqa hpb
    (_root_.GD.N0069.d023851 sizes hn θ i) (_root_.GD.N0069.d023851 sizes hn θ j)
  rw [← ofReal_integral_eq_lintegral_ofReal hb.1 (ae_of_all _ fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hb.2

end
end GD.N0069

#print axioms _root_.GD.N0069.d023853
#print axioms _root_.GD.N0069.d023855
#print axioms _root_.GD.N0069.d023856
#print axioms _root_.GD.N0069.d023857
