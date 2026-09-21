import GD.Module1440
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0068
noncomputable section

open _root_.GD.N0232.N0719

variable {k : ℕ}

def d023020 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i j : Fin k) :
    _root_.GD.N0232.N0720.N1080.d014168 where
  location := θ.location
  scale₁ := θ.scale i
  scale₂ := θ.scale j
  scale₁_pos := θ.scale_pos i
  scale₂_pos := θ.scale_pos j

def d023021 (sizes : Fin k → ℕ) (i j : Fin k)
    (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) :=
  (ω i, ω j)

theorem d023022 (sizes : Fin k → ℕ) (i j : Fin k) :
    Measurable (_root_.GD.N0068.d023021 sizes i j) := by unfold _root_.GD.N0068.d023021; fun_prop


theorem d023023 (sizes : Fin k → ℕ)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i j : Fin k) (hij : i ≠ j) :
    MeasurePreserving (_root_.GD.N0068.d023021 sizes i j) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
      (_root_.GD.N0232.N0720.N1080.d014171 (sizes i) (sizes j) (_root_.GD.N0068.d023020 θ i j)) := by
  let μ := fun l => _root_.GD.N0232.N0719.d009174 (sizes l) θ.location (θ.scale l)
  have hind := (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hh := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq] at hh
  refine ⟨_root_.GD.N0068.d023022 sizes i j, ?_⟩
  change Measure.map (fun ω => (ω i, ω j)) (Measure.pi μ) = _
  rw [hh]
  unfold _root_.GD.N0232.N0720.N1080.d014171
  rw [_root_.GD.N0232.N0720.d009061]
  rfl

def d023024 (sizes : Fin k → ℕ) (i j : Fin k)
    (d : _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ := d ∘ _root_.GD.N0068.d023021 sizes i j

theorem d023025 (sizes : Fin k → ℕ) (i j : Fin k)
    (d : _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : Measurable d) : Measurable (_root_.GD.N0068.d023024 sizes i j d) :=
  hd.comp (_root_.GD.N0068.d023022 sizes i j)


theorem d023026 (sizes : Fin k → ℕ) (i j : Fin k) (hij : i ≠ j)
    (d : _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : Measurable d) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0068.d023024 sizes i j d) =
      _root_.GD.N0232.N0720.N1080.d014197 (sizes i) (sizes j)
        (_root_.GD.N0068.d023020 θ i j) d := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
    _root_.GD.N0232.N0720.N1080.d014197
  rw [← (_root_.GD.N0068.d023023 sizes θ i j hij).map_eq]
  exact (lintegral_map (show Measurable (fun x => ENNReal.ofReal ((d x - θ.location) ^ 2)) by fun_prop)
    (_root_.GD.N0068.d023022 sizes i j)).symm

def d023027 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  θ.scale i ^ 2 / (sizes i : ℝ)

theorem d023028 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : 0 < _root_.GD.N0068.d023027 sizes θ i :=
  div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (by have := hn i; omega))

theorem d023029 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i j : Fin k) :
    _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes j) (_root_.GD.N0068.d023020 θ i j) ≤
      min (_root_.GD.N0068.d023027 sizes θ i) (_root_.GD.N0068.d023027 sizes θ j) := by
  have hi : 0 < (sizes i : ℝ) / θ.scale i ^ 2 :=
    div_pos (Nat.cast_pos.mpr (by have := hn i; omega)) (sq_pos_of_pos (θ.scale_pos i))
  have hj : 0 < (sizes j : ℝ) / θ.scale j ^ 2 :=
    div_pos (Nat.cast_pos.mpr (by have := hn j; omega)) (sq_pos_of_pos (θ.scale_pos j))
  apply le_min
  · simpa only [_root_.GD.N0232.N0720.N1257.d015508,
      _root_.GD.N0068.d023020, _root_.GD.N0068.d023027, one_div, inv_div] using
      one_div_le_one_div_of_le hi (le_add_of_nonneg_right hj.le)
  · simpa only [_root_.GD.N0232.N0720.N1257.d015508,
      _root_.GD.N0068.d023020, _root_.GD.N0068.d023027, one_div, inv_div] using
      one_div_le_one_div_of_le hj (le_add_of_nonneg_left hi.le)

theorem d023030 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes θ = (∑ i, (_root_.GD.N0068.d023027 sizes θ i)⁻¹)⁻¹ := by
  simp only [_root_.GD.N0232.N0719.N0963.d012141,
    _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, _root_.GD.N0068.d023027, inv_div]

end
end GD.N0068

#print axioms _root_.GD.N0068.d023023
#print axioms _root_.GD.N0068.d023026
#print axioms _root_.GD.N0068.d023029
