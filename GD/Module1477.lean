import GD.Module0437
import GD.Module1474
import GD.Module1327
import GD.Module1325

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0405
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0351 _root_.GD.N0101.N0406
open _root_.GD.N0230.N0665

variable {k : ℕ}

theorem d023217 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (i j : Fin k) :
    Integrable (fun β => (β i)⁻¹ * β j) (_root_.GD.N0232.N0719.N0954.d009342 b r) := by
  letI (l : Fin k) := isProbabilityMeasure_gammaMeasure (zero_lt_one.trans (hb l)) (hr l)
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0954.d009342 b r) := by
    unfold _root_.GD.N0232.N0719.N0954.d009342
    infer_instance
  by_cases hij : i = j
  · subst j
    apply (integrable_const (1 : ℝ)).congr
    filter_upwards [_root_.GD.N0101.N0357.d023165 b r (fun l => zero_lt_one.trans (hb l)) hr]
      with β hβ
    exact (inv_mul_cancel₀ (hβ i).ne').symm
  · have hmap : MeasurePreserving (fun β : Fin k → ℝ => (β i, β j))
        (_root_.GD.N0232.N0719.N0954.d009342 b r) ((gammaMeasure (b i) (r i)).prod (gammaMeasure (b j) (r j))) :=
      ⟨by fun_prop, _root_.GD.N0105.d021633 _ i j hij⟩
    exact hmap.integrable_comp_of_integrable
      ((_root_.GD.N0232.N0719.N0876.d020682 (hb i) (hr i)).mul_prod
        (_root_.GD.N0232.N0719.N0960.d009683 (zero_lt_one.trans (hb j)) (hr j)))

theorem d023218 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (i j : Fin k) :
    (∫ β, (β i)⁻¹ * β j ∂_root_.GD.N0232.N0719.N0954.d009342 b r) =
      if i = j then 1 else (b j / (b i - 1)) * (r i / r j) := by
  letI (l : Fin k) := isProbabilityMeasure_gammaMeasure (zero_lt_one.trans (hb l)) (hr l)
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    calc
      _ = ∫ _β : Fin k → ℝ, (1 : ℝ) ∂_root_.GD.N0232.N0719.N0954.d009342 b r := by
        apply integral_congr_ae
        filter_upwards [_root_.GD.N0101.N0357.d023165 b r (fun l => zero_lt_one.trans (hb l)) hr]
          with β hβ
        exact inv_mul_cancel₀ (hβ i).ne'
      _ = 1 := by simp [_root_.GD.N0232.N0719.N0954.d009342]
  · rw [if_neg hij]
    have hm := integral_map
      (μ := _root_.GD.N0232.N0719.N0954.d009342 b r) (f := fun z : ℝ × ℝ => z.1⁻¹ * z.2)
      (show Measurable (fun β : Fin k → ℝ => (β i, β j)) by fun_prop).aemeasurable
      (show AEStronglyMeasurable (fun z : ℝ × ℝ => z.1⁻¹ * z.2)
        ((_root_.GD.N0232.N0719.N0954.d009342 b r).map (fun β => (β i, β j))) by fun_prop)
    rw [show (_root_.GD.N0232.N0719.N0954.d009342 b r).map (fun β => (β i, β j)) =
      (gammaMeasure (b i) (r i)).prod (gammaMeasure (b j) (r j)) from
        _root_.GD.N0105.d021633 _ i j hij] at hm
    rw [← hm, integral_prod_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x),
      _root_.GD.N0023.N0257.d021615 (hb i) (hr i),
      _root_.GD.N0023.N0257.d021616
        (zero_lt_one.trans (hb j)) (hr j)]
    ring

theorem d023219 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (i : Fin k) :
    Integrable (fun β => (∑ j, β j) * (β i)⁻¹) (_root_.GD.N0232.N0719.N0954.d009342 b r) := by
  have hi := integrable_finsetSum Finset.univ
    (fun j _ => _root_.GD.N0101.N0405.d023217 b r hb hr i j)
  apply hi.congr
  filter_upwards with β
  rw [← Finset.mul_sum, mul_comm]

theorem d023220 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (i : Fin k) :
    (∫ β, (∑ j, β j) * (β i)⁻¹ ∂_root_.GD.N0232.N0719.N0954.d009342 b r) =
      1 + ∑ j ∈ Finset.univ.erase i, (b j / (b i - 1)) * (r i / r j) := by
  simp_rw [Finset.sum_mul, mul_comm _ ((_)⁻¹)]
  rw [integral_finsetSum Finset.univ
    (fun j _ => _root_.GD.N0101.N0405.d023217 b r hb hr i j)]
  simp_rw [_root_.GD.N0101.N0405.d023218 b r hb hr i]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => if i = j then (1 : ℝ) else b j / (b i - 1) * (r i / r j)) (Finset.mem_univ i)]
  congr 1
  · exact if_pos rfl
  · apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1.symm]

def d023221 (v β : Fin k → ℝ) : ℝ := (∑ j, β j) * _root_.GD.N0101.N0351.d023186 β v

theorem d023222 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (v : Fin k → ℝ) :
    Integrable (_root_.GD.N0101.N0405.d023221 v) (_root_.GD.N0232.N0719.N0954.d009342 b r) := by
  have hi := integrable_finsetSum Finset.univ
    (fun i _ => (_root_.GD.N0101.N0405.d023219 b r hb hr i).const_mul (v i ^ 2))
  apply hi.congr
  filter_upwards with β
  unfold _root_.GD.N0101.N0405.d023221 _root_.GD.N0101.N0351.d023186
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d023223 (b r : Fin k → ℝ)
    (hb : ∀ i, 1 < b i) (hr : ∀ i, 0 < r i) (v : Fin k → ℝ) :
    (∫ β, _root_.GD.N0101.N0405.d023221 v β ∂_root_.GD.N0232.N0719.N0954.d009342 b r) =
      ∑ i, v i ^ 2 *
        (1 + ∑ j ∈ Finset.univ.erase i, (b j / (b i - 1)) * (r i / r j)) := by
  have heq : _root_.GD.N0101.N0405.d023221 v = fun β => ∑ i, v i ^ 2 * ((∑ j, β j) * (β i)⁻¹) := by
    funext β
    unfold _root_.GD.N0101.N0405.d023221 _root_.GD.N0101.N0351.d023186
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, integral_finsetSum Finset.univ
    (fun i _ => (_root_.GD.N0101.N0405.d023219 b r hb hr i).const_mul (v i ^ 2))]
  simp_rw [integral_const_mul, _root_.GD.N0101.N0405.d023220 b r hb hr]

def d023224 (a b : Fin k → ℝ) : ℝ :=
  1 + ∑ i, ∑ j ∈ Finset.univ.erase i, (b j / (b i - 1)) * max 1 (a i / a j)

theorem d023225 [NeZero k]
    (a b t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 1 < b i)
    (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    (∫ β, _root_.GD.N0101.N0405.d023221 (_root_.GD.N0230.N0665.d000407 t) β
      ∂_root_.GD.N0232.N0719.N0954.d009342 b (fun i => 1 + a i * t i)) ≤ _root_.GD.N0101.N0405.d023224 a b := by
  rw [_root_.GD.N0101.N0405.d023223 b _ hb
    (fun i => add_pos zero_lt_one (mul_pos (ha i) (ht i)))]
  exact _root_.GD.N0101.N0406.d006760 a b t ha hb ht

theorem d023226 [NeZero k]
    (a b t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 1 < b i)
    (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    (∫⁻ β, ENNReal.ofReal (_root_.GD.N0101.N0405.d023221 (_root_.GD.N0230.N0665.d000407 t) β)
      ∂_root_.GD.N0232.N0719.N0954.d009342 b (fun i => 1 + a i * t i)) ≤ ENNReal.ofReal (_root_.GD.N0101.N0405.d023224 a b) := by
  have hr (i : Fin k) : 0 < 1 + a i * t i := add_pos zero_lt_one (mul_pos (ha i) (ht i))
  rw [← ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0101.N0405.d023222 b _ hb hr _) ?_]
  · exact ENNReal.ofReal_le_ofReal (_root_.GD.N0101.N0405.d023225 a b t ha hb ht)
  · filter_upwards [_root_.GD.N0101.N0357.d023165 b _ (fun i => zero_lt_one.trans (hb i)) hr]
      with β hβ
    exact mul_nonneg (Finset.sum_nonneg fun j _ => (hβ j).le) (_root_.GD.N0101.N0351.d023192 hβ _)

end
end GD.N0101.N0405

#print axioms _root_.GD.N0101.N0405.d023217
#print axioms _root_.GD.N0101.N0405.d023218
#print axioms _root_.GD.N0101.N0405.d023223
#print axioms _root_.GD.N0101.N0405.d023225
#print axioms _root_.GD.N0101.N0405.d023226
