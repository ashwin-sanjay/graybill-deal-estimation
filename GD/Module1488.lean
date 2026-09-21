import GD.Module1472
import GD.Module1484
import GD.Module0748
import GD.Module0800







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0399
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0101.N0357

variable {k : ℕ}

local instance d023323 : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := borel (_root_.GD.N0232.N0719.N0859.d010809 k)
local instance d023324 : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨rfl⟩

def d023325 (x : ℝ) : ℝ := if 0 < x then x else 1

theorem d023326 (x : ℝ) : 0 < _root_.GD.N0101.N0399.d023325 x := by
  unfold _root_.GD.N0101.N0399.d023325
  split_ifs with h
  · exact h
  · norm_num

theorem d023327 : Measurable _root_.GD.N0101.N0399.d023325 := by
  exact measurable_id.ite (measurableSet_lt measurable_const measurable_id) measurable_const

def d023328 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (β : Fin k → ℝ) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := fun i => Real.sqrt ((sizes i : ℝ) / _root_.GD.N0101.N0399.d023325 (β i))
  scale_pos := fun i => Real.sqrt_pos.mpr
    (div_pos (by exact_mod_cast hn i) (_root_.GD.N0101.N0399.d023326 _))

theorem d023329 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i) :
    Measurable (_root_.GD.N0101.N0399.d023328 sizes hn) := by
  let f : (Fin k → ℝ) → _root_.GD.N0232.N0719.N0859.d011204 k := fun β =>
    ⟨(0, (_root_.GD.N0101.N0399.d023328 sizes hn β).scale), (_root_.GD.N0101.N0399.d023328 sizes hn β).scale_pos⟩
  have hf : Measurable f := by
    apply Measurable.subtype_mk
    apply Measurable.prodMk measurable_const
    apply measurable_pi_lambda
    intro i
    exact (measurable_const.div
      (_root_.GD.N0101.N0399.d023327.comp (measurable_pi_apply i))).sqrt
  exact (_root_.GD.N0232.N0719.N0859.d011208 k).symm.measurable.comp hf

theorem d023330 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) (i : Fin k) :
    (_root_.GD.N0101.N0399.d023328 sizes hn β).scale i ^ 2 / (sizes i : ℝ) = (β i)⁻¹ := by
  have hni : 0 < (sizes i : ℝ) := by exact_mod_cast hn i
  change (Real.sqrt ((sizes i : ℝ) / _root_.GD.N0101.N0399.d023325 (β i))) ^ 2 /
    (sizes i : ℝ) = _
  rw [_root_.GD.N0101.N0399.d023325, if_pos (hβ i), Real.sq_sqrt (div_pos hni (hβ i)).le]
  field_simp [hni.ne', (hβ i).ne']

theorem d023331 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0232.N0719.N0954.d009357 sizes (_root_.GD.N0101.N0399.d023328 sizes hn β).scale =
      fun i => _root_.GD.N0232.N0719.N0954.d009355 sizes i * β i := by
  funext i
  unfold _root_.GD.N0232.N0719.N0954.d009357 _root_.GD.N0232.N0719.N0954.d009356
  rw [_root_.GD.N0101.N0399.d023330 sizes hn hβ i, div_inv_eq_mul]

theorem d023332 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0232.N0719.N0933.d009301 k sizes
      (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega) β).scale =
      _root_.GD.N0101.N0357.d023160 (_root_.GD.N0232.N0719.N0954.d009355 sizes) β := by
  rw [_root_.GD.N0232.N0719.N0954.d009362 sizes hn _
    (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega) β).scale_pos,
    _root_.GD.N0101.N0399.d023331 sizes _ hβ]
  rfl


theorem d023333 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
      (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega) β)
      (_root_.GD.N0072.d023291 sizes w) =
      ∫⁻ t, ENNReal.ofReal (∑ i, (β i)⁻¹ * (w t i) ^ 2)
        ∂_root_.GD.N0101.N0357.d023160 (_root_.GD.N0232.N0719.N0954.d009355 sizes) β := by
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0101.N0399.d023332 sizes hn hβ]
  congr 1
  funext t
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (w t i) ^ 2 * ((_root_.GD.N0101.N0399.d023328 sizes _ β).scale i ^ 2 / (sizes i : ℝ)) = _
  rw [_root_.GD.N0101.N0399.d023330 sizes _ hβ i, mul_comm]

theorem d023334 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0101.N0399.d023328 sizes hn β) =
      (∑ i, β i)⁻¹ := by
  unfold _root_.GD.N0232.N0719.N0963.d012141
    _root_.GD.N0232.N0719.N0838.d012097
    _root_.GD.N0232.N0719.N0838.d012096
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hni : 0 < (sizes i : ℝ) := by exact_mod_cast hn i
  change (sizes i : ℝ) / (Real.sqrt ((sizes i : ℝ) / _root_.GD.N0101.N0399.d023325 (β i))) ^ 2 = _
  rw [_root_.GD.N0101.N0399.d023325, if_pos (hβ i), Real.sq_sqrt (div_pos hni (hβ i)).le]
  field_simp [hni.ne', (hβ i).ne']

end
end GD.N0101.N0399

#print axioms _root_.GD.N0101.N0399.d023329
#print axioms _root_.GD.N0101.N0399.d023330
#print axioms _root_.GD.N0101.N0399.d023332
#print axioms _root_.GD.N0101.N0399.d023333
#print axioms _root_.GD.N0101.N0399.d023334
