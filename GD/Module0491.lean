import GD.Module0489
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0038
noncomputable section

variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def d007554 (P : Measure Ω) (μ : ℝ) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((f z - μ) ^ 2) ∂P


theorem d007555 (hk : 2 ≤ k) (P : Measure Ω) (μ : ℝ)
    (e : Fin k → Fin k → Ω → ℝ) (he : ∀ i j, Measurable (e i j))
    (hsym : ∀ i j z, e i j z = e j i z) (i : Fin k) :
    _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤
      ∑ j ∈ Finset.univ.erase i, _root_.GD.N0038.d007554 P μ (e i j) := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (∑ j ∈ Finset.univ.erase i, (e i j z - μ) ^ 2) ∂P :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal
        (_root_.GD.N0038.d007545 hk _ (fun i j => hsym i j z) i μ)
    _ = ∑ j ∈ Finset.univ.erase i, _root_.GD.N0038.d007554 P μ (e i j) := by
      simp only [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact lintegral_finsetSum _ (fun j _ => by fun_prop)

def d007556 (hk : 2 ≤ k) (v : Fin k → ℝ) : ℝ :=
  Finset.univ.inf' (_root_.GD.N0038.d007536 hk) v


theorem d007557 (hk : 2 ≤ k) (P : Measure Ω) (μ : ℝ)
    (e : Fin k → Fin k → Ω → ℝ) (he : ∀ i j, Measurable (e i j))
    (hsym : ∀ i j z, e i j z = e j i z)
    (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i j, i ≠ j → _root_.GD.N0038.d007554 P μ (e i j) ≤ ENNReal.ofReal (C * min (v i) (v j))) :
    _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤
      ENNReal.ofReal (((k - 1 : ℕ) : ℝ) * C * _root_.GD.N0038.d007556 hk v) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (_root_.GD.N0038.d007536 hk) v
  change _root_.GD.N0038.d007556 hk v = v i at hi
  rw [hi]
  apply (_root_.GD.N0038.d007555 hk P μ e he hsym i).trans
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, ENNReal.ofReal (C * v i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hb i j (Ne.symm (Finset.mem_erase.mp hj).1)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hC))
    _ = ENNReal.ofReal (((k - 1 : ℕ) : ℝ) * C * v i) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg hC (hv i))]
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      ring


theorem d007558 (hk : 2 ≤ k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) :
    _root_.GD.N0038.d007556 hk v ≤ (k : ℝ) * (∑ i, (v i)⁻¹)⁻¹ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (_root_.GD.N0038.d007536 hk) v
  change _root_.GD.N0038.d007556 hk v = v i at hi
  have hm : 0 < _root_.GD.N0038.d007556 hk v := by rw [hi]; exact hv i
  have hle (j : Fin k) : _root_.GD.N0038.d007556 hk v ≤ v j := Finset.inf'_le v (Finset.mem_univ j)
  have hs : (∑ j, (v j)⁻¹) ≤ (k : ℝ) * (_root_.GD.N0038.d007556 hk v)⁻¹ := by
    calc
      _ ≤ ∑ _j : Fin k, (_root_.GD.N0038.d007556 hk v)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [one_div] using one_div_le_one_div_of_le hm (hle j)
      _ = _ := by simp
  have hpos : 0 < ∑ j, (v j)⁻¹ :=
    Finset.sum_pos (fun j _ => inv_pos.mpr (hv j)) (_root_.GD.N0038.d007536 hk)
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hpos).mpr
  calc
    _root_.GD.N0038.d007556 hk v * (∑ j, (v j)⁻¹) ≤
        _root_.GD.N0038.d007556 hk v * ((k : ℝ) * (_root_.GD.N0038.d007556 hk v)⁻¹) :=
      mul_le_mul_of_nonneg_left hs hm.le
    _ = (k : ℝ) := by field_simp


theorem d007559 (hk : 2 ≤ k) (P : Measure Ω) (μ : ℝ)
    (e : Fin k → Fin k → Ω → ℝ) (he : ∀ i j, Measurable (e i j))
    (hsym : ∀ i j z, e i j z = e j i z)
    (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i j, i ≠ j → _root_.GD.N0038.d007554 P μ (e i j) ≤ ENNReal.ofReal (C * min (v i) (v j))) :
    _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤
      ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C * (∑ i, (v i)⁻¹)⁻¹) := by
  apply (_root_.GD.N0038.d007557 hk P μ e he hsym v (fun i => (hv i).le) hC hb).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (_root_.GD.N0038.d007558 hk v hv)
    (show 0 ≤ ((k - 1 : ℕ) : ℝ) * C by positivity)
  nlinarith

end
end GD.N0038

#print axioms _root_.GD.N0038.d007555
#print axioms _root_.GD.N0038.d007557
#print axioms _root_.GD.N0038.d007558
#print axioms _root_.GD.N0038.d007559
