import GD.Module1694
import GD.Module1677

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0083
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0089 _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0102.N0422

variable {k : ℕ}

def d028551 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := fun i => Real.sqrt ((sizes i : ℝ) * v i)
  scale_pos := fun i => Real.sqrt_pos.2
    (mul_pos (by exact_mod_cast hn i) (hv i))

theorem d028552 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) (i : Fin k) :
    (_root_.GD.N0083.d028551 sizes hn v hv).scale i ^ 2 / (sizes i : ℝ) = v i := by
  have hni : 0 < (sizes i : ℝ) := by exact_mod_cast hn i
  rw [_root_.GD.N0083.d028551, Real.sq_sqrt (mul_pos hni (hv i)).le]
  field_simp [hni.ne']

theorem d028553 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0083.d028551 sizes hn v hv) = _root_.GD.N0089.d028298 v := by
  unfold _root_.GD.N0232.N0719.N0963.d012141 _root_.GD.N0232.N0719.N0838.d012097
    _root_.GD.N0232.N0719.N0838.d012096 _root_.GD.N0089.d028298 _root_.GD.N0102.N0422.d028281
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hni : 0 < (sizes i : ℝ) := by exact_mod_cast hn i
  change (sizes i : ℝ) / (Real.sqrt ((sizes i : ℝ) * v i)) ^ 2 = (v i)⁻¹
  rw [Real.sq_sqrt (mul_pos hni (hv i)).le]
  field_simp [hni.ne', (hv i).ne']

theorem d028554
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (v : Fin k → ℝ) (hv : ∀ i, 0 < v i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ x, ∑ i, w x i = 1) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
      (_root_.GD.N0083.d028551 sizes (fun i => by have := hn i; omega) v hv)
      (_root_.GD.N0072.d023291 sizes w) = _root_.GD.N0083.d028538 (_root_.GD.N0232.N0719.N0954.d009355 sizes) v w := by
  let hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0232.N0719.N0954.d009362 sizes hn _
      (_root_.GD.N0083.d028551 sizes hn0 v hv).scale_pos]
  have hV : (fun i => (_root_.GD.N0083.d028551 sizes hn0 v hv).scale i ^ 2 / (sizes i : ℝ)) = v := by
    funext i
    exact _root_.GD.N0083.d028552 sizes hn0 v hv i
  have hR : _root_.GD.N0232.N0719.N0954.d009357 sizes (_root_.GD.N0083.d028551 sizes hn0 v hv).scale =
      (fun i => _root_.GD.N0232.N0719.N0954.d009355 sizes i / v i) := by
    funext i
    unfold _root_.GD.N0232.N0719.N0954.d009357 _root_.GD.N0232.N0719.N0954.d009356
    rw [_root_.GD.N0083.d028552]
  rw [hV, hR]
  rfl



theorem d028555
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i : Fin k) (hi : sizes i = 2)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ x, ∑ j, w x j = 1) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ)) := by
  intro hcap
  apply _root_.GD.N0083.d028550 hk (_root_.GD.N0232.N0719.N0954.d009358 hn) i
    (by norm_num [_root_.GD.N0232.N0719.N0954.d009355, hi]) w hw hunit C hC
  intro v hv
  let hn0 : ∀ j, 0 < sizes j := fun j => by have := hn j; omega
  have hh := hcap (_root_.GD.N0083.d028551 sizes hn0 v hv)
  rw [_root_.GD.N0083.d028554 sizes hn v hv w hw hunit,
    _root_.GD.N0083.d028553 sizes hn0 v hv] at hh
  exact hh

theorem d028556
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i : Fin k) (hi : sizes i = 2)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ x, ∑ j, w x j = 1) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0072.d023291 sizes w) = ⊤ := by
  by_contra hfinite
  let C := (_root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0072.d023291 sizes w)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  apply _root_.GD.N0083.d028555 hk sizes hn i hi w hw hunit C hC
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
    (fun j => by have := hn j; omega) C hC θ (_root_.GD.N0072.d023291 sizes w)).mp
  rw [show ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0072.d023291 sizes w) from
    ENNReal.ofReal_toReal hfinite]
  exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ (_root_.GD.N0072.d023291 sizes w)) θ



theorem d028557
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ x, ∑ j, w x j = 1) ∧
        _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0072.d023291 sizes w) ≠ ⊤) ↔
      ∀ i, 3 ≤ sizes i := by
  constructor
  · rintro ⟨w, hw, hunit, hfinite⟩ i
    by_contra hi
    have htwo : sizes i = 2 := by have := hn i; omega
    exact hfinite (_root_.GD.N0083.d028556 hk sizes hn i htwo w hw hunit)
  · intro hn3
    refine ⟨_root_.GD.N0021.d023313, _root_.GD.N0021.d023314, ?_, ?_⟩
    · intro x
      exact _root_.GD.N0232.N0719.N0900.d009131 (by omega) (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), x))
    · rw [← _root_.GD.N0021.d023315]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (_root_.GD.N0070.d028368 (by omega) sizes hn3)

end
end GD.N0083

#print axioms _root_.GD.N0083.d028554
#print axioms _root_.GD.N0083.d028555
#print axioms _root_.GD.N0083.d028556
#print axioms _root_.GD.N0083.d028557
