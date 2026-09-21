import GD.Module1392















set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0164
noncomputable section

section AtomicMeasure
variable {I X : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]


def d022426 (p : I → ℝ) (t : I → X) : Measure X :=
  Measure.sum fun i => ENNReal.ofReal (p i) • Measure.dirac (t i)

theorem d022427 (p : I → ℝ) (t : I → X) (f : X → ℝ) :
    Integrable f (_root_.GD.N0164.d022426 p t) := by
  classical
  rw [_root_.GD.N0164.d022426, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp : ‖f (t i)‖ₑ < ∞)).smul_measure
    ENNReal.ofReal_ne_top


theorem d022428 (p : I → ℝ) (t : I → X)
    (hp : ∀ i, 0 ≤ p i) (f : X → ℝ) :
    (∫ x, f x ∂_root_.GD.N0164.d022426 p t) = ∑ i, p i * f (t i) := by
  classical
  rw [_root_.GD.N0164.d022426, Measure.sum_fintype]
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp : ‖f (t i)‖ₑ < ∞)).smul_measure
      ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp i), smul_eq_mul]

theorem d022429 (p : I → ℝ) (t : I → X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (_root_.GD.N0164.d022426 p t) := by
  have h : HasSum p 1 := by simpa only [hsum] using hasSum_fintype p
  exact HasSum.isProbabilityMeasure_sum_dirac (d := t) hp h

end AtomicMeasure

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163
open _root_.GD.N0193 _root_.GD.N0177


def d022430 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then _root_.GD.N0180.d022173 ⟨t, ht⟩ g else 0

theorem d022431 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0164.d022430 g t = _root_.GD.N0180.d022173 t g := by
  simp only [_root_.GD.N0164.d022430, dif_pos t.property]


def d022432 {I : Type*} [Fintype I] (p : I → ℝ)
    (t : I → _root_.GD.N0232.N0720.N1441.d013676) : Measure ℝ :=
  _root_.GD.N0164.d022426 p (fun i => (t i : ℝ))

theorem d022433 {I : Type*} [Fintype I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : IsProbabilityMeasure (_root_.GD.N0164.d022432 p t) :=
  _root_.GD.N0164.d022429 p (fun i => (t i : ℝ)) hp hsum

theorem d022434 {I : Type*} [Fintype I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    Integrable (_root_.GD.N0164.d022430 g) (_root_.GD.N0164.d022432 p t) :=
  _root_.GD.N0164.d022427 p (fun i => (t i : ℝ)) (_root_.GD.N0164.d022430 g)

theorem d022435 {I : Type*} [Fintype I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 ≤ p i)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ r, _root_.GD.N0164.d022430 g r ∂_root_.GD.N0164.d022432 p t) = _root_.GD.N0163.d022185 p t g := by
  rw [_root_.GD.N0164.d022432, _root_.GD.N0164.d022428 p _ hp]
  simp only [_root_.GD.N0164.d022431, _root_.GD.N0163.d022185]

theorem d022436 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0193.d007351 N =
      _root_.GD.N0164.d022432 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) := by
  rfl


theorem d022437 {N : ℕ} (hN : 2 ≤ N) (f : ℝ → ℝ) :
    (∫ r, f r ∂_root_.GD.N0193.d007351 N) = ∑ i : _root_.GD.N0193.d007344 N, _root_.GD.N0193.d007348 N * f (_root_.GD.N0193.d007347 N i) :=
  _root_.GD.N0164.d022428 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0193.d007347 N)
    (fun _ => (_root_.GD.N0193.d007367 hN).le) f

theorem d022438 (N : ℕ) (f : ℝ → ℝ) :
    Integrable f (_root_.GD.N0193.d007351 N) :=
  _root_.GD.N0164.d022427 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0193.d007347 N) f

theorem d022439 {N : ℕ} (hN : 2 ≤ N)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ r, _root_.GD.N0164.d022430 g r ∂_root_.GD.N0193.d007351 N) =
      _root_.GD.N0163.d022185 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) g := by
  rw [_root_.GD.N0164.d022436 hN]
  exact _root_.GD.N0164.d022435 _ _ (fun _ => (_root_.GD.N0193.d007367 hN).le) g

end
end GD.N0164

#print axioms _root_.GD.N0164.d022427
#print axioms _root_.GD.N0164.d022428
#print axioms _root_.GD.N0164.d022429
#print axioms _root_.GD.N0164.d022431
#print axioms _root_.GD.N0164.d022433
#print axioms _root_.GD.N0164.d022434
#print axioms _root_.GD.N0164.d022435
#print axioms _root_.GD.N0164.d022436
#print axioms _root_.GD.N0164.d022437
#print axioms _root_.GD.N0164.d022438
#print axioms _root_.GD.N0164.d022439
