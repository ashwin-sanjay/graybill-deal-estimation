import GD.Module0664
import GD.Module0644














open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace GD.N0232.N0719.N0984

open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0928 _root_.GD.N0232.N0719.N0931

noncomputable section

variable {k : ℕ} [NeZero k]
variable {J : Type*} [Fintype J]

def d009738 (j : Fin k) : _root_.GD.N0232.N0719.N0983.d009709 k := by
  classical
  refine ⟨fun i => ⟨if i = j then 1 else 0, ?_⟩, ?_⟩
  · split_ifs <;> constructor <;> norm_num
  · simp

local instance : Nonempty (_root_.GD.N0232.N0719.N0983.d009709 k) := ⟨_root_.GD.N0232.N0719.N0984.d009738 0⟩

def d009739 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ) (j : J) : ℝ :=
  w j * _root_.GD.N0232.N0719.N0928.d009409 shape (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ))

omit [NeZero k] [Fintype J] in
theorem d009740 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) (j : J) :
    0 ≤ _root_.GD.N0232.N0719.N0984.d009739 shape p w j :=
  mul_nonneg (hw j) (_root_.GD.N0232.N0719.N0928.d009438 shape _ (hp j)).le

omit [NeZero k] [Fintype J] in
theorem d009741 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) {j : J} (hj : 0 < w j) :
    0 < _root_.GD.N0232.N0719.N0984.d009739 shape p w j :=
  mul_pos hj (_root_.GD.N0232.N0719.N0928.d009438 shape _ (hp j))

def d009742 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ) :
    FiniteMeasure (_root_.GD.N0232.N0719.N0983.d009709 k) :=
  ⟨∑ j, ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) • Measure.dirac (p j), by
    letI : ∀ j : J, IsFiniteMeasure
        (ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) • Measure.dirac (p j)) :=
      fun j => (Measure.dirac (p j)).smul_finite ENNReal.ofReal_ne_top
    infer_instance⟩

omit [NeZero k] in
theorem d009743 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) (hwpos : ∃ j, 0 < w j) :
    _root_.GD.N0232.N0719.N0984.d009742 shape p w ≠ 0 := by
  obtain ⟨j, hj⟩ := hwpos
  have hmass : 0 < (_root_.GD.N0232.N0719.N0984.d009742 shape p w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) univ := by
    change 0 < (∑ j, ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) • Measure.dirac (p j)) univ
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    have hbound : ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) ≤
        ∑ j, ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) := by
      exact Finset.single_le_sum
        (f := fun j => ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j))
        (fun _ _ => bot_le) (Finset.mem_univ j)
    exact (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0719.N0984.d009741 shape p w hp hj)).trans_le hbound
  intro hz
  simp [hz] at hmass

def d009744 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ) :
    ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k) := (_root_.GD.N0232.N0719.N0984.d009742 shape p w).normalize

omit [NeZero k] in
theorem d009745 (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ))
    (f : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ) :
    (∫ t, f t ∂(_root_.GD.N0232.N0719.N0984.d009742 shape p w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) =
      ∑ j, _root_.GD.N0232.N0719.N0984.d009739 shape p w j * f (p j) := by
  change (∫ t, f t ∂(∑ j, ENNReal.ofReal (_root_.GD.N0232.N0719.N0984.d009739 shape p w j) •
    Measure.dirac (p j))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0719.N0984.d009740 shape p w hw hp j), smul_eq_mul]
  · intro j hj
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d009746
    (shape : Fin k → ℝ) (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) (hwpos : ∃ j, 0 < w j)
    (q : ℝ) (y r : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0983.d009724 q y r (_root_.GD.N0232.N0719.N0984.d009744 shape p w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) =
      _root_.GD.N0232.N0719.N0983.d009724 q y r (_root_.GD.N0232.N0719.N0984.d009742 shape p w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  have hn := _root_.GD.N0232.N0719.N0984.d009743 shape p w hp hwpos
  have hm : ((_root_.GD.N0232.N0719.N0984.d009742 shape p w).mass)⁻¹ ≠ 0 :=
    inv_ne_zero ((_root_.GD.N0232.N0719.N0984.d009742 shape p w).mass_nonzero_iff.mpr hn)
  have hmreal : (↑((_root_.GD.N0232.N0719.N0984.d009742 shape p w).mass)⁻¹ : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold _root_.GD.N0232.N0719.N0984.d009744 _root_.GD.N0232.N0719.N0983.d009724 _root_.GD.N0232.N0719.N0983.d009723
  rw [(_root_.GD.N0232.N0719.N0984.d009742 shape p w).toMeasure_normalize_eq_of_nonzero hn,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ hmreal


def d009747 (shape : Fin k → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s)

omit [NeZero k] in
theorem d009748 (shape : Fin k → ℝ) (s : ℝ)
    (hs : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) : 0 < _root_.GD.N0232.N0719.N0984.d009747 shape s := by
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.Gamma_pos_of_pos hs)

omit [NeZero k] [Fintype J] in
theorem d009749 (shape : Fin k → ℝ) (s : ℝ)
    (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ) (y t : Fin k → ℝ) (j : J) :
    w j * _root_.GD.N0232.N0719.N0928.d009437 shape (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) y t s =
      _root_.GD.N0232.N0719.N0984.d009747 shape s * _root_.GD.N0232.N0719.N0984.d009739 shape p w j *
        _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun i => shape i * t i) (p j) := by
  unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0984.d009747 _root_.GD.N0232.N0719.N0984.d009739 _root_.GD.N0232.N0719.N0983.d009720
  rw [_root_.GD.N0232.N0719.N0983.d009719]
  ring


theorem d009750
    (shape : Fin k → ℝ) (s : ℝ) (hs : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (p : J → _root_.GD.N0232.N0719.N0983.d009709 k) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hp : ∀ j i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ))
    (hwpos : ∃ j, 0 < w j) (y t : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0931.d009454 shape s w (fun j i => (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) y t =
      _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun i => shape i * t i)
        (_root_.GD.N0232.N0719.N0984.d009744 shape p w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  rw [_root_.GD.N0232.N0719.N0984.d009746 shape p w hp hwpos]
  unfold _root_.GD.N0232.N0719.N0931.d009454 _root_.GD.N0232.N0719.N0931.d009453 _root_.GD.N0232.N0719.N0931.d009452 _root_.GD.N0232.N0719.N0983.d009724 _root_.GD.N0232.N0719.N0983.d009723
  rw [_root_.GD.N0232.N0719.N0984.d009745 shape p w hw hp, _root_.GD.N0232.N0719.N0984.d009745 shape p w hw hp]
  simp_rw [_root_.GD.N0232.N0719.N0984.d009749]
  have hN : (∑ j, _root_.GD.N0232.N0719.N0984.d009747 shape s * _root_.GD.N0232.N0719.N0984.d009739 shape p w j *
        _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun i => shape i * t i) (p j) *
        _root_.GD.N0232.N0719.N0928.d009405 (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i (p j) : ℝ)) y) =
      _root_.GD.N0232.N0719.N0984.d009747 shape s * ∑ j, _root_.GD.N0232.N0719.N0984.d009739 shape p w j *
        (_root_.GD.N0232.N0719.N0983.d009713 y (p j) * _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y
          (fun i => shape i * t i) (p j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change _ * ∑ i, _ = _ * (_ * ((∑ i, _) * _))
    ring
  have hD : (∑ j, _root_.GD.N0232.N0719.N0984.d009747 shape s * _root_.GD.N0232.N0719.N0984.d009739 shape p w j *
        _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun i => shape i * t i) (p j)) =
      _root_.GD.N0232.N0719.N0984.d009747 shape s * ∑ j, _root_.GD.N0232.N0719.N0984.d009739 shape p w j *
        _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun i => shape i * t i) (p j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hN, hD]
  exact mul_div_mul_left _ _ (_root_.GD.N0232.N0719.N0984.d009748 shape s hs).ne'

omit [NeZero k] in


theorem d009751 (sizes : Fin k → ℕ) (hn : ∀ i, 1 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0954.d009355 sizes) 2 =
      ((∑ i, (sizes i : ℝ)) + 1) / 2 := by
  unfold _root_.GD.N0232.N0719.N0928.d009415
  rw [_root_.GD.N0232.N0719.N0928.d009418 sizes hn]
  rw [← Finset.sum_div]
  ring



theorem d009752
    {X : Type*} [MeasurableSpace X] (rho : Measure X)
    (shape : Fin k → ℝ) (s : ℝ) (hs : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (n : ℕ → ℕ) (p : (j : ℕ) → Fin (n j) → _root_.GD.N0232.N0719.N0983.d009709 k)
    (w : (j : ℕ) → Fin (n j) → ℝ)
    (hw : ∀ j a, 0 ≤ w j a)
    (hp : ∀ j a i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i (p j a) : ℝ))
    (hwpos : ∀ j, ∃ a, 0 < w j a)
    (y t : X → Fin k → ℝ) (g : X → ℝ)
    (ht : ∀ᵐ x ∂rho, ∀ i, 0 < shape i * t x i)
    (hlim : ∀ᵐ x ∂rho, Tendsto
      (fun j => _root_.GD.N0232.N0719.N0931.d009454 shape s (w j)
        (fun a i => (_root_.GD.N0232.N0719.N0983.d009710 i (p j a) : ℝ)) (y x) (t x)) atTop (𝓝 (g x))) :
    ∃ nu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      g =ᵐ[rho] fun x => _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0232.N0719.N0928.d009415 shape s) (y x)
        (fun i => shape i * t x i) (nu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  apply _root_.GD.N0232.N0719.N0983.d009737 rho
    (_root_.GD.N0232.N0719.N0928.d009415 shape s) y (fun x i => shape i * t x i) g
    (fun j => _root_.GD.N0232.N0719.N0984.d009744 shape (p j) (w j)) ht
  filter_upwards [hlim] with x hx
  simpa only [_root_.GD.N0232.N0719.N0984.d009750 shape s hs _ _
    (hw _) (hp _) (hwpos _)] using hx

end

end GD.N0232.N0719.N0984

#print axioms _root_.GD.N0232.N0719.N0984.d009750
#print axioms _root_.GD.N0232.N0719.N0984.d009751
#print axioms _root_.GD.N0232.N0719.N0984.d009752
