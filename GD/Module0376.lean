import GD.Module0240
import GD.Module0370
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact




















noncomputable section

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open _root_.GD.N0229.N0550

namespace GD.N0106.N0428.N0765.N1622

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem d005770
    (f : E → ℝ) (hf : Continuous f)
    (hhom : ∀ (a : ℝ) x, f (a • x) = a ^ 2 * f x)
    (hpos : ∀ x, x ≠ 0 → 0 < f x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ f x := by
  have hzero : f 0 = 0 := by
    simpa using hhom 0 (0 : E)
  obtain ⟨κ, hκ, hbound⟩ :=
    (isCompact_sphere (0 : E) (1 : ℝ)).exists_forall_le'
      hf.continuousOn (a := (0 : ℝ)) (by
        intro x hx
        apply hpos x
        intro hxzero
        simpa [hxzero, Metric.mem_sphere] using hx)
  refine ⟨κ, hκ, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, hzero]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let u : E := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      exact inv_mul_cancel₀ hn.ne'
    have husphere : u ∈ Metric.sphere (0 : E) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hu
    have hscale : ‖x‖ • u = x := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc
      κ * ‖x‖ ^ 2 ≤ f u * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hbound u husphere) (sq_nonneg ‖x‖)
      _ = ‖x‖ ^ 2 * f u := mul_comm _ _
      _ = f (‖x‖ • u) := (hhom ‖x‖ u).symm
      _ = f x := congrArg f hscale

variable {ι : Type*} [Fintype ι] [Nonempty ι]



theorem d005771
    (w value : ι → ℝ) (hw : ∀ i, 0 < w i) (threshold : ℝ)
    (hbound : threshold * (∑ i, w i) ≤ ∑ i, w i * value i) :
    ∃ i, threshold ≤ value i := by
  classical
  by_contra h
  push Not at h
  have hlt : (∑ i, w i * value i) < ∑ i, w i * threshold := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (mul_lt_mul_of_pos_left (h i) (hw i)).le
    · let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (h i) (hw i)⟩
  have heq : (∑ i, w i * threshold) = threshold * ∑ i, w i := by
    rw [← Finset.sum_mul, mul_comm]
  rw [heq] at hlt
  exact (not_lt_of_ge hbound) hlt


def d005772 (w : ι → ℝ) (energy : ι → E → ℝ) (x : E) : ℝ :=
  ∑ i, w i * energy i x




theorem d005773
    (w : ι → ℝ) (energy : ι → E → ℝ)
    (hcont : ∀ i, Continuous (energy i))
    (hhom : ∀ i (a : ℝ) x, energy i (a • x) = a ^ 2 * energy i x)
    (hpos : ∀ x, x ≠ 0 → 0 < _root_.GD.N0106.N0428.N0765.N1622.d005772 w energy x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1622.d005772 w energy x := by
  apply _root_.GD.N0106.N0428.N0765.N1622.d005770 (_root_.GD.N0106.N0428.N0765.N1622.d005772 w energy)
  · unfold _root_.GD.N0106.N0428.N0765.N1622.d005772
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hcont i)
  · intro a x
    unfold _root_.GD.N0106.N0428.N0765.N1622.d005772
    simp_rw [hhom]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · exact hpos




theorem d005774
    (w : ι → ℝ) (charge energy : ι → E → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (hcont : ∀ i, Continuous (energy i))
    (hhom : ∀ i (a : ℝ) x, energy i (a • x) = a ^ 2 * energy i x)
    (hpos : ∀ x, x ≠ 0 → 0 < _root_.GD.N0106.N0428.N0765.N1622.d005772 w energy x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, ∃ i,
      κ * ‖x‖ ^ 2 ≤ 2 * charge i x + energy i x := by
  classical
  obtain ⟨κ₀, hκ₀, hbound⟩ :=
    _root_.GD.N0106.N0428.N0765.N1622.d005773 w energy hcont hhom hpos
  have hmass : 0 < ∑ i, w i := by
    apply Finset.sum_pos'
    · intro i _
      exact (hw i).le
    · exact ⟨Classical.choice (inferInstance : Nonempty ι), Finset.mem_univ _, hw _⟩
  refine ⟨κ₀ / (∑ i, w i), div_pos hκ₀ hmass, ?_⟩
  intro x
  apply _root_.GD.N0106.N0428.N0765.N1622.d005771 w
    (fun i => 2 * charge i x + energy i x) hw
  rw [_root_.GD.N0229.N0550.d003509 w charge energy hbalance x]
  have hcancel : (κ₀ / (∑ i, w i) * ‖x‖ ^ 2) * (∑ i, w i) = κ₀ * ‖x‖ ^ 2 := by
    calc
      _ = (κ₀ / (∑ i, w i) * (∑ i, w i)) * ‖x‖ ^ 2 := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hmass.ne']
  rw [hcancel]
  exact hbound x



theorem d005775
    (w : ι → ℝ) (charge energy : ι → E → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (hcont : ∀ i, Continuous (energy i))
    (hhom : ∀ i (a : ℝ) x, energy i (a • x) = a ^ 2 * energy i x)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (hstrict : ∀ i x, x ≠ 0 → 0 < energy i x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, ∃ i,
      κ * ‖x‖ ^ 2 ≤ 2 * charge i x + energy i x := by
  apply _root_.GD.N0106.N0428.N0765.N1622.d005774 w charge energy hw hbalance hcont hhom
  intro x hx
  unfold _root_.GD.N0106.N0428.N0765.N1622.d005772
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hw i).le (henergy i x)
  · exact ⟨Classical.choice (inferInstance : Nonempty ι), Finset.mem_univ _,
      mul_pos (hw _) (hstrict _ x hx)⟩



theorem d005776
    (w : ι → ℝ) (charge energy : ι → E → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (hcont : ∀ i, Continuous (energy i))
    (hhom : ∀ i (a : ℝ) x, energy i (a • x) = a ^ 2 * energy i x)
    (hpos : ∀ x, x ≠ 0 → 0 < _root_.GD.N0106.N0428.N0765.N1622.d005772 w energy x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (a : ℝ) x, ∃ i,
      κ * a ^ 2 * ‖x‖ ^ 2 ≤ 2 * charge i (a • x) + energy i (a • x) := by
  obtain ⟨κ, hκ, hbound⟩ :=
    _root_.GD.N0106.N0428.N0765.N1622.d005774 w charge energy hw hbalance hcont hhom hpos
  refine ⟨κ, hκ, ?_⟩
  intro a x
  obtain ⟨i, hi⟩ := hbound (a • x)
  refine ⟨i, ?_⟩
  have heq : κ * ‖a • x‖ ^ 2 = κ * a ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rwa [heq] at hi



theorem d005777
    (w : ι → ℝ) (charge energy : ι → E → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (hcont : ∀ i, Continuous (energy i))
    (hhom : ∀ i (a : ℝ) x, energy i (a • x) = a ^ 2 * energy i x)
    (hpos : ∀ x, x ≠ 0 → 0 < _root_.GD.N0106.N0428.N0765.N1622.d005772 w energy x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x, ‖x‖ = 1 → ∃ i,
      κ ≤ 2 * charge i x + energy i x := by
  obtain ⟨κ, hκ, hbound⟩ :=
    _root_.GD.N0106.N0428.N0765.N1622.d005774 w charge energy hw hbalance hcont hhom hpos
  refine ⟨κ, hκ, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hbound x
  exact ⟨i, by simpa [hx] using hi⟩

open _root_.GD.N0232.N0720.N1249
open _root_.GD.N0106.N0428.N0765.N1603
open _root_.GD.N0106.N0428.N0765.N1604







theorem d005778
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (energy : Sum (Fin 5) (Fin 5) → (Fin 5 → Fin 2 → ℝ) → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ∧
        _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r ≤ (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ))
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hcont : ∀ atom, Continuous (energy atom))
    (hhom : ∀ atom (a : ℝ) c, energy atom (a • c) = a ^ 2 * energy atom c)
    (henergy : ∀ atom c, 0 ≤ energy atom c)
    (hjoint : ∀ c, c ≠ 0 → ∃ atom, 0 < energy atom c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c, ∃ atom,
      κ * ‖c‖ ^ 2 ≤ 2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c := by
  obtain ⟨alpha, hpos, hoddOne, hoddThree⟩ :=
    _root_.GD.N0106.N0428.N0765.N1603.d005620 forward colScale hcol hbox
  have hw := _root_.GD.N0232.N0720.N1249.d002219 eta alpha heta hpos
  apply _root_.GD.N0106.N0428.N0765.N1622.d005774 (_root_.GD.N0232.N0720.N1249.d002217 eta alpha)
    (fun atom c => _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom) energy hw
    (fun c => _root_.GD.N0232.N0720.N1249.d002222 eta alpha forward reciprocal c
      hswap hoddOne hoddThree) hcont hhom
  intro c hc
  unfold _root_.GD.N0106.N0428.N0765.N1622.d005772
  apply Finset.sum_pos'
  · intro atom _
    exact mul_nonneg (hw atom).le (henergy atom c)
  · obtain ⟨atom, hatom⟩ := hjoint c hc
    exact ⟨atom, Finset.mem_univ _, mul_pos (hw atom) hatom⟩

end GD.N0106.N0428.N0765.N1622

#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005770
#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005774
#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005775
#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005776
#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005777
#print axioms _root_.GD.N0106.N0428.N0765.N1622.d005778
