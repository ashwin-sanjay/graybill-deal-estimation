import GD.Module0764
import GD.Module0809

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0039

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0851
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0896

noncomputable section

def d022623 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : ℝ :=
  (∑ σ : Equiv.Perm (Fin k),
    _root_.GD.N0232.N0719.N1013.d011537
      k (sizes ∘ σ) hk (fun i => hs (σ i)) (_root_.GD.N0232.N0719.N0851.d010783 sizes σ z)) /
    Fintype.card (Equiv.Perm (Fin k))

@[fun_prop] theorem d022624 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) : Measurable (_root_.GD.N0039.d022623 sizes hk hs) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro σ _
  exact (_root_.GD.N0232.N0719.N1013.d011538
    k (sizes ∘ σ) hk (fun i => hs (σ i))).comp (_root_.GD.N0232.N0719.N0851.d010783 sizes σ).measurable



theorem d022625 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) (τ : Equiv.Perm (Fin k))
    (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0039.d022623 (sizes ∘ τ) hk (fun i => hs (τ i)) (_root_.GD.N0232.N0719.N0851.d010783 sizes τ z) =
      _root_.GD.N0039.d022623 sizes hk hs z := by
  unfold _root_.GD.N0039.d022623
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ =>
    _root_.GD.N0232.N0719.N1013.d011537
      k (sizes ∘ σ) hk (fun i => hs (σ i)) (_root_.GD.N0232.N0719.N0851.d010783 sizes σ z))

theorem d022626 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0039.d022623 sizes hk hs =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hs := by
  have hall := ae_all_iff.mpr (fun σ =>
    _root_.GD.N0232.N0719.N0871.d011574 sizes σ hk hs θ)
  filter_upwards [hall] with z hz
  have hcard : (Fintype.card (Equiv.Perm (Fin k)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [_root_.GD.N0039.d022623, hz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem d022627 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) :
    Measurable (_root_.GD.N0039.d022623 sizes hk hs) ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes (_root_.GD.N0039.d022623 sizes hk hs) ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0039.d022623 sizes hk hs) := by
  let f := _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hs
  have hf := _root_.GD.N0232.N0719.N1013.d011547 k sizes hk hs
  have hae := _root_.GD.N0039.d022626 sizes hk hs
  have hr (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0039.d022623 sizes hk hs) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hae θ)
  refine ⟨_root_.GD.N0039.d022624 sizes hk hs, ?_, ?_⟩
  · intro θ
    rw [hr]
    exact hf.2.1 θ
  · intro e hem he θ
    exact (hf.2.2.1 e hem (fun η => by simpa only [hr η] using he η) θ).trans (hae θ).symm


def d022628 {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (hσ : sizes ∘ σ = sizes) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes :=
  hσ ▸ _root_.GD.N0232.N0719.N0851.d010783 sizes σ z

theorem d022629 {k : ℕ} (sizes sizes' : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) (hs' : ∀ i, 2 ≤ sizes' i) (h : sizes = sizes')
    (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0039.d022623 sizes' hk hs' (h ▸ z) = _root_.GD.N0039.d022623 sizes hk hs z := by
  subst sizes'
  rfl

theorem d022630 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) (σ : Equiv.Perm (Fin k)) (hσ : sizes ∘ σ = sizes)
    (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0039.d022623 sizes hk hs (_root_.GD.N0039.d022628 sizes σ hσ z) = _root_.GD.N0039.d022623 sizes hk hs z := by
  exact (_root_.GD.N0039.d022629 (sizes ∘ σ) sizes hk (fun i => hs (σ i)) hs hσ
    (_root_.GD.N0232.N0719.N0851.d010783 sizes σ z)).trans (_root_.GD.N0039.d022625 sizes hk hs σ z)



theorem d022631 {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hs : ∀ i, 2 ≤ sizes i) :
    ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ, Measurable f ∧
      (∀ σ hσ z, f (_root_.GD.N0039.d022628 sizes σ hσ z) = f z) ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes f := by
  have h := _root_.GD.N0039.d022627 sizes hk hs
  exact ⟨_root_.GD.N0039.d022623 sizes hk hs, h.1, _root_.GD.N0039.d022630 sizes hk hs, h.2⟩

end
end GD.N0039

#print axioms _root_.GD.N0039.d022625
#print axioms _root_.GD.N0039.d022626
#print axioms _root_.GD.N0039.d022627
#print axioms _root_.GD.N0039.d022630
#print axioms _root_.GD.N0039.d022631
