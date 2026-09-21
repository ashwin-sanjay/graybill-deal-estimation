import GD.Module1480
import GD.Module0353
import GD.Module1698

set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators

namespace GD.N0213.N0487
noncomputable section
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0517

variable {k : ℕ}




theorem d028587 (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a)
    (s : Finset (Fin k)) (hs : s.Nonempty) :
    (s.card : ℝ) - 1 < ∑ i ∈ s, a i ∧
      ∀ i, ((s.card : ℝ) - 1) * a i < ∑ j ∈ s, a j := by
  have hcardk : s.card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ s)
  have hk0 : 0 < k := lt_of_lt_of_le hs.card_pos hcardk
  letI : NeZero k := ⟨Nat.ne_of_gt hk0⟩
  have hshapes := _root_.GD.N0213.N0517.d023250 a ha hreg
  constructor
  · exact _root_.GD.N0104.d005222 a
      (_root_.GD.N0213.N0523.d023154 a) ha hshapes.1
      (fun i => (hshapes.2.1 i).le) hshapes.2.2 s hs
  · intro i
    by_cases hc1 : s.card = 1
    · rw [hc1]
      simp only [Nat.cast_one, sub_self, zero_mul]
      exact Finset.sum_pos (fun j _ => ha j) hs
    · have hc2 : 2 ≤ s.card := by have := hs.card_pos; omega
      have hcard : (0 : ℝ) < (s.card : ℝ) - 1 := by
        have hc2' : (2 : ℝ) ≤ s.card := by exact_mod_cast hc2
        linarith
      have hkm : (0 : ℝ) < (k : ℝ) - 1 := by
        have hk2 : 2 ≤ k := le_trans hc2 hcardk
        have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
      have hA : 0 < ∑ j, a j :=
        Finset.sum_pos (fun j _ => ha j) Finset.univ_nonempty
      have hρ : 0 < _root_.GD.N0213.N0523.d023154 a := div_pos hkm hA
      have hbound := _root_.GD.N0104.d005221
        (_root_.GD.N0213.N0523.d023155 a) (fun j => (hshapes.2.1 j).le) hshapes.2.2 s
      unfold _root_.GD.N0213.N0523.d023155 at hbound
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one, ← Finset.mul_sum] at hbound
      have hprod := mul_pos hcard (hshapes.2.1 i)
      unfold _root_.GD.N0213.N0523.d023155 at hprod
      apply (mul_lt_mul_iff_right₀ hρ).mp
      nlinarith only [hbound, hprod]



theorem d028588 {m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a)
    (f : Fin m → Fin k) (hf : Function.Injective f) :
    _root_.GD.N0213.N0517.d023248 (a ∘ f) := by
  let s : Finset (Fin k) := Finset.univ.image f
  have hs : s.Nonempty := by
    exact ⟨f ⟨0, hm⟩, Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩⟩
  have hcard : s.card = m := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) hf
  have hsum : (∑ j ∈ s, a j) = ∑ i, (a ∘ f) i := by
    exact Finset.sum_image (fun i _ j _ hij => hf hij)
  have h := _root_.GD.N0213.N0487.d028587 a ha hreg s hs
  rw [hcard, hsum] at h
  exact ⟨h.1, fun i => h.2 (f i)⟩



theorem d028589 {m : ℕ} (hm : 0 < m)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a)
    (f : Fin m → Fin k) (hf : Function.Injective f) :
    _root_.GD.N0213.N0523.d023154 (a ∘ f) < 1 ∧
      (∀ i, 0 < _root_.GD.N0213.N0523.d023155 (a ∘ f) i) ∧
      ∑ i, _root_.GD.N0213.N0523.d023155 (a ∘ f) i = 1 := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact _root_.GD.N0213.N0517.d023250 (a ∘ f) (fun i => ha (f i))
    (_root_.GD.N0213.N0487.d028588 hm a ha hreg f hf)

theorem d028590 {n m : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes)
    (f : Fin (m + 1) → Fin (n + 1)) (hf : Function.Injective f) :
    _root_.GD.N0213.N0485.d028566 (sizes ∘ f) := by
  apply _root_.GD.N0213.N0486.d028581 _ (fun i => hn (f i))
  apply (_root_.GD.N0213.N0486.d028579 _).mp
  exact _root_.GD.N0213.N0487.d028588 (Nat.succ_pos _)
    (_root_.GD.N0232.N0719.N0954.d009355 sizes)
    (_root_.GD.N0232.N0719.N0954.d009358 hn)
    ((_root_.GD.N0213.N0486.d028579 sizes).mpr hcone) f hf

end
end GD.N0213.N0487

#print axioms _root_.GD.N0213.N0487.d028587
#print axioms _root_.GD.N0213.N0487.d028588
#print axioms _root_.GD.N0213.N0487.d028589
#print axioms _root_.GD.N0213.N0487.d028590
