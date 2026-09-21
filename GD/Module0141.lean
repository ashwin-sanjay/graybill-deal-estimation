import GD.Module0137





















open scoped ENNReal

namespace GD
namespace N0230
namespace N0601

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0701
open _root_.GD.N0230.N0654
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0718

variable {G Theta D : Type*}



def d001578
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ENNReal)
    (tax : ℕ → D → D → ENNReal) : Prop :=
  ∀ i p q,
    objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q ≤
      (objective i p + objective i q) / 2


def d001579
    (tax : ℕ → D → D → ENNReal) : Prop :=
  ∀ p q, p ≠ q → ∃ i, 0 < tax i p q



theorem d001580 (a : ENNReal) :
    (a + a) / 2 = a := by
  rw [ENNReal.div_eq_inv_mul, ← two_mul]
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)



theorem d001581
    {a x t : ENNReal} (ha : a ≠ ⊤) (ht : 0 < t)
    (h : x + t ≤ (a + a) / 2) :
    x < a := by
  rw [_root_.GD.N0230.N0601.d001580] at h
  by_contra hxa
  have hax : a ≤ x := le_of_not_gt hxa
  have hat : a + t ≤ x + t := by
    simpa [add_comm] using add_le_add_right hax t
  have hale : a + t ≤ a := hat.trans h
  have halt : a < a + t := by
    simpa using (ENNReal.add_lt_add_iff_left ha).2 ht
  exact (not_lt_of_ge hale) halt




theorem d001582
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hdominated : _root_.GD.N0230.N0601.d001578 objective tax)
    (hcomplete : _root_.GD.N0230.N0601.d001579 tax)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (hpfinite : ∀ i, objective i p ≠ ⊤)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  obtain ⟨i, hitax⟩ := hcomplete p q hpq
  refine ⟨i, ?_⟩
  have hpNext : p ∈ face (i + 1) := hp (i + 1)
  have hqNext : q ∈ face (i + 1) := hq (i + 1)
  rw [htower.2 i] at hpNext hqNext
  have heq : objective i p = objective i q :=
    le_antisymm (hpNext.2 q (hq i)) (hqNext.2 p (hp i))
  have hmid := hdominated i p q
  rw [← heq] at hmid
  exact _root_.GD.N0230.N0601.d001581 (hpfinite i) hitax hmid




theorem d001583
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0601.d001578 objective tax) :
    ∀ i, _root_.GD.N0230.N0600.d001552 (face i) := by
  intro i
  induction i with
  | zero =>
      rw [htower.1]
      exact hCmidpoint
  | succ i ih =>
      rw [htower.2 i]
      intro p hp q hq
      refine ⟨ih p hp.1 q hq.1, ?_⟩
      intro e he
      have hpqeq : objective i p = objective i q :=
        le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
      calc
        objective i (_root_.GD.N0230.N0718.d001528 p q) ≤
            objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q :=
          self_le_add_right _ _
        _ ≤ (objective i p + objective i q) / 2 :=
          hdominated i p q
        _ = objective i p := by
          rw [hpqeq, _root_.GD.N0230.N0601.d001580]
        _ ≤ objective i e := hp.2 e he






theorem d001584
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (transform : (g : G) → (i : ℕ) →
      (Fin i → ENNReal) → ENNReal → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0601.d001578 objective tax)
    (hcomplete : _root_.GD.N0230.N0601.d001579 tax)
    (hfinite : ∀ p, (∀ i, p ∈ face i) → ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i) :=
    _root_.GD.N0230.N0601.d001583
      objective C face tax htower hCmidpoint hdominated
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp =>
        _root_.GD.N0230.N0601.d001582
          objective C face tax htower hdominated hcomplete hd hp
          (hfinite d hd) hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0654.d000879
    risk objective transform C p hhereditary hmono hC hcov hlex hfaithful


theorem d001585
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (transform : (g : G) → (i : ℕ) →
      (Fin i → ENNReal) → ENNReal → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0601.d001578 objective tax)
    (hcomplete : _root_.GD.N0230.N0601.d001579 tax)
    (hfinite : ∀ p, (∀ i, p ∈ face i) → ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact _root_.GD.N0230.N0601.d001584
    risk objective C face tax transform htower hCnonempty hcompact hlsc
    (_root_.GD.N0230.N0600.d001553 C hCconvex) hdominated hcomplete hfinite
    hhereditary hmono hC hcov

end N0601
end N0230
end GD

#print axioms _root_.GD.N0230.N0601.d001581
#print axioms _root_.GD.N0230.N0601.d001582
#print axioms _root_.GD.N0230.N0601.d001583
#print axioms _root_.GD.N0230.N0601.d001584
#print axioms _root_.GD.N0230.N0601.d001585
