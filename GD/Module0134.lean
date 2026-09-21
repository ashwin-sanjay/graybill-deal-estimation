import GD.Module0062
import GD.Module0133




















namespace GD
namespace N0230
namespace N0580

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0718

variable {G Theta D O : Type*}



theorem d001536
    [PartialOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    {p d : D}
    (hp : ∀ i, p ∈ face i)
    (hdC : d ∈ C)
    (heq : ∀ i, objective i d = objective i p) :
    ∀ i, d ∈ face i := by
  intro i
  induction i with
  | zero =>
      rw [htower.1]
      exact hdC
  | succ i ih =>
      rw [htower.2 i]
      refine ⟨ih, ?_⟩
      intro e he
      have hpSucc : p ∈ face (i + 1) := hp (i + 1)
      rw [htower.2 i] at hpSucc
      rw [heq i]
      exact hpSucc.2 e he



theorem d001537
    [PartialOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    {p : D}
    (hp : ∀ i, p ∈ face i)
    (hunique : ∀ d, (∀ i, d ∈ face i) → d = p) :
    _root_.GD.N0230.N0596.d000731 objective C p := by
  intro d hdC heq
  exact hunique d
    (_root_.GD.N0230.N0580.d001536 objective C face htower hp hdC heq)




theorem d001538
    [LinearOrder O]
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hconvex : ∀ i, Convex ℝ (face i))
    {p q : D}
    (hp : ∀ i, p ∈ face i)
    (hq : ∀ i, q ∈ face i)
    (hgap : p ≠ q → ∃ i,
      objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p) :
    p = q := by
  by_contra hpq
  obtain ⟨i, hstrict⟩ := hgap hpq
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ face i := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hconvex i (hp i) (hq i)
    · norm_num
    · norm_num
    · norm_num
  have hpSucc : p ∈ face (i + 1) := hp (i + 1)
  rw [htower.2 i] at hpSucc
  exact (not_lt_of_ge (hpSucc.2 _ hmid)) hstrict



theorem d001539
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [LinearOrder O]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hconvex : ∀ i, Convex ℝ (face i))
    (hcollective : ∀ p q,
      (∀ i, p ∈ face i) → (∀ i, q ∈ face i) → p ≠ q →
        ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0596.d000734 (G := G) objective) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0580.d001538
      objective C face htower hconvex hd hp
        (fun hdp ↦ hcollective d p hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0596.d000736
    risk objective C p hhereditary hmono hC hinvariant hlex hfaithful

end N0580
end N0230
end GD

#print axioms _root_.GD.N0230.N0580.d001536
#print axioms _root_.GD.N0230.N0580.d001537
#print axioms _root_.GD.N0230.N0580.d001538
#print axioms _root_.GD.N0230.N0580.d001539
