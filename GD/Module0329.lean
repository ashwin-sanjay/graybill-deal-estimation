import GD.Module0328





















namespace GD
namespace N0234
namespace N0737

noncomputable section

open Set
open _root_.GD.N0234.N0741
open _root_.GD.N0234.N0740

variable {Θ I n : Type*}
variable [TopologicalSpace Θ]
variable [Fintype n] [DecidableEq n]



def d004904
    (M : I → Θ → Matrix n n ℝ) (i : I) : Set Θ :=
  {θ | (M i θ).det ≠ 0}


theorem d004905
    (M : I → Θ → Matrix n n ℝ) (i : I)
    (hdet : Continuous (fun θ ↦ (M i θ).det)) :
    IsOpen (_root_.GD.N0234.N0737.d004904 M i) := by
  change IsOpen ((fun θ ↦ (M i θ).det) ⁻¹' ({0}ᶜ : Set ℝ))
  exact isOpen_compl_singleton.preimage hdet

omit [TopologicalSpace Θ] in


theorem d004906
    (K : Set Θ) (M : I → Θ → Matrix n n ℝ) :
    K ⊆ ⋃ i, _root_.GD.N0234.N0737.d004904 M i ↔
      ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0 := by
  constructor
  · intro hcover θ hθ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hθ)
    exact ⟨i, hi⟩
  · intro hpoint θ hθ
    obtain ⟨i, hi⟩ := hpoint θ hθ
    exact Set.mem_iUnion.mpr ⟨i, hi⟩





theorem d004907
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet : ∀ i, Continuous (fun θ ↦ (M i θ).det))
    (hcover : ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0) :
    ∃ u : Finset I, K ⊆ ⋃ i ∈ u, _root_.GD.N0234.N0737.d004904 M i := by
  apply hK.elim_finite_subcover (_root_.GD.N0234.N0737.d004904 M)
  · exact fun i ↦ _root_.GD.N0234.N0737.d004905 M i (hdet i)
  · exact (_root_.GD.N0234.N0737.d004906 K M).2 hcover




theorem d004908
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet : ∀ i, Continuous (fun θ ↦ (M i θ).det))
    (hcover : ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0) :
    ∃ u : Finset I,
      ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0 := by
  obtain ⟨u, hu⟩ :=
    _root_.GD.N0234.N0737.d004907 K hK M hdet hcover
  refine ⟨u, ?_⟩
  intro θ hθ
  obtain ⟨i, hiu, hiθ⟩ := Set.mem_iUnion₂.mp (hu hθ)
  exact ⟨i, hiu, hiθ⟩








theorem d004909
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet : ∀ i, Continuous (fun θ ↦ (M i θ).det)) :
    (∃ θ ∈ K, ∀ i, (M i θ).det = 0) ∨
      ∃ u : Finset I,
        ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0 := by
  classical
  by_cases hcover : ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0
  · exact Or.inr <|
      _root_.GD.N0234.N0737.d004908 K hK M hdet hcover
  · left
    push Not at hcover
    obtain ⟨θ, hθ, hall⟩ := hcover
    exact ⟨θ, hθ, hall⟩









theorem d004910
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet : ∀ i, Continuous (fun θ ↦ (M i θ).det)) :
    (∃ θ ∈ K, ∀ i, ∃ x : EuclideanSpace ℝ n,
        x ≠ 0 ∧ _root_.GD.N0234.N0741.d004813 (M i θ) x = 0) ∨
      ∃ u : Finset I,
        ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0 := by
  rcases
      _root_.GD.N0234.N0737.d004909
        K hK M hdet with hsingular | hatlas
  · left
    obtain ⟨θ, hθ, hall⟩ := hsingular
    refine ⟨θ, hθ, ?_⟩
    intro i
    exact
      (_root_.GD.N0234.N0741.d004823 (M i θ)).1
        (hall i)
  · exact Or.inr hatlas


def d004911
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (z : Θ × EuclideanSpace ℝ n) : ℝ :=
  ∑ i ∈ u, _root_.GD.N0234.N0741.d004813 (M i z.1) z.2

omit [DecidableEq n] in


theorem d004912
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (henergy :
      ∀ i ∈ u,
        Continuous (_root_.GD.N0234.N0740.d004897 (M i))) :
    Continuous (_root_.GD.N0234.N0737.d004911 M u) := by
  unfold _root_.GD.N0234.N0737.d004911
  exact continuous_finsetSum u fun i hi ↦ henergy i hi

omit [TopologicalSpace Θ] in

theorem d004913
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (θ : Θ) (x : EuclideanSpace ℝ n) :
    0 ≤ _root_.GD.N0234.N0737.d004911 M u (θ, x) := by
  unfold _root_.GD.N0234.N0737.d004911
  exact Finset.sum_nonneg fun i _ ↦
    _root_.GD.N0234.N0741.d004814 (M i θ) x

omit [TopologicalSpace Θ] in

theorem d004914
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (θ : Θ) (r : ℝ) (x : EuclideanSpace ℝ n) :
    _root_.GD.N0234.N0737.d004911 M u (θ, r • x) =
      r ^ 2 * _root_.GD.N0234.N0737.d004911 M u (θ, x) := by
  unfold _root_.GD.N0234.N0737.d004911
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact _root_.GD.N0234.N0741.d004815 (M i θ) r x

omit [TopologicalSpace Θ] in







theorem d004915
    (K : Set Θ)
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (hcover :
      ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0) :
    ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
      _root_.GD.N0234.N0737.d004911 M u (θ, x) = 0 → x = 0 := by
  intro θ hθ x hzero
  obtain ⟨i, hiu, hdet⟩ := hcover θ hθ
  have hall :
      ∀ j ∈ u, _root_.GD.N0234.N0741.d004813 (M j θ) x = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ u) ↦
          _root_.GD.N0234.N0741.d004814 (M j θ) x)).mp hzero
  exact
    (_root_.GD.N0234.N0740.d004898 (M i θ)).1
      hdet x (hall i hiu)











theorem d004916
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ) (u : Finset I)
    (henergy :
      ∀ i ∈ u,
        Continuous (_root_.GD.N0234.N0740.d004897 (M i)))
    (hcover :
      ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0737.d004911 M u (θ, x) := by
  exact
    _root_.GD.N0238.N0758.d004893
      K hK (_root_.GD.N0234.N0737.d004911 M u)
      (_root_.GD.N0234.N0737.d004912 M u henergy)
      (fun θ _ x ↦ _root_.GD.N0234.N0737.d004913 M u θ x)
      (fun θ _ r x ↦ _root_.GD.N0234.N0737.d004914 M u θ r x)
      (_root_.GD.N0234.N0737.d004915
        K M u hcover)










theorem d004917
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet_cont : ∀ i, Continuous (fun θ ↦ (M i θ).det))
    (henergy :
      ∀ i, Continuous (_root_.GD.N0234.N0740.d004897 (M i)))
    (hcover : ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0) :
    ∃ u : Finset I, ∃ δ : ℝ, 0 < δ ∧
      (∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0) ∧
      ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0737.d004911 M u (θ, x) := by
  obtain ⟨u, hu⟩ :=
    _root_.GD.N0234.N0737.d004908
      K hK M hdet_cont hcover
  obtain ⟨δ, hδ, hcoercive⟩ :=
    _root_.GD.N0234.N0737.d004916
      K hK M u (fun i _ ↦ henergy i) hu
  exact ⟨u, δ, hδ, hu, hcoercive⟩










theorem d004918
    (K : Set Θ) (hK : IsCompact K)
    (M : I → Θ → Matrix n n ℝ)
    (hdet_cont : ∀ i, Continuous (fun θ ↦ (M i θ).det))
    (henergy :
      ∀ i, Continuous (_root_.GD.N0234.N0740.d004897 (M i))) :
    (∃ θ ∈ K, ∀ i, (M i θ).det = 0) ∨
      ∃ u : Finset I, ∃ δ : ℝ, 0 < δ ∧
        (∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0) ∧
        ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0737.d004911 M u (θ, x) := by
  classical
  by_cases hcover : ∀ θ ∈ K, ∃ i, (M i θ).det ≠ 0
  · exact Or.inr <|
      _root_.GD.N0234.N0737.d004917
        K hK M hdet_cont henergy hcover
  · left
    push Not at hcover
    obtain ⟨θ, hθ, hall⟩ := hcover
    exact ⟨θ, hθ, hall⟩

omit [TopologicalSpace Θ] in




theorem d004919
    (K : Set Θ) (M : I → Θ → Matrix n n ℝ) :
    ¬ ((∃ θ ∈ K, ∀ i, (M i θ).det = 0) ∧
      ∃ u : Finset I,
        ∀ θ ∈ K, ∃ i ∈ u, (M i θ).det ≠ 0) := by
  rintro ⟨⟨θ, hθ, hsingular⟩, u, hcover⟩
  obtain ⟨i, hiu, hi⟩ := hcover θ hθ
  exact hi (hsingular i)












theorem d004920
    (K : Set Θ)
    (u : Finset I) (C : I → Set Θ)
    (hC : ∀ i ∈ u, IsCompact (C i))
    (hcover : K ⊆ ⋃ i ∈ u, C i)
    (M : I → Θ → Matrix n n ℝ)
    (henergy :
      ∀ i ∈ u,
        Continuous (_root_.GD.N0234.N0740.d004897 (M i)))
    (hdet :
      ∀ i ∈ u, ∀ θ ∈ C i, (M i θ).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θ ∈ K, ∃ i ∈ u, θ ∈ C i ∧
        ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M i θ) x := by
  classical
  by_cases hu : u.Nonempty
  · have hcell :
        ∀ i ∈ u, ∃ δ : ℝ, 0 < δ ∧
          ∀ θ ∈ C i, ∀ x : EuclideanSpace ℝ n,
            δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M i θ) x := by
      intro i hi
      exact
        (_root_.GD.N0234.N0740.d004900
          (C i) (hC i hi) (M i) (henergy i hi)).1
          (hdet i hi)
    let δ : I → ℝ :=
      fun i ↦ if hi : i ∈ u then Classical.choose (hcell i hi) else 1
    have hδ : ∀ i ∈ u, 0 < δ i := by
      intro i hi
      rw [show δ i = Classical.choose (hcell i hi) by simp [δ, hi]]
      exact (Classical.choose_spec (hcell i hi)).1
    have hcoercive :
        ∀ i ∈ u, ∀ θ ∈ C i, ∀ x : EuclideanSpace ℝ n,
          δ i * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M i θ) x := by
      intro i hi θ hθ x
      rw [show δ i = Classical.choose (hcell i hi) by simp [δ, hi]]
      exact (Classical.choose_spec (hcell i hi)).2 θ hθ x
    let δmin : ℝ := u.inf' hu δ
    have hδmin : 0 < δmin := by
      exact (Finset.lt_inf'_iff hu).2 fun i hi ↦ hδ i hi
    refine ⟨δmin, hδmin, ?_⟩
    intro θ hθ
    obtain ⟨i, hiu, hiC⟩ := Set.mem_iUnion₂.mp (hcover hθ)
    refine ⟨i, hiu, hiC, ?_⟩
    intro x
    calc
      δmin * ‖x‖ ^ 2 ≤ δ i * ‖x‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (Finset.inf'_le δ hiu) (sq_nonneg ‖x‖)
      _ ≤ _root_.GD.N0234.N0741.d004813 (M i θ) x :=
        hcoercive i hiu θ hiC x
  · have huempty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    refine ⟨1, zero_lt_one, ?_⟩
    intro θ hθ
    have : θ ∈ (∅ : Set Θ) := by
      simpa [huempty] using hcover hθ
    exact False.elim ((Set.mem_empty_iff_false θ).mp this)

end

end N0737
end N0234
end GD
