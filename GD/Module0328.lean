import GD.Module0323
import GD.Module0327































namespace GD
namespace N0234
namespace N0740

noncomputable section

open scoped ENNReal

variable {Θ n : Type*}
variable [TopologicalSpace Θ]
variable [Fintype n] [DecidableEq n]

open _root_.GD.N0234.N0741



def d004897
    (M : Θ → Matrix n n ℝ) :
    Θ × EuclideanSpace ℝ n → ℝ :=
  fun z ↦ _root_.GD.N0234.N0741.d004813 (M z.1) z.2





theorem d004898
    (M : Matrix n n ℝ) :
    M.det ≠ 0 ↔
      ∀ x : EuclideanSpace ℝ n,
        _root_.GD.N0234.N0741.d004813 M x = 0 → x = 0 := by
  constructor
  · intro hdet x henergy
    by_contra hx
    exact hdet <|
      (_root_.GD.N0234.N0741.d004823 M).2
        ⟨x, hx, henergy⟩
  · intro hzero
    by_contra hdet
    obtain ⟨x, hx, henergy⟩ :=
      (_root_.GD.N0234.N0741.d004823 M).1
        hdet
    exact hx (hzero x henergy)





theorem d004899
    (K : Set Θ) (M : Θ → Matrix n n ℝ) :
    (∀ θ ∈ K, (M θ).det ≠ 0) ↔
      ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
        _root_.GD.N0234.N0741.d004813 (M θ) x = 0 → x = 0 := by
  constructor
  · intro hdet θ hθ
    exact
      (_root_.GD.N0234.N0740.d004898 (M θ)).1
        (hdet θ hθ)
  · intro hzero θ hθ
    exact
      (_root_.GD.N0234.N0740.d004898 (M θ)).2
        (hzero θ hθ)









theorem d004900
    (K : Set Θ) (hK : IsCompact K)
    (M : Θ → Matrix n n ℝ)
    (henergy : Continuous (_root_.GD.N0234.N0740.d004897 M)) :
    (∀ θ ∈ K, (M θ).det ≠ 0) ↔
      ∃ δ : ℝ, 0 < δ ∧
        ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M θ) x := by
  rw [_root_.GD.N0234.N0740.d004899]
  exact
    _root_.GD.N0238.N0758.d004895
        K hK (_root_.GD.N0234.N0740.d004897 M) henergy
        (fun θ hθ x ↦ _root_.GD.N0234.N0741.d004814 (M θ) x)
        (fun θ hθ r x ↦ _root_.GD.N0234.N0741.d004815 (M θ) r x)





theorem d004901
    (K : Set Θ) (M : Θ → Matrix n n ℝ) :
    (∃ θ ∈ K, (M θ).det = 0) ↔
      ∃ θ ∈ K, ∃ x : EuclideanSpace ℝ n,
        x ≠ 0 ∧ _root_.GD.N0234.N0741.d004813 (M θ) x = 0 := by
  constructor
  · rintro ⟨θ, hθ, hdet⟩
    obtain ⟨x, hx, henergy⟩ :=
      (_root_.GD.N0234.N0741.d004823 (M θ)).1 hdet
    exact ⟨θ, hθ, x, hx, henergy⟩
  · rintro ⟨θ, hθ, x, hx, henergy⟩
    exact
      ⟨θ, hθ,
        (_root_.GD.N0234.N0741.d004823 (M θ)).2
          ⟨x, hx, henergy⟩⟩








theorem d004902
    (K : Set Θ) (hK : IsCompact K)
    (M : Θ → Matrix n n ℝ)
    (henergy : Continuous (_root_.GD.N0234.N0740.d004897 M)) :
    (∃ θ ∈ K, ∃ x : EuclideanSpace ℝ n,
        (M θ).det = 0 ∧ x ≠ 0 ∧
          _root_.GD.N0234.N0741.d004813 (M θ) x = 0) ∨
      ∃ δ : ℝ, 0 < δ ∧
        ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M θ) x := by
  classical
  by_cases hdet : ∀ θ ∈ K, (M θ).det ≠ 0
  · exact Or.inr <|
      (_root_.GD.N0234.N0740.d004900
        K hK M henergy).1 hdet
  · left
    push Not at hdet
    obtain ⟨θ, hθ, hsingular⟩ := hdet
    obtain ⟨x, hx, henergy_zero⟩ :=
      (_root_.GD.N0234.N0741.d004823 (M θ)).1
        hsingular
    exact ⟨θ, hθ, x, hsingular, hx, henergy_zero⟩





theorem d004903
    (K : Set Θ) (hK : IsCompact K)
    (M : Θ → Matrix n n ℝ)
    (henergy : Continuous (_root_.GD.N0234.N0740.d004897 M)) :
    (∃ θ ∈ K, (M θ).det = 0) ∨
      ∃ δ : ℝ, 0 < δ ∧
        ∀ θ ∈ K, ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 (M θ) x := by
  rcases
      _root_.GD.N0234.N0740.d004902
        K hK M henergy with hsingular | hcoercive
  · exact Or.inl ⟨hsingular.choose, hsingular.choose_spec.1,
      hsingular.choose_spec.2.choose_spec.1⟩
  · exact Or.inr hcoercive

end

end N0740
end N0234
end GD
