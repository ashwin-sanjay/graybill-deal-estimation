import GD.Module0125









































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0696

noncomputable section

open _root_.GD.N0230.N0604
open _root_.GD.N0230.N0669

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}


theorem d001492 (ψ : Θ → H) (d : H) : _root_.GD.N0230.N0604.d001484 ψ d d :=
  fun _ ↦ le_refl _


theorem d001493 {ψ : Θ → H} {a b c : H}
    (h₁ : _root_.GD.N0230.N0604.d001484 ψ a b) (h₂ : _root_.GD.N0230.N0604.d001484 ψ b c) :
    _root_.GD.N0230.N0604.d001484 ψ a c :=
  fun θ ↦ le_trans (h₁ θ) (h₂ θ)



theorem d001494 {ψ : Θ → H} {d₀ d : H} :
    _root_.GD.N0230.N0604.d001484 ψ d d₀ ↔ d ∈ _root_.GD.N0230.N0669.d001375 ψ d₀ :=
  Iff.rfl




theorem d001495 {D : Set H} (hD : Convex ℝ D)
    {a p q : H} (hp : p ∈ D) (hq : q ∈ D)
    (hpmin : ∀ r ∈ D, ‖a - p‖ ≤ ‖a - r‖)
    (hqmin : ∀ r ∈ D, ‖a - q‖ ≤ ‖a - r‖) :
    p = q := by
  have h := _root_.GD.N0230.N0661.d001475
    (a := a) (b := a) hD hp hq hpmin hqmin
  rw [sub_self, inner_zero_right] at h
  have hz : ‖q - p‖ ^ 2 = 0 :=
    le_antisymm h (by positivity)
  have : q - p = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm h (by positivity) : ‖q - p‖ ^ 2 = 0)
    exact norm_eq_zero.mp this
  exact (sub_eq_zero.mp this).symm





theorem d001496 [CompleteSpace H]
    {S : Set H} (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    {ψ : Θ → H} {d₀ : H} (hd₀ : d₀ ∈ S) (θref : Θ) :
    ∃ dstar ∈ S, _root_.GD.N0230.N0604.d001484 ψ dstar d₀ ∧ _root_.GD.N0230.N0604.d001486 S ψ dstar := by

  set D : Set H := S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀ with hD
  have hDconv : Convex ℝ D := hSconv.inter (_root_.GD.N0230.N0669.d001387 ψ d₀)
  have hDclosed : IsClosed D :=
    hSclosed.inter
      (_root_.GD.N0230.N0575.d001454 ψ d₀)
  have hDne : D.Nonempty := ⟨d₀, hd₀, _root_.GD.N0230.N0669.d001376 ψ d₀⟩

  obtain ⟨dstar, hdstarD, hdist⟩ :=
    exists_norm_eq_iInf_of_complete_convex hDne
      hDclosed.isComplete hDconv (ψ θref)
  have hmin : ∀ r ∈ D, ‖ψ θref - dstar‖ ≤ ‖ψ θref - r‖ := by
    intro r hr
    rw [hdist]
    haveI : Nonempty D := hDne.to_subtype
    have hbdd : BddBelow (Set.range fun w : D ↦ ‖ψ θref - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  refine ⟨dstar, hdstarD.1, hdstarD.2, hdstarD.1, ?_⟩

  rintro d' hd'S ⟨hdom', θ', hstrict⟩
  have hd'D : d' ∈ D :=
    ⟨hd'S, (_root_.GD.N0230.N0696.d001494).mp
      (_root_.GD.N0230.N0696.d001493 hdom' hdstarD.2)⟩
  have hd'min : ∀ r ∈ D, ‖ψ θref - d'‖ ≤ ‖ψ θref - r‖ := by
    intro r hr
    calc ‖ψ θref - d'‖ = ‖d' - ψ θref‖ := norm_sub_rev _ _
      _ ≤ ‖dstar - ψ θref‖ := hdom' θref
      _ = ‖ψ θref - dstar‖ := norm_sub_rev _ _
      _ ≤ ‖ψ θref - r‖ := hmin r hr
  have heq : dstar = d' :=
    _root_.GD.N0230.N0696.d001495 hDconv hdstarD hd'D hmin hd'min
  rw [heq] at hstrict
  exact lt_irrefl _ hstrict





theorem d001497 [CompleteSpace H]
    {S : Set H} (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    {ψ : Θ → H} {d₀ m : H} (hd₀ : d₀ ∈ S)
    (hstrict : ∀ θ, ‖d₀ - ψ θ‖ < ‖m - ψ θ‖) (θref : Θ) :
    ∃ dstar ∈ S, (∀ θ, ‖dstar - ψ θ‖ < ‖m - ψ θ‖) ∧
      _root_.GD.N0230.N0604.d001486 S ψ dstar := by
  obtain ⟨dstar, hmem, hdom, hterm⟩ :=
    _root_.GD.N0230.N0696.d001496 hSconv hSclosed hd₀ θref
  exact ⟨dstar, hmem,
    fun θ ↦ lt_of_le_of_lt (hdom θ) (hstrict θ), hterm⟩

end

end N0696
end N0230
end GD

#print axioms _root_.GD.N0230.N0696.d001495
#print axioms _root_.GD.N0230.N0696.d001496
#print axioms _root_.GD.N0230.N0696.d001497
