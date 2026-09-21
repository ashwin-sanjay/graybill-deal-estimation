import GD.Module0126







































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0603

noncomputable section

open _root_.GD.N0230.N0604
open _root_.GD.N0230.N0696
open _root_.GD.N0230.N0669

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}




theorem d001498 [Nonempty Θ] {S : Set H}
    (hS : Convex ℝ S) {ψ : Θ → H} {t x : H}
    (ht : _root_.GD.N0230.N0604.d001486 S ψ t) (hx : x ∈ S)
    (hdom : _root_.GD.N0230.N0604.d001484 ψ x t) : x = t := by
  by_cases hstrict : ∃ θ, ‖x - ψ θ‖ < ‖t - ψ θ‖
  · exact absurd ⟨hdom, hstrict⟩ (ht.2 x hx)
  · push Not at hstrict
    by_contra hne
    have heq : ∀ θ, ‖t - ψ θ‖ = ‖x - ψ θ‖ := fun θ ↦
      le_antisymm (hstrict θ) (hdom θ)
    have hmidS : (1 / 2 : ℝ) • (t + x) ∈ S := by
      have := hS ht.1 hx (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      rwa [← smul_add] at this
    exact ht.2 _ hmidS
      (_root_.GD.N0230.N0604.d001487 (Ne.symm hne) heq)




theorem d001499
    {S : Set H} (hSconv : Convex ℝ S)
    {ψ : Θ → H} {d₀ : H} {θref : Θ} {p : H}
    (hp : p ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀)
    (hmin : ∀ r ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀,
      ‖ψ θref - p‖ ≤ ‖ψ θref - r‖) :
    _root_.GD.N0230.N0604.d001486 S ψ p := by
  have hDconv : Convex ℝ (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀) :=
    hSconv.inter (_root_.GD.N0230.N0669.d001387 ψ d₀)
  refine ⟨hp.1, ?_⟩
  rintro d' hd'S ⟨hdom', θ', hstrict⟩
  have hd'D : d' ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀ :=
    ⟨hd'S, _root_.GD.N0230.N0696.d001494.mp
      (_root_.GD.N0230.N0696.d001493 hdom' hp.2)⟩
  have hd'min : ∀ r ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀,
      ‖ψ θref - d'‖ ≤ ‖ψ θref - r‖ := by
    intro r hr
    calc ‖ψ θref - d'‖ = ‖d' - ψ θref‖ := norm_sub_rev _ _
      _ ≤ ‖p - ψ θref‖ := hdom' θref
      _ = ‖ψ θref - p‖ := norm_sub_rev _ _
      _ ≤ ‖ψ θref - r‖ := hmin r hr
  have heq : p = d' :=
    _root_.GD.N0230.N0696.d001495 hDconv hp hd'D hmin hd'min
  rw [heq] at hstrict
  exact lt_irrefl _ hstrict




theorem d001500
    {D : Set H} (hD : Convex ℝ D)
    {T T' : H → H} {lam lam' : ℝ}
    (hlam : 0 < lam) (hlam' : 0 < lam')
    (hsim : ∀ x y : H, ‖T x - T y‖ = lam * ‖x - y‖)
    (hsim' : ∀ x y : H, ‖T' x - T' y‖ = lam' * ‖x - y‖)
    (hTD : ∀ x ∈ D, T x ∈ D) (hT'D : ∀ x ∈ D, T' x ∈ D)
    (hinv : ∀ x, T' (T x) = x)
    {a p : H} (hfixa : T a = a) (hp : p ∈ D)
    (hmin : ∀ r ∈ D, ‖a - p‖ ≤ ‖a - r‖) :
    T p = p := by
  have hinj : Function.Injective T' := by
    intro u v huv
    have h := hsim' u v
    rw [huv, sub_self, norm_zero] at h
    have h0 := (mul_eq_zero.mp h.symm).resolve_left hlam'.ne'
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hrT : ∀ r : H, T (T' r) = r := by
    intro r
    apply hinj
    exact hinv (T' r)
  have hTp : T p ∈ D := hTD p hp
  have hmin' : ∀ r ∈ D, ‖a - T p‖ ≤ ‖a - r‖ := by
    intro r hr
    calc ‖a - T p‖ = ‖T a - T p‖ := by rw [hfixa]
      _ = lam * ‖a - p‖ := hsim a p
      _ ≤ lam * ‖a - T' r‖ :=
          mul_le_mul_of_nonneg_left (hmin _ (hT'D r hr)) hlam.le
      _ = ‖T a - T (T' r)‖ := (hsim _ _).symm
      _ = ‖a - r‖ := by rw [hfixa, hrT]
  exact (_root_.GD.N0230.N0696.d001495 hD hp hTp hmin hmin').symm







theorem d001501 [CompleteSpace H]
    {S : Set H} (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    {ψ : Θ → H} {d₀ : H} (hd₀ : d₀ ∈ S) (θref : Θ)
    {G : Type*} {T T' : G → H → H} {lam lam' : G → ℝ}
    (hlam : ∀ g, 0 < lam g) (hlam' : ∀ g, 0 < lam' g)
    (hsim : ∀ g, ∀ x y : H, ‖T g x - T g y‖ = lam g * ‖x - y‖)
    (hsim' : ∀ g, ∀ x y : H, ‖T' g x - T' g y‖ = lam' g * ‖x - y‖)
    (hinv : ∀ g x, T' g (T g x) = x)
    (hfixref : ∀ g, T g (ψ θref) = ψ θref)
    (hDT : ∀ g, ∀ x ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀,
      T g x ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀)
    (hDT' : ∀ g, ∀ x ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀,
      T' g x ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀) :
    ∃ dstar ∈ S, _root_.GD.N0230.N0604.d001484 ψ dstar d₀ ∧ _root_.GD.N0230.N0604.d001486 S ψ dstar ∧
      ∀ g, T g dstar = dstar := by
  have hDconv : Convex ℝ (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀) :=
    hSconv.inter (_root_.GD.N0230.N0669.d001387 ψ d₀)
  have hDclosed : IsClosed (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀) :=
    hSclosed.inter
      (_root_.GD.N0230.N0575.d001454 ψ d₀)
  have hDne : (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀).Nonempty :=
    ⟨d₀, hd₀, _root_.GD.N0230.N0669.d001376 ψ d₀⟩
  obtain ⟨dstar, hdstarD, hdist⟩ :=
    exists_norm_eq_iInf_of_complete_convex hDne
      hDclosed.isComplete hDconv (ψ θref)
  have hmin : ∀ r ∈ S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀,
      ‖ψ θref - dstar‖ ≤ ‖ψ θref - r‖ := by
    intro r hr
    rw [hdist]
    haveI : Nonempty (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀ : Set H) := hDne.to_subtype
    have hbdd : BddBelow (Set.range
        fun w : (S ∩ _root_.GD.N0230.N0669.d001375 ψ d₀ : Set H) ↦ ‖ψ θref - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  refine ⟨dstar, hdstarD.1, hdstarD.2,
    _root_.GD.N0230.N0603.d001499 hSconv hdstarD hmin,
    fun g ↦ ?_⟩
  exact _root_.GD.N0230.N0603.d001500 hDconv (hlam g) (hlam' g)
    (hsim g) (hsim' g) (hDT g) (hDT' g) (hinv g) (hfixref g)
    hdstarD hmin

end

end N0603
end N0230
end GD

#print axioms _root_.GD.N0230.N0603.d001498
#print axioms _root_.GD.N0230.N0603.d001499
#print axioms _root_.GD.N0230.N0603.d001500
#print axioms _root_.GD.N0230.N0603.d001501
