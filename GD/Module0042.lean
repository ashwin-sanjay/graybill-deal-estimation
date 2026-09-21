import GD.Module0041





















namespace GD
namespace N0230
namespace N0558

open RealInnerProductSpace
open _root_.GD.N0230.N0685

set_option maxHeartbeats 50000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def d000527 (p q : E) : E := q - p


def d000528 (p q : E) : ℝ := ‖q‖ ^ 2 - ‖p‖ ^ 2


theorem d000529 (p q : E) :
    _root_.GD.N0230.N0558.d000528 p q =
      ‖_root_.GD.N0230.N0558.d000527 p q‖ ^ 2 + 2 * ⟪p, _root_.GD.N0230.N0558.d000527 p q⟫ := by
  unfold _root_.GD.N0230.N0558.d000528 _root_.GD.N0230.N0558.d000527
  calc
    ‖q‖ ^ 2 - ‖p‖ ^ 2 = ‖p + (q - p)‖ ^ 2 - ‖p‖ ^ 2 := by
      rw [show p + (q - p) = q by abel]
    _ = ‖q - p‖ ^ 2 + 2 * ⟪p, q - p⟫ := by
      rw [norm_add_sq_real]
      ring



theorem d000530 {K : Set E} {p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K 0 p) (hq : q ∈ K) :
    0 ≤ ⟪p, _root_.GD.N0230.N0558.d000527 p q⟫ := by
  have h := hp.2 q hq
  unfold _root_.GD.N0230.N0558.d000527
  simp only [zero_sub, inner_neg_left] at h
  linarith



theorem d000531 {p q : E}
    (htax : ‖q - p‖ ^ 2 ≤ ‖q‖ ^ 2 - ‖p‖ ^ 2) :
    0 ≤ ⟪p, _root_.GD.N0230.N0558.d000527 p q⟫ := by
  change ‖_root_.GD.N0230.N0558.d000527 p q‖ ^ 2 ≤ _root_.GD.N0230.N0558.d000528 p q at htax
  rw [_root_.GD.N0230.N0558.d000529] at htax
  linarith



theorem d000532 {K : Set E} {p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K 0 p) (hq : q ∈ K) :
    ‖_root_.GD.N0230.N0558.d000527 p q‖ ^ 2 ≤ _root_.GD.N0230.N0558.d000528 p q := by
  rw [_root_.GD.N0230.N0558.d000529]
  nlinarith [_root_.GD.N0230.N0558.d000530 hp hq]


theorem d000533 {K : Set E} {p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K 0 p) (hq : q ∈ K) :
    0 ≤ _root_.GD.N0230.N0558.d000528 p q := by
  exact le_trans (sq_nonneg _) (_root_.GD.N0230.N0558.d000532 hp hq)



theorem d000534 {K : Set E} {p q : E}
    (hp : _root_.GD.N0230.N0685.d000511 K 0 p) (hq : q ∈ K) :
    _root_.GD.N0230.N0558.d000528 p q = 0 ↔ q = p := by
  constructor
  · intro hzero
    have henergy : ‖_root_.GD.N0230.N0558.d000527 p q‖ ^ 2 ≤ 0 := by
      simpa only [hzero] using _root_.GD.N0230.N0558.d000532 hp hq
    have hnorm : ‖_root_.GD.N0230.N0558.d000527 p q‖ = 0 := by
      nlinarith [norm_nonneg (_root_.GD.N0230.N0558.d000527 p q)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · rintro rfl
    simp [_root_.GD.N0230.N0558.d000528]



variable {G : Type*} [Mul G]


def d000535 (T : E → E) (p : E) : E := T p - p







theorem d000536
    (T : G → E → E) (L : G → E →ₗ[ℝ] E)
    (haction : ∀ (g h : G) (x : E), T (g * h) x = T g (T h x))
    (hlinearPart : ∀ (g : G) (x y : E),
      T g x - T g y = L g (x - y))
    (g h : G) (p : E) :
    _root_.GD.N0230.N0558.d000535 (T (g * h)) p =
      L g (_root_.GD.N0230.N0558.d000535 (T h) p) + _root_.GD.N0230.N0558.d000535 (T g) p := by
  unfold _root_.GD.N0230.N0558.d000535
  rw [haction]
  calc
    T g (T h p) - p =
        (T g (T h p) - T g p) + (T g p - p) := by abel
    _ = L g (T h p - p) + (T g p - p) := by
      rw [hlinearPart]

end N0558
end N0230
end GD

#print axioms _root_.GD.N0230.N0558.d000529
#print axioms _root_.GD.N0230.N0558.d000530
#print axioms _root_.GD.N0230.N0558.d000534
#print axioms _root_.GD.N0230.N0558.d000536
