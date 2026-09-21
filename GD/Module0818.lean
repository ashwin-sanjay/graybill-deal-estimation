import GD.Module0817
import GD.Module0217





















namespace GD
namespace N0232
namespace N0720
namespace N1041

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1437





theorem d012486
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (xbar ybar vx vy : ℝ) (hcontrast : xbar - ybar = 0) :
    d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) = ybar := by
  have hxy : xbar = ybar := by linarith
  subst xbar
  have href := hreflect 0 0 vx vy
  have hzero : d (_root_.GD.N0232.N0720.N1209.d012458 0 0 vx vy) = 0 := by
    simp only [neg_zero] at href
    linarith
  have hcov := haffine ybar 1 (by norm_num : (0 : ℝ) < 1)
    (_root_.GD.N0232.N0720.N1209.d012458 0 0 vx vy)
  have hsummary :
      _root_.GD.N0232.N0719.N0900.d009101 ybar 1
          (_root_.GD.N0232.N0720.N1209.d012458 0 0 vx vy) =
        _root_.GD.N0232.N0720.N1209.d012458 ybar ybar vx vy := by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
      simp [_root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458]
  rw [hsummary] at hcov
  rw [hcov, hzero]
  ring



theorem d012487
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (hswap : _root_.GD.N0232.N0720.N1209.d012479 d)
    (xbar ybar : ℝ) :
    d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar 0 0) = (xbar + ybar) / 2 := by
  have href := hreflect xbar ybar 0 0
  have hcov := haffine (xbar + ybar) 1
    (by norm_num : (0 : ℝ) < 1)
    (_root_.GD.N0232.N0720.N1209.d012458 (-xbar) (-ybar) 0 0)
  have hsummary :
      _root_.GD.N0232.N0719.N0900.d009101 (xbar + ybar) 1
          (_root_.GD.N0232.N0720.N1209.d012458 (-xbar) (-ybar) 0 0) =
        _root_.GD.N0232.N0720.N1209.d012458 ybar xbar 0 0 := by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
      simp [_root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458] <;>
      ring
  rw [hsummary] at hcov
  have hsw := hswap xbar ybar 0 0
  rw [hsw, href] at hcov
  linarith








theorem d012488
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (hmeasurable : Measurable d)
    (haffine : _root_.GD.N0232.N0719.N0860.d011447 d)
    (hreflect : _root_.GD.N0232.N0720.N1209.d012478 d)
    (hswap : _root_.GD.N0232.N0720.N1209.d012479 d) :
    ∃ h : ℝ → ℝ → ℝ,
      Measurable (fun p : ℝ × ℝ ↦ h p.1 p.2) ∧
      (∀ r s, h (1 - r) s = 1 - h r s) ∧
      (∀ r, h r 0 = 1 / 2) ∧
      ∀ xbar ybar vx vy,
        0 ≤ vx → 0 ≤ vy →
        d (_root_.GD.N0232.N0720.N1209.d012458 xbar ybar vx vy) =
          _root_.GD.N0232.N0720.N1437.d003016 h xbar ybar vx vy := by
  let h : ℝ → ℝ → ℝ := _root_.GD.N0232.N0720.N1209.d012474 d
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1209.d012475 d hmeasurable
  · intro r s
    exact _root_.GD.N0232.N0720.N1209.d012482
      d haffine hreflect hswap r s
  · intro r
    exact _root_.GD.N0232.N0720.N1209.d012476 d r
  · intro xbar ybar vx vy hvx hvy
    by_cases hsum : _root_.GD.N0232.N0720.N1437.d003012 vx vy
    · rw [_root_.GD.N0232.N0720.N1437.d003018
        h xbar ybar vx vy hsum]
      by_cases hcontrast : xbar - ybar = 0
      · rw [_root_.GD.N0232.N0720.N1041.d012486
          d haffine hreflect xbar ybar vx vy hcontrast]
        unfold _root_.GD.N0232.N0720.N1437.d002998
        rw [hcontrast]
        ring
      · have hnormal :=
          _root_.GD.N0232.N0720.N1209.d012485
            d haffine hreflect hsum hcontrast
        rw [hnormal]
        unfold _root_.GD.N0232.N0720.N1437.d002998
        dsimp only [h]
        have hsumPos : 0 < vx + vy :=
          lt_of_le_of_ne (add_nonneg hvx hvy) hsum.symm
        have hratioPos :
            0 < _root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy := by
          unfold _root_.GD.N0232.N0720.N1437.d002997
          exact div_pos (sq_pos_of_ne_zero hcontrast) hsumPos
        rw [_root_.GD.N0232.N0720.N1209.d012477
          d (_root_.GD.N0232.N0720.N1437.d002996 vx vy)
            (_root_.GD.N0232.N0720.N1437.d002997 xbar ybar vx vy) hratioPos.ne']
    · have hsumEq : vx + vy = 0 := not_ne_iff.mp hsum
      have hvx0 : vx = 0 := by nlinarith
      have hvy0 : vy = 0 := by nlinarith
      subst vx
      subst vy
      rw [_root_.GD.N0232.N0720.N1437.d003019
        h xbar ybar 0 0 (by simp [_root_.GD.N0232.N0720.N1437.d003012])]
      exact _root_.GD.N0232.N0720.N1041.d012487
        d haffine hreflect hswap xbar ybar






theorem d012489
    {H : Type*} [Norm H]
    {C : Set H} {p : H}
    (hp : p ∈ C)
    (hunique : ∀ q ∈ C, ‖q‖ ≤ ‖p‖ → q = p)
    (T : H → H)
    (hT : Set.MapsTo T C C)
    (hnorm : ‖T p‖ ≤ ‖p‖) :
    T p = p := by
  exact hunique (T p) (hT hp) hnorm



theorem d012490
    {H : Type*} [Norm H]
    {C : Set H} {p : H}
    (hp : p ∈ C)
    (hunique : ∀ q ∈ C, ‖q‖ ≤ ‖p‖ → q = p)
    (T : H → H)
    (hT : Set.MapsTo T C C)
    (hnorm : ∀ q, ‖T q‖ = ‖q‖) :
    T p = p := by
  apply _root_.GD.N0232.N0720.N1041.d012489 hp hunique T hT
  rw [hnorm]

end

end N1041
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1041.d012488
#print axioms _root_.GD.N0232.N0720.N1041.d012489
