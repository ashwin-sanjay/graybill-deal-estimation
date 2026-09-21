import Mathlib.Analysis.Matrix.Order























open Matrix
open scoped MatrixOrder

namespace GD
namespace N0234
namespace N0735

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]


def d003254 (P S : Matrix n n ℝ) : ℝ :=
  (P * S).trace


def d003255 (v : n → ℝ) : Matrix n n ℝ :=
  vecMulVec v v


theorem d003256 (v : n → ℝ) :
    (_root_.GD.N0234.N0735.d003255 v).PosSemidef := by
  simpa [_root_.GD.N0234.N0735.d003255] using
    (Matrix.posSemidef_vecMulVec_self_star (R := ℝ) v)




theorem d003257
    (v : n → ℝ) (S : Matrix n n ℝ) :
    _root_.GD.N0234.N0735.d003254 (_root_.GD.N0234.N0735.d003255 v) S = v ⬝ᵥ (S *ᵥ v) := by
  classical
  calc
    _root_.GD.N0234.N0735.d003254 (_root_.GD.N0234.N0735.d003255 v) S =
        ((_root_.GD.N0234.N0735.d003255 v) * S).trace := rfl
    _ = (S * _root_.GD.N0234.N0735.d003255 v).trace :=
      Matrix.trace_mul_comm _ _
    _ = (vecMulVec (S *ᵥ v) v).trace := by
      congr 1
      ext i j
      simp only [_root_.GD.N0234.N0735.d003255, mul_apply, vecMulVec_apply, mulVec, dotProduct]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (S *ᵥ v) ⬝ᵥ v :=
      Matrix.trace_vecMulVec _ _
    _ = v ⬝ᵥ (S *ᵥ v) :=
      dotProduct_comm _ _





theorem d003258
    {P S : Matrix n n ℝ}
    (hP : P.PosSemidef) (hS : S.PosSemidef) :
    0 ≤ _root_.GD.N0234.N0735.d003254 P S := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  rw [star_eq_conjTranspose] at hB
  rw [hB, _root_.GD.N0234.N0735.d003254]
  rw [← Matrix.trace_mul_cycle B S Bᴴ]
  exact (hS.mul_mul_conjTranspose_same B).trace_nonneg





theorem d003259
    {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S.PosSemidef ↔
      ∀ v : n → ℝ, 0 ≤ _root_.GD.N0234.N0735.d003254 (_root_.GD.N0234.N0735.d003255 v) S := by
  constructor
  · intro hPSD v
    exact _root_.GD.N0234.N0735.d003258
      (_root_.GD.N0234.N0735.d003256 v) hPSD
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS
    intro v
    simpa [_root_.GD.N0234.N0735.d003257] using h v





theorem d003260
    {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S.PosSemidef ↔
      ∀ P : Matrix n n ℝ, P.PosSemidef → 0 ≤ _root_.GD.N0234.N0735.d003254 P S := by
  constructor
  · intro hPSD P hP
    exact _root_.GD.N0234.N0735.d003258 hP hPSD
  · intro h
    exact (_root_.GD.N0234.N0735.d003259 hS).2
      (fun v ↦ h (_root_.GD.N0234.N0735.d003255 v) (_root_.GD.N0234.N0735.d003256 v))





theorem d003261
    {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (hzero : ∀ v : n → ℝ, _root_.GD.N0234.N0735.d003254 (_root_.GD.N0234.N0735.d003255 v) S = 0) :
    S = 0 := by
  have hPSD : S.PosSemidef :=
    (_root_.GD.N0234.N0735.d003259 hS).2
      (fun v ↦ (hzero v).ge)
  apply hPSD.trace_eq_zero_iff.mp
  rw [trace]
  apply Finset.sum_eq_zero
  intro i hi
  have hz := hzero (Pi.single i 1)
  rw [_root_.GD.N0234.N0735.d003257] at hz
  simpa [dotProduct, mulVec, Pi.single_apply] using hz





theorem d003262
    {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (hzero :
      ∀ P : Matrix n n ℝ, P.PosSemidef → _root_.GD.N0234.N0735.d003254 P S = 0) :
    S = 0 :=
  _root_.GD.N0234.N0735.d003261 hS
    (fun v ↦ hzero (_root_.GD.N0234.N0735.d003255 v) (_root_.GD.N0234.N0735.d003256 v))





theorem d003263
    {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (∀ v : n → ℝ, _root_.GD.N0234.N0735.d003254 (_root_.GD.N0234.N0735.d003255 v) S = 0) ↔ S = 0 := by
  constructor
  · exact _root_.GD.N0234.N0735.d003261 hS
  · rintro rfl v
    simp [_root_.GD.N0234.N0735.d003254]





theorem d003264
    {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (∀ P : Matrix n n ℝ, P.PosSemidef → _root_.GD.N0234.N0735.d003254 P S = 0) ↔ S = 0 := by
  constructor
  · exact _root_.GD.N0234.N0735.d003262 hS
  · rintro rfl P hP
    simp [_root_.GD.N0234.N0735.d003254]






theorem d003265
    {S : Matrix n n ℝ}
    (hS : S.PosSemidef) (htrace : S.trace = 0) :
    S = 0 :=
  hS.trace_eq_zero_iff.mp htrace







theorem d003266
    {P C : Matrix n n ℝ} {ε : ℝ}
    (hP : P.PosSemidef)
    (hshift : (C + ε • (1 : Matrix n n ℝ)).PosSemidef) :
    -ε * P.trace ≤ _root_.GD.N0234.N0735.d003254 P C := by
  have hnonneg :
      0 ≤ _root_.GD.N0234.N0735.d003254 P (C + ε • (1 : Matrix n n ℝ)) :=
    _root_.GD.N0234.N0735.d003258 hP hshift
  have hexpand :
      _root_.GD.N0234.N0735.d003254 P (C + ε • (1 : Matrix n n ℝ)) =
        _root_.GD.N0234.N0735.d003254 P C + ε * P.trace := by
    simp [_root_.GD.N0234.N0735.d003254, Matrix.mul_add]
  rw [hexpand] at hnonneg
  linarith

end

end N0735
end N0234
end GD
