import GD.Module1504
import GD.Module1677








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0411
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0399 _root_.GD.N0101.N0398 _root_.GD.N0101.N0400
open _root_.GD.N0225.N0539
open _root_.GD.N0225.N0540
open _root_.GD.N0225.N0538

variable {k : ℕ}

local instance d028558 : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := borel (_root_.GD.N0232.N0719.N0859.d010809 k)
local instance d028559 : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨rfl⟩

theorem d028560 (hk : 0 < k) (t : Fin k → ℝ) :
    ∑ i, _root_.GD.N0021.d023313 t i = 1 :=
  _root_.GD.N0232.N0719.N0900.d009131 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t))

theorem d028561 (hk : 0 < k) (t : Fin k → ℝ) (i : Fin k) :
    0 ≤ _root_.GD.N0021.d023313 t i :=
  _root_.GD.N0232.N0719.N0900.d009132 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i

theorem d028562 [NeZero k] (t : Fin k → ℝ) (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0021.d023313 t = _root_.GD.N0230.N0665.d000407 t := by
  let s := _root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)
  have hp (i : Fin k) : _root_.GD.N0232.N0719.N0900.d009106 s i = (t i)⁻¹ :=
    _root_.GD.N0232.N0719.N0900.d009127 (ht i)
  have hsum : _root_.GD.N0232.N0719.N0900.d009107 s =
      _root_.GD.N0230.N0665.d000406 t :=
    Finset.sum_congr rfl (fun i _ => hp i)
  have hpos := _root_.GD.N0230.N0665.d000408 ht
  funext i
  change (if _root_.GD.N0232.N0719.N0900.d009107 s = 0 then _ else
    _root_.GD.N0232.N0719.N0900.d009106 s i / _root_.GD.N0232.N0719.N0900.d009107 s) = _
  rw [hsum, if_neg hpos.ne', hp]
  rfl



theorem d028563 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    {L : ℝ} (hL : 0 < L)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : _root_.GD.N0232.N0719.N0962.d012187 k sizes d ≤ ENNReal.ofReal C) :
    Integrable (fun β => (_root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0101.N0399.d023328 sizes hn β) d).toReal)
      (_root_.GD.N0225.N0539.d008058 α L) := by
  apply _root_.GD.N0225.N0540.d023482 sizes α hα hsum hL
    (_root_.GD.N0101.N0399.d023328 sizes hn) (_root_.GD.N0101.N0399.d023329 sizes hn) d hd C
  intro β hβ
  have hθ := (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hn C hC (_root_.GD.N0101.N0399.d023328 sizes hn β) d).mp
    ((le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d) (_root_.GD.N0101.N0399.d023328 sizes hn β)).trans hcap)
  rw [_root_.GD.N0101.N0399.d023334 sizes hn hβ] at hθ
  have hr : 0 < ∑ i, β i := Finset.sum_pos (fun i _ => hβ i)
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  simpa only [div_eq_mul_inv] using
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (inv_pos.mpr hr).le) hθ

theorem d028564 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1)
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes (fun i => by have := hn i; omega) _root_.GD.N0021.d023313 β).toReal)
      (_root_.GD.N0225.N0539.d008058 α L) := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  have hf := _root_.GD.N0225.N0538.d023463 sizes hn2 _root_.GD.N0021.d023313 _root_.GD.N0021.d023314
    (_root_.GD.N0101.N0411.d028560 hk) (_root_.GD.N0101.N0411.d028561 hk)
  have hcap : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0072.d023291 sizes _root_.GD.N0021.d023313) ≤
      ENNReal.ofReal (k : ℝ) := by
    rw [← _root_.GD.N0021.d023315]
    exact _root_.GD.N0070.d028368 hk sizes hn
  exact _root_.GD.N0101.N0411.d028563 hk sizes (fun i => by have := hn i; omega)
    α hα hsum hL _ hf k (Nat.cast_nonneg _) hcap



theorem d028565 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) := by
  rw [_root_.GD.N0021.d023315]
  have hab (i j : Fin (n + 1)) (_hij : i ≠ j) :
      1 < _root_.GD.N0232.N0719.N0954.d009355 sizes i + _root_.GD.N0232.N0719.N0954.d009355 sizes j := by
    have hi : (2 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ sizes i - 1 by have := hn i; omega)
    have hj : (2 : ℝ) ≤ ((sizes j - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ sizes j - 1 by have := hn j; omega)
    unfold _root_.GD.N0232.N0719.N0954.d009355
    linarith
  exact _root_.GD.N0101.N0400.d023491 sizes
    (fun i => by have := hn i; omega) ρ hρ hα hsum hab
    _root_.GD.N0021.d023313 _root_.GD.N0021.d023314 (_root_.GD.N0101.N0411.d028560 (Nat.succ_pos _))
    (_root_.GD.N0101.N0411.d028561 (Nat.succ_pos _)) _root_.GD.N0101.N0411.d028562
    (fun m => _root_.GD.N0101.N0411.d028564 (Nat.succ_pos _) sizes hn _ hα hsum (by positivity))

end
end GD.N0101.N0411

#print axioms _root_.GD.N0101.N0411.d028560
#print axioms _root_.GD.N0101.N0411.d028561
#print axioms _root_.GD.N0101.N0411.d028562
#print axioms _root_.GD.N0101.N0411.d028563
#print axioms _root_.GD.N0101.N0411.d028564
#print axioms _root_.GD.N0101.N0411.d028565
