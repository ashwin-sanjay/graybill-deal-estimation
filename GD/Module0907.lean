import GD.Module0599
import GD.Module0607
import GD.Module0906

open MeasureTheory Set

namespace GD.N0145

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0147
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131


def d014117
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) : ℝ :=
  A.emitted.table.d008715 A.rho
    (fun _ ↦ (A.emitted.ledger.inversePower : ℝ))


theorem d014118
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn) :
    A.emitted.table.d008715 A.rho A.power ≤ _root_.GD.N0145.d014117 A := by
  let T := A.emitted.table
  let inv : ℝ := (A.emitted.ledger.inversePower : ℝ)
  have hinv : 0 ≤ inv := by
    dsimp [inv]
    exact_mod_cast A.emitted.ledger.inversePower_pos.le
  have hmono := _root_.GD.N0147.d008619
    (s := (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)))
    (center₁ := fun i ↦ ((T.d008652 i).ell : ℝ))
    (center₂ := fun i ↦ ((T.d008652 i).f : ℝ))
    (coeff := fun i ↦ T.d008699 i * T.d008700 i)
    (w := (T.width : ℝ))
    (density₁ := fun x ↦ A.rho x * A.power x)
    (density₂ := fun x ↦ A.rho x * inv)
    (by
      intro i hi j hj hij x
      have ht := A.envelope.tents_pairwise_disjoint i j hij x
      calc
        ((T.d008699 i * T.d008700 i) * T.d008697 i x) *
            ((T.d008699 j * T.d008700 j) * T.d008697 j x) =
          ((T.d008699 i * T.d008700 i) *
            (T.d008699 j * T.d008700 j)) *
              (T.d008697 i x * T.d008697 j x) := by ring
        _ = 0 := by rw [ht, mul_zero])
    (by
      intro i hi
      exact T.d008710 A.rho A.power i
        (((T.boxes i).upper * A.emitted.ledger.inversePower : ℚ) : ℝ)
        (by
          exact_mod_cast
            (mul_nonneg (T.d008703 i).le
              A.emitted.ledger.inversePower_pos.le))
        A.envelope.measurable_rho A.envelope.measurable_power
        (A.envelope.d008708
          A.emitted.ledger.inversePower_pos.le i))
    (by
      intro i hi
      exact T.d008710 A.rho (fun _ ↦ inv) i
        (((T.boxes i).upper * A.emitted.ledger.inversePower : ℚ) : ℝ)
        (by
          exact_mod_cast
            (mul_nonneg (T.d008703 i).le
              A.emitted.ledger.inversePower_pos.le))
        A.envelope.measurable_rho measurable_const
        (by
          intro x hx
          have hrho := A.envelope.density_bounds i x hx
          have hrho0 := A.envelope.d008707 i x hx
          constructor
          · exact mul_nonneg hrho0 hinv
          · norm_num only [Rat.cast_mul]
            exact mul_le_mul_of_nonneg_right hrho.2 hinv))
    (by
      intro i hi x hx
      have hrho0 := A.envelope.d008707 i x hx
      have hp := (A.envelope.power_bounds i x hx).2
      exact mul_le_mul_of_nonneg_left hp hrho0)
  simpa only [T, _root_.GD.N0145.d014117, _root_.GD.N0113.d008651.d008715,
    _root_.GD.N0113.d008651.d008701, _root_.GD.N0113.d008651.d008697] using hmono




theorem d014119
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (A : _root_.GD.N0113.d008651.d008723 m n hm hn)
    (hrho : A.rho = _root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn)) :
    _root_.GD.N0145.d014117 A <
      ((_root_.GD.N0113.d008670 A.emitted.table
        A.emitted.ledger.inversePower : ℚ) : ℝ) := by
  let T := A.emitted.table
  let inv : ℝ := (A.emitted.ledger.inversePower : ℝ)
  have hinv : 0 < inv := by
    dsimp [inv]
    exact_mod_cast A.emitted.ledger.inversePower_pos
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  have hnonzeroWeight : ∃ i : _root_.GD.N0113.d008651.d008696 T, T.d008699 i ≠ 0 := by
    have hC : (0 : ℝ) < A.emitted.ledger.C := by
      exact_mod_cast A.emitted.ledger.C_pos
    have hatomic : T.d008711 A.carrier < 0 :=
      A.atomic_margin.trans_lt (by nlinarith)
    exact _root_.GD.N0145.d014110 T A.carrier hatomic
  have hstrict := _root_.GD.N0147.d008618
    (s := (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)))
    (center₁ := fun i ↦ ((T.d008652 i).ell : ℝ))
    (center₂ := fun i ↦ ((T.d008652 i).f : ℝ))
    (coeff := fun i ↦ T.d008699 i * T.d008700 i)
    (upper := fun i ↦ ((T.boxes i).upper : ℝ) * inv)
    (w := (T.width : ℝ))
    (density := fun x ↦ A.rho x * inv)
    hw
    (by
      intro i hi
      exact mul_nonneg (by exact_mod_cast (T.d008703 i).le) hinv.le)
    (by
      intro i hi j hj hij x
      have ht := A.envelope.tents_pairwise_disjoint i j hij x
      calc
        ((T.d008699 i * T.d008700 i) * T.d008697 i x) *
            ((T.d008699 j * T.d008700 j) * T.d008697 j x) =
          ((T.d008699 i * T.d008700 i) *
            (T.d008699 j * T.d008700 j)) *
              (T.d008697 i x * T.d008697 j x) := by ring
        _ = 0 := by rw [ht, mul_zero])
    (by
      intro i hi
      exact T.d008710 A.rho (fun _ ↦ inv) i
        (((T.boxes i).upper * A.emitted.ledger.inversePower : ℚ) : ℝ)
        (by
          exact_mod_cast
            (mul_nonneg (T.d008703 i).le
              A.emitted.ledger.inversePower_pos.le))
        A.envelope.measurable_rho measurable_const
        (by
          intro x hx
          have hrhoBounds := A.envelope.density_bounds i x hx
          have hrho0 := A.envelope.d008707 i x hx
          constructor
          · exact mul_nonneg hrho0 hinv.le
          · norm_num only [Rat.cast_mul]
            exact mul_le_mul_of_nonneg_right hrhoBounds.2 hinv.le))
    (by
      intro i hi x hx
      have hrho0 := A.envelope.d008707 i x hx
      have hrhoStrict : A.rho x < ((T.boxes i).upper : ℝ) := by
        rw [hrho]
        apply _root_.GD.N0131.d008800 T i x hx
        intro z hz
        have hzUpper := (A.envelope.density_bounds i z hz).2
        simpa only [hrho] using hzUpper
      exact ⟨mul_nonneg hrho0 hinv.le,
        mul_lt_mul_of_pos_right hrhoStrict hinv⟩)
    (by
      obtain ⟨i, hi⟩ := hnonzeroWeight
      refine ⟨i, Finset.mem_univ i, mul_ne_zero hi ?_⟩
      apply ne_of_gt
      change (0 : ℝ) < (T.d008653 i : ℝ)
      exact_mod_cast (_root_.GD.N0145.d014105 T i))
  have hright :
      (∑ i : _root_.GD.N0113.d008651.d008696 T,
          4 / (9 * (T.width : ℝ) ^ 2) *
            (T.d008699 i * T.d008700 i) ^ 2 *
              (((T.boxes i).upper : ℝ) * inv)) =
        ((_root_.GD.N0113.d008670 T A.emitted.ledger.inversePower : ℚ) : ℝ) := by
    simp only [_root_.GD.N0113.d008670, Rat.cast_mul, Rat.cast_sum,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [_root_.GD.N0113.d008651.d008699, _root_.GD.N0113.d008651.d008700, inv]
    ring
  unfold _root_.GD.N0145.d014117
  change
    T.d008715 A.rho (fun _ ↦ inv) <
      ((_root_.GD.N0113.d008670 T A.emitted.ledger.inversePower : ℚ) : ℝ)
  unfold _root_.GD.N0113.d008651.d008715
  simpa only [_root_.GD.N0113.d008651.d008701, _root_.GD.N0113.d008651.d008697] using
    hstrict.trans_eq hright

end

end GD.N0145
