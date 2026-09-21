import GD.Module1106
import Mathlib.Tactic















open Filter Topology
open scoped Topology

namespace GD.N0232.N0720.N1293

noncomputable section

open _root_.GD.N0232.N0720.N1350
open _root_.GD.N0232.N0720.N1300

private theorem d017793 :
    Summable (_root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) (1 / 16)) := by
  exact _root_.GD.N0232.N0720.N1350.d002727
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)




theorem d017794 :
    (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) (1 / 16) < 1 / 8 := by
  let f : ℤ → ℝ := fun s ↦
    (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) (1 / 16) s
  have hsumF : Summable f := _root_.GD.N0232.N0720.N1293.d017793.mul_left (1 / 16 : ℝ)
  have hpos : Summable (fun n : ℕ ↦ f ((n + 1 : ℕ) : ℤ)) :=
    hsumF.comp_injective (by
      intro a b h
      have hnat : a + 1 = b + 1 := Int.ofNat.inj h
      exact Nat.add_right_cancel hnat)
  have hneg : Summable (fun n : ℕ ↦ f (-((n + 1 : ℕ) : ℤ))) :=
    hsumF.comp_injective (by
      intro a b h
      have hcast : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) :=
        neg_injective h
      omega)

  have hgeomPos : HasSum
      (fun n : ℕ ↦ (64 : ℝ) * (1 / 4096 : ℝ) ^ (n + 1))
      (64 * ((1 / 4096 : ℝ) * (1 - 1 / 4096)⁻¹)) := by
    have h := hasSum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4096) (by norm_num : (1 / 4096 : ℝ) < 1)
    simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      h.mul_left (64 * (1 / 4096 : ℝ))
  have hgeomNeg : HasSum
      (fun n : ℕ ↦ (1 / 16 : ℝ) * (1 / 256 : ℝ) ^ (n + 1))
      ((1 / 16 : ℝ) * ((1 / 256 : ℝ) * (1 - 1 / 256)⁻¹)) := by
    have h := hasSum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 256) (by norm_num : (1 / 256 : ℝ) < 1)
    simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      h.mul_left ((1 / 16 : ℝ) * (1 / 256 : ℝ))

  have hposBound :
      (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) ≤
        64 * ((1 / 4096 : ℝ) * (1 - 1 / 4096)⁻¹) := by
    rw [← hgeomPos.tsum_eq]
    apply hpos.tsum_le_tsum
    · intro n
      have h := _root_.GD.N0232.N0720.N1350.d002725
        (rho := (1 / 256 : ℝ)) (beta := (3 / 2 : ℝ))
        (x := (1 / 16 : ℝ)) (by norm_num) (by norm_num) (n + 1)
      change (1 / 16 : ℝ) *
          _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) (1 / 16) ((n + 1 : ℕ) : ℤ) ≤
        64 * (1 / 4096 : ℝ) ^ (n + 1)
      calc
        _ ≤ (1 / 16 : ℝ) *
            ((1 / (1 / 16 : ℝ) ^ (5 / 2 : ℝ)) *
              ((1 / 256 : ℝ) ^ (3 / 2 : ℝ)) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
        _ = _ := by
          norm_num
          ring
    · exact hgeomPos.summable

  have hnegBound :
      (∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ))) ≤
        (1 / 16 : ℝ) * ((1 / 256 : ℝ) * (1 - 1 / 256)⁻¹) := by
    rw [← hgeomNeg.tsum_eq]
    apply hneg.tsum_le_tsum
    · intro n
      have h := _root_.GD.N0232.N0720.N1350.d002726
        (rho := (1 / 256 : ℝ)) (beta := (3 / 2 : ℝ))
        (x := (1 / 16 : ℝ)) (by norm_num) (by norm_num) (n + 1)
      change (1 / 16 : ℝ) *
          _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) (1 / 16)
            (-((n + 1 : ℕ) : ℤ)) ≤
        (1 / 16 : ℝ) * (1 / 256 : ℝ) ^ (n + 1)
      calc
        _ ≤ (1 / 16 : ℝ) *
            (((1 / 256 : ℝ) ^ (5 / 2 - 3 / 2 : ℝ)) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
        _ = _ := by norm_num
    · exact hgeomNeg.summable

  have hzero : f 0 ≤ (1 / 16 : ℝ) := by
    have hden : (1 : ℝ) ≤
        ((1 / 16 : ℝ) + 1) ^ (5 / 2 : ℝ) := by
      exact Real.one_le_rpow (by norm_num) (by norm_num)
    have hfrac : 1 /
        ((1 / 16 : ℝ) + 1) ^ (5 / 2 : ℝ) ≤ 1 := by
      exact (div_le_one (by positivity)).2 hden
    have hm := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 1 / 16)
    simpa [f, _root_.GD.N0232.N0720.N1350.d002722] using hm

  have hsplit :
      (∑' s : ℤ, f s) =
        (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) + f 0 +
          ∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ)) := by
    exact tsum_of_add_one_of_neg_add_one hpos hneg
  calc
    (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) (1 / 16) =
        ∑' s : ℤ, f s := by
      unfold _root_.GD.N0232.N0720.N1350.d002729
      rw [← tsum_mul_left]
    _ = (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) + f 0 +
          ∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ)) := hsplit
    _ ≤ 64 * ((1 / 4096 : ℝ) * (1 - 1 / 4096)⁻¹) +
          (1 / 16 : ℝ) +
          (1 / 16 : ℝ) * ((1 / 256 : ℝ) * (1 - 1 / 256)⁻¹) := by
      gcongr
    _ < 1 / 8 := by norm_num



theorem d017795 :
    (1 / 8 : ℝ) < _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) 1 := by
  have hsum : Summable (_root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) 1) := by
    exact _root_.GD.N0232.N0720.N1350.d002727
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpow : (2 : ℝ) ^ (5 / 2 : ℝ) < 8 := by
    calc
      (2 : ℝ) ^ (5 / 2 : ℝ) < 2 ^ (3 : ℝ) :=
        (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2))
          (by norm_num : (5 / 2 : ℝ) < 3)
      _ = 8 := by norm_num
  have hterm : (1 / 8 : ℝ) <
      _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) 1 0 := by
    unfold _root_.GD.N0232.N0720.N1350.d002722
    norm_num only [Int.cast_zero, mul_zero, Real.rpow_zero]
    exact one_div_lt_one_div_of_lt (by positivity) hpow
  have hle : _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) 1 0 ≤
      _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) 1 := by
    unfold _root_.GD.N0232.N0720.N1350.d002729
    have hnonneg : ∀ s : ℤ,
        0 ≤ _root_.GD.N0232.N0720.N1350.d002722 (1 / 256) (3 / 2) 1 s := by
      intro s
      exact (_root_.GD.N0232.N0720.N1350.d002723 (by norm_num) (by norm_num) _ s).le
    simpa using hsum.sum_le_tsum ({0} : Finset ℤ) (fun s _ ↦ hnonneg s)
  exact hterm.trans_le hle


theorem d017796 :
    _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) (1 / 16) ≠
      _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) 1 / (1 / 16) := by
  intro h
  have hm : (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) (1 / 16) =
      _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) 1 := by
    rw [h]
    ring
  linarith [_root_.GD.N0232.N0720.N1293.d017794,
    _root_.GD.N0232.N0720.N1293.d017795]



theorem d017797 :
    _root_.GD.N0232.N0720.N1350.d002732 (1 / 256) (3 / 2) 1 (16 / 17) (16 / 17) ≠ 16 / 17 := by
  have hD1 := _root_.GD.N0232.N0720.N1350.d002731
    (rho := (1 / 256 : ℝ)) (beta := (3 / 2 : ℝ)) (x := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hDq := _root_.GD.N0232.N0720.N1350.d002731
    (rho := (1 / 256 : ℝ)) (beta := (3 / 2 : ℝ)) (x := (1 / 16 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro htrace
  unfold _root_.GD.N0232.N0720.N1350.d002732 at htrace
  dsimp only at htrace
  norm_num only [one_mul] at htrace
  apply _root_.GD.N0232.N0720.N1293.d017796
  have hden : _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) 1 +
      _root_.GD.N0232.N0720.N1350.d002729 (1 / 256) (3 / 2) (1 / 16) ≠ 0 := by positivity
  field_simp [hden] at htrace
  field_simp
  nlinarith




theorem d017798 :
    ¬ Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1300.d017783
          (1 / 256) (3 / 2) (16 / 17) (16 / 17) n -
        _root_.GD.N0232.N0720.N1300.d017789
          (1 / 256) (16 / 17) (16 / 17) n)
      atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.N1300.d017785
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (_root_.GD.N0232.N0720.N1300.d017789 (1 / 256) (16 / 17) (16 / 17))
  · exact _root_.GD.N0232.N0720.N1300.d017791
      (by norm_num) (by norm_num) (by norm_num)
  · exact _root_.GD.N0232.N0720.N1293.d017797

end

end GD.N0232.N0720.N1293

#print axioms _root_.GD.N0232.N0720.N1293.d017796
#print axioms _root_.GD.N0232.N0720.N1293.d017798
