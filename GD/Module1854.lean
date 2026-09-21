import GD.Module1852
import GD.Module1546
import GD.Module1542
import GD.Module1188

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0037
noncomputable section
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0046.N0305 _root_.GD.N0034.N0294
open _root_.GD.N0064

theorem d030434
    (m n : ℕ) (hm : 2 ≤ m) (hn : 4 ≤ n)
    (hab : 1 < _root_.GD.N0064.d023942 m * _root_.GD.N0064.d023942 n) :
    _root_.GD.N0046.N0305.d030202 m n hm (by omega) = ∅ := by
  obtain ⟨f, hf, hfb, C, hcap, hzero⟩ :=
    _root_.GD.N0064.d023962 m n hm (by omega) hab
  exact _root_.GD.N0065.d030419 m n hm hn f hf hfb C hcap hzero


theorem d030435 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : _root_.GD.N0046.N0305.d030202 n m hn hm = ∅) : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hK
  obtain ⟨d, hd, hcap⟩ := (_root_.GD.N0034.N0294.d030324 m n hm hn).mpr hK
  have hswap : (_root_.GD.N0034.N0294.d030312 n m).Nonempty := by
    refine ⟨d ∘ _root_.GD.N0232.N0720.N1101.d019094 n m, hd.comp measurable_swap, ?_⟩
    intro θ
    rw [_root_.GD.N0232.N0720.N1101.d019101 n m θ d hd]
    have hc := hcap (_root_.GD.N0232.N0720.N1043.d019058 θ)
    have ho : _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0232.N0720.N1043.d019058 θ) =
        _root_.GD.N0232.N0720.N1257.d015508 n m θ := by
      simp only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1043.d019058, add_comm]
    constructor
    · simpa only [ho, _root_.GD.N0086.d023916 n m] using hc.1
    · exact hc.2.trans_eq
        (_root_.GD.N0232.N0720.N1101.d019106 n m hn hm θ).symm
  have hk := (_root_.GD.N0034.N0294.d030324 n m hn hm).mp hswap
  rw [h] at hk
  exact Set.not_nonempty_empty hk


theorem d030436
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hprod : 4 < (m - 1) * (n - 1)) : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ := by
  have hab : 1 < _root_.GD.N0064.d023942 m * _root_.GD.N0064.d023942 n := by
    have hh : (4 : ℝ) < ((m - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hprod
    unfold _root_.GD.N0064.d023942
    nlinarith
  by_cases hn4 : 4 ≤ n
  · exact _root_.GD.N0037.d030434 m n hm hn4 hab
  · have hm4 : 4 ≤ m := by
      by_contra hh
      have hm' : m - 1 ≤ 2 := by omega
      have hn' : n - 1 ≤ 2 := by omega
      have hle : (m - 1) * (n - 1) ≤ 4 := Nat.mul_le_mul hm' hn'
      omega
    exact _root_.GD.N0037.d030435 m n hm hn
      (_root_.GD.N0037.d030434 n m hn hm4
        (by simpa only [mul_comm] using hab))

theorem d030437
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hprod : 4 < (m - 1) * (n - 1)) :
    _root_.GD.N0232.N0720.N1256.d015549 m n < _root_.GD.N0022.N0255.d030394 m n :=
  (_root_.GD.N0022.N0255.d030398 m n hm hn).mp
    (_root_.GD.N0037.d030436 m n hm hn hprod)

theorem d030438
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hprod : 4 < (m - 1) * (n - 1)) :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 m n := by
  intro h
  obtain ⟨p, hp, _⟩ := (_root_.GD.N0046.N0305.d030214 m n hm hn).mp h
  rw [_root_.GD.N0037.d030436 m n hm hn hprod] at hp
  exact hp

theorem d030439 (n : ℕ) (hn : 4 ≤ n) :
    _root_.GD.N0046.N0305.d030202 3 n (by decide) (by omega) = ∅ := by
  apply _root_.GD.N0037.d030436 3 n (by decide) (by omega)
  simp only [Nat.reduceSub]
  omega

theorem d030440 (n : ℕ) (hn : 6 ≤ n) :
    _root_.GD.N0046.N0305.d030202 2 n (by decide) (by omega) = ∅ := by
  apply _root_.GD.N0037.d030436 2 n (by decide) (by omega)
  simp only [Nat.reduceSub, one_mul]
  omega

end
end GD.N0037

#print axioms _root_.GD.N0037.d030434
#print axioms _root_.GD.N0037.d030435
#print axioms _root_.GD.N0037.d030436
#print axioms _root_.GD.N0037.d030437
#print axioms _root_.GD.N0037.d030438
#print axioms _root_.GD.N0037.d030439
#print axioms _root_.GD.N0037.d030440
