import GD.Module1493
import GD.Module1547

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0427
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0968 _root_.GD.N0092
open _root_.GD.N0102.N0426

variable {k : ℕ}



theorem d023984
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤
        _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := by
  have hs := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn
  let s := _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn
  have hsFin : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := ⟨hs.1.1, hs.2⟩
  have hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes s := _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn
  let e := _root_.GD.N0232.N0719.N0970.d012314 k sizes s hsFin
  refine ⟨e, ⟨_root_.GD.N0232.N0719.N0970.d012316 k sizes s hsFin,
    _root_.GD.N0232.N0719.N0970.d012321 k sizes s hsFin hstrict,
    _root_.GD.N0232.N0719.N0970.d012317 k sizes s hsFin⟩, ?_⟩
  exact (_root_.GD.N0232.N0719.N0970.d012319 k sizes s hsFin).trans
    (_root_.GD.N0232.N0719.N0970.d012318 k sizes fun θ => (hstrict θ).le)


theorem d023985
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 4 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤ ENNReal.ofReal (_root_.GD.N0102.N0426.d023370 sizes) := by
  obtain ⟨e, he, hbound⟩ := _root_.GD.N0102.N0427.d023984 sizes hk
    (fun i => by have := hn i; omega)
  exact ⟨e, he, hbound.trans (_root_.GD.N0102.N0426.d023374 sizes (by omega) hn)⟩

theorem d023986
    (sizes : Fin k → ℕ) (hk : 0 < k) (N : ℕ) (hN : 4 ≤ N)
    (hn : ∀ i, N ≤ sizes i) :
    _root_.GD.N0102.N0426.d023370 sizes ≤
      1 + (k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) - 3)) := by
  have hNreal : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hsum : (∑ i, 1 / ((sizes i : ℝ) - 3)) ≤ (k : ℝ) / ((N : ℝ) - 3) := by
    calc
      _ ≤ ∑ _i : Fin k, 1 / ((N : ℝ) - 3) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : (N : ℝ) ≤ (sizes i : ℝ) := by exact_mod_cast hn i
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = _ := by simp [div_eq_mul_inv]
  calc
    _ ≤ 1 + (((k : ℝ) - 1) / 2) * ((k : ℝ) / ((N : ℝ) - 3)) := by
      change 1 + (((k : ℝ) - 1) / 2) * (∑ i, 1 / ((sizes i : ℝ) - 3)) ≤ _
      have hcoef : 0 ≤ ((k : ℝ) - 1) / 2 :=
        div_nonneg (sub_nonneg.mpr hkreal) (by norm_num)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hcoef)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring



theorem d023987
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (N : ℕ) (hN : 4 ≤ N)
    (hn : ∀ i, N ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤
        ENNReal.ofReal (1 + (k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) - 3))) := by
  obtain ⟨e, he, hbound⟩ := _root_.GD.N0102.N0427.d023985 sizes hk
    (fun i => hN.trans (hn i))
  exact ⟨e, he, hbound.trans (ENNReal.ofReal_le_ofReal
    (_root_.GD.N0102.N0427.d023986 sizes (by omega) N hN hn))⟩


theorem d023988
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (N : ℕ) (hN : 4 ≤ N)
    (hn : ∀ i, N ≤ sizes i) (ε : ℝ) (hε : 0 < ε)
    (hgap : (k : ℝ) * ((k : ℝ) - 1) < 2 * ε * ((N : ℝ) - 3)) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e < ENNReal.ofReal (1 + ε) := by
  obtain ⟨e, he, hbound⟩ := _root_.GD.N0102.N0427.d023987 sizes hk N hN hn
  have hNr : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hratio : (k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) - 3)) < ε := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (by linarith : (0 : ℝ) < (N : ℝ) - 3))).mpr
    nlinarith
  refine ⟨e, he, hbound.trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < 1 + ε)).mpr
  linarith

def d023989 (k : ℕ) (ε : ℝ) : ℕ :=
  4 + Nat.ceil ((k : ℝ) * ((k : ℝ) - 1) / (2 * ε))




theorem d023990
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ i, _root_.GD.N0102.N0427.d023989 k ε ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e < ENNReal.ofReal (1 + ε) := by
  have hN : 4 ≤ _root_.GD.N0102.N0427.d023989 k ε := by unfold _root_.GD.N0102.N0427.d023989; omega
  apply _root_.GD.N0102.N0427.d023988 sizes hk (_root_.GD.N0102.N0427.d023989 k ε) hN hn ε hε
  let A : ℝ := (k : ℝ) * ((k : ℝ) - 1) / (2 * ε)
  have hceil : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
  have hcast : (_root_.GD.N0102.N0427.d023989 k ε : ℝ) = 4 + (Nat.ceil A : ℝ) := by
    simp [_root_.GD.N0102.N0427.d023989, A]
  have hlt : A < (_root_.GD.N0102.N0427.d023989 k ε : ℝ) - 3 := by
    rw [hcast]
    linarith
  have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp hlt
  nlinarith

end
end GD.N0102.N0427

#print axioms _root_.GD.N0102.N0427.d023984
#print axioms _root_.GD.N0102.N0427.d023985
#print axioms _root_.GD.N0102.N0427.d023986
#print axioms _root_.GD.N0102.N0427.d023987
#print axioms _root_.GD.N0102.N0427.d023988
#print axioms _root_.GD.N0102.N0427.d023990
