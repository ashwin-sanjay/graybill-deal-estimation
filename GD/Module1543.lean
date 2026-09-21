import GD.Module1462
import GD.Module1542
import GD.Module0809
import GD.Module0983

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0067
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256


theorem d023923 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ ↔ 4 ≤ (m - 1) * (n - 1) :=
  _root_.GD.N0086.d023918
    _root_.GD.N0067.d023072 m n hm hn

theorem d023924 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤ ↔ (m = 2 ∧ n ≤ 4) ∨ (n = 2 ∧ m ≤ 4) := by
  constructor
  · exact _root_.GD.N0030.d023899 m n hm hn
  · intro h
    by_contra hf
    have hp := (_root_.GD.N0067.d023923 m n hm hn).mp hf
    rcases h with ⟨hm2, hn4⟩ | ⟨hn2, hm4⟩
    · rw [hm2] at hp
      norm_num at hp
      omega
    · rw [hn2] at hp
      norm_num at hp
      omega


theorem d023925 {k : ℕ} (hk : 2 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔
      ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1) :=
  _root_.GD.N0086.d023920
    _root_.GD.N0067.d023072 hk sizes hn



theorem d023926 {k : ℕ} (hk : 2 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔
      (∀ i, 3 ≤ sizes i) ∨
        ∃ i₀ : Fin k, sizes i₀ = 2 ∧ ∀ i, i ≠ i₀ → 5 ≤ sizes i :=
  _root_.GD.N0086.d023922
    _root_.GD.N0067.d023072 hk sizes hn


theorem d023927 {k : ℕ} (hk : 2 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤ ↔
      ∃ i j : Fin k, i ≠ j ∧ sizes i = 2 ∧ sizes j ≤ 4 := by
  rw [_root_.GD.N0068.d023044 hk sizes hn]
  constructor
  · rintro ⟨i, j, hij, ht⟩
    rcases (_root_.GD.N0067.d023924 _ _ (hn i) (hn j)).mp ht with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · exact ⟨i, j, hij, hi, hj⟩
    · exact ⟨j, i, Ne.symm hij, hj, hi⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨i, j, hij, (_root_.GD.N0067.d023924 _ _ (hn i) (hn j)).mpr (Or.inl ⟨hi, hj⟩)⟩

end
end GD.N0067

#print axioms _root_.GD.N0067.d023923
#print axioms _root_.GD.N0067.d023924
#print axioms _root_.GD.N0067.d023925
#print axioms _root_.GD.N0067.d023926
#print axioms _root_.GD.N0067.d023927

namespace GD.N0067
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970



theorem d023928
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hsmall : ∃ i j, i ≠ j ∧ sizes i = 2 ∧ sizes j ≤ 4) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = ⊤ ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes d := by
  have htop := (_root_.GD.N0067.d023927 (by omega : 2 ≤ k) sizes hn).mpr hsmall
  obtain ⟨d, hd, hv, ht, hs⟩ :=
    _root_.GD.N0232.N0719.N0970.d012331 k sizes hk hn htop
  exact ⟨d, hd, hv.trans htop, hv, ht, hs⟩


theorem d023929
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hsmall : ∃ i j, i ≠ j ∧ sizes i = 2 ∧ sizes j ≤ 4) :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d :=
  _root_.GD.N0232.N0719.N0970.d012330 k sizes hk hn
    ((_root_.GD.N0067.d023927 (by omega : 2 ≤ k) sizes hn).mpr hsmall)

end
end GD.N0067

#print axioms _root_.GD.N0067.d023928
#print axioms _root_.GD.N0067.d023929

namespace GD.N0067
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226



theorem d023930
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsmall : (m = 2 ∧ n ≤ 4) ∨ (n = 2 ∧ m ≤ 4)) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0232.N0720.N1226.d015577 m n d := by
  obtain ⟨d, hd⟩ := _root_.GD.N0232.N0720.N1226.d015586
    m n hm hn ((_root_.GD.N0067.d023924 m n hm hn).mpr hsmall)
  exact ⟨d, _root_.GD.N0232.N0720.N1226.d015576.d015579 m n hd.1, hd⟩

end
end GD.N0067

#print axioms _root_.GD.N0067.d023930
