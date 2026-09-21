import GD.Module1801
import GD.Module1543
import GD.Module1081
import GD.Module0812

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open scoped ENNReal

namespace GD.N0153.N0440

open _root_.GD.N0101.N0390

namespace N0773

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1220



theorem d029975 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
        (1 + _root_.GD.N0101.N0390.d029966 m n / 6) * _root_.GD.N0232.N0720.N1220.d017307 m n F w < _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  have hω := _root_.GD.N0101.N0390.d029969 m n hm hn
  apply (_root_.GD.N0232.N0720.N1220.d017314 m n hm hn (1 + _root_.GD.N0101.N0390.d029966 m n / 6)
    (by positivity)).mp
  apply lt_of_lt_of_le ?_ (_root_.GD.N0101.N0390.d029973 m n hm hn)
  exact (ENNReal.ofReal_lt_ofReal_iff (show 0 < 1 + _root_.GD.N0101.N0390.d029966 m n / 3 by positivity)).mpr
    (by linarith)



theorem d029976 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ C * _root_.GD.N0232.N0720.N1220.d017307 m n F w) ↔
      4 ≤ (m - 1) * (n - 1) :=
  (_root_.GD.N0232.N0720.N1220.d017315 m n hm hn).symm.trans
    (_root_.GD.N0067.d023923 m n hm hn)



theorem d029977 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∀ C : ℝ, 0 ≤ C → ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
        C * _root_.GD.N0232.N0720.N1220.d017307 m n F w < _root_.GD.N0232.N0720.N1220.d017301 m n F w) ↔
      (m = 2 ∧ n ≤ 4) ∨ (n = 2 ∧ m ≤ 4) := by
  classical
  have hdual := (_root_.GD.N0232.N0720.N1220.d017315 m n hm hn).not
  push Not at hdual
  exact hdual.symm.trans (_root_.GD.N0067.d023924 m n hm hn)

end N0773

namespace N0772

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0966



theorem d029978
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j) :
    ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
        (1 + _root_.GD.N0101.N0390.d029966 (sizes i) (sizes j) / 6) * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w <
          _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  have hω := _root_.GD.N0101.N0390.d029969 (sizes i) (sizes j) (hn i) (hn j)
  apply (_root_.GD.N0232.N0719.N0966.d012372 k sizes hk hn
    (1 + _root_.GD.N0101.N0390.d029966 (sizes i) (sizes j) / 6) (by positivity)).mp
  apply lt_of_lt_of_le ?_
    (_root_.GD.N0101.N0390.d029974 sizes hn i j hij)
  exact (ENNReal.ofReal_lt_ofReal_iff
    (show 0 < 1 + _root_.GD.N0101.N0390.d029966 (sizes i) (sizes j) / 3 by positivity)).mpr (by linarith)



theorem d029979
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w) ↔
      ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1) :=
  (_root_.GD.N0232.N0719.N0966.d012373 k sizes hk hn).symm.trans
    (_root_.GD.N0067.d023925 (by omega) sizes hn)



theorem d029980
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    (∀ C : ℝ, 0 ≤ C → ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
        C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w) ↔
      ∃ i j : Fin k, i ≠ j ∧ sizes i = 2 ∧ sizes j ≤ 4 :=
  (_root_.GD.N0232.N0719.N0966.d012374 k sizes hk hn).symm.trans
    (_root_.GD.N0067.d023927 (by omega) sizes hn)

end N0772

end GD.N0153.N0440

#print axioms _root_.GD.N0153.N0440.N0773.d029975
#print axioms _root_.GD.N0153.N0440.N0773.d029976
#print axioms _root_.GD.N0153.N0440.N0773.d029977
#print axioms _root_.GD.N0153.N0440.N0772.d029978
#print axioms _root_.GD.N0153.N0440.N0772.d029979
#print axioms _root_.GD.N0153.N0440.N0772.d029980
