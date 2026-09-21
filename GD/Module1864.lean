import GD.Module1862
import GD.Module1863
import GD.Module1417
import GD.Module1509
import GD.Module1506
import GD.Module1722
import GD.Module1543

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0207
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0096.N0344
open _root_.GD.N0207.N0451 _root_.GD.N0207.N0454 _root_.GD.N0207.N0452

theorem d030561
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    _root_.GD.N0232.N0720.N1256.d015548 m n d ≠ _root_.GD.N0232.N0720.N1256.d015549 m n := by
  intro hmin
  let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hv : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 m n := ENNReal.ofReal_toReal hfinite
  have hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    intro theta
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta d).mp
    rw [hv, ← hmin]
    exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta
  have hrep := _root_.GD.N0207.d030557 m n hm hn hd C hC hcap
  by_cases hsmall : m ≤ 3 ∨ n ≤ 3
  · apply _root_.GD.N0207.N0454.d023524 hm hn hsmall hC
    intro theta
    have h := hcap theta
    rwa [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta)] at h
  · have hm4 : 4 ≤ m := by omega
    have hn4 : 4 ≤ n := by omega
    have htwo : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
        ENNReal.ofReal (2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
      intro theta
      apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) 2 (by norm_num) theta d).mp
      have hle : _root_.GD.N0232.N0720.N1256.d015547 m n theta d ≤ _root_.GD.N0232.N0720.N1256.d015548 m n d :=
        le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta
      rw [hmin] at hle
      simpa using hle.trans (_root_.GD.N0098.d028729 m n
        (by omega) (by omega))
    apply _root_.GD.N0207.N0452.d023497 hm4 hn4
    intro p hp
    have h := _root_.GD.N0207.N0451.d022703 hm hn
      ((_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst)
      (fun x => _root_.GD.N0232.N0720.N1328.d014758 (_root_.GD.N0232.N0720.N1436.d013211 hm)
        (_root_.GD.N0232.N0720.N1436.d013212 hn) x.1) hrep (by norm_num : (0 : ℝ) ≤ 2) htwo ⟨p, hp⟩
    change (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 - p) ^ 2
      ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) ≤ (2 - 1) * p * (1 - p) at h
    norm_num at h
    exact h

theorem d030562
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    ¬ ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n,
      _root_.GD.N0207.d030558 m n d ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  rintro ⟨d, hd, hadm, hmin⟩
  let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hv : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 m n := ENNReal.ofReal_toReal hfinite
  have hcap : ∀ theta, _root_.GD.N0232.N0720.N1256.d015547 m n theta d ≤ ENNReal.ofReal C := by
    intro theta
    rw [hv, ← hmin]
    exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta
  have hdFinite : d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n :=
    ⟨hd, _root_.GD.N0232.N0720.N1256.d015558 m n (by omega) C hC d hcap⟩
  exact _root_.GD.N0207.d030561 m n hm hn hfinite
    (_root_.GD.N0207.d030560 m n hdFinite hadm) hmin

theorem d030563
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdesign : 4 ≤ (m - 1) * (n - 1)) :
    ¬ ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015546 m n,
      _root_.GD.N0207.d030558 m n d ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n :=
  _root_.GD.N0207.d030562 m n hm hn
    ((_root_.GD.N0067.d023923 m n hm hn).2 hdesign)

end
end GD.N0207

#print axioms _root_.GD.N0207.d030561
#print axioms _root_.GD.N0207.d030562
#print axioms _root_.GD.N0207.d030563
