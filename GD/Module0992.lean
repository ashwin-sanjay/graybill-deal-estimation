import GD.Module0907
import GD.Module0972

open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1466

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131
open _root_.GD.N0145
open _root_.GD.N0120
open _root_.GD.N0141
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1085

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d015732
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : ℝ :=
  U.emitted.table.d008715
    (_root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn))
    (fun _ ↦ (U.emitted.ledger.inversePower : ℝ))

theorem d015733
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U < (U.M : ℝ) := by
  let e : ℝ := 0
  have he : e ∈ Icc (0 : ℝ) 1 := by simp [e]
  let A := U.realized e he
  have hAemitted : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have hArho : A.rho = _root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn) := by
    simpa [A] using U.realized_rho e he
  have hstrict := _root_.GD.N0145.d014119 A hArho
  rw [_root_.GD.N0145.d014117, hArho, hAemitted] at hstrict
  rw [_root_.GD.N0232.N0720.N1466.d015732]
  exact hstrict.trans_eq (by exact_mod_cast U.M_eq.symm)

theorem d015734
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 ≤
      _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U := by
  let A := U.realized e he
  have hAemitted : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have hArho : A.rho = _root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn) := by
    simpa [A] using U.realized_rho e he
  have hApower : A.power = _root_.GD.N0131.d008767 (_root_.GD.N0134.d006543 m n hm hn) e := by
    simpa [A] using U.realized_power e he
  have hbridge := U.d014131 e he
  change
    _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008714 A.rho A.carrier ∧
      _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008715 A.rho A.power at hbridge
  have hmono := _root_.GD.N0145.d014118 A
  calc
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 =
      A.emitted.table.d008715 A.rho A.power := by
        rw [← hAemitted]
        exact hbridge.2
    _ ≤ _root_.GD.N0145.d014117 A := hmono
    _ = _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U := by
      simp only [_root_.GD.N0145.d014117, _root_.GD.N0232.N0720.N1466.d015732]
      rw [hAemitted, hArho]

def d015735
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : ℝ :=
  _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U / (U.M : ℝ)

theorem d015736
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U := by
  have hM : (0 : ℝ) < U.M := by exact_mod_cast U.M_pos
  have hB : 0 ≤ _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U := by
    let e : ℝ := 0
    have he : e ∈ Icc (0 : ℝ) 1 := by simp [e]
    let A := U.realized e he
    have hAemitted : A.emitted = U.emitted := by
      simpa [A] using U.realized_emitted e he
    have hArho : A.rho = _root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn) := by
      simpa [A] using U.realized_rho e he
    have hmono := _root_.GD.N0145.d014118 A
    have hactual : 0 ≤ A.emitted.table.d008715 A.rho A.power :=
      A.emitted.table.d008722 A.rho A.carrier A.power
        A.emitted.ledger.gradientBound A.emitted.ledger.carrierBound
        A.emitted.ledger.inversePower A.envelope
    calc
      0 ≤ A.emitted.table.d008715 A.rho A.power := hactual
      _ ≤ _root_.GD.N0145.d014117 A := hmono
      _ = _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U := by
        simp only [_root_.GD.N0145.d014117, _root_.GD.N0232.N0720.N1466.d015732]
        rw [hAemitted, hArho]
  exact div_nonneg hB hM.le

theorem d015737
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U < 1 := by
  have hM : (0 : ℝ) < U.M := by exact_mod_cast U.M_pos
  rw [_root_.GD.N0232.N0720.N1466.d015735, div_lt_one hM]
  exact _root_.GD.N0232.N0720.N1466.d015733 m n hm hn U

theorem d015738
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 ≤
      _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * (U.M : ℝ) := by
  have hM : (U.M : ℝ) ≠ 0 := by exact_mod_cast U.M_pos.ne'
  calc
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 ≤
      _root_.GD.N0232.N0720.N1466.d015732 m n hm hn U :=
        _root_.GD.N0232.N0720.N1466.d015734 m n hm hn U e he
    _ = _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * (U.M : ℝ) := by
      unfold _root_.GD.N0232.N0720.N1466.d015735
      field_simp

end

end GD.N0232.N0720.N1466
