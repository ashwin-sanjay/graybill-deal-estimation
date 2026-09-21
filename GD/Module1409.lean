import GD.Module1109
import GD.Module0932

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0206.N0448
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

variable (m n : ℕ)


def d022618 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ¬ ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) ∧
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e < _root_.GD.N0232.N0720.N1080.d014197 m n theta d


def d022619 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d

theorem d022620 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 d ≠ ⊤)
    (ha : _root_.GD.N0206.N0448.d022618 m n d) : _root_.GD.N0206.N0448.d022619 m n d := by
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hd hfinite
  let p := hmem.toLp d
  have hp : _root_.GD.N0232.N0720.N1036.d014669 m n p := by
    intro q hq theta
    have hweak (eta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n eta (_root_.GD.N0232.N0720.N1214.d014265 m n q) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n eta d := by
      rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014198 m n eta d hmem]
      exact hq eta
    have heq : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n q) =
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
      apply le_antisymm (hweak theta)
      exact not_lt.mp (fun hlt => ha ⟨_root_.GD.N0232.N0720.N1214.d014265 m n q,
        _root_.GD.N0232.N0720.N1214.d014266 m n q, hweak, theta, hlt⟩)
    simpa only [_root_.GD.N0232.N0720.N1215.d014286,
      _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem] using heq
  have hstrong := _root_.GD.N0232.N0720.N1478.d017820
    m n hp
  intro e he hbelow theta
  have hemem : MemLp e 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n e he
      (ne_top_of_le_ne_top hfinite (hbelow _root_.GD.N0232.N0720.N1080.d014169))
  have hclass : hemem.toLp e = hmem.toLp d := by
    apply hstrong
    intro eta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n eta e hemem,
      ← _root_.GD.N0232.N0720.N1080.d014198 m n eta d hmem]
    exact hbelow eta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    ((MemLp.toLp_eq_toLp_iff hemem hmem).mp hclass)

theorem d022621 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (ht : _root_.GD.N0206.N0448.d022619 m n d) : _root_.GD.N0206.N0448.d022618 m n d := by
  rintro ⟨e, he, hweak, theta, hstrict⟩
  have heq := _root_.GD.N0232.N0720.N1159.d014662 m n theta (ht e he hweak theta)
  exact (ne_of_lt hstrict) heq

theorem d022622 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 d ≠ ⊤) :
    _root_.GD.N0206.N0448.d022618 m n d ↔ _root_.GD.N0206.N0448.d022619 m n d :=
  ⟨_root_.GD.N0206.N0448.d022620 m n hd hfinite, _root_.GD.N0206.N0448.d022621 m n⟩

end
end GD.N0206.N0448

#print axioms _root_.GD.N0206.N0448.d022620
#print axioms _root_.GD.N0206.N0448.d022621
#print axioms _root_.GD.N0206.N0448.d022622
