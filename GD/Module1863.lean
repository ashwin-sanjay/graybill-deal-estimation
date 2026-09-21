import GD.Module1860
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0207
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1354
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0096.N0344

def d030558 (m n : ℕ) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ¬ ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) ∧
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e < _root_.GD.N0232.N0720.N1080.d014197 m n theta d

theorem d030559
    (m n : ℕ) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : Measurable d)
    (hfinite : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤)
    (hadm : _root_.GD.N0207.d030558 m n d) :
    ∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hd (hfinite _root_.GD.N0232.N0720.N1080.d014169)
  let p := hmem.toLp d
  have hprisk (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem).symm
  have hpfin : _root_.GD.N0232.N0720.N1159.d014637 m n p := fun theta => by
    rw [hprisk]
    exact hfinite theta
  have hstrong : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
    apply (_root_.GD.N0232.N0720.N1354.d018748 p hpfin).1
    intro q hq
    apply hadm
    refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n q, _root_.GD.N0232.N0720.N1214.d014266 m n q, ?_, ?_⟩
    · intro theta
      rw [_root_.GD.N0232.N0720.N1215.d014286, ← hprisk]
      exact (hq theta).le
    · refine ⟨_root_.GD.N0232.N0720.N1080.d014169, ?_⟩
      rw [_root_.GD.N0232.N0720.N1215.d014286, ← hprisk]
      exact hq _root_.GD.N0232.N0720.N1080.d014169
  intro e he hbelow theta
  have hemem : MemLp e 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n e he
      (ne_top_of_le_ne_top (hfinite _root_.GD.N0232.N0720.N1080.d014169) (hbelow _root_.GD.N0232.N0720.N1080.d014169))
  have hclass : hemem.toLp e = p := by
    apply hstrong
    intro eta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n eta e hemem, hprisk]
    exact hbelow eta
  have href : e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d := by
    filter_upwards [hemem.coeFn_toLp, hmem.coeFn_toLp] with omega heq hdq
    exact heq.symm.trans ((congrArg (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) => q omega)
      hclass).trans hdq)
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq href

theorem d030560
    (m n : ℕ) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n) (hadm : _root_.GD.N0207.d030558 m n d) :
    _root_.GD.N0096.N0344.d030491 m n d := by
  refine ⟨hd.1.1, ?_, hd.2, _root_.GD.N0207.d030559 m n hd.1.1 hd.2 hadm⟩
  intro g omega
  simpa only [_root_.GD.N0232.N0720.N1214.d014259,
    _root_.GD.N0232.N0719.N0946.d009229.d009244] using hd.1.2 g.shift g.d009239 g.d009240 omega

end
end GD.N0207

#print axioms _root_.GD.N0207.d030559
#print axioms _root_.GD.N0207.d030560
