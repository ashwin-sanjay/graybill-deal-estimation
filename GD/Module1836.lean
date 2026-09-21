import GD.Module1830

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0034.N0293

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0046.N0305

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030260
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0046.N0305.d030204 m n hp) ∈
      _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro η
  let θ := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ η
  have hη : _root_.GD.N0232.N0720.N1215.d014272 g θ = η := by simp [θ]
  rw [← hη, _root_.GD.N0232.N0720.N1159.d014643,
    _root_.GD.N0232.N0720.N1257.d015512, _root_.GD.N0232.N0720.N1215.d014293]
  constructor
  · calc
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤
          ENNReal.ofReal (g.d009239 ^ 2) *
            (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) :=
        mul_le_mul' le_rfl (hp θ).1
      _ = _root_.GD.N0232.N0720.N1256.d015549 m n *
          ENNReal.ofReal (g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
        rw [ENNReal.ofReal_mul (sq_nonneg g.d009239)]
        ac_rfl
  · exact mul_le_mul' le_rfl (hp θ).2

theorem d030261
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hmove : _root_.GD.N0232.N0720.N1159.d014642 m n g p
      (_root_.GD.N0046.N0305.d030204 m n hp) ≠ p) :
    (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty := by
  have hq := _root_.GD.N0034.N0293.d030260 m n hm hn g hp
  have hs := _root_.GD.N0046.N0305.d030210 m n hp hq hmove.symm
  exact (_root_.GD.N0046.N0305.d030214 m n hm hn).1
    (_root_.GD.N0232.N0720.N1226.d015583 m n _ hs)

theorem d030262
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hmove : _root_.GD.N0232.N0720.N1159.d014642 m n g p
      (_root_.GD.N0046.N0305.d030204 m n hp) ≠ p) :
    _root_.GD.N0232.N0720.N1226.d015578 m n :=
  (_root_.GD.N0046.N0305.d030214 m n hm hn).2
    (_root_.GD.N0034.N0293.d030261 m n hm hn g hp hmove)

theorem d030263
    (hsub : (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton)
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0046.N0305.d030204 m n hp) = p :=
  hsub (_root_.GD.N0034.N0293.d030260 m n hm hn g hp) hp

end
end GD.N0034.N0293

#print axioms _root_.GD.N0034.N0293.d030260
#print axioms _root_.GD.N0034.N0293.d030261
#print axioms _root_.GD.N0034.N0293.d030262
#print axioms _root_.GD.N0034.N0293.d030263
