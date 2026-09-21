import GD.Module0200
import Mathlib.Data.Fin.VecNotation










open Set
open scoped ContDiff

namespace GD.N0232.N0720.N1351

noncomputable section

open _root_.GD.N0232.N0720.N1352

abbrev d002812 := Fin 3 → ℝ

def d002813 (i : Fin 3) : _root_.GD.N0232.N0720.N1351.d002812 := Pi.single i 1

def d002814 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1351.d002812 := ![x 2, x 3, _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2]

def d002815 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] _root_.GD.N0232.N0720.N1351.d002812 :=
  ContinuousLinearMap.pi ![_root_.GD.N0232.N0720.N1352.d002741 2, _root_.GD.N0232.N0720.N1352.d002741 3, _root_.GD.N0232.N0720.N1352.d002742 x • _root_.GD.N0232.N0720.N1352.d002743]

theorem d002816 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    HasFDerivAt (fun y : _root_.GD.N0232.N0720.N1352.d002739 ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 / 2)
      (_root_.GD.N0232.N0720.N1352.d002742 x • _root_.GD.N0232.N0720.N1352.d002743) x := by
  have h := ((_root_.GD.N0232.N0720.N1352.d002746 x).pow 2).mul_const ((1 / 2 : ℝ))
  have hc : (1 / 2 : ℝ) * (2 * _root_.GD.N0232.N0720.N1352.d002742 x) = _root_.GD.N0232.N0720.N1352.d002742 x := by ring
  simpa [div_eq_mul_inv, nsmul_eq_mul, smul_smul, hc] using h


theorem d002817 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    HasFDerivAt _root_.GD.N0232.N0720.N1351.d002814 (_root_.GD.N0232.N0720.N1351.d002815 x) x := by
  unfold _root_.GD.N0232.N0720.N1351.d002815
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1351.d002814, _root_.GD.N0232.N0720.N1352.d002741] using hasFDerivAt_apply (2 : Fin 4) x
  · simpa [_root_.GD.N0232.N0720.N1351.d002814, _root_.GD.N0232.N0720.N1352.d002741] using hasFDerivAt_apply (3 : Fin 4) x
  · simpa [_root_.GD.N0232.N0720.N1351.d002814] using _root_.GD.N0232.N0720.N1351.d002816 x

theorem d002818 : ContDiff ℝ ∞ _root_.GD.N0232.N0720.N1351.d002814 := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1351.d002814, _root_.GD.N0232.N0720.N1352.d002742] <;> fun_prop

def d002819 (g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ) (i : Fin 3) (p : _root_.GD.N0232.N0720.N1351.d002812) : ℝ :=
  fderiv ℝ g p (_root_.GD.N0232.N0720.N1351.d002813 i)

def d002820 (g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ) (i : Fin 3) : _root_.GD.N0232.N0720.N1352.d002739 → ℝ :=
  _root_.GD.N0232.N0720.N1351.d002819 g i ∘ _root_.GD.N0232.N0720.N1351.d002814

private theorem d002821 (x v : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1351.d002815 x v =
      v 2 • _root_.GD.N0232.N0720.N1351.d002813 0 + v 3 • _root_.GD.N0232.N0720.N1351.d002813 1 +
        (_root_.GD.N0232.N0720.N1352.d002742 x * (v 1 - v 0)) • _root_.GD.N0232.N0720.N1351.d002813 2 := by
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1351.d002815, _root_.GD.N0232.N0720.N1351.d002813, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002743, smul_eq_mul]



theorem d002822 {g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hg : DifferentiableAt ℝ g (_root_.GD.N0232.N0720.N1351.d002814 x)) :
    HasFDerivAt (g ∘ _root_.GD.N0232.N0720.N1351.d002814)
      (_root_.GD.N0232.N0720.N1352.d002750 (_root_.GD.N0232.N0720.N1351.d002820 g 0) (_root_.GD.N0232.N0720.N1351.d002820 g 1) (_root_.GD.N0232.N0720.N1351.d002820 g 2) x) x := by
  apply (hg.hasFDerivAt.comp x (_root_.GD.N0232.N0720.N1351.d002817 x)).congr_fderiv
  ext v
  rw [ContinuousLinearMap.comp_apply, _root_.GD.N0232.N0720.N1351.d002821,
    _root_.GD.N0232.N0720.N1352.d002751]
  simp only [map_add, map_smul, smul_eq_mul]
  simp only [_root_.GD.N0232.N0720.N1351.d002820, _root_.GD.N0232.N0720.N1351.d002819, Function.comp_apply]
  ring

theorem d002823 {t : Set _root_.GD.N0232.N0720.N1351.d002812} (ht : IsOpen t)
    {g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ} (hg : ContDiffOn ℝ ∞ g t) (i : Fin 3) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1351.d002819 g i) t := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ g) t :=
    hg.fderiv_of_isOpen ht (m := ∞) (by simp)
  exact hfd.clm_apply contDiffOn_const




def d002824 {s : Set _root_.GD.N0232.N0720.N1352.d002739} {t : Set _root_.GD.N0232.N0720.N1351.d002812} (ht : IsOpen t)
    (g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ) (hg : ContDiffOn ℝ ∞ g t) (hmap : MapsTo _root_.GD.N0232.N0720.N1351.d002814 s t) :
    _root_.GD.N0232.N0720.N1352.d002752 s where
  G := g ∘ _root_.GD.N0232.N0720.N1351.d002814
  Gz := _root_.GD.N0232.N0720.N1351.d002820 g 0
  Gw := _root_.GD.N0232.N0720.N1351.d002820 g 1
  Gu := _root_.GD.N0232.N0720.N1351.d002820 g 2
  smooth_G := hg.comp _root_.GD.N0232.N0720.N1351.d002818.contDiffOn hmap
  smooth_Gz := (_root_.GD.N0232.N0720.N1351.d002823 ht hg 0).comp _root_.GD.N0232.N0720.N1351.d002818.contDiffOn hmap
  smooth_Gw := (_root_.GD.N0232.N0720.N1351.d002823 ht hg 1).comp _root_.GD.N0232.N0720.N1351.d002818.contDiffOn hmap
  smooth_Gu := (_root_.GD.N0232.N0720.N1351.d002823 ht hg 2).comp _root_.GD.N0232.N0720.N1351.d002818.contDiffOn hmap
  first_jet := fun x hx ↦ _root_.GD.N0232.N0720.N1351.d002822
    ((hg.contDiffAt (ht.mem_nhds (hmap hx))).differentiableAt (by simp))

end

#print axioms _root_.GD.N0232.N0720.N1351.d002817
#print axioms _root_.GD.N0232.N0720.N1351.d002822
#print axioms _root_.GD.N0232.N0720.N1351.d002824

end GD.N0232.N0720.N1351
