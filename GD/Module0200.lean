import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


















open Filter Set Topology
open scoped ContDiff

namespace GD.N0232.N0720.N1352

noncomputable section

abbrev d002739 := Fin 4 → ℝ

def d002740 (i : Fin 4) : _root_.GD.N0232.N0720.N1352.d002739 := Pi.single i 1

def d002741 (i : Fin 4) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def d002742 (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ := x 1 - x 0

def d002743 : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ := _root_.GD.N0232.N0720.N1352.d002741 1 - _root_.GD.N0232.N0720.N1352.d002741 0

@[simp] theorem d002744 (i : Fin 4) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002741 i x = x i := rfl

@[simp] theorem d002745 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002743 x = _root_.GD.N0232.N0720.N1352.d002742 x := rfl

theorem d002746 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    HasFDerivAt _root_.GD.N0232.N0720.N1352.d002742 _root_.GD.N0232.N0720.N1352.d002743 x := by
  exact (hasFDerivAt_apply 1 x).sub (hasFDerivAt_apply 0 x)

theorem d002747 : Differentiable ℝ _root_.GD.N0232.N0720.N1352.d002742 :=
  fun x ↦ (_root_.GD.N0232.N0720.N1352.d002746 x).differentiableAt

theorem d002748 : ContDiff ℝ ∞ _root_.GD.N0232.N0720.N1352.d002742 := by
  unfold _root_.GD.N0232.N0720.N1352.d002742
  fun_prop

def d002749 (f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (i : Fin 4) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  fderiv ℝ f x (_root_.GD.N0232.N0720.N1352.d002740 i)

def d002750 (Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ :=
  Gz x • _root_.GD.N0232.N0720.N1352.d002741 2 + Gw x • _root_.GD.N0232.N0720.N1352.d002741 3 +
    (_root_.GD.N0232.N0720.N1352.d002742 x * Gu x) • _root_.GD.N0232.N0720.N1352.d002743

theorem d002751 (Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x v : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002750 Gz Gw Gu x v =
      Gz x * v 2 + Gw x * v 3 + _root_.GD.N0232.N0720.N1352.d002742 x * Gu x * (v 1 - v 0) := by
  simp [_root_.GD.N0232.N0720.N1352.d002750, _root_.GD.N0232.N0720.N1352.d002743, smul_eq_mul]



structure d002752 (s : Set _root_.GD.N0232.N0720.N1352.d002739) where
  G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  Gz : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  Gw : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ
  smooth_G : ContDiffOn ℝ ∞ G s
  smooth_Gz : ContDiffOn ℝ ∞ Gz s
  smooth_Gw : ContDiffOn ℝ ∞ Gw s
  smooth_Gu : ContDiffOn ℝ ∞ Gu s
  first_jet : ∀ x ∈ s, HasFDerivAt G (_root_.GD.N0232.N0720.N1352.d002750 Gz Gw Gu x) x

def d002753 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 :=
  _root_.GD.N0232.N0720.N1352.d002740 0 + (_root_.GD.N0232.N0720.N1352.d002742 x * G x) • _root_.GD.N0232.N0720.N1352.d002740 2

def d002754 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 :=
  _root_.GD.N0232.N0720.N1352.d002740 1 + (_root_.GD.N0232.N0720.N1352.d002742 x * (G x - 1)) • _root_.GD.N0232.N0720.N1352.d002740 3

def d002755 (f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 :=
  f x • _root_.GD.N0232.N0720.N1352.d002740 2 + g x • _root_.GD.N0232.N0720.N1352.d002740 3

def d002756 (G Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  Gu x + (G x - 1) * Gw x

def d002757 (G Gz Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  -Gu x + G x * Gz x

def d002758 (G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) : _root_.GD.N0232.N0720.N1352.d002739 → _root_.GD.N0232.N0720.N1352.d002739 :=
  _root_.GD.N0232.N0720.N1352.d002755
    (fun x ↦ -G x - _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x)
    (fun x ↦ 1 - G x + _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x)

def d002759 (G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  3 * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x -
    _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) 0 x +
    _root_.GD.N0232.N0720.N1352.d002742 x ^ 3 *
      (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x * Gz x - _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x * Gw x -
        G x * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) 2 x)

def d002760 (G Gz _Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  -3 * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x +
    _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) 0 x +
    _root_.GD.N0232.N0720.N1352.d002742 x ^ 3 * G x * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) 2 x

def d002761 (G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) : _root_.GD.N0232.N0720.N1352.d002739 → _root_.GD.N0232.N0720.N1352.d002739 :=
  _root_.GD.N0232.N0720.N1352.d002755 (_root_.GD.N0232.N0720.N1352.d002759 G Gz Gw Gu) (_root_.GD.N0232.N0720.N1352.d002760 G Gz Gw Gu)

def d002762 (G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  G x ^ 2 * Gz x + (1 - G x) ^ 2 * Gw x - Gu x

private theorem d002763 {G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {G' : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ}
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hG : HasFDerivAt G G' x) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002753 G)
      ((_root_.GD.N0232.N0720.N1352.d002742 x • G' + G x • _root_.GD.N0232.N0720.N1352.d002743).smulRight (_root_.GD.N0232.N0720.N1352.d002740 2)) x := by
  simpa [_root_.GD.N0232.N0720.N1352.d002753] using
    (hasFDerivAt_const (_root_.GD.N0232.N0720.N1352.d002740 0) x).add
      (((_root_.GD.N0232.N0720.N1352.d002746 x).mul hG).smul_const (_root_.GD.N0232.N0720.N1352.d002740 2))

private theorem d002764 {G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {G' : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ}
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hG : HasFDerivAt G G' x) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002754 G)
      ((_root_.GD.N0232.N0720.N1352.d002742 x • G' + (G x - 1) • _root_.GD.N0232.N0720.N1352.d002743).smulRight (_root_.GD.N0232.N0720.N1352.d002740 3)) x := by
  simpa [_root_.GD.N0232.N0720.N1352.d002754] using
    (hasFDerivAt_const (_root_.GD.N0232.N0720.N1352.d002740 1) x).add
      (((_root_.GD.N0232.N0720.N1352.d002746 x).mul (hG.sub_const 1)).smul_const (_root_.GD.N0232.N0720.N1352.d002740 3))

private theorem d002765
    {f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {f' g' : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002755 f g)
      (f'.smulRight (_root_.GD.N0232.N0720.N1352.d002740 2) + g'.smulRight (_root_.GD.N0232.N0720.N1352.d002740 3)) x :=
  (hf.smul_const (_root_.GD.N0232.N0720.N1352.d002740 2)).add (hg.smul_const (_root_.GD.N0232.N0720.N1352.d002740 3))


theorem d002766
    {G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hG : HasFDerivAt G (_root_.GD.N0232.N0720.N1352.d002750 Gz Gw Gu x) x) :
    VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 G) (_root_.GD.N0232.N0720.N1352.d002754 G) x =
      _root_.GD.N0232.N0720.N1352.d002758 G Gz Gw Gu x := by
  rw [VectorField.lieBracket, (_root_.GD.N0232.N0720.N1352.d002763 hG).fderiv,
    (_root_.GD.N0232.N0720.N1352.d002764 hG).fderiv]
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0720.N1352.d002754, _root_.GD.N0232.N0720.N1352.d002758, _root_.GD.N0232.N0720.N1352.d002755, _root_.GD.N0232.N0720.N1352.d002756, _root_.GD.N0232.N0720.N1352.d002757,
      _root_.GD.N0232.N0720.N1352.d002750, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0720.N1352.d002742, smul_eq_mul] <;> ring

private theorem d002767 {f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : _root_.GD.N0232.N0720.N1352.d002739) :
    fderiv ℝ (_root_.GD.N0232.N0720.N1352.d002755 f g) x v =
      (fderiv ℝ f x v) • _root_.GD.N0232.N0720.N1352.d002740 2 + (fderiv ℝ g x v) • _root_.GD.N0232.N0720.N1352.d002740 3 := by
  rw [(_root_.GD.N0232.N0720.N1352.d002765 hf.hasFDerivAt hg.hasFDerivAt).fderiv]
  rfl

private theorem d002768
    {G Gz Gw Gu f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hG : HasFDerivAt G (_root_.GD.N0232.N0720.N1352.d002750 Gz Gw Gu x) x)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 G) (_root_.GD.N0232.N0720.N1352.d002755 f g) x =
      (_root_.GD.N0232.N0720.N1352.d002749 f 0 x + _root_.GD.N0232.N0720.N1352.d002742 x * G x * _root_.GD.N0232.N0720.N1352.d002749 f 2 x -
        _root_.GD.N0232.N0720.N1352.d002742 x * (f x * Gz x + g x * Gw x)) • _root_.GD.N0232.N0720.N1352.d002740 2 +
      (_root_.GD.N0232.N0720.N1352.d002749 g 0 x + _root_.GD.N0232.N0720.N1352.d002742 x * G x * _root_.GD.N0232.N0720.N1352.d002749 g 2 x) • _root_.GD.N0232.N0720.N1352.d002740 3 := by
  rw [VectorField.lieBracket, _root_.GD.N0232.N0720.N1352.d002767 hf hg,
    (_root_.GD.N0232.N0720.N1352.d002763 hG).fderiv]
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0720.N1352.d002755, _root_.GD.N0232.N0720.N1352.d002750, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002741,
      _root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0720.N1352.d002749, map_add, map_smul, smul_eq_mul]
  ring

private theorem d002769 {f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ f y + g y) i x = _root_.GD.N0232.N0720.N1352.d002749 f i x + _root_.GD.N0232.N0720.N1352.d002749 g i x := by
  rw [_root_.GD.N0232.N0720.N1352.d002749, fderiv_fun_add hf hg]
  rfl

private theorem d002770 {f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ f y - g y) i x = _root_.GD.N0232.N0720.N1352.d002749 f i x - _root_.GD.N0232.N0720.N1352.d002749 g i x := by
  rw [_root_.GD.N0232.N0720.N1352.d002749, fderiv_fun_sub hf hg]
  rfl

private theorem d002771 {f g : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ f y * g y) i x =
      f x * _root_.GD.N0232.N0720.N1352.d002749 g i x + g x * _root_.GD.N0232.N0720.N1352.d002749 f i x := by
  rw [_root_.GD.N0232.N0720.N1352.d002749, fderiv_fun_mul hf hg]
  simp [_root_.GD.N0232.N0720.N1352.d002749, smul_eq_mul]

private theorem d002772 (x : _root_.GD.N0232.N0720.N1352.d002739) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2) i x =
      2 * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1352.d002743 (_root_.GD.N0232.N0720.N1352.d002740 i) := by
  rw [_root_.GD.N0232.N0720.N1352.d002749, ((_root_.GD.N0232.N0720.N1352.d002746 x).pow 2).fderiv]
  simp [smul_eq_mul]

private theorem d002773 (f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ -f y) i x = -_root_.GD.N0232.N0720.N1352.d002749 f i x := by
  simp [_root_.GD.N0232.N0720.N1352.d002749, fderiv_fun_neg]

private theorem d002774 (f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (c : ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) (i : Fin 4) :
    _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ c - f y) i x = -_root_.GD.N0232.N0720.N1352.d002749 f i x := by
  simp [_root_.GD.N0232.N0720.N1352.d002749, fderiv_const_sub]



theorem d002775
    {G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hG : HasFDerivAt G (_root_.GD.N0232.N0720.N1352.d002750 Gz Gw Gu x) x)
    (hK : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) x)
    (hL : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) x) :
    VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 G) (_root_.GD.N0232.N0720.N1352.d002758 G Gz Gw Gu) x =
      _root_.GD.N0232.N0720.N1352.d002761 G Gz Gw Gu x := by
  have hd := (_root_.GD.N0232.N0720.N1352.d002746 x).differentiableAt
  have hsq : DifferentiableAt ℝ (fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2) x := hd.pow 2
  have hf : DifferentiableAt ℝ
      (fun y ↦ -G y - _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu y) x := by
    exact hG.differentiableAt.fun_neg.fun_sub (hsq.fun_mul hK)
  have hg : DifferentiableAt ℝ
      (fun y ↦ 1 - G y + _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu y) x := by
    exact (hG.differentiableAt.const_sub 1).fun_add (hsq.fun_mul hL)
  rw [_root_.GD.N0232.N0720.N1352.d002758, _root_.GD.N0232.N0720.N1352.d002768 hG hf hg]
  have hG0 : _root_.GD.N0232.N0720.N1352.d002749 G 0 x = -_root_.GD.N0232.N0720.N1352.d002742 x * Gu x := by
    simp [_root_.GD.N0232.N0720.N1352.d002749, hG.fderiv, _root_.GD.N0232.N0720.N1352.d002750, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002740,
      smul_eq_mul]
  have hG2 : _root_.GD.N0232.N0720.N1352.d002749 G 2 x = Gz x := by
    simp [_root_.GD.N0232.N0720.N1352.d002749, hG.fderiv, _root_.GD.N0232.N0720.N1352.d002750, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002740,
      smul_eq_mul]
  have hfdir (i : Fin 4) :
      _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ -G y - _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu y) i x =
        -_root_.GD.N0232.N0720.N1352.d002749 G i x - (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) i x +
          _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x * (2 * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1352.d002743 (_root_.GD.N0232.N0720.N1352.d002740 i))) := by
    rw [_root_.GD.N0232.N0720.N1352.d002770 (f := fun y ↦ -G y)
        (g := fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu y)
        hG.differentiableAt.neg (hsq.mul hK), _root_.GD.N0232.N0720.N1352.d002773,
      _root_.GD.N0232.N0720.N1352.d002771 hsq hK, _root_.GD.N0232.N0720.N1352.d002772]
  have hgdir (i : Fin 4) :
      _root_.GD.N0232.N0720.N1352.d002749 (fun y ↦ 1 - G y + _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu y) i x =
        -_root_.GD.N0232.N0720.N1352.d002749 G i x + (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 * _root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) i x +
          _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x * (2 * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1352.d002743 (_root_.GD.N0232.N0720.N1352.d002740 i))) := by
    rw [_root_.GD.N0232.N0720.N1352.d002769 (f := fun y ↦ 1 - G y)
        (g := fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu y)
        (hG.differentiableAt.const_sub 1) (hsq.mul hL),
      _root_.GD.N0232.N0720.N1352.d002774, _root_.GD.N0232.N0720.N1352.d002771 hsq hL, _root_.GD.N0232.N0720.N1352.d002772]
  simp only [hfdir, hgdir, hG0, hG2]
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1352.d002761, _root_.GD.N0232.N0720.N1352.d002759, _root_.GD.N0232.N0720.N1352.d002760, _root_.GD.N0232.N0720.N1352.d002755,
      _root_.GD.N0232.N0720.N1352.d002756, _root_.GD.N0232.N0720.N1352.d002757, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul] <;> ring

private theorem d002776 {f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hx : _root_.GD.N0232.N0720.N1352.d002742 x = 0) (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 2 * f y) (0 : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ) x := by
  convert! ((_root_.GD.N0232.N0720.N1352.d002746 x).pow 2).fun_mul hf.hasFDerivAt using 1
  simp [hx]

private theorem d002777 {f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hx : _root_.GD.N0232.N0720.N1352.d002742 x = 0) (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1352.d002742 y ^ 3 * f y) (0 : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ) x := by
  convert! ((_root_.GD.N0232.N0720.N1352.d002746 x).pow 3).fun_mul hf.hasFDerivAt using 1
  simp [hx]

private theorem d002778 {f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hx : _root_.GD.N0232.N0720.N1352.d002742 x = 0) (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    HasFDerivAt (fun y ↦ c * _root_.GD.N0232.N0720.N1352.d002742 y * f y)
      ((c * f x) • _root_.GD.N0232.N0720.N1352.d002743) x := by
  convert! ((_root_.GD.N0232.N0720.N1352.d002746 x).const_mul c).fun_mul hf.hasFDerivAt using 1
  simp [hx, smul_smul, mul_comm]



theorem d002779
    {G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hx : _root_.GD.N0232.N0720.N1352.d002742 x = 0)
    (hG : DifferentiableAt ℝ G x)
    (hGz : DifferentiableAt ℝ Gz x) (hGw : DifferentiableAt ℝ Gw x)
    (hK : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) x)
    (hL : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) x)
    (hK0 : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) 0) x)
    (hK2 : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002756 G Gw Gu) 2) x)
    (hL0 : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) 0) x)
    (hL2 : DifferentiableAt ℝ (_root_.GD.N0232.N0720.N1352.d002749 (_root_.GD.N0232.N0720.N1352.d002757 G Gz Gu) 2) x) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002761 G Gz Gw Gu)
      (((3 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x) • _root_.GD.N0232.N0720.N1352.d002743).smulRight (_root_.GD.N0232.N0720.N1352.d002740 2) +
        ((-3 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x) • _root_.GD.N0232.N0720.N1352.d002743).smulRight (_root_.GD.N0232.N0720.N1352.d002740 3)) x := by
  have hR := ((hK.fun_mul hGz).fun_sub (hL.fun_mul hGw)).fun_sub (hG.fun_mul hK2)
  have hZ : HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002759 G Gz Gw Gu)
      ((3 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x) • _root_.GD.N0232.N0720.N1352.d002743) x := by
    convert! ((_root_.GD.N0232.N0720.N1352.d002778 hx hK 3).fun_sub
        (_root_.GD.N0232.N0720.N1352.d002776 hx hK0)).fun_add
          (_root_.GD.N0232.N0720.N1352.d002777 hx hR)
      using 1
    simp
  have hW : HasFDerivAt (_root_.GD.N0232.N0720.N1352.d002760 G Gz Gw Gu)
      ((-3 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x) • _root_.GD.N0232.N0720.N1352.d002743) x := by
    convert! ((_root_.GD.N0232.N0720.N1352.d002778 hx hL (-3)).fun_add
        (_root_.GD.N0232.N0720.N1352.d002776 hx hL0)).fun_add
          (_root_.GD.N0232.N0720.N1352.d002777 hx (hG.fun_mul hL2))
      using 1
    · ext y
      simp only [_root_.GD.N0232.N0720.N1352.d002760]
      ring
    · simp
  exact _root_.GD.N0232.N0720.N1352.d002765 hZ hW

private theorem d002780 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    {f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} (hf : ContDiffOn ℝ ∞ f s) (i : Fin 4) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002749 f i) s := by
  intro x hx
  have hfat : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hs.mem_nhds hx)
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    hfat.fderiv_right (m := ∞) (by simp)
  exact (hfd.clm_apply contDiffAt_const).contDiffWithinAt

private theorem d002781 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (c : _root_.GD.N0232.N0720.N1352.d002752 s) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002756 c.G c.Gw c.Gu) s := by
  exact c.smooth_Gu.add ((c.smooth_G.sub contDiffOn_const).mul c.smooth_Gw)

private theorem d002782 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (c : _root_.GD.N0232.N0720.N1352.d002752 s) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002757 c.G c.Gz c.Gu) s := by
  exact c.smooth_Gu.neg.add (c.smooth_G.mul c.smooth_Gz)

private theorem d002783 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    {f : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} (hf : ContDiffOn ℝ ∞ f s) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)

private theorem d002784 {V W W' : _root_.GD.N0232.N0720.N1352.d002739 → _root_.GD.N0232.N0720.N1352.d002739} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hW : W =ᶠ[𝓝 x] W') :
    VectorField.lieBracket ℝ V W x = VectorField.lieBracket ℝ V W' x := by
  simp only [VectorField.lieBracket, hW.fderiv_eq, hW.self_of_nhds]

private theorem d002785 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    (c : _root_.GD.N0232.N0720.N1352.d002752 s) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) :
    VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G)
      (VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G) (_root_.GD.N0232.N0720.N1352.d002754 c.G)) x =
        _root_.GD.N0232.N0720.N1352.d002761 c.G c.Gz c.Gw c.Gu x := by
  have heq : VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G) (_root_.GD.N0232.N0720.N1352.d002754 c.G) =ᶠ[𝓝 x]
      _root_.GD.N0232.N0720.N1352.d002758 c.G c.Gz c.Gw c.Gu := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact _root_.GD.N0232.N0720.N1352.d002766 (c.first_jet y hy)
  rw [_root_.GD.N0232.N0720.N1352.d002784 heq]
  exact _root_.GD.N0232.N0720.N1352.d002775 (c.first_jet x hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002781 c) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002782 c) hx)



theorem d002786 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    (c : _root_.GD.N0232.N0720.N1352.d002752 s) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) (hd : _root_.GD.N0232.N0720.N1352.d002742 x = 0) :
    VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G)
      (VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G)
        (VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G) (_root_.GD.N0232.N0720.N1352.d002754 c.G))) x =
      (-3 * _root_.GD.N0232.N0720.N1352.d002756 c.G c.Gw c.Gu x) • _root_.GD.N0232.N0720.N1352.d002740 2 +
        (3 * _root_.GD.N0232.N0720.N1352.d002757 c.G c.Gz c.Gu x) • _root_.GD.N0232.N0720.N1352.d002740 3 := by
  have heq : VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G)
      (VectorField.lieBracket ℝ (_root_.GD.N0232.N0720.N1352.d002753 c.G) (_root_.GD.N0232.N0720.N1352.d002754 c.G)) =ᶠ[𝓝 x]
      _root_.GD.N0232.N0720.N1352.d002761 c.G c.Gz c.Gw c.Gu := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact _root_.GD.N0232.N0720.N1352.d002785 hs c hy
  rw [_root_.GD.N0232.N0720.N1352.d002784 heq]
  have hC := _root_.GD.N0232.N0720.N1352.d002779 hd
    (_root_.GD.N0232.N0720.N1352.d002783 hs c.smooth_G hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs c.smooth_Gz hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs c.smooth_Gw hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002781 c) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002782 c) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002780 hs (_root_.GD.N0232.N0720.N1352.d002781 c) 0) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002780 hs (_root_.GD.N0232.N0720.N1352.d002781 c) 2) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002780 hs (_root_.GD.N0232.N0720.N1352.d002782 c) 0) hx)
    (_root_.GD.N0232.N0720.N1352.d002783 hs (_root_.GD.N0232.N0720.N1352.d002780 hs (_root_.GD.N0232.N0720.N1352.d002782 c) 2) hx)
  rw [VectorField.lieBracket, hC.fderiv]
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0720.N1352.d002761, _root_.GD.N0232.N0720.N1352.d002755, _root_.GD.N0232.N0720.N1352.d002759,
      _root_.GD.N0232.N0720.N1352.d002760, hd, _root_.GD.N0232.N0720.N1352.d002743, _root_.GD.N0232.N0720.N1352.d002741, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul]


theorem d002787 (G Gz Gw Gu : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    (-G x) * (3 * _root_.GD.N0232.N0720.N1352.d002757 G Gz Gu x) -
      (1 - G x) * (-3 * _root_.GD.N0232.N0720.N1352.d002756 G Gw Gu x) =
        -3 * _root_.GD.N0232.N0720.N1352.d002762 G Gz Gw Gu x := by
  simp only [_root_.GD.N0232.N0720.N1352.d002757, _root_.GD.N0232.N0720.N1352.d002756, _root_.GD.N0232.N0720.N1352.d002762]
  ring

private theorem d002788 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (c : _root_.GD.N0232.N0720.N1352.d002752 s) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002753 c.G) s := by
  exact contDiffOn_const.add
    ((_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul c.smooth_G).smul_const (_root_.GD.N0232.N0720.N1352.d002740 2))

private theorem d002789 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (c : _root_.GD.N0232.N0720.N1352.d002752 s) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002754 c.G) s := by
  exact contDiffOn_const.add
    ((_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul (c.smooth_G.sub contDiffOn_const)).smul_const (_root_.GD.N0232.N0720.N1352.d002740 3))

private theorem d002790 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    {V W : _root_.GD.N0232.N0720.N1352.d002739 → _root_.GD.N0232.N0720.N1352.d002739} (hV : ContDiffOn ℝ ∞ V s) (hW : ContDiffOn ℝ ∞ W s) :
    ContDiffOn ℝ ∞ (VectorField.lieBracket ℝ V W) s := by
  intro x hx
  exact ((hV.contDiffAt (hs.mem_nhds hx)).lieBracket_vectorField
    (hW.contDiffAt (hs.mem_nhds hx)) (m := ∞) (by simp)).contDiffWithinAt



theorem d002791 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    {H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {V W : _root_.GD.N0232.N0720.N1352.d002739 → _root_.GD.N0232.N0720.N1352.d002739}
    (hH : ContDiffOn ℝ 2 H s)
    (hV : ContDiffOn ℝ ∞ V s) (hW : ContDiffOn ℝ ∞ W s)
    (hVH : ∀ x ∈ s, fderiv ℝ H x (V x) = 0)
    (hWH : ∀ x ∈ s, fderiv ℝ H x (W x) = 0) :
    ∀ x ∈ s, fderiv ℝ H x (VectorField.lieBracket ℝ V W x) = 0 := by
  intro x hx
  have hVx := (hV.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hWx := (hW.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  rw [VectorField.fderiv_apply_lieBracket
    (hH.contDiffAt (hs.mem_nhds hx)) (by simp) hWx hVx]
  have hVe : (fun y ↦ fderiv ℝ H y (V y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hVH y hy
  have hWe : (fun y ↦ fderiv ℝ H y (W y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hWH y hy
  rw [hVe.fderiv_eq, hWe.fderiv_eq]
  simp



theorem d002792 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    (c : _root_.GD.N0232.N0720.N1352.d002752 s) {H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (h1 : ∀ x ∈ s, fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002753 c.G x) = 0)
    (h2 : ∀ x ∈ s, fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002754 c.G x) = 0)
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) (hd : _root_.GD.N0232.N0720.N1352.d002742 x = 0)
    (hF : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x ≠ 0) :
    ∀ i : Fin 4, fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 i) = 0 := by
  have hV := _root_.GD.N0232.N0720.N1352.d002788 c
  have hW := _root_.GD.N0232.N0720.N1352.d002789 c
  have hB := _root_.GD.N0232.N0720.N1352.d002790 hs hV hW
  have hC := _root_.GD.N0232.N0720.N1352.d002790 hs hV hB
  have hBH := _root_.GD.N0232.N0720.N1352.d002791 hs hH hV hW h1 h2
  have hCH := _root_.GD.N0232.N0720.N1352.d002791 hs hH hV hB h1 hBH
  have hEH := _root_.GD.N0232.N0720.N1352.d002791 hs hH hV hC h1 hCH
  have h0 : fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 0) = 0 := by
    simpa [_root_.GD.N0232.N0720.N1352.d002753, hd] using h1 x hx
  have h1' : fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 1) = 0 := by
    simpa [_root_.GD.N0232.N0720.N1352.d002754, hd] using h2 x hx
  have hzw := hBH x hx
  rw [_root_.GD.N0232.N0720.N1352.d002766 (c.first_jet x hx)] at hzw
  simp [_root_.GD.N0232.N0720.N1352.d002758, _root_.GD.N0232.N0720.N1352.d002755, hd, map_add, map_smul, smul_eq_mul] at hzw
  have hzw' := hEH x hx
  rw [_root_.GD.N0232.N0720.N1352.d002786 hs c hx hd] at hzw'
  simp only [map_add, map_smul, smul_eq_mul] at hzw'
  have hdet := _root_.GD.N0232.N0720.N1352.d002787 c.G c.Gz c.Gw c.Gu x
  have hzprod : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x *
      fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 2) = 0 := by
    have ha := congrArg (fun r : ℝ ↦ r * (3 * _root_.GD.N0232.N0720.N1352.d002757 c.G c.Gz c.Gu x)) hzw
    have hb := congrArg (fun r : ℝ ↦ r * (1 - c.G x)) hzw'
    have hc := congrArg (fun r : ℝ ↦ r * fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 2)) hdet
    nlinarith [ha, hb, hc]
  have hwprod : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x *
      fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 3) = 0 := by
    have ha := congrArg (fun r : ℝ ↦ r * (-3 * _root_.GD.N0232.N0720.N1352.d002756 c.G c.Gw c.Gu x)) hzw
    have hb := congrArg (fun r : ℝ ↦ r * (-c.G x)) hzw'
    have hc := congrArg (fun r : ℝ ↦ r * fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002740 3)) hdet
    nlinarith [ha, hb, hc]
  have hz := (mul_eq_zero.mp hzprod).resolve_left hF
  have hw := (mul_eq_zero.mp hwprod).resolve_left hF
  intro i
  fin_cases i <;> assumption

def d002793 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 := x 0 • _root_.GD.N0232.N0720.N1352.d002740 0 + x 1 • _root_.GD.N0232.N0720.N1352.d002740 1

def d002794 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 := x 2 • _root_.GD.N0232.N0720.N1352.d002740 2 + x 3 • _root_.GD.N0232.N0720.N1352.d002740 3

def d002795 (x : _root_.GD.N0232.N0720.N1352.d002739) (a : ℝ) : _root_.GD.N0232.N0720.N1352.d002739 :=
  a • _root_.GD.N0232.N0720.N1352.d002793 x + a ^ 2 • _root_.GD.N0232.N0720.N1352.d002794 x

def d002796 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 := _root_.GD.N0232.N0720.N1352.d002793 x + (2 : ℝ) • _root_.GD.N0232.N0720.N1352.d002794 x

@[simp] theorem d002797 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002795 x 1 = x := by
  ext i
  fin_cases i <;> simp [_root_.GD.N0232.N0720.N1352.d002795, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794, _root_.GD.N0232.N0720.N1352.d002740]

theorem d002798 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    HasDerivAt (_root_.GD.N0232.N0720.N1352.d002795 x) (_root_.GD.N0232.N0720.N1352.d002796 x) 1 := by
  convert! ((hasDerivAt_id (1 : ℝ)).smul_const (_root_.GD.N0232.N0720.N1352.d002793 x)).fun_add
      (((hasDerivAt_id (1 : ℝ)).pow 2).smul_const (_root_.GD.N0232.N0720.N1352.d002794 x))
    using 1
  simp [_root_.GD.N0232.N0720.N1352.d002796]



theorem d002799 {H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hH : DifferentiableAt ℝ H x)
    (hhom : ∀ᶠ a : ℝ in 𝓝 1, a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x) :
    H x + fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002796 x) = 0 := by
  have hH' : HasFDerivAt H (fderiv ℝ H x) (_root_.GD.N0232.N0720.N1352.d002795 x 1) := by
    simpa using hH.hasFDerivAt
  have hcomp := hH'.comp_hasDerivAt 1 (_root_.GD.N0232.N0720.N1352.d002798 x)
  have hprod := (hasDerivAt_id (1 : ℝ)).mul hcomp
  have hconst := hprod.congr_of_eventuallyEq (Filter.EventuallyEq.symm hhom)
  have heq := hconst.unique (hasDerivAt_const (1 : ℝ) (H x))
  simpa [Function.comp_def, Pi.mul_apply] using heq




theorem d002800 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    (c : _root_.GD.N0232.N0720.N1352.d002752 s) {H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (h1 : ∀ x ∈ s, fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002753 c.G x) = 0)
    (h2 : ∀ x ∈ s, fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002754 c.G x) = 0)
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) (hd : _root_.GD.N0232.N0720.N1352.d002742 x = 0)
    (hF : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x ≠ 0) (hHx : H x ≠ 0)
    (hhom : ∀ᶠ a : ℝ in 𝓝 1, a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x) : False := by
  have hzero := _root_.GD.N0232.N0720.N1352.d002792 hs c hH h1 h2 hx hd hF
  have hE : fderiv ℝ H x (_root_.GD.N0232.N0720.N1352.d002796 x) = 0 := by
    simp only [_root_.GD.N0232.N0720.N1352.d002796, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794, map_add, map_smul, hzero,
      smul_zero, add_zero]
  have hdiff := (hH.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have heuler := _root_.GD.N0232.N0720.N1352.d002799 hdiff hhom
  exact hHx (by simpa [hE] using heuler)



theorem d002801
    {H M₀ M₁ : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x v : _root_.GD.N0232.N0720.N1352.d002739} {a : ℝ}
    (hH : DifferentiableAt ℝ H x) (hM₀ : DifferentiableAt ℝ M₀ x)
    (hprod : M₁ =ᶠ[𝓝 x] fun y ↦ H y * M₀ y)
    (hne : M₀ x ≠ 0)
    (h0 : fderiv ℝ M₀ x v = a * M₀ x)
    (h1 : fderiv ℝ M₁ x v = a * M₁ x) :
    fderiv ℝ H x v = 0 := by
  have hp := (hH.hasFDerivAt.mul hM₀.hasFDerivAt).congr_of_eventuallyEq hprod
  have hpv := congrArg (fun L : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ ↦ L v) hp.fderiv
  simp only [add_apply, smul_apply,
    smul_eq_mul] at hpv
  have hvalue := hprod.self_of_nhds
  have hz : M₀ x * fderiv ℝ H x v = 0 := by
    rw [hvalue] at h1
    rw [h0, h1] at hpv
    nlinarith [hpv]
  exact (mul_eq_zero.mp hz).resolve_left hne



theorem d002802
    {δ M N : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739} (i j : Fin 4)
    (hδ : DifferentiableAt ℝ δ x) (hM : DifferentiableAt ℝ M x)
    (hprod : N =ᶠ[𝓝 x] fun y ↦ δ y * M y)
    (hpost : fderiv ℝ N x (_root_.GD.N0232.N0720.N1352.d002740 j) =
      x i * fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 j) - fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 i)) :
    fderiv ℝ M x (_root_.GD.N0232.N0720.N1352.d002740 i + (δ x - x i) • _root_.GD.N0232.N0720.N1352.d002740 j) =
      (-fderiv ℝ δ x (_root_.GD.N0232.N0720.N1352.d002740 j)) * M x := by
  have hp := (hδ.hasFDerivAt.mul hM.hasFDerivAt).congr_of_eventuallyEq hprod
  have hpv := congrArg (fun L : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ ↦ L (_root_.GD.N0232.N0720.N1352.d002740 j)) hp.fderiv
  simp only [add_apply, smul_apply,
    smul_eq_mul] at hpv
  simp only [map_add, map_smul, smul_eq_mul]
  rw [hpost] at hpv
  nlinarith [hpv]



theorem d002803
    {H M₀ M₁ : _root_.GD.N0232.N0720.N1352.d002739 → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739} {a : ℝ}
    (hne : M₀ x ≠ 0)
    (hp : M₁ x = H x * M₀ x)
    (hpa : M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a))
    (h0 : a ^ 5 * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₀ x)
    (h1 : a ^ 6 * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₁ x) :
    a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x := by
  apply mul_right_cancel₀ hne
  calc
    a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ x =
        a ^ 6 * (H (_root_.GD.N0232.N0720.N1352.d002795 x a) * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a)) := by
      rw [← h0]
      ring
    _ = a ^ 6 * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) := by rw [hpa]
    _ = M₁ x := h1
    _ = H x * M₀ x := hp

def d002804 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ := x 0 + _root_.GD.N0232.N0720.N1352.d002742 x * G x

private theorem d002805 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002753 G x = _root_.GD.N0232.N0720.N1352.d002740 0 + (_root_.GD.N0232.N0720.N1352.d002804 G x - x 0) • _root_.GD.N0232.N0720.N1352.d002740 2 := by
  simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0720.N1352.d002804]

private theorem d002806 (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1352.d002754 G x = _root_.GD.N0232.N0720.N1352.d002740 1 + (_root_.GD.N0232.N0720.N1352.d002804 G x - x 1) • _root_.GD.N0232.N0720.N1352.d002740 3 := by
  have h : _root_.GD.N0232.N0720.N1352.d002742 x * (G x - 1) = _root_.GD.N0232.N0720.N1352.d002804 G x - x 1 := by
    unfold _root_.GD.N0232.N0720.N1352.d002804 _root_.GD.N0232.N0720.N1352.d002742
    ring
  rw [_root_.GD.N0232.N0720.N1352.d002754, h]





theorem d002807 {s : Set _root_.GD.N0232.N0720.N1352.d002739} (hs : IsOpen s)
    (c : _root_.GD.N0232.N0720.N1352.d002752 s)
    {H M₀ M₁ N₀ N₁ : _root_.GD.N0232.N0720.N1352.d002739 → ℝ}
    (hH : ContDiffOn ℝ 2 H s)
    (hM₀ : ContDiffOn ℝ ∞ M₀ s) (hM₁ : ContDiffOn ℝ ∞ M₁ s)
    (hM₀ne : ∀ y ∈ s, M₀ y ≠ 0)
    (hratio : ∀ y ∈ s, M₁ y = H y * M₀ y)
    (hN₀ : ∀ y ∈ s, N₀ y = _root_.GD.N0232.N0720.N1352.d002804 c.G y * M₀ y)
    (hN₁ : ∀ y ∈ s, N₁ y = _root_.GD.N0232.N0720.N1352.d002804 c.G y * M₁ y)
    (hpde₀ : ∀ y ∈ s,
      fderiv ℝ N₀ y (_root_.GD.N0232.N0720.N1352.d002740 2) = y 0 * fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 2) -
        fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ N₀ y (_root_.GD.N0232.N0720.N1352.d002740 3) = y 1 * fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 3) -
        fderiv ℝ M₀ y (_root_.GD.N0232.N0720.N1352.d002740 1))
    (hpde₁ : ∀ y ∈ s,
      fderiv ℝ N₁ y (_root_.GD.N0232.N0720.N1352.d002740 2) = y 0 * fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 2) -
        fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ N₁ y (_root_.GD.N0232.N0720.N1352.d002740 3) = y 1 * fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 3) -
        fderiv ℝ M₁ y (_root_.GD.N0232.N0720.N1352.d002740 1))
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ s) (hd : _root_.GD.N0232.N0720.N1352.d002742 x = 0)
    (hF : _root_.GD.N0232.N0720.N1352.d002762 c.G c.Gz c.Gw c.Gu x ≠ 0) (hM₁x : M₁ x ≠ 0)
    (hdegrees : ∀ᶠ a : ℝ in 𝓝 1,
      a ^ 5 * M₀ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₀ x ∧
      a ^ 6 * M₁ (_root_.GD.N0232.N0720.N1352.d002795 x a) = M₁ x) : False := by
  have hδ : ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002804 c.G) s := by
    have hcoordinate : ContDiffOn ℝ ∞ (fun y : _root_.GD.N0232.N0720.N1352.d002739 ↦ y 0) s := by fun_prop
    exact hcoordinate.add (_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul c.smooth_G)
  have htransport (y : _root_.GD.N0232.N0720.N1352.d002739) (hy : y ∈ s) :
      fderiv ℝ H y (_root_.GD.N0232.N0720.N1352.d002753 c.G y) = 0 ∧
      fderiv ℝ H y (_root_.GD.N0232.N0720.N1352.d002754 c.G y) = 0 := by
    have hHy := (hH.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
    have h0y := _root_.GD.N0232.N0720.N1352.d002783 hs hM₀ hy
    have h1y := _root_.GD.N0232.N0720.N1352.d002783 hs hM₁ hy
    have hδy := _root_.GD.N0232.N0720.N1352.d002783 hs hδ hy
    have he₀ : N₀ =ᶠ[𝓝 y] fun z ↦ _root_.GD.N0232.N0720.N1352.d002804 c.G z * M₀ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hN₀ z hz
    have he₁ : N₁ =ᶠ[𝓝 y] fun z ↦ _root_.GD.N0232.N0720.N1352.d002804 c.G z * M₁ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hN₁ z hz
    have her : M₁ =ᶠ[𝓝 y] fun z ↦ H z * M₀ z := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hratio z hz
    constructor
    · apply _root_.GD.N0232.N0720.N1352.d002801 hHy h0y her (hM₀ne y hy)
        (a := -fderiv ℝ (_root_.GD.N0232.N0720.N1352.d002804 c.G) y (_root_.GD.N0232.N0720.N1352.d002740 2))
      · rw [_root_.GD.N0232.N0720.N1352.d002805]
        exact _root_.GD.N0232.N0720.N1352.d002802 0 2 hδy h0y he₀ (hpde₀ y hy).1
      · rw [_root_.GD.N0232.N0720.N1352.d002805]
        exact _root_.GD.N0232.N0720.N1352.d002802 0 2 hδy h1y he₁ (hpde₁ y hy).1
    · apply _root_.GD.N0232.N0720.N1352.d002801 hHy h0y her (hM₀ne y hy)
        (a := -fderiv ℝ (_root_.GD.N0232.N0720.N1352.d002804 c.G) y (_root_.GD.N0232.N0720.N1352.d002740 3))
      · rw [_root_.GD.N0232.N0720.N1352.d002806]
        exact _root_.GD.N0232.N0720.N1352.d002802 1 3 hδy h0y he₀ (hpde₀ y hy).2
      · rw [_root_.GD.N0232.N0720.N1352.d002806]
        exact _root_.GD.N0232.N0720.N1352.d002802 1 3 hδy h1y he₁ (hpde₁ y hy).2
  have hHx : H x ≠ 0 := by
    intro hz
    apply hM₁x
    simp [hratio x hx, hz]
  have hstay : ∀ᶠ a : ℝ in 𝓝 1, _root_.GD.N0232.N0720.N1352.d002795 x a ∈ s :=
    (_root_.GD.N0232.N0720.N1352.d002798 x).continuousAt.eventually
      (by simpa using hs.mem_nhds hx)
  have hhom : ∀ᶠ a : ℝ in 𝓝 1, a * H (_root_.GD.N0232.N0720.N1352.d002795 x a) = H x := by
    filter_upwards [hdegrees, hstay] with a ha has
    exact _root_.GD.N0232.N0720.N1352.d002803 (hM₀ne x hx)
      (hratio x hx) (hratio _ has) ha.1 ha.2
  exact _root_.GD.N0232.N0720.N1352.d002800 hs c hH
    (fun y hy ↦ (htransport y hy).1) (fun y hy ↦ (htransport y hy).2)
    hx hd hF hHx hhom

end

#print axioms _root_.GD.N0232.N0720.N1352.d002766
#print axioms _root_.GD.N0232.N0720.N1352.d002775
#print axioms _root_.GD.N0232.N0720.N1352.d002786
#print axioms _root_.GD.N0232.N0720.N1352.d002792
#print axioms _root_.GD.N0232.N0720.N1352.d002800
#print axioms _root_.GD.N0232.N0720.N1352.d002802
#print axioms _root_.GD.N0232.N0720.N1352.d002803
#print axioms _root_.GD.N0232.N0720.N1352.d002807

end GD.N0232.N0720.N1352
