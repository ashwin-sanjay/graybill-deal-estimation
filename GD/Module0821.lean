import GD.Module0624
import Mathlib.MeasureTheory.MeasurableSpace.Embedding















namespace GD
namespace N0232
namespace N0720
namespace N1467

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900


def d012537 (m n : ℕ) : Fin 2 → ℕ := ![m, n]

@[simp] theorem d012538 (m n : ℕ) :
    _root_.GD.N0232.N0720.N1467.d012537 m n 0 = m := rfl

@[simp] theorem d012539 (m n : ℕ) :
    _root_.GD.N0232.N0720.N1467.d012537 m n 1 = n := rfl



def d012540 (m n : ℕ) :
    _root_.GD.N0232.N0719.N0900.d009094 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) ≃ᵐ
      (_root_.GD.N0137.d008894 (_root_.GD.N0232.N0720.N1467.d012537 m n 0) ×
        _root_.GD.N0137.d008894 (_root_.GD.N0232.N0720.N1467.d012537 m n 1)) :=
  MeasurableEquiv.piFinTwo
    (fun i : Fin 2 ↦ _root_.GD.N0137.d008894 (_root_.GD.N0232.N0720.N1467.d012537 m n i))


def d012541 (m n : ℕ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0719.N0900.d009094 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) :=
  (piFinTwoEquiv
    (fun i : Fin 2 ↦ _root_.GD.N0137.d008894 (_root_.GD.N0232.N0720.N1467.d012537 m n i))).symm omega


def d012542 (m n : ℕ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0719.N0900.d009096 2 :=
  _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (_root_.GD.N0232.N0720.N1467.d012541 m n omega)

@[simp] theorem d012543
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1467.d012541 m n omega 0 = omega.1 := by
  rfl

@[simp] theorem d012544
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1467.d012541 m n omega 1 = omega.2 := by
  rfl


@[simp] theorem d012545
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0 = _root_.GD.N0107.d009084 omega.1 := by
  rfl


@[simp] theorem d012546
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1 = _root_.GD.N0107.d009084 omega.2 := by
  rfl


@[simp] theorem d012547
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0 =
      _root_.GD.N0107.d009085 omega.1 / m := by
  rfl


@[simp] theorem d012548
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1 =
      _root_.GD.N0107.d009085 omega.2 / n := by
  rfl


@[simp] theorem d012549
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1467.d012540 m n (_root_.GD.N0232.N0720.N1467.d012541 m n omega) = omega := by
  exact (_root_.GD.N0232.N0720.N1467.d012540 m n).apply_symm_apply omega

end

end N1467
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1467.d012549
#print axioms _root_.GD.N0232.N0720.N1467.d012545
#print axioms _root_.GD.N0232.N0720.N1467.d012547
