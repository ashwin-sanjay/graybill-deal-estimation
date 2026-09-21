import GD.Module0700
import GD.Module0629
import GD.Module0821























open MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1497

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0867
open _root_.GD.N0232.N0720.N1467





theorem d012550
    (m n : ℕ) (location scale₁ scale₂ : ℝ) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1467.d012540 m n)
      (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
        ![scale₁, scale₂])
      (_root_.GD.N0107.d009030 m n location scale₁ scale₂) := by
  have h :=
    measurePreserving_piFinTwo
      (fun i : Fin 2 ↦
        _root_.GD.N0232.N0719.d009174 (_root_.GD.N0232.N0720.N1467.d012537 m n i) location
          (![scale₁, scale₂] i))
  rw [_root_.GD.N0232.N0720.d009061]
  change MeasurePreserving (_root_.GD.N0232.N0720.N1467.d012540 m n)
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
      ![scale₁, scale₂])
    (((_root_.GD.N0137.d008895 m).map (_root_.GD.N0107.d009018 m location scale₁)).prod
      ((_root_.GD.N0137.d008895 n).map (_root_.GD.N0107.d009018 n location scale₂))) at h
  with_unfolding_all exact h


theorem d012551
    (m n : ℕ) (location scale₁ scale₂ : ℝ) :
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
        ![scale₁, scale₂]).map (_root_.GD.N0232.N0720.N1467.d012540 m n) =
      _root_.GD.N0107.d009030 m n location scale₁ scale₂ :=
  (_root_.GD.N0232.N0720.N1497.d012550
    m n location scale₁ scale₂).map_eq



theorem d012552
    (m n : ℕ) (location scale₁ scale₂ : ℝ) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1467.d012541 m n)
      (_root_.GD.N0107.d009030 m n location scale₁ scale₂)
      (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
        ![scale₁, scale₂]) := by
  have h := MeasurePreserving.symm (_root_.GD.N0232.N0720.N1467.d012540 m n)
    (_root_.GD.N0232.N0720.N1497.d012550
      m n location scale₁ scale₂)
  change MeasurePreserving (_root_.GD.N0232.N0720.N1467.d012541 m n)
    (_root_.GD.N0107.d009030 m n location scale₁ scale₂)
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
      ![scale₁, scale₂]) at h
  exact h


theorem d012553
    (m n : ℕ) (location scale₁ scale₂ : ℝ) :
    (_root_.GD.N0107.d009030 m n location scale₁ scale₂).map
        (_root_.GD.N0232.N0720.N1467.d012541 m n) =
      _root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
        ![scale₁, scale₂] :=
  (_root_.GD.N0232.N0720.N1497.d012552
    m n location scale₁ scale₂).map_eq

@[fun_prop]
theorem d012554 (m n : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1467.d012541 m n) := by
  change Measurable ((_root_.GD.N0232.N0720.N1467.d012540 m n).symm :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      _root_.GD.N0232.N0719.N0900.d009094 2 (_root_.GD.N0232.N0720.N1467.d012537 m n))
  exact (_root_.GD.N0232.N0720.N1467.d012540 m n).symm.measurable



theorem d012555
    (m n : ℕ) (location scale₁ scale₂ : ℝ)
    (p : ℝ≥0∞)
    (f : _root_.GD.N0232.N0719.N0900.d009094 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) → ℝ)
    (hf : MemLp f p
      (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) location
        ![scale₁, scale₂])) :
    MemLp (f ∘ _root_.GD.N0232.N0720.N1467.d012541 m n) p
      (_root_.GD.N0107.d009030 m n location scale₁ scale₂) :=
  hf.comp_measurePreserving
    (_root_.GD.N0232.N0720.N1497.d012552
      m n location scale₁ scale₂)





theorem d012556
    (m n : ℕ) (location scale : ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1467.d012541 m n
        (_root_.GD.N0107.d009024 m n location scale scale omega) =
      _root_.GD.N0232.N0719.N0900.d009095 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)
        location scale (_root_.GD.N0232.N0720.N1467.d012541 m n omega) := by
  funext i
  fin_cases i <;> rfl





def d012557
    (m n : ℕ) (shape : Fin 2 → ℝ) (s : ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0232.N0719.N0867.d010315
    (by norm_num : 0 < (2 : ℕ)) shape s (_root_.GD.N0232.N0720.N1467.d012537 m n)
      (_root_.GD.N0232.N0720.N1467.d012541 m n omega)

@[fun_prop]
theorem d012558
    (m n : ℕ) (shape : Fin 2 → ℝ) (s : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1497.d012557 m n shape s) := by
  unfold _root_.GD.N0232.N0720.N1497.d012557
  exact
    (_root_.GD.N0232.N0719.N0867.d010316
      (by norm_num : 0 < (2 : ℕ)) shape s (_root_.GD.N0232.N0720.N1467.d012537 m n)).comp
        (_root_.GD.N0232.N0720.N1497.d012554 m n)



theorem d012559
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (shape : Fin 2 → ℝ) (s location : ℝ) {scale : ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 <
      _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hscale : 0 < scale)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1497.d012557 m n shape s
        (_root_.GD.N0107.d009024 m n location scale scale omega) =
      location + scale *
        _root_.GD.N0232.N0720.N1497.d012557 m n shape s omega := by
  have hsizes : ∀ i, 0 < _root_.GD.N0232.N0720.N1467.d012537 m n i := by
    intro i
    fin_cases i
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hm
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hn
  unfold _root_.GD.N0232.N0720.N1497.d012557
  rw [_root_.GD.N0232.N0720.N1497.d012556]
  exact _root_.GD.N0232.N0719.N0867.d010317
    (by norm_num : 0 < (2 : ℕ)) shape s location hshape hpower hscale
      (_root_.GD.N0232.N0720.N1467.d012537 m n) hsizes (_root_.GD.N0232.N0720.N1467.d012541 m n omega)



theorem d012560
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (shape : Fin 2 → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 <
      _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (location scale₁ scale₂ : ℝ) :
    MemLp
      (fun omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n ↦
        _root_.GD.N0232.N0720.N1497.d012557 m n shape s omega - location)
      2 (_root_.GD.N0107.d009030 m n location scale₁ scale₂) := by
  have hsizes : ∀ i, 2 ≤ _root_.GD.N0232.N0720.N1467.d012537 m n i := by
    intro i
    fin_cases i
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hm
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hn
  have hmany :=
    _root_.GD.N0232.N0719.N0867.d010318
      (by norm_num : 0 < (2 : ℕ)) shape s hshape hpower
        (_root_.GD.N0232.N0720.N1467.d012537 m n) hsizes location ![scale₁, scale₂]
  have hpull := hmany.comp_measurePreserving
    (_root_.GD.N0232.N0720.N1497.d012552
      m n location scale₁ scale₂)
  simpa [_root_.GD.N0232.N0720.N1497.d012557, Function.comp_def] using hpull



theorem d012561
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (shape : Fin 2 → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hpower : 0 <
      _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (location scale₁ scale₂ : ℝ) :
    Integrable
      (fun omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n ↦
        (_root_.GD.N0232.N0720.N1497.d012557 m n shape s omega -
          location) ^ 2)
      (_root_.GD.N0107.d009030 m n location scale₁ scale₂) :=
  (_root_.GD.N0232.N0720.N1497.d012560
    m n hm hn shape s hshape hpower location scale₁ scale₂).integrable_sq

end

end N1497
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1497.d012552
#print axioms _root_.GD.N0232.N0720.N1497.d012556
#print axioms _root_.GD.N0232.N0720.N1497.d012559
#print axioms _root_.GD.N0232.N0720.N1497.d012560
