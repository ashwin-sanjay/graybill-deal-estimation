import GD.Module0710











open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0925

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0917
open _root_.GD.N0232.N0719.N0927
open _root_.GD.N0232.N0719.N0926
open _root_.GD.N0232.N0719.N0920


abbrev d010543 : _root_.GD.N0232.N0719.N0917.d009868 3 :=
  ⟨Finset.cons 0 {1} (by decide), by simp⟩


abbrev d010544 : _root_.GD.N0232.N0719.N0917.d009868 3 :=
  ⟨Finset.cons 0 {2} (by decide), by simp⟩

@[simp]
theorem d010545 : _root_.GD.N0232.N0719.N0925.d010543.1.card = 2 := by
  rfl

@[simp]
theorem d010546 : _root_.GD.N0232.N0719.N0925.d010544.1.card = 2 := by
  rfl

@[simp]
theorem d010547 :
    _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) = 0 := by
  have hmem0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010543.1 :=
    (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl (0 : Fin 2)).2
  have hmem1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010543.1 :=
    (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl (1 : Fin 2)).2
  have hlt : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) <
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) := by
    exact (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl).strictMono (by decide)
  have hor0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) ∈ ({1} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2))
      (s := ({1} : Finset (Fin 3))) (h := by decide)).mp hmem0
  have hor1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) ∈ ({1} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2))
      (s := ({1} : Finset (Fin 3))) (h := by decide)).mp hmem1
  have hv0 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2)).val = 1 := by
    exact hor0.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  have hv1 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2)).val = 1 := by
    exact hor1.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  apply Fin.ext
  omega

@[simp]
theorem d010548 :
    _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) = 1 := by
  have hmem0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010543.1 :=
    (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl (0 : Fin 2)).2
  have hmem1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010543.1 :=
    (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl (1 : Fin 2)).2
  have hlt : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) <
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) := by
    exact (_root_.GD.N0232.N0719.N0925.d010543.1.orderIsoOfFin rfl).strictMono (by decide)
  have hor0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2) ∈ ({1} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2))
      (s := ({1} : Finset (Fin 3))) (h := by decide)).mp hmem0
  have hor1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2) ∈ ({1} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2))
      (s := ({1} : Finset (Fin 3))) (h := by decide)).mp hmem1
  have hv0 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2)).val = 1 := by
    exact hor0.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  have hv1 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2)).val = 1 := by
    exact hor1.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  apply Fin.ext
  omega

@[simp]
theorem d010549 :
    _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) = 0 := by
  have hmem0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010544.1 :=
    (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl (0 : Fin 2)).2
  have hmem1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010544.1 :=
    (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl (1 : Fin 2)).2
  have hlt : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) <
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) := by
    exact (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl).strictMono (by decide)
  have hor0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) ∈ ({2} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2))
      (s := ({2} : Finset (Fin 3))) (h := by decide)).mp hmem0
  have hor1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) ∈ ({2} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2))
      (s := ({2} : Finset (Fin 3))) (h := by decide)).mp hmem1
  have hv0 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2)).val = 2 := by
    exact hor0.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  have hv1 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2)).val = 2 := by
    exact hor1.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  apply Fin.ext
  omega

@[simp]
theorem d010550 :
    _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) = 2 := by
  have hmem0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010544.1 :=
    (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl (0 : Fin 2)).2
  have hmem1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) ∈
      _root_.GD.N0232.N0719.N0925.d010544.1 :=
    (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl (1 : Fin 2)).2
  have hlt : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) <
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) := by
    exact (_root_.GD.N0232.N0719.N0925.d010544.1.orderIsoOfFin rfl).strictMono (by decide)
  have hor0 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2) ∈ ({2} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2))
      (s := ({2} : Finset (Fin 3))) (h := by decide)).mp hmem0
  have hor1 : _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) = 0 ∨
      _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2) ∈ ({2} : Finset (Fin 3)) :=
    (Finset.mem_cons (a := (0 : Fin 3))
      (b := _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2))
      (s := ({2} : Finset (Fin 3))) (h := by decide)).mp hmem1
  have hv0 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2)).val = 2 := by
    exact hor0.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  have hv1 : (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2)).val = 0 ∨
      (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2)).val = 2 := by
    exact hor1.imp
      (fun h ↦ congrArg Fin.val h)
      (fun h ↦ congrArg Fin.val (Finset.mem_singleton.mp h))
  apply Fin.ext
  omega

@[simp]
theorem d010551 (x : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0917.d009870 x _root_.GD.N0232.N0719.N0925.d010543 = ![x 0, x 1] := by
  funext i
  rcases i with ⟨i, hi⟩
  have hi2 : i < 2 := by simpa using hi
  interval_cases i
  · change x (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (0 : Fin 2)) = x 0
    rw [_root_.GD.N0232.N0719.N0925.d010547]
  · change x (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010543 (1 : Fin 2)) = x 1
    rw [_root_.GD.N0232.N0719.N0925.d010548]

@[simp]
theorem d010552 (x : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0917.d009870 x _root_.GD.N0232.N0719.N0925.d010544 = ![x 0, x 2] := by
  funext i
  rcases i with ⟨i, hi⟩
  have hi2 : i < 2 := by simpa using hi
  interval_cases i
  · change x (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (0 : Fin 2)) = x 0
    rw [_root_.GD.N0232.N0719.N0925.d010549]
  · change x (_root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0925.d010544 (1 : Fin 2)) = x 2
    rw [_root_.GD.N0232.N0719.N0925.d010550]

@[simp]
theorem d010553 :
    _root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0925.d010543 = ![(1 / 2 : ℝ), 5 / 2] := by
  rw [_root_.GD.N0232.N0719.N0917.d009871, _root_.GD.N0232.N0719.N0925.d010551]
  funext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0927.d009909]

@[simp]
theorem d010554 :
    _root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0925.d010544 = ![(1 / 2 : ℝ), 5 / 2] := by
  rw [_root_.GD.N0232.N0719.N0917.d009871, _root_.GD.N0232.N0719.N0925.d010552]
  funext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0927.d009909]

@[simp]
theorem d010555 :
    _root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0925.d010543 = 11 / 2 := by
  rw [_root_.GD.N0232.N0719.N0917.d009885 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910]
  rw [_root_.GD.N0232.N0719.N0926.d010516]
  simp [_root_.GD.N0232.N0719.N0927.d009909]
  norm_num

@[simp]
theorem d010556 :
    _root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0925.d010544 = 11 / 2 := by
  rw [_root_.GD.N0232.N0719.N0917.d009885 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910]
  rw [_root_.GD.N0232.N0719.N0926.d010516]
  simp [_root_.GD.N0232.N0719.N0927.d009909]
  norm_num




def d010557 (u : ℝ) : _root_.GD.N0232.N0719.N0857.d009377 2 :=
  (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)).symm u

@[simp]
theorem d010558 (u : ℝ) (i : Fin 1) : _root_.GD.N0232.N0719.N0925.d010557 u i = u := by
  fin_cases i
  rfl



theorem d010559 (u : ℝ) :
    _root_.GD.N0232.N0719.N0925.d010557 u ∈ _root_.GD.N0232.N0719.N0955.d009607 2 ↔
      u ∈ Set.Ioo (0 : ℝ) 1 := by
  simp [_root_.GD.N0232.N0719.N0955.d009607, _root_.GD.N0232.N0719.N0925.d010557]



theorem d010560
    (f : _root_.GD.N0232.N0719.N0857.d009377 2 → ℝ) :
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 2, f q) =
      ∫ u in Set.Ioo (0 : ℝ) 1, f (_root_.GD.N0232.N0719.N0925.d010557 u) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 2
  let T := Set.Ioo (0 : ℝ) 1
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)
  let g : _root_.GD.N0232.N0719.N0857.d009377 2 → ℝ :=
    S.indicator f
  have hmp : MeasurePreserving e.symm (volume : Measure ℝ)
      (volume : Measure (_root_.GD.N0232.N0719.N0857.d009377 2)) :=
    MeasurePreserving.symm e
      (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ))
  have htransport := hmp.integral_comp e.symm.measurableEmbedding g
  have hpreimage : e.symm ⁻¹' S = T := by
    ext u
    simpa [e, T, _root_.GD.N0232.N0719.N0925.d010557] using _root_.GD.N0232.N0719.N0925.d010559 u
  have hcomp : g ∘ e.symm = T.indicator (f ∘ e.symm) := by
    funext u
    by_cases hu : u ∈ T
    · have hs : e.symm u ∈ S := by
        have := (_root_.GD.N0232.N0719.N0925.d010559 u).2 (by simpa [T] using hu)
        simpa [e, _root_.GD.N0232.N0719.N0925.d010557, S] using this
      simp [g, Function.comp_apply, Set.indicator_of_mem hu,
        Set.indicator_of_mem hs]
    · have hs : e.symm u ∉ S := by
        intro hs
        apply hu
        have := (_root_.GD.N0232.N0719.N0925.d010559 u).1 (by
          simpa [e, _root_.GD.N0232.N0719.N0925.d010557, S] using hs)
        simpa [T] using this
      simp [g, Function.comp_apply, Set.indicator_of_notMem hu,
        Set.indicator_of_notMem hs]
  have hS : MeasurableSet S :=
    _root_.GD.N0232.N0719.N0955.d009608 2
  have hT : MeasurableSet T := measurableSet_Ioo
  have hleft :
      (∫ u, g (e.symm u)) = ∫ u in T, f (e.symm u) := by
    rw [show (fun u ↦ g (e.symm u)) =
        T.indicator (f ∘ e.symm) by
      simpa [Function.comp_def] using hcomp]
    exact integral_indicator hT
  have hright :
      (∫ q, g q) = ∫ q in S, f q := by
    simpa [g] using (integral_indicator (f := f) hS)
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 2, f q) =
        ∫ q, g q := by simpa [S] using hright.symm
    _ = ∫ u, g (e.symm u) := htransport.symm
    _ = ∫ u in T, f (e.symm u) := hleft
    _ = ∫ u in Set.Ioo (0 : ℝ) 1, f (_root_.GD.N0232.N0719.N0925.d010557 u) := by
      rfl




def d010561 : Fin 2 → ℝ := ![(1 / 2 : ℝ), 5 / 2]


def d010562 (u : ℝ) : Fin 2 → ℝ :=
  _root_.GD.N0232.N0719.N0853.d009567 (by norm_num) (_root_.GD.N0232.N0719.N0925.d010557 u)

@[simp]
theorem d010563 (u : ℝ) : _root_.GD.N0232.N0719.N0925.d010562 u 0 = u := by
  rw [show (0 : Fin 2) = _root_.GD.N0232.N0719.N0954.d009344 2
      (by norm_num) (Sum.inl 0) by rfl]
  exact _root_.GD.N0232.N0719.N0853.d009568
    (by norm_num) (_root_.GD.N0232.N0719.N0925.d010557 u) 0

@[simp]
theorem d010564 (u : ℝ) :
    _root_.GD.N0232.N0719.N0925.d010562 u 1 = 1 - u := by
  rw [show (1 : Fin 2) = _root_.GD.N0232.N0719.N0954.d009344 2
      (by norm_num) (Sum.inr 0) by rfl]
  unfold _root_.GD.N0232.N0719.N0925.d010562
  rw [_root_.GD.N0232.N0719.N0853.d009569]
  simp [_root_.GD.N0232.N0719.N0925.d010557]

@[simp]
theorem d010565 :
    _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0925.d010561 (11 / 2) = 8 := by
  simp [_root_.GD.N0232.N0719.N0928.d009415, _root_.GD.N0232.N0719.N0928.d009408, _root_.GD.N0232.N0719.N0925.d010561,
    Fin.sum_univ_two]
  norm_num


def d010566 : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.Gamma 8

theorem d010567 : 0 < _root_.GD.N0232.N0719.N0925.d010566 := by
  exact mul_pos (Real.sqrt_pos.2 (by positivity))
    (Real.Gamma_pos_of_pos (by norm_num))


theorem d010568
    (u : ℝ) (y t : Fin 2 → ℝ) :
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u)
        y t (11 / 2) =
      _root_.GD.N0232.N0719.N0925.d010566 *
        _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0925.d010561
          (_root_.GD.N0232.N0719.N0925.d010562 u) *
        _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) y t ^
          (-(8 : ℝ)) := by
  unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0925.d010566
  rw [_root_.GD.N0232.N0719.N0925.d010565]
  ring


theorem d010569
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) =
      u * (1 - u) ^ 3 := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  rw [Fin.prod_univ_two]
  simp only [_root_.GD.N0232.N0719.N0925.d010563, _root_.GD.N0232.N0719.N0925.d010564]
  norm_num [_root_.GD.N0232.N0719.N0925.d010561, Real.rpow_one, Real.rpow_natCast]



theorem d010570
    {epsilon u : ℝ} {y t : Fin 2 → ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (ht0 : epsilon ≤ t 0) (ht1 : 1 ≤ t 1) :
    (1 / 4 : ℝ) * (epsilon + (1 - u)) ≤
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) y t := by
  have hp : ∀ i, 0 ≤ _root_.GD.N0232.N0719.N0925.d010562 u i := by
    exact fun i ↦ (_root_.GD.N0232.N0719.N0929.d009631 (by norm_num)
      ((_root_.GD.N0232.N0719.N0925.d010559 u).2 hu) i).le
  have hcontrast := _root_.GD.N0232.N0719.N0928.d009441
    (_root_.GD.N0232.N0719.N0925.d010562 u) y hp
  have hu0 : 0 ≤ u := hu.1.le
  have hz0 : 0 ≤ 1 - u := by linarith [hu.2]
  have hz1 : 1 - u ≤ 1 := by linarith [hu.1]
  have h0 := mul_le_mul_of_nonneg_left ht0 hu0
  have h1 := mul_le_mul_of_nonneg_left ht1 hz0
  have hez0 : 0 ≤ epsilon * (1 - (1 - u)) := by positivity
  have hze0 : 0 ≤ (1 - u) * (1 - epsilon) := by positivity
  unfold _root_.GD.N0232.N0719.N0928.d009407
  rw [Fin.sum_univ_two]
  simp only [_root_.GD.N0232.N0719.N0925.d010563, _root_.GD.N0232.N0719.N0925.d010564]
  norm_num [_root_.GD.N0232.N0719.N0925.d010561] at ⊢ h0 h1
  nlinarith



theorem d010571
    {epsilon u : ℝ} {y t : Fin 2 → ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (ht0 : epsilon ≤ t 0) (ht1 : 1 ≤ t 1) :
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u)
        y t (11 / 2) ≤
      65536 * _root_.GD.N0232.N0719.N0925.d010566 *
        ((1 - u) ^ 3 / (epsilon + (1 - u)) ^ 8) := by
  have henergyLower := _root_.GD.N0232.N0719.N0925.d010570
    (y := y) (t := t) hepsilon hepsilonOne hu ht0 ht1
  have hbase : 0 < epsilon + (1 - u) := by linarith [hu.2]
  have hquarter : 0 < (1 / 4 : ℝ) * (epsilon + (1 - u)) := by
    positivity
  have henergy : 0 <
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) y t :=
    lt_of_lt_of_le hquarter henergyLower
  have hpow :
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) y t ^
          (-(8 : ℝ)) ≤
        ((1 / 4 : ℝ) * (epsilon + (1 - u))) ^ (-(8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hquarter henergyLower (by norm_num)
  have hrpow :
      ((1 / 4 : ℝ) * (epsilon + (1 - u))) ^ (-(8 : ℝ)) =
        65536 / (epsilon + (1 - u)) ^ 8 := by
    rw [show (-(8 : ℝ)) = ((-8 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
    norm_num [zpow_neg, hbase.ne']
    field_simp [hbase.ne']
    ring
  have hmono := _root_.GD.N0232.N0719.N0925.d010569 hu
  have huOne : u ≤ 1 := hu.2.le
  have hz0 : 0 ≤ 1 - u := by linarith
  have hmonole : u * (1 - u) ^ 3 ≤ (1 - u) ^ 3 := by
    nlinarith [pow_nonneg hz0 3]
  rw [_root_.GD.N0232.N0719.N0925.d010568, hmono]
  have hfront0 : 0 ≤ _root_.GD.N0232.N0719.N0925.d010566 := _root_.GD.N0232.N0719.N0925.d010567.le
  calc
    _root_.GD.N0232.N0719.N0925.d010566 * (u * (1 - u) ^ 3) *
          _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0925.d010561 (_root_.GD.N0232.N0719.N0925.d010562 u) y t ^
            (-(8 : ℝ)) ≤
        _root_.GD.N0232.N0719.N0925.d010566 * (u * (1 - u) ^ 3) *
          ((1 / 4 : ℝ) * (epsilon + (1 - u))) ^ (-(8 : ℝ)) := by
      gcongr
      exact mul_nonneg hfront0
        (mul_nonneg hu.1.le (pow_nonneg hz0 3))
    _ = _root_.GD.N0232.N0719.N0925.d010566 * (u * (1 - u) ^ 3) *
          (65536 / (epsilon + (1 - u)) ^ 8) := by
      rw [hrpow]
    _ ≤ _root_.GD.N0232.N0719.N0925.d010566 * (1 - u) ^ 3 *
          (65536 / (epsilon + (1 - u)) ^ 8) := by
      gcongr
    _ = 65536 * _root_.GD.N0232.N0719.N0925.d010566 *
        ((1 - u) ^ 3 / (epsilon + (1 - u)) ^ 8) := by ring

end

end GD.N0232.N0719.N0925

#print axioms _root_.GD.N0232.N0719.N0925.d010560
