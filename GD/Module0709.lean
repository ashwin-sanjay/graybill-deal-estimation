import GD.Module0686
import GD.Module0675
import GD.Module0707
import GD.Module0676














open scoped BigOperators

namespace GD.N0232.N0719.N0926

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0917
open _root_.GD.N0232.N0719.N0927
open _root_.GD.N0232.N0719.N1008
open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0907
open _root_.GD.N0232.N0719.N0918
open _root_.GD.N0232.N0719.N0867


abbrev d010512 : _root_.GD.N0232.N0719.N0917.d009868 3 :=
  ⟨{0}, by simp⟩

@[simp]
theorem d010513 : _root_.GD.N0232.N0719.N0926.d010512.1.card = 1 := by
  simp [_root_.GD.N0232.N0719.N0926.d010512]

@[simp]
theorem d010514 (i : Fin _root_.GD.N0232.N0719.N0926.d010512.1.card) :
    _root_.GD.N0232.N0719.N0917.d009869 _root_.GD.N0232.N0719.N0926.d010512 i = 0 := by
  change ((_root_.GD.N0232.N0719.N0926.d010512.1.orderIsoOfFin rfl i).1 : Fin 3) = 0
  simpa only [Finset.mem_singleton] using
    (_root_.GD.N0232.N0719.N0926.d010512.1.orderIsoOfFin rfl i).2

@[simp]
theorem d010515 (x : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0917.d009870 x _root_.GD.N0232.N0719.N0926.d010512 = fun _ : Fin 1 ↦ x 0 := by
  funext i
  simp [_root_.GD.N0232.N0719.N0917.d009870]


@[simp]
theorem d010516 :
    _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 = 8 := by
  unfold _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0907.d009858
  rw [_root_.GD.N0232.N0719.N0928.d009418 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910]
  norm_num [_root_.GD.N0232.N0719.N0927.d009909, Fin.sum_univ_succ]


@[simp]
theorem d010517 :
    _root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512 = 17 / 2 := by
  rw [_root_.GD.N0232.N0719.N0917.d009885 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910]
  rw [_root_.GD.N0232.N0719.N0926.d010516]
  norm_num [_root_.GD.N0232.N0719.N0927.d009909]


theorem d010518
    (y t : Fin 3 → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512 = y 0 := by
  unfold _root_.GD.N0232.N0719.N0917.d009874
  have hshape : ∀ i : Fin 1,
      0 < _root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512 i := by
    intro i
    fin_cases i
    simpa [_root_.GD.N0232.N0719.N0917.d009871, _root_.GD.N0232.N0719.N0917.d009870,
      _root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0927.d009909] using
        (show (0 : ℝ) < 1 / 2 by norm_num)
  have ht' : ∀ i : Fin 1,
      0 < _root_.GD.N0232.N0719.N0917.d009870 t _root_.GD.N0232.N0719.N0926.d010512 i := by
    intro i
    simpa using ht 0
  have hpowerEq : _root_.GD.N0232.N0719.N0928.d009415
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512) = _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 := by
    exact _root_.GD.N0232.N0719.N1007.d009823 _ _
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512) := by
    rw [hpowerEq]
    norm_num
  convert _root_.GD.N0232.N0719.N1008.d010007
    (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
    (_root_.GD.N0232.N0719.N0917.d009870 y _root_.GD.N0232.N0719.N0926.d010512)
    (_root_.GD.N0232.N0719.N0917.d009870 t _root_.GD.N0232.N0719.N0926.d010512)
    (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
      _root_.GD.N0232.N0719.N0926.d010512) hshape ht' hpower using 1 <;>
    try congr <;> simp [_root_.GD.N0232.N0719.N0917.d009870]


def d010519 : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
    (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
      _root_.GD.N0232.N0719.N0926.d010512)


@[simp]
theorem d010520 : _root_.GD.N0232.N0719.N0926.d010519 = 8 := by
  unfold _root_.GD.N0232.N0719.N0926.d010519
  calc
    _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
        (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
          _root_.GD.N0232.N0719.N0926.d010512) = _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 :=
      _root_.GD.N0232.N0719.N1007.d009823 _ _
    _ = 8 := _root_.GD.N0232.N0719.N0926.d010516



def d010521 : ℝ :=
  _root_.GD.N0232.N0719.N0929.d009647 Nat.zero_lt_one
    (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512) (fun _ ↦ 0) (fun _ ↦ 1)
    (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
      _root_.GD.N0232.N0719.N0926.d010512)


theorem d010522 : 0 < _root_.GD.N0232.N0719.N0926.d010521 := by
  unfold _root_.GD.N0232.N0719.N0926.d010521
  apply _root_.GD.N0232.N0719.N0929.d009648
  · intro i
    fin_cases i
    simpa [_root_.GD.N0232.N0719.N0917.d009871, _root_.GD.N0232.N0719.N0917.d009870,
      _root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0927.d009909] using
        (show (0 : ℝ) < 1 / 2 by norm_num)
  · intro i
    norm_num
  · change 0 < _root_.GD.N0232.N0719.N0926.d010519
    norm_num



theorem d010523
    (y t : Fin 3 → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512 =
      (t 0) ^ (-_root_.GD.N0232.N0719.N0926.d010519) * _root_.GD.N0232.N0719.N0926.d010521 := by
  unfold _root_.GD.N0232.N0719.N0917.d009873
  change _root_.GD.N0232.N0719.N0929.d009647 Nat.zero_lt_one
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009870 y _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009870 t _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512) = _
  have hshape : ∀ i : Fin 1,
      0 < _root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512 i := by
    intro i
    fin_cases i
    simpa [_root_.GD.N0232.N0719.N0917.d009871, _root_.GD.N0232.N0719.N0917.d009870,
      _root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0927.d009909] using
        (show (0 : ℝ) < 1 / 2 by norm_num)
  have ht0 : 0 < _root_.GD.N0232.N0719.N0917.d009870 t _root_.GD.N0232.N0719.N0926.d010512 (0 : Fin 1) := by
    simpa using ht 0
  have hpowerEqCommon : _root_.GD.N0232.N0719.N0928.d009415
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512) = _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 := by
    exact _root_.GD.N0232.N0719.N1007.d009823 _ _
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
        _root_.GD.N0232.N0719.N0926.d010512) := by
    have hc : 0 < _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 := by norm_num
    linarith
  have hscale := _root_.GD.N0232.N0719.N1008.d010008
      (_root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009870 y _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009870 t _root_.GD.N0232.N0719.N0926.d010512)
      (_root_.GD.N0232.N0719.N0917.d009872 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
      _root_.GD.N0232.N0719.N0926.d010512) hshape ht0 hpower
  unfold _root_.GD.N0232.N0719.N0926.d010519 _root_.GD.N0232.N0719.N0926.d010521
  simp only [_root_.GD.N0232.N0719.N0926.d010515] at hscale ⊢
  convert hscale using 1 <;> congr






def d010524 (y t : Fin 3 → ℝ) : ℝ :=
  ∑ face ∈ (Finset.univ.erase _root_.GD.N0232.N0719.N0926.d010512),
    _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face *
      |_root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face - y 0|


def d010525 (y t : Fin 3 → ℝ) : ℝ :=
  ∑ face ∈ (Finset.univ.erase _root_.GD.N0232.N0719.N0926.d010512),
    _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face

theorem d010526 (i : Fin 3) : 2 ≤ _root_.GD.N0232.N0719.N0927.d009909 i := by
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0927.d009909]




def d010527 (ε : ℝ) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ if i = 0 then ε else t i

@[simp]
theorem d010528 (ε : ℝ) (t : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0926.d010527 ε t 0 = ε := by
  simp [_root_.GD.N0232.N0719.N0926.d010527]



theorem d010529
    (ε : ℝ) (t : Fin 3 → ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 3)
    (hzero : 0 ∉ face.1) :
    _root_.GD.N0232.N0719.N0917.d009870 (_root_.GD.N0232.N0719.N0926.d010527 ε t) face =
      _root_.GD.N0232.N0719.N0917.d009870 t face := by
  funext j
  have hmem : _root_.GD.N0232.N0719.N0917.d009869 face j ∈ face.1 :=
    (face.1.orderIsoOfFin rfl j).2
  have hne : _root_.GD.N0232.N0719.N0917.d009869 face j ≠ 0 := by
    intro hz
    apply hzero
    simpa [hz] using hmem
  simp [_root_.GD.N0232.N0719.N0917.d009870, _root_.GD.N0232.N0719.N0926.d010527, hne]



theorem d010530
    (ε : ℝ) (y t : Fin 3 → ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 3)
    (hzero : 0 ∉ face.1) :
    _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y (_root_.GD.N0232.N0719.N0926.d010527 ε t)
        (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face =
      _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face := by
  unfold _root_.GD.N0232.N0719.N0917.d009873
  rw [_root_.GD.N0232.N0719.N0926.d010529 ε t face hzero]


theorem d010531
    (ε : ℝ) (y t : Fin 3 → ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 3)
    (hzero : 0 ∉ face.1) :
    _root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y (_root_.GD.N0232.N0719.N0926.d010527 ε t)
        (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face =
      _root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face := by
  unfold _root_.GD.N0232.N0719.N0917.d009874
  rw [_root_.GD.N0232.N0719.N0926.d010529 ε t face hzero]





theorem d010532
    (y t : Fin 3 → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0926.d010524 y t ≤
      _root_.GD.N0232.N0719.N0910.d010278 (y 0) y *
        _root_.GD.N0232.N0719.N0926.d010525 y t := by
  classical
  let u : _root_.GD.N0232.N0719.N0900.d009096 3 :=
    { mean := y, meanVariance := t }
  have hpos : _root_.GD.N0232.N0719.N0867.d010301 u := ht
  have hcommon : 0 < _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 := by norm_num
  have hevidence : ∀ face,
      0 ≤ _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face := by
    intro face
    exact (_root_.GD.N0232.N0719.N0917.d009890 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010526 y t ht
      (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) hcommon face).le
  unfold _root_.GD.N0232.N0719.N0926.d010524 _root_.GD.N0232.N0719.N0926.d010525
  calc
    (∑ face ∈ Finset.univ.erase _root_.GD.N0232.N0719.N0926.d010512,
        _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face *
          |_root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face -
            y 0|) ≤
        ∑ face ∈ Finset.univ.erase _root_.GD.N0232.N0719.N0926.d010512,
          _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face *
            _root_.GD.N0232.N0719.N0910.d010278 (y 0) y := by
      apply Finset.sum_le_sum
      intro face hface
      apply mul_le_mul_of_nonneg_left _ (hevidence face)
      simpa [u] using _root_.GD.N0232.N0719.N0918.d010425
        _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010526 (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
          hcommon (y 0) u hpos face
    _ = _root_.GD.N0232.N0719.N0910.d010278 (y 0) y *
        (∑ face ∈ Finset.univ.erase _root_.GD.N0232.N0719.N0926.d010512,
          _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) face) := by
      rw [← Finset.sum_mul]
      ring



theorem d010533
    {B E : ℝ} (y t : Fin 3 → ℝ) (ht : ∀ i, 0 < t i)
    (hB : _root_.GD.N0232.N0719.N0910.d010278 (y 0) y ≤ B)
    (hE0 : 0 ≤ E) (hE : _root_.GD.N0232.N0719.N0926.d010525 y t ≤ E) :
    _root_.GD.N0232.N0719.N0926.d010524 y t ≤ B * E := by
  have hcentered0 : 0 ≤ _root_.GD.N0232.N0719.N0910.d010278 (y 0) y := by
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hmass0 : 0 ≤ _root_.GD.N0232.N0719.N0926.d010525 y t := by
    unfold _root_.GD.N0232.N0719.N0926.d010525
    exact Finset.sum_nonneg fun face hface ↦
      (_root_.GD.N0232.N0719.N0917.d009890 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010526 y t ht
        (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) (by norm_num) face).le
  calc
    _root_.GD.N0232.N0719.N0926.d010524 y t ≤
        _root_.GD.N0232.N0719.N0910.d010278 (y 0) y *
          _root_.GD.N0232.N0719.N0926.d010525 y t :=
      _root_.GD.N0232.N0719.N0926.d010532 y t ht
    _ ≤ B * _root_.GD.N0232.N0719.N0926.d010525 y t :=
      mul_le_mul_of_nonneg_right hB hmass0
    _ ≤ B * E := by
      exact mul_le_mul_of_nonneg_left hE (hcentered0.trans hB)





theorem d010534
    {ε : ℝ} (hε : 0 < ε) (y t : Fin 3 → ℝ)
    (ht : ∀ i, 0 < t i) (ht0 : t 0 = ε) :
    |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 y t - y 0| ≤
      _root_.GD.N0232.N0719.N0926.d010524 y t /
        (ε ^ (-_root_.GD.N0232.N0719.N0926.d010519) * _root_.GD.N0232.N0719.N0926.d010521) := by
  classical
  let evidence : _root_.GD.N0232.N0719.N0917.d009868 3 → ℝ :=
    _root_.GD.N0232.N0719.N0917.d009873 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
  let action : _root_.GD.N0232.N0719.N0917.d009868 3 → ℝ :=
    _root_.GD.N0232.N0719.N0917.d009874 _root_.GD.N0232.N0719.N0927.d009909 y t (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909)
  have hcommon : 0 < _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909 := by norm_num
  have hevidence : ∀ face, 0 < evidence face := by
    intro face
    exact _root_.GD.N0232.N0719.N0917.d009890 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0926.d010526 y t ht
      (_root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0927.d009909) hcommon face
  have hmass : ∀ face,
      0 ≤ (1 : ℝ) * evidence face := by
    intro face
    simpa using (hevidence face).le
  have hmass0 :
      0 < (1 : ℝ) * evidence _root_.GD.N0232.N0719.N0926.d010512 := by
    simpa using hevidence _root_.GD.N0232.N0719.N0926.d010512
  have haction : action _root_.GD.N0232.N0719.N0926.d010512 = y 0 := by
    exact _root_.GD.N0232.N0719.N0926.d010518 y t ht
  have hshield :=
    _root_.GD.N0232.N0719.N1008.d010011
      (fun _ : _root_.GD.N0232.N0719.N0917.d009868 3 ↦ (1 : ℝ)) evidence action (y 0)
      _root_.GD.N0232.N0719.N0926.d010512 hmass hmass0 haction
  have he0 : evidence _root_.GD.N0232.N0719.N0926.d010512 =
      ε ^ (-_root_.GD.N0232.N0719.N0926.d010519) * _root_.GD.N0232.N0719.N0926.d010521 := by
    simpa [evidence, ht0] using _root_.GD.N0232.N0719.N0926.d010523 y t ht
  rw [he0] at hshield
  simpa [_root_.GD.N0232.N0719.N0917.d009880,
    _root_.GD.N0232.N0719.N0917.d009878, _root_.GD.N0232.N0719.N0917.d009877,
    evidence, action, _root_.GD.N0232.N0719.N0926.d010524] using hshield





theorem d010535
    {ε Cpair Ccritical Caway : ℝ}
    (hε : 0 < ε) (y t : Fin 3 → ℝ)
    (ht : ∀ i, 0 < t i) (ht0 : t 0 = ε)
    (hresponse : _root_.GD.N0232.N0719.N0926.d010524 y t ≤
      Cpair * ε ^ (-4 : ℝ) +
        Ccritical * Real.log ((ε + 1) / ε) + Caway) :
    |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 y t - y 0| ≤
      (Cpair * ε ^ (-4 : ℝ) +
        Ccritical * Real.log ((ε + 1) / ε) + Caway) /
          (ε ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) := by
  have hbase :
      |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 y t - y 0| ≤
        _root_.GD.N0232.N0719.N0926.d010524 y t /
          (ε ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) := by
    simpa using
      _root_.GD.N0232.N0719.N0926.d010534 hε y t ht ht0
  exact hbase.trans
      (div_le_div_of_nonneg_right hresponse
        (mul_nonneg (Real.rpow_nonneg hε.le _)
          _root_.GD.N0232.N0719.N0926.d010522.le))





theorem d010536
    {ε B Cpair Ccritical Caway : ℝ}
    (hε : 0 < ε) (y t : Fin 3 → ℝ)
    (ht : ∀ i, 0 < t i) (ht0 : t 0 = ε)
    (hB : _root_.GD.N0232.N0719.N0910.d010278 (y 0) y ≤ B)
    (hE0 : 0 ≤ Cpair * ε ^ (-4 : ℝ) +
      Ccritical * Real.log ((ε + 1) / ε) + Caway)
    (hevidence : _root_.GD.N0232.N0719.N0926.d010525 y t ≤
      Cpair * ε ^ (-4 : ℝ) +
        Ccritical * Real.log ((ε + 1) / ε) + Caway) :
    |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 y t - y 0| ≤
      (B * (Cpair * ε ^ (-4 : ℝ) +
        Ccritical * Real.log ((ε + 1) / ε) + Caway)) /
          (ε ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) := by
  have hresponse : _root_.GD.N0232.N0719.N0926.d010524 y t ≤
      B * (Cpair * ε ^ (-4 : ℝ) +
        Ccritical * Real.log ((ε + 1) / ε) + Caway) :=
    _root_.GD.N0232.N0719.N0926.d010533 y t ht hB hE0 hevidence
  have hbase :
      |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 y t - y 0| ≤
        _root_.GD.N0232.N0719.N0926.d010524 y t /
          (ε ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) := by
    simpa using
      _root_.GD.N0232.N0719.N0926.d010534 hε y t ht ht0
  exact hbase.trans
    (div_le_div_of_nonneg_right hresponse
      (mul_nonneg (Real.rpow_nonneg hε.le _)
        _root_.GD.N0232.N0719.N0926.d010522.le))





theorem d010537
    (ε bound : ℕ → ℝ) (y t : ℕ → Fin 3 → ℝ)
    (hε : ∀ n, 0 < ε n) (ht : ∀ n i, 0 < t n i)
    (ht0 : ∀ n, t n 0 = ε n)
    (hbound : ∀ n,
      _root_.GD.N0232.N0719.N0926.d010524 (y n) (t n) /
          ((ε n) ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) ≤ bound n)
    (_hbound0 : ∀ n, 0 ≤ bound n)
    (hboundTendsto : Filter.Tendsto bound Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 (y n) (t n) - y n 0)
      Filter.atTop (nhds 0) := by
  have habs : Filter.Tendsto
      (fun n ↦
        |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 (y n) (t n) - y n 0|)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n ↦ abs_nonneg _
    · intro n
      have hbase :
          |_root_.GD.N0232.N0719.N0917.d009880 _root_.GD.N0232.N0719.N0927.d009909 (y n) (t n) - y n 0| ≤
            _root_.GD.N0232.N0719.N0926.d010524 (y n) (t n) /
              ((ε n) ^ (-8 : ℝ) * _root_.GD.N0232.N0719.N0926.d010521) := by
        simpa using _root_.GD.N0232.N0719.N0926.d010534
          (hε n) (y n) (t n) (ht n) (ht0 n)
      exact hbase.trans (hbound n)
    · exact hboundTendsto
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

end

end GD.N0232.N0719.N0926

#print axioms _root_.GD.N0232.N0719.N0926.d010523
#print axioms _root_.GD.N0232.N0719.N0926.d010532
#print axioms _root_.GD.N0232.N0719.N0926.d010536
#print axioms _root_.GD.N0232.N0719.N0926.d010537
