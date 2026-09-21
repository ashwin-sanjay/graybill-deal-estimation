import Mathlib.Data.Finset.Sort
import GD.Module0655
import GD.Module0673
import GD.Module0674


























open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0917

noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0866
open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0906
open _root_.GD.N0232.N0719.N0869
open _root_.GD.N0232.N0719.N0907


abbrev d009868 (k : ℕ) :=
  {face : Finset (Fin k) // face.Nonempty}


def d009869 {k : ℕ} (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    Fin face.1.card → Fin k :=
  fun j ↦ (face.1.orderIsoOfFin rfl j).1



def d009870 {k : ℕ} (x : Fin k → ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) : Fin face.1.card → ℝ :=
  fun j ↦ x (_root_.GD.N0232.N0719.N0917.d009869 face j)


def d009871 {k : ℕ} (sizes : Fin k → ℕ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) : Fin face.1.card → ℝ :=
  _root_.GD.N0232.N0719.N0917.d009870 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face


def d009872 {k : ℕ} (sizes : Fin k → ℕ)
    (commonPower : ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 k) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009817 commonPower (_root_.GD.N0232.N0719.N0928.d009408 (_root_.GD.N0232.N0719.N0917.d009871 sizes face))


def d009873 {k : ℕ} (sizes : Fin k → ℕ)
    (y t : Fin k → ℝ) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) : ℝ :=
  _root_.GD.N0232.N0719.N0929.d009647 (Finset.card_pos.mpr face.2)
    (_root_.GD.N0232.N0719.N0917.d009871 sizes face) (_root_.GD.N0232.N0719.N0917.d009870 y face) (_root_.GD.N0232.N0719.N0917.d009870 t face)
    (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face)


def d009874 {k : ℕ} (sizes : Fin k → ℕ)
    (y t : Fin k → ℝ) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) : ℝ :=
  _root_.GD.N0232.N0719.N0929.d009653 (Finset.card_pos.mpr face.2)
    (_root_.GD.N0232.N0719.N0917.d009871 sizes face) (_root_.GD.N0232.N0719.N0917.d009870 y face) (_root_.GD.N0232.N0719.N0917.d009870 t face)
    (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face)


def d009875 {k : ℕ} (sizes : Fin k → ℕ)
    (y t : Fin k → ℝ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009826 weight (_root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower)


def d009876 {k : ℕ} (sizes : Fin k → ℕ)
    (y t : Fin k → ℝ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009827 weight (_root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower)
    (_root_.GD.N0232.N0719.N0917.d009874 sizes y t commonPower)


def d009877 {k : ℕ} (sizes : Fin k → ℕ)
    (y t : Fin k → ℝ) (commonPower : ℝ)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009828 weight (_root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower)
    (_root_.GD.N0232.N0719.N0917.d009874 sizes y t commonPower)



def d009878 {k : ℕ}
    (sizes : Fin k → ℕ) (y t : Fin k → ℝ)
    (commonPower : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0917.d009877 sizes y t commonPower (fun _ ↦ 1)



def d009879 {k : ℕ} (sizes : Fin k → ℕ) : ℝ :=
  _root_.GD.N0232.N0719.N0907.d009858 (_root_.GD.N0232.N0719.N0928.d009408 (_root_.GD.N0232.N0719.N0954.d009355 sizes))



def d009880 {k : ℕ}
    (sizes : Fin k → ℕ) (y t : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0917.d009878 sizes y t (_root_.GD.N0232.N0719.N0917.d009879 sizes)



@[simp]
theorem d009881
    {k : ℕ} (y : Fin k → ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 k)
    (shift dilation : ℝ) :
    _root_.GD.N0232.N0719.N0917.d009870 (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y) face =
      _root_.GD.N0232.N0719.N0866.d009655 shift dilation (_root_.GD.N0232.N0719.N0917.d009870 y face) := by
  rfl

@[simp]
theorem d009882
    {k : ℕ} (t : Fin k → ℝ) (face : _root_.GD.N0232.N0719.N0917.d009868 k)
    (dilation : ℝ) :
    _root_.GD.N0232.N0719.N0917.d009870 (_root_.GD.N0232.N0719.N0866.d009656 dilation t) face =
      _root_.GD.N0232.N0719.N0866.d009656 dilation (_root_.GD.N0232.N0719.N0917.d009870 t face) := by
  rfl



theorem d009883
    {k : ℕ} (sizes : Fin k → ℕ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    _root_.GD.N0232.N0719.N0928.d009408 (_root_.GD.N0232.N0719.N0917.d009871 sizes face) =
      _root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face.1 := by
  unfold _root_.GD.N0232.N0719.N0928.d009408 _root_.GD.N0232.N0719.N1007.d009816 _root_.GD.N0232.N0719.N0917.d009871 _root_.GD.N0232.N0719.N0917.d009870
    _root_.GD.N0232.N0719.N0917.d009869
  have hsum :
      (∑ j : Fin face.1.card,
          _root_.GD.N0232.N0719.N0954.d009355 sizes ((face.1.orderIsoOfFin rfl j).1)) =
        ∑ i : face.1, _root_.GD.N0232.N0719.N0954.d009355 sizes i.1 := by
    exact Fintype.sum_equiv (face.1.orderIsoOfFin rfl).toEquiv
      _ _ (fun _ ↦ rfl)
  have hattach :
      (∑ i : face.1, _root_.GD.N0232.N0719.N0954.d009355 sizes i.1) =
        ∑ i ∈ face.1, _root_.GD.N0232.N0719.N0954.d009355 sizes i := by
    exact (Finset.sum_subtype face.1 (fun _ ↦ Iff.rfl)
      (_root_.GD.N0232.N0719.N0954.d009355 sizes)).symm
  rw [hsum, hattach]
  simp



theorem d009884
    {k : ℕ} (sizes : Fin k → ℕ) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    _root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face.1) := by
  unfold _root_.GD.N0232.N0719.N0917.d009872
  rw [_root_.GD.N0232.N0719.N0917.d009883]



theorem d009885
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) (commonPower : ℝ)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    _root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face =
      commonPower + 3 / 2 -
        ∑ i ∈ face.1, (sizes i : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0917.d009884,
    _root_.GD.N0232.N0719.N0906.d009843 sizes hsizes]
  rfl



theorem d009886
    {k : ℕ} (shape : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1007.d009816 shape Finset.univ = _root_.GD.N0232.N0719.N0928.d009408 shape := by
  unfold _root_.GD.N0232.N0719.N1007.d009816 _root_.GD.N0232.N0719.N0928.d009408
  simp




theorem d009887
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    _root_.GD.N0232.N0719.N0917.d009872 sizes (_root_.GD.N0232.N0719.N0917.d009879 sizes) face =
      5 / 2 + ∑ i ∈ Finset.univ \ face.1, (sizes i : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0917.d009884]
  unfold _root_.GD.N0232.N0719.N0917.d009879
  rw [_root_.GD.N0232.N0719.N0907.d009860]
  have hsplit := _root_.GD.N0232.N0719.N0869.d009837
    (_root_.GD.N0232.N0719.N0954.d009355 sizes) face.1 Finset.univ (Finset.subset_univ face.1)
  rw [_root_.GD.N0232.N0719.N0917.d009886,
    _root_.GD.N0232.N0719.N0906.d009844 sizes hsizes] at hsplit
  linarith





theorem d009888
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) :
    0 < _root_.GD.N0232.N0719.N0917.d009879 sizes := by
  unfold _root_.GD.N0232.N0719.N0917.d009879 _root_.GD.N0232.N0719.N0907.d009858
  rw [_root_.GD.N0232.N0719.N0928.d009418 sizes hsizes]
  have hsum : 0 < ∑ i : Fin k, (sizes i : ℝ) / 2 := by
    let i : Fin k := ⟨0, hk⟩
    exact Finset.sum_pos'
      (fun j _ ↦ (div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le
        Nat.zero_lt_one (hsizes j))) (by norm_num)).le)
      ⟨i, Finset.mem_univ _, div_pos
        (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (hsizes i)))
        (by norm_num)⟩
  linarith

theorem d009889
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    ∀ j, 0 < _root_.GD.N0232.N0719.N0917.d009871 sizes face j := by
  intro j
  exact _root_.GD.N0232.N0719.N0954.d009358 hsizes (_root_.GD.N0232.N0719.N0917.d009869 face j)



theorem d009890
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) :
    0 < _root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower face := by
  unfold _root_.GD.N0232.N0719.N0917.d009873
  apply _root_.GD.N0232.N0719.N0929.d009648
  · exact _root_.GD.N0232.N0719.N0917.d009889 sizes hsizes face
  · intro j
    exact ht (_root_.GD.N0232.N0719.N0917.d009869 face j)
  · simpa [_root_.GD.N0232.N0719.N0917.d009872] using
      (show 0 < _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
          (_root_.GD.N0232.N0719.N1007.d009817 commonPower
            (_root_.GD.N0232.N0719.N0928.d009408 (_root_.GD.N0232.N0719.N0917.d009871 sizes face))) by
        rw [_root_.GD.N0232.N0719.N1007.d009823]
        exact hcommon)



theorem d009891
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) (hweight : ∀ f, 0 < weight f) :
    0 < _root_.GD.N0232.N0719.N0917.d009875 sizes y t commonPower weight := by
  classical
  let i : Fin k := ⟨0, hk⟩
  let face : _root_.GD.N0232.N0719.N0917.d009868 k := ⟨{i}, by simp⟩
  unfold _root_.GD.N0232.N0719.N0917.d009875 _root_.GD.N0232.N0719.N1007.d009826
  exact Finset.sum_pos'
    (fun f _ ↦ (mul_pos (hweight f)
      (_root_.GD.N0232.N0719.N0917.d009890 sizes hsizes y t ht commonPower hcommon f)).le)
    ⟨face, Finset.mem_univ _, mul_pos (hweight face)
      (_root_.GD.N0232.N0719.N0917.d009890 sizes hsizes y t ht commonPower hcommon face)⟩




theorem d009892
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) (shift dilation : ℝ)
    (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0917.d009873 sizes (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y)
        (_root_.GD.N0232.N0719.N0866.d009656 dilation t) commonPower face =
      (dilation ^ 2) ^ (-commonPower) *
        _root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower face := by
  unfold _root_.GD.N0232.N0719.N0917.d009873
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) := by
    rw [_root_.GD.N0232.N0719.N0917.d009872, _root_.GD.N0232.N0719.N1007.d009823]
    exact hcommon
  have hmatched : _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) = commonPower := by
    rw [_root_.GD.N0232.N0719.N0917.d009872, _root_.GD.N0232.N0719.N1007.d009823]
  simpa [hmatched] using _root_.GD.N0232.N0719.N0866.d009661
    (Finset.card_pos.mpr face.2)
    (_root_.GD.N0232.N0719.N0917.d009871 sizes face) (_root_.GD.N0232.N0719.N0917.d009870 y face) (_root_.GD.N0232.N0719.N0917.d009870 t face)
    (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) shift dilation
    (_root_.GD.N0232.N0719.N0917.d009889 sizes hsizes face)
    (fun j ↦ ht (_root_.GD.N0232.N0719.N0917.d009869 face j)) hpower hdilation


theorem d009893
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (face : _root_.GD.N0232.N0719.N0917.d009868 k) (shift dilation : ℝ)
    (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0917.d009874 sizes (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y)
        (_root_.GD.N0232.N0719.N0866.d009656 dilation t) commonPower face =
      shift + dilation * _root_.GD.N0232.N0719.N0917.d009874 sizes y t commonPower face := by
  unfold _root_.GD.N0232.N0719.N0917.d009874
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0917.d009871 sizes face)
      (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) := by
    rw [_root_.GD.N0232.N0719.N0917.d009872, _root_.GD.N0232.N0719.N1007.d009823]
    exact hcommon
  simpa using _root_.GD.N0232.N0719.N0866.d009663
    (Finset.card_pos.mpr face.2)
    (_root_.GD.N0232.N0719.N0917.d009871 sizes face) (_root_.GD.N0232.N0719.N0917.d009870 y face) (_root_.GD.N0232.N0719.N0917.d009870 t face)
    (_root_.GD.N0232.N0719.N0917.d009872 sizes commonPower face) shift dilation
    (_root_.GD.N0232.N0719.N0917.d009889 sizes hsizes face)
    (fun j ↦ ht (_root_.GD.N0232.N0719.N0917.d009869 face j)) hpower hdilation


theorem d009894
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (weight : _root_.GD.N0232.N0719.N0917.d009868 k → ℝ) (hweight : ∀ f, 0 < weight f)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0917.d009877 sizes (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y)
        (_root_.GD.N0232.N0719.N0866.d009656 dilation t) commonPower weight =
      shift + dilation *
        _root_.GD.N0232.N0719.N0917.d009877 sizes y t commonPower weight := by
  let character : ℝ := (dilation ^ 2) ^ (-commonPower)
  have hcharacter : character ≠ 0 := by
    exact (Real.rpow_pos_of_pos (sq_pos_of_pos hdilation) _).ne'
  have hdenom :
      _root_.GD.N0232.N0719.N1007.d009826 weight (_root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower) ≠ 0 := by
    exact (_root_.GD.N0232.N0719.N0917.d009891 hk sizes hsizes y t ht
      commonPower hcommon weight hweight).ne'
  unfold _root_.GD.N0232.N0719.N0917.d009877
  rw [show _root_.GD.N0232.N0719.N0917.d009873 sizes (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y)
      (_root_.GD.N0232.N0719.N0866.d009656 dilation t) commonPower =
        fun face ↦ character * _root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower face by
      funext face
      exact _root_.GD.N0232.N0719.N0917.d009892 sizes hsizes y t ht commonPower hcommon
        face shift dilation hdilation]
  rw [show _root_.GD.N0232.N0719.N0917.d009874 sizes (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y)
      (_root_.GD.N0232.N0719.N0866.d009656 dilation t) commonPower =
        fun face ↦ shift + dilation * _root_.GD.N0232.N0719.N0917.d009874 sizes y t commonPower face by
      funext face
      exact _root_.GD.N0232.N0719.N0917.d009893 sizes hsizes y t ht commonPower hcommon
        face shift dilation hdilation]
  exact _root_.GD.N0232.N0719.N1007.d009830
    weight (_root_.GD.N0232.N0719.N0917.d009873 sizes y t commonPower)
      (_root_.GD.N0232.N0719.N0917.d009874 sizes y t commonPower)
      character shift dilation hcharacter hdenom


theorem d009895
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (commonPower : ℝ) (hcommon : 0 < commonPower)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0917.d009878 sizes
        (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y) (_root_.GD.N0232.N0719.N0866.d009656 dilation t)
        commonPower =
      shift + dilation *
        _root_.GD.N0232.N0719.N0917.d009878 sizes y t commonPower := by
  exact _root_.GD.N0232.N0719.N0917.d009894 hk sizes hsizes y t ht
    commonPower hcommon (fun _ ↦ 1) (fun _ ↦ by norm_num)
    shift dilation hdilation



theorem d009896
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0917.d009880 sizes
        (_root_.GD.N0232.N0719.N0866.d009655 shift dilation y) (_root_.GD.N0232.N0719.N0866.d009656 dilation t) =
      shift + dilation * _root_.GD.N0232.N0719.N0917.d009880 sizes y t := by
  unfold _root_.GD.N0232.N0719.N0917.d009880
  exact _root_.GD.N0232.N0719.N0917.d009895 hk sizes hsizes y t ht
    (_root_.GD.N0232.N0719.N0917.d009879 sizes)
    (_root_.GD.N0232.N0719.N0917.d009888 hk sizes
      (fun i ↦ le_trans (by norm_num) (hsizes i)))
    shift dilation hdilation

end

end N0917
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0917.d009883
#print axioms _root_.GD.N0232.N0719.N0917.d009890
#print axioms _root_.GD.N0232.N0719.N0917.d009891
#print axioms _root_.GD.N0232.N0719.N0917.d009894
#print axioms _root_.GD.N0232.N0719.N0917.d009895
#print axioms _root_.GD.N0232.N0719.N0917.d009887
#print axioms _root_.GD.N0232.N0719.N0917.d009896
