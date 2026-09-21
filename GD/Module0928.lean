import GD.Module0893
import GD.Module0901
import GD.Module0923
import GD.Module0920
import GD.Module0061





























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1075

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1070
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0230.N0565
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn

noncomputable local instance : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩





def d014487 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1442.d013869
    (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
    (_root_.GD.N0232.N0720.N1069.d014352 m n theta)


def d014488 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1442.d013868
    (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
    (_root_.GD.N0232.N0720.N1069.d014352 m n theta)

theorem d014489 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0232.N0720.N1075.d014488 m n theta := by
  unfold _root_.GD.N0232.N0720.N1075.d014488 _root_.GD.N0232.N0720.N1442.d013868
  exact div_nonneg
    (_root_.GD.N0232.N0720.N1442.d013870 _ _ _)
    (_root_.GD.N0232.N0720.N1442.d013871
      (_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta)).le

theorem d014490 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0232.N0720.N1075.d014487 m n theta := by
  unfold _root_.GD.N0232.N0720.N1075.d014487 _root_.GD.N0232.N0720.N1442.d013869 _root_.GD.N0232.N0720.N1442.d013866
  exact div_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta).le
      (sub_nonneg.mpr (_root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta).le))
    (_root_.GD.N0232.N0720.N1442.d013871
      (_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta)).le


theorem d014491 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1075.d014487 m n theta +
        _root_.GD.N0232.N0720.N1075.d014488 m n theta = 1 := by
  exact _root_.GD.N0232.N0720.N1442.d013872
    (alpha := _root_.GD.N0232.N0720.N1433.d014024 m) (beta := _root_.GD.N0232.N0720.N1433.d014025 n)
    (_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta)

theorem d014492 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1075.d014487 m n theta ≤ 1 := by
  linarith [_root_.GD.N0232.N0720.N1075.d014491 m n hm hn theta,
    _root_.GD.N0232.N0720.N1075.d014489 m n hm hn theta]

theorem d014493 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1075.d014488 m n theta ≤ 1 := by
  linarith [_root_.GD.N0232.N0720.N1075.d014491 m n hm hn theta,
    _root_.GD.N0232.N0720.N1075.d014490 m n hm hn theta]



theorem d014494
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1075.d014487 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
      _root_.GD.N0232.N0720.N1075.d014487 m n theta := by
  unfold _root_.GD.N0232.N0720.N1075.d014487
  rw [_root_.GD.N0232.N0720.N1069.d014355 m n hm hn]

theorem d014495
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1075.d014488 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
      _root_.GD.N0232.N0720.N1075.d014488 m n theta := by
  unfold _root_.GD.N0232.N0720.N1075.d014488
  rw [_root_.GD.N0232.N0720.N1069.d014355 m n hm hn]






def d014496
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d -
      _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
    _root_.GD.N0232.N0720.N1075.d014488 m n theta


def d014497
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q /
    _root_.GD.N0232.N0720.N1075.d014488 m n theta



theorem d014498
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q =
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  have h := _root_.GD.N0230.N0567.d001642
    (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)
    (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta) p q
  rw [_root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hp,
    _root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hq,
    _root_.GD.N0230.N0567.d001633
      (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta hmid] at h
  exact h


theorem d014499
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1075.d014496 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0232.N0720.N1075.d014497 m n hm hn theta p q =
      (_root_.GD.N0232.N0720.N1075.d014496 m n hm hn theta p +
        _root_.GD.N0232.N0720.N1075.d014496 m n hm hn theta q) / 2 := by
  have h := _root_.GD.N0232.N0720.N1075.d014498
    m n hm hn theta hp hq
  unfold _root_.GD.N0232.N0720.N1075.d014496 _root_.GD.N0232.N0720.N1075.d014497
  calc
    (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta +
        _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta =
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta := by ring
    _ = (((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2) -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta := by rw [h]
    _ = ((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta +
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014488 m n theta) / 2 := by ring

theorem d014500
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1075.d014497 m n hm hn theta p q := by
  exact div_nonneg
    (_root_.GD.N0232.N0720.N1066.d014339 m n hm hn hp hq
      (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta))
    (_root_.GD.N0232.N0720.N1075.d014489 m n hm hn theta)




def d014501 (epsilon : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1075.d014488 m n theta + epsilon

theorem d014502
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta := by
  unfold _root_.GD.N0232.N0720.N1075.d014501
  exact add_pos_of_nonneg_of_pos
    (_root_.GD.N0232.N0720.N1075.d014489 m n hm hn theta) hepsilon


def d014503
    (epsilon : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d -
      _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
    _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta


def d014504
    (epsilon : ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p q : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q /
    _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta

theorem d014505
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta d ∈
      Set.Icc (-1 / epsilon) (1 / epsilon) := by
  have hscale := _root_.GD.N0232.N0720.N1075.d014502
    m n hm hn hepsilon theta
  have hscaleLower : epsilon ≤
      _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta := by
    unfold _root_.GD.N0232.N0720.N1075.d014501
    linarith [_root_.GD.N0232.N0720.N1075.d014489 m n hm hn theta]
  have hnumLower : -1 ≤
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d -
        _root_.GD.N0232.N0720.N1075.d014487 m n theta := by
    linarith [_root_.GD.N0232.N0720.N1066.d014328 m n hm hn theta d,
      _root_.GD.N0232.N0720.N1075.d014492 m n hm hn theta]
  have hnumUpper :
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta ≤ 1 := by
    linarith [_root_.GD.N0232.N0720.N1066.d014329 m n hm hn theta d,
      _root_.GD.N0232.N0720.N1075.d014490 m n hm hn theta]
  constructor
  · unfold _root_.GD.N0232.N0720.N1075.d014503
    rw [le_div_iff₀ hscale]
    have hcoeff : -1 / epsilon ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hepsilon.le
    calc
      (-1 / epsilon) * _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta ≤
          (-1 / epsilon) * epsilon :=
        mul_le_mul_of_nonpos_left hscaleLower hcoeff
      _ = -1 := by field_simp [hepsilon.ne']
      _ ≤ _ := hnumLower
  · unfold _root_.GD.N0232.N0720.N1075.d014503
    rw [div_le_iff₀ hscale]
    have hcoeff : 0 ≤ 1 / epsilon := by positivity
    calc
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta ≤ 1 := hnumUpper
      _ = (1 / epsilon) * epsilon := by field_simp [hepsilon.ne']
      _ ≤ (1 / epsilon) *
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta :=
        mul_le_mul_of_nonneg_left hscaleLower hcoeff



def d014506
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0567.d001622 _root_.GD.N0232.N0720.N1080.d014168 (_root_.GD.N0232.N0720.N1025.d014303 m n)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (-1 / epsilon) (1 / epsilon) where
  profile := _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon
  mem_Icc := by
    intro theta d _hd
    exact _root_.GD.N0232.N0720.N1075.d014505
      m n hm hn hepsilon theta d



def d014507
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0230.N0567.d001636 (_root_.GD.N0232.N0720.N1075.d014506 m n hm hn epsilon hepsilon) d

theorem d014508
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    BddAbove (Set.range (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
      _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta d)) := by
  refine ⟨1 / epsilon, ?_⟩
  rintro value ⟨theta, rfl⟩
  exact (_root_.GD.N0232.N0720.N1075.d014505
    m n hm hn hepsilon theta d).2

theorem d014509
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n} (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    IsLUB
      (Set.range (fun theta : _root_.GD.N0232.N0720.N1080.d014168 =>
        _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta d))
      (_root_.GD.N0232.N0720.N1075.d014507 m n hm hn epsilon hepsilon d) := by
  exact _root_.GD.N0230.N0567.d001638
    (_root_.GD.N0232.N0720.N1075.d014506 m n hm hn epsilon hepsilon) hd





theorem d014510 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta) := by
  intro e d hed
  by_cases hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · have he : e ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      _root_.GD.N0232.N0720.N1025.d014314 m n hm hn hd hed
    exact _root_.GD.N0232.N0720.N1066.d014346
      m n hm hn he hd hed theta
  · rw [show _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta d = 1 by
      simp [_root_.GD.N0232.N0720.N1066.d014327, hd]]
    exact _root_.GD.N0232.N0720.N1066.d014329 m n hm hn theta e

theorem d014511
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta) := by
  exact _root_.GD.N0230.N0565.d000739
    (_root_.GD.N0232.N0720.N1025.d014305 m n) (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1075.d014487 m n theta)
    (_root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta)
    (_root_.GD.N0232.N0720.N1075.d014510 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1075.d014502 m n hm hn hepsilon theta)

theorem d014512
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1075.d014507 m n hm hn epsilon hepsilon) := by
  intro e d hed
  unfold _root_.GD.N0232.N0720.N1075.d014507 _root_.GD.N0230.N0567.d001636
  apply ciSup_le
  intro theta
  calc
    _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta e ≤
        _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta d :=
      _root_.GD.N0232.N0720.N1075.d014511
        m n hm hn hepsilon theta hed
    _ ≤ ⨆ eta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon eta d := by
      exact le_ciSup
        (_root_.GD.N0232.N0720.N1075.d014508
          m n hm hn hepsilon d) theta



theorem d014513
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta
          (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0232.N0720.N1075.d014504 m n hm hn epsilon theta p q =
      (_root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta p +
        _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta q) / 2 := by
  have h := _root_.GD.N0232.N0720.N1075.d014498
    m n hm hn theta hp hq
  unfold _root_.GD.N0232.N0720.N1075.d014503 _root_.GD.N0232.N0720.N1075.d014504
  calc
    (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta +
        _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta =
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta := by ring
    _ = (((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2) -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta := by rw [h]
    _ = ((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta +
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta) / 2 := by ring

theorem d014514
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1075.d014504 m n hm hn epsilon theta p q := by
  exact div_nonneg
    (_root_.GD.N0232.N0720.N1066.d014339 m n hm hn hp hq
      (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta))
    (_root_.GD.N0232.N0720.N1075.d014502 m n hm hn hepsilon theta).le



theorem d014515
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta) p.1 := by
  unfold _root_.GD.N0232.N0720.N1075.d014503 _root_.GD.N0232.N0720.N1075.d014501
  rw [_root_.GD.N0232.N0720.N1066.d014349 m n hm hn g theta p,
    _root_.GD.N0232.N0720.N1075.d014494 m n hm hn g⁻¹ theta,
    _root_.GD.N0232.N0720.N1075.d014495 m n hm hn g⁻¹ theta]



theorem d014516
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1075.d014507 m n hm hn epsilon hepsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1075.d014507 m n hm hn epsilon hepsilon p.1 := by
  unfold _root_.GD.N0232.N0720.N1075.d014507 _root_.GD.N0230.N0567.d001636
  change
    (⨆ theta, _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1) =
      ⨆ theta, _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta p.1
  apply le_antisymm
  · apply ciSup_le
    intro theta
    rw [_root_.GD.N0232.N0720.N1075.d014515
      m n hm hn hepsilon g theta p]
    exact le_ciSup
      (_root_.GD.N0232.N0720.N1075.d014508
        m n hm hn hepsilon p.1)
      (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta)
  · apply ciSup_le
    intro eta
    have hle := le_ciSup
      (_root_.GD.N0232.N0720.N1075.d014508
        m n hm hn hepsilon (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1)
      (_root_.GD.N0232.N0720.N1215.d014272 g eta)
    rw [_root_.GD.N0232.N0720.N1075.d014515
      m n hm hn hepsilon g (_root_.GD.N0232.N0720.N1215.d014272 g eta) p] at hle
    simpa using hle

end

end N1075
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1075.d014489
#print axioms _root_.GD.N0232.N0720.N1075.d014499
#print axioms _root_.GD.N0232.N0720.N1075.d014505
#print axioms _root_.GD.N0232.N0720.N1075.d014512
#print axioms _root_.GD.N0232.N0720.N1075.d014513
#print axioms _root_.GD.N0232.N0720.N1075.d014515
#print axioms _root_.GD.N0232.N0720.N1075.d014516
