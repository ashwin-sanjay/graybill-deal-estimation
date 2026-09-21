import GD.Module0512
import GD.Module1522
import GD.Module1298








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Finset
open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1549
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1623 _root_.GD.N0106.N0428.N0765.N1545 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1611
  _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1627
open _root_.GD.N0232.N0720.N1249

def d023693 (k : ℕ) (I : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨I.lo ^ k, I.hi ^ k⟩

theorem d023694 {k : ℕ} (hk : Odd k) {I : _root_.GD.N0232.N0720.N1164.d006809} {x : ℝ}
    (hx : I.d006810 x) : (_root_.GD.N0106.N0428.N0765.N1549.d023693 k I).d006810 (x ^ k) := by
  unfold _root_.GD.N0106.N0428.N0765.N1549.d023693 _root_.GD.N0232.N0720.N1164.d006809.d006810
  push_cast
  exact ⟨hk.pow_le_pow.mpr hx.1, hk.pow_le_pow.mpr hx.2⟩

def d023695 (k : ℕ) (H : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1623.d007722 (_root_.GD.N0106.N0428.N0765.N1623.d007722 H (_root_.GD.N0232.N0720.N1164.d006809.d006811.d006813 H))
    (_root_.GD.N0106.N0428.N0765.N1549.d023693 k (H.d006813 (_root_.GD.N0106.N0428.N0765.N1545.d006828 (1 / 2))))

theorem d023696 {k : ℕ} (hk : Odd k) {H : _root_.GD.N0232.N0720.N1164.d006809} {h : ℝ}
    (hH : H.d006810 h) : (_root_.GD.N0106.N0428.N0765.N1549.d023695 k H).d006810 (_root_.GD.N0232.N0720.N1249.d002197 k h) := by
  have hhalf : (_root_.GD.N0106.N0428.N0765.N1545.d006828 (1 / 2)).d006810 (1 / 2 : ℝ) := by
    simpa using _root_.GD.N0106.N0428.N0765.N1545.d006829 (1 / 2)
  exact _root_.GD.N0106.N0428.N0765.N1623.d007724 (_root_.GD.N0106.N0428.N0765.N1623.d007724 hH (_root_.GD.N0232.N0720.N1164.d006809.d006820 _root_.GD.N0232.N0720.N1164.d006809.d006818 hH))
    (_root_.GD.N0106.N0428.N0765.N1549.d023694 hk (_root_.GD.N0232.N0720.N1164.d006809.d006820 hH hhalf))

def d023697 (V D G O H : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1623.d007722 V (_root_.GD.N0106.N0428.N0765.N1623.d007722 D ((_root_.GD.N0106.N0428.N0765.N1545.d006833 (G.d006813 O)).d006813 (_root_.GD.N0106.N0428.N0765.N1545.d006833 (H.d006813 O))))

def d023698 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (H F : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if j.2 = 1 then _root_.GD.N0106.N0428.N0765.N1623.d007722 (_root_.GD.N0106.N0428.N0765.N1549.d023695 j.1.val H) F
  else (_root_.GD.N0106.N0428.N0765.N1549.d023695 j.1.val H).d006817 (-1)

def d023699 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (V D O H F : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1623.d007722 V (_root_.GD.N0106.N0428.N0765.N1623.d007722 D (_root_.GD.N0106.N0428.N0765.N1623.d007722 (H.d006813 O) (_root_.GD.N0106.N0428.N0765.N1549.d023698 j H F)))


def d023700 (eta : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((1 + eta) / 11) * _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)



def d023701 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((1 + eta) / 11) * _root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)

theorem d023702 {eta : ℝ} (heta : 0 < eta) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) = Real.exp b / (Real.exp b + eta) := by
  change ((1 - Real.sigmoid a) * Real.sigmoid b) /
    ((1 - Real.sigmoid a) * Real.sigmoid b +
      eta * ((1 - Real.sigmoid a) * (1 - Real.sigmoid b))) = _
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  field_simp [show 1 + Real.exp a ≠ 0 by positivity,
    show 1 + Real.exp b ≠ 0 by positivity, show Real.exp b + eta ≠ 0 by positivity]
  <;> ring

theorem d023703 {eta : ℝ} (heta : 0 < eta) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) =
      10 * (1 + eta) * Real.exp a * (1 + Real.exp b) / (Real.exp b + eta) := by
  change 10 * (1 + eta) * Real.sigmoid a /
    ((1 - Real.sigmoid a) * Real.sigmoid b +
      eta * ((1 - Real.sigmoid a) * (1 - Real.sigmoid b))) = _
  simp only [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  field_simp [show 1 + Real.exp a ≠ 0 by positivity,
    show 1 + Real.exp b ≠ 0 by positivity, show Real.exp b + eta ≠ 0 by positivity]
  <;> ring

theorem d023704 {eta : ℝ} {p : ℝ × ℝ} {V D G O H : _root_.GD.N0232.N0720.N1164.d006809}
    (hV : V.d006810 ((1 + eta) / 11)) (hD : D.d006810 (_root_.GD.N0106.N0428.N0765.N1521.d020868 p))
    (hG : G.d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)))
    (hO : O.d006810 (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
    (hH : H.d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p))) :
    (_root_.GD.N0106.N0428.N0765.N1549.d023697 V D G O H).d006810 (_root_.GD.N0106.N0428.N0765.N1549.d023700 eta p) := by
  have h := _root_.GD.N0106.N0428.N0765.N1623.d007724 hV (_root_.GD.N0106.N0428.N0765.N1623.d007724 hD
    (_root_.GD.N0232.N0720.N1164.d006809.d006820 (_root_.GD.N0106.N0428.N0765.N1545.d006834 (_root_.GD.N0232.N0720.N1164.d006809.d006820 hG hO))
      (_root_.GD.N0106.N0428.N0765.N1545.d006834 (_root_.GD.N0232.N0720.N1164.d006809.d006820 hH hO))))
  simpa only [_root_.GD.N0106.N0428.N0765.N1549.d023697, _root_.GD.N0106.N0428.N0765.N1549.d023700, _root_.GD.N0106.N0428.N0765.N1529.d020802, mul_assoc] using h

theorem d023705 {j : _root_.GD.N0106.N0428.N0765.N1607.d012643} (hj : Odd j.1.val)
    {H F : _root_.GD.N0232.N0720.N1164.d006809} {h f : ℝ} (hH : H.d006810 h) (hF : F.d006810 f) :
    (_root_.GD.N0106.N0428.N0765.N1549.d023698 j H F).d006810 (_root_.GD.N0106.N0428.N0765.N1627.d021101 j h f) := by
  by_cases hc : j.2 = 1
  · simp only [_root_.GD.N0106.N0428.N0765.N1549.d023698, _root_.GD.N0106.N0428.N0765.N1627.d021101, if_pos hc]
    exact _root_.GD.N0106.N0428.N0765.N1623.d007724 (_root_.GD.N0106.N0428.N0765.N1549.d023696 hj hH) hF
  · simp only [_root_.GD.N0106.N0428.N0765.N1549.d023698, _root_.GD.N0106.N0428.N0765.N1627.d021101, if_neg hc]
    simpa only [Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      _root_.GD.N0232.N0720.N1164.d006809.d006824 (-1) (_root_.GD.N0106.N0428.N0765.N1549.d023696 hj hH)

theorem d023706 {j : _root_.GD.N0106.N0428.N0765.N1607.d012643} (hj : Odd j.1.val)
    {eta : ℝ} {p : ℝ × ℝ} {V D O H F : _root_.GD.N0232.N0720.N1164.d006809}
    (hV : V.d006810 ((1 + eta) / 11)) (hD : D.d006810 (_root_.GD.N0106.N0428.N0765.N1521.d020868 p))
    (hO : O.d006810 (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
    (hH : H.d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)))
    (hF : F.d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 p))) :
    (_root_.GD.N0106.N0428.N0765.N1549.d023699 j V D O H F).d006810 (_root_.GD.N0106.N0428.N0765.N1549.d023701 j eta p) := by
  have h := _root_.GD.N0106.N0428.N0765.N1623.d007724 hV (_root_.GD.N0106.N0428.N0765.N1623.d007724 hD
    (_root_.GD.N0106.N0428.N0765.N1623.d007724 (_root_.GD.N0232.N0720.N1164.d006809.d006820 hH hO) (_root_.GD.N0106.N0428.N0765.N1549.d023705 hj hH hF)))
  simpa only [_root_.GD.N0106.N0428.N0765.N1549.d023699, _root_.GD.N0106.N0428.N0765.N1549.d023701, _root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102,
    mul_assoc] using h



theorem d023707 (eta : ℝ) (p : ℕ → ℝ × ℝ) (N : ℕ) (h : ℚ)
    (V O : _root_.GD.N0232.N0720.N1164.d006809) (D G H : ℕ → _root_.GD.N0232.N0720.N1164.d006809)
    (hV : V.d006810 ((1 + eta) / 11)) (hO : O.d006810 (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
    (hD : ∀ i, i < N → (D i).d006810 (_root_.GD.N0106.N0428.N0765.N1521.d020868 (p i)))
    (hG : ∀ i, i < N → (G i).d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (p i))))
    (hH : ∀ i, i < N → (H i).d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (p i)))) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006837 (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023697 V (D i) (G i) O (H i)) N).d006817 (h ^ 2)).d006810
      ((h : ℝ) ^ 2 * ∑ i ∈ range N, _root_.GD.N0106.N0428.N0765.N1549.d023700 eta (p i)) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1545.d006838
    (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023697 V (D i) (G i) O (H i)) (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023700 eta (p i)) N
    (fun i hi => _root_.GD.N0106.N0428.N0765.N1549.d023704 hV (hD i hi) (hG i hi) hO (hH i hi))
  have hcast : ((h ^ 2 : ℚ) : ℝ) = (h : ℝ) ^ 2 :=
    (Rat.castHom ℝ).map_pow h 2
  exact (congrArg
    (fun r : ℝ =>
      ((_root_.GD.N0106.N0428.N0765.N1545.d006837 (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023697 V (D i) (G i) O (H i)) N).d006817 (h ^ 2)).d006810
        (r * ∑ i ∈ range N, _root_.GD.N0106.N0428.N0765.N1549.d023700 eta (p i))) hcast).mp
    (_root_.GD.N0232.N0720.N1164.d006809.d006824 (h ^ 2) hs)


theorem d023708 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (hj : Odd j.1.val)
    (eta : ℝ) (p : ℕ → ℝ × ℝ) (N : ℕ) (h : ℚ)
    (V O : _root_.GD.N0232.N0720.N1164.d006809) (D H F : ℕ → _root_.GD.N0232.N0720.N1164.d006809)
    (hV : V.d006810 ((1 + eta) / 11)) (hO : O.d006810 (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
    (hD : ∀ i, i < N → (D i).d006810 (_root_.GD.N0106.N0428.N0765.N1521.d020868 (p i)))
    (hH : ∀ i, i < N → (H i).d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (p i))))
    (hF : ∀ i, i < N → (F i).d006810 (_root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (p i)))) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006837 (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023699 j V (D i) O (H i) (F i)) N).d006817 (h ^ 2)).d006810
      ((h : ℝ) ^ 2 * ∑ i ∈ range N, _root_.GD.N0106.N0428.N0765.N1549.d023701 j eta (p i)) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1545.d006838
    (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023699 j V (D i) O (H i) (F i)) (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023701 j eta (p i)) N
    (fun i hi => _root_.GD.N0106.N0428.N0765.N1549.d023706 hj hV (hD i hi) hO (hH i hi) (hF i hi))
  have hcast : ((h ^ 2 : ℚ) : ℝ) = (h : ℝ) ^ 2 :=
    (Rat.castHom ℝ).map_pow h 2
  exact (congrArg
    (fun r : ℝ =>
      ((_root_.GD.N0106.N0428.N0765.N1545.d006837 (fun i => _root_.GD.N0106.N0428.N0765.N1549.d023699 j V (D i) O (H i) (F i)) N).d006817 (h ^ 2)).d006810
        (r * ∑ i ∈ range N, _root_.GD.N0106.N0428.N0765.N1549.d023701 j eta (p i))) hcast).mp
    (_root_.GD.N0232.N0720.N1164.d006809.d006824 (h ^ 2) hs)

end
end GD.N0106.N0428.N0765.N1549

#print axioms _root_.GD.N0106.N0428.N0765.N1549.d023707
#print axioms _root_.GD.N0106.N0428.N0765.N1549.d023708
