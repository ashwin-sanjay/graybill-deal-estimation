import GD.Module0671
























namespace GD
namespace N0232
namespace N0719
namespace N0907

noncomputable section

open _root_.GD.N0232.N0719.N1007


def d009855 (s : ℝ) : ℝ :=
  5 - 2 * s


def d009856 (n : ℕ) : ℝ :=
  n


def d009857 {I : Type*}
    (sizes : I → ℕ) (deleted : Finset I) : ℝ :=
  ∑ i ∈ deleted, (sizes i : ℝ)



def d009858 (fullInformationOrder : ℝ) : ℝ :=
  fullInformationOrder + 1



theorem d009859
    (fullInformationOrder : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817
        (_root_.GD.N0232.N0719.N0907.d009858 fullInformationOrder)
        fullInformationOrder = 5 / 2 := by
  unfold _root_.GD.N0232.N0719.N0907.d009858 _root_.GD.N0232.N0719.N1007.d009817
  ring



theorem d009860
    (fullInformationOrder faceInformationOrder : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817
        (_root_.GD.N0232.N0719.N0907.d009858 fullInformationOrder)
        faceInformationOrder =
      5 / 2 + (fullInformationOrder - faceInformationOrder) := by
  unfold _root_.GD.N0232.N0719.N0907.d009858 _root_.GD.N0232.N0719.N1007.d009817
  ring



theorem d009861
    (s : ℝ) (n : ℕ) :
    _root_.GD.N0232.N0719.N0907.d009855 (s + (n : ℝ) / 2) =
      _root_.GD.N0232.N0719.N0907.d009855 s - n := by
  unfold _root_.GD.N0232.N0719.N0907.d009855
  ring


theorem d009862
    (s : ℝ) (n : ℕ) :
    _root_.GD.N0232.N0719.N0907.d009855 (s + (n : ℝ) / 2) +
        _root_.GD.N0232.N0719.N0907.d009856 n =
      _root_.GD.N0232.N0719.N0907.d009855 s := by
  rw [_root_.GD.N0232.N0719.N0907.d009861]
  unfold _root_.GD.N0232.N0719.N0907.d009856
  ring



theorem d009863
    (s deletedDimension : ℝ) :
    _root_.GD.N0232.N0719.N0907.d009855 (s + deletedDimension / 2) +
        deletedDimension =
      _root_.GD.N0232.N0719.N0907.d009855 s := by
  unfold _root_.GD.N0232.N0719.N0907.d009855
  ring


theorem d009864
    {I : Type*} (sizes : I → ℕ) (deleted : Finset I) (s : ℝ) :
    _root_.GD.N0232.N0719.N0907.d009855
          (s + _root_.GD.N0232.N0719.N0907.d009857 sizes deleted / 2) +
        _root_.GD.N0232.N0719.N0907.d009857 sizes deleted =
      _root_.GD.N0232.N0719.N0907.d009855 s :=
  _root_.GD.N0232.N0719.N0907.d009863 s
    (_root_.GD.N0232.N0719.N0907.d009857 sizes deleted)



theorem d009865
    (n : ℕ) (hn : 1 ≤ n) :
    (((n - 1 : ℕ) : ℝ) / 2) + 1 / 2 = (n : ℝ) / 2 := by
  rw [Nat.cast_sub hn]
  norm_num
  ring



theorem d009866
    (commonPower parentOrder : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (parentOrder - (((n - 1 : ℕ) : ℝ) / 2 + 1 / 2)) =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower parentOrder + (n : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0907.d009865 n hn]
  unfold _root_.GD.N0232.N0719.N1007.d009817
  ring





theorem d009867
    (commonPower parentOrder : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    _root_.GD.N0232.N0719.N0907.d009855
          (_root_.GD.N0232.N0719.N1007.d009817 commonPower
            (parentOrder - (((n - 1 : ℕ) : ℝ) / 2 + 1 / 2))) +
        _root_.GD.N0232.N0719.N0907.d009856 n =
      _root_.GD.N0232.N0719.N0907.d009855
        (_root_.GD.N0232.N0719.N1007.d009817 commonPower parentOrder) := by
  rw [_root_.GD.N0232.N0719.N0907.d009866
    commonPower parentOrder n hn]
  exact _root_.GD.N0232.N0719.N0907.d009862
    (_root_.GD.N0232.N0719.N1007.d009817 commonPower parentOrder) n

end

end N0907
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0907.d009861
#print axioms _root_.GD.N0232.N0719.N0907.d009860
#print axioms _root_.GD.N0232.N0719.N0907.d009862
#print axioms _root_.GD.N0232.N0719.N0907.d009864
#print axioms _root_.GD.N0232.N0719.N0907.d009865
#print axioms _root_.GD.N0232.N0719.N0907.d009867
