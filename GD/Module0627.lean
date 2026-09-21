import GD.Module0624
import GD.Module0317



























namespace GD.N0232.N0719.N0919

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0238.N0754

noncomputable section



def d009163 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0238.N0754.d004714 k where
  mean := s.mean
  scale i := Real.sqrt (s.meanVariance i)



theorem d009164 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hs : ∀ i, 0 ≤ s.meanVariance i) :
    _root_.GD.N0238.N0754.d004716 (_root_.GD.N0232.N0719.N0919.d009163 s) := by
  intro i
  exact Real.sqrt_nonneg _



theorem d009165 {k : ℕ}
    (shift dilation : ℝ) (hdilation : 0 ≤ dilation)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0919.d009163 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      _root_.GD.N0238.N0754.d004715
        shift dilation (_root_.GD.N0232.N0719.N0919.d009163 s) := by
  ext i
  · rfl
  · change Real.sqrt (dilation ^ 2 * s.meanVariance i) =
      dilation * Real.sqrt (s.meanVariance i)
    rw [Real.sqrt_mul (sq_nonneg dilation), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hdilation]



theorem d009166
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0238.N0754.d004716 (_root_.GD.N0232.N0719.N0919.d009163 (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) := by
  apply _root_.GD.N0232.N0719.N0919.d009164
  intro i
  exact _root_.GD.N0232.N0719.N0900.d009125 hsizes omega i



theorem d009167
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 ≤ dilation)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0919.d009163
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes
          (_root_.GD.N0232.N0719.N0900.d009095
            k sizes shift dilation omega)) =
      _root_.GD.N0238.N0754.d004715
        shift dilation (_root_.GD.N0232.N0719.N0919.d009163 (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) := by
  rw [_root_.GD.N0232.N0719.N0900.d009139
    (fun i ↦ lt_of_lt_of_le (by omega) (hsizes i))]
  exact _root_.GD.N0232.N0719.N0919.d009165 shift dilation hdilation _



theorem d009168
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (anchor : Fin k)
    (shift dilation : ℝ) (hdilation : 0 ≤ dilation)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0238.N0754.d004718 anchor
        (_root_.GD.N0232.N0719.N0919.d009163
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes
            (_root_.GD.N0232.N0719.N0900.d009095
              k sizes shift dilation omega))) =
      dilation • _root_.GD.N0238.N0754.d004718 anchor
        (_root_.GD.N0232.N0719.N0919.d009163 (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) := by
  rw [_root_.GD.N0232.N0719.N0919.d009167
    hsizes shift dilation hdilation omega]
  exact _root_.GD.N0238.N0754.d004719 anchor shift dilation _

end

end GD.N0232.N0719.N0919

#print axioms _root_.GD.N0232.N0719.N0919.d009165
#print axioms _root_.GD.N0232.N0719.N0919.d009166
#print axioms _root_.GD.N0232.N0719.N0919.d009168
