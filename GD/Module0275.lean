import GD.Module0023
import GD.Module0274

































open MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1443

noncomputable section





def d004045 (a b : ℝ) : ℝ :=
  a + b + 3 / 2



def d004046
    (a b observation contrast parameter : ℝ) : ℝ :=
  a * observation * (1 - parameter) +
    b * (1 - observation) * parameter +
    contrast * parameter * (1 - parameter)



def d004047 (a b t : ℝ) : ℝ :=
  b / (b + a * t)



theorem d004048
    {a b t parameter : ℝ}
    (hden : b + a * t ≠ 0) :
    _root_.GD.N0232.N0720.N1443.d004046 a b (_root_.GD.N0232.N0720.N1443.d004047 a b t) 0 parameter =
      (a * b / (b + a * t)) * (1 + (t - 1) * parameter) := by
  unfold _root_.GD.N0232.N0720.N1443.d004046 _root_.GD.N0232.N0720.N1443.d004047
  field_simp [hden]
  ring



theorem d004049
    {a b parameter : ℝ} (hab : a + b ≠ 0) :
    _root_.GD.N0232.N0720.N1443.d004046 a b (b / (a + b)) 0 parameter =
      a * b / (a + b) := by
  unfold _root_.GD.N0232.N0720.N1443.d004046
  field_simp [hab]
  ring




def d004050 (a b : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1443.d004045 a b - 1) * b / (a + b)


def d004051 (a b : ℝ) : ℝ :=
  (_root_.GD.N0232.N0720.N1443.d004045 a b - 1) * a / (a + b)

theorem d004052
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < _root_.GD.N0232.N0720.N1443.d004045 a b - 1 := by
  unfold _root_.GD.N0232.N0720.N1443.d004045
  linarith

theorem d004053
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < _root_.GD.N0232.N0720.N1443.d004050 a b := by
  unfold _root_.GD.N0232.N0720.N1443.d004050
  exact div_pos
    (mul_pos (_root_.GD.N0232.N0720.N1443.d004052 ha hb) hb)
    (add_pos ha hb)

theorem d004054
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < _root_.GD.N0232.N0720.N1443.d004051 a b := by
  unfold _root_.GD.N0232.N0720.N1443.d004051
  exact div_pos
    (mul_pos (_root_.GD.N0232.N0720.N1443.d004052 ha hb) ha)
    (add_pos ha hb)


theorem d004055
    {a b : ℝ} (hab : a + b ≠ 0) :
    _root_.GD.N0232.N0720.N1443.d004050 a b + _root_.GD.N0232.N0720.N1443.d004051 a b =
      _root_.GD.N0232.N0720.N1443.d004045 a b - 1 := by
  unfold _root_.GD.N0232.N0720.N1443.d004050 _root_.GD.N0232.N0720.N1443.d004051
  field_simp [hab]
  ring


theorem d004056
    {a b : ℝ} (hab : a + b ≠ 0)
    (hshape : _root_.GD.N0232.N0720.N1443.d004045 a b + 1 ≠ 0) :
    (_root_.GD.N0232.N0720.N1443.d004050 a b + 1) /
          (_root_.GD.N0232.N0720.N1443.d004045 a b + 1) - b / (a + b) =
      (a - b) /
        ((a + b) * (_root_.GD.N0232.N0720.N1443.d004045 a b + 1)) := by
  unfold _root_.GD.N0232.N0720.N1443.d004050
  field_simp [hab, hshape]
  ring



theorem d004057
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    (_root_.GD.N0232.N0720.N1443.d004050 a b + 1) /
          (_root_.GD.N0232.N0720.N1443.d004045 a b + 1) ≠ b / (a + b) := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hshape : _root_.GD.N0232.N0720.N1443.d004045 a b + 1 ≠ 0 := by
    unfold _root_.GD.N0232.N0720.N1443.d004045
    positivity
  intro heq
  have hgap := _root_.GD.N0232.N0720.N1443.d004056 hab hshape
  rw [heq, sub_self] at hgap
  have hden : (a + b) * (_root_.GD.N0232.N0720.N1443.d004045 a b + 1) ≠ 0 :=
    mul_ne_zero hab hshape
  have : a - b = 0 := (div_eq_zero_iff).mp hgap.symm |>.resolve_right hden
  exact hne (sub_eq_zero.mp this)



open _root_.GD.N0235


theorem d004058
    {g : ℝ} (hg : 0 < g) :
    (∫ p : ℝ, p ^ 1 * (1 - p) ^ 1 ∂betaMeasure g g) =
      g / (2 * (2 * g + 1)) := by
  rw [_root_.GD.N0235.d004044 hg hg 1 1]
  norm_num only [Nat.cast_one]
  rw [_root_.GD.N0235.d004039 (add_pos hg zero_lt_one) hg]
  rw [_root_.GD.N0235.d004038 hg hg]
  field_simp [hg.ne', (add_pos hg hg).ne',
    (by linarith : g + 1 + g ≠ 0),
    (beta_pos hg hg).ne']
  ring


theorem d004059
    {g : ℝ} (hg : 0 < g) :
    (∫ p : ℝ, p ^ 2 * (1 - p) ^ 1 ∂betaMeasure g g) =
      g / (4 * (2 * g + 1)) := by
  rw [_root_.GD.N0235.d004044 hg hg 2 1]
  norm_num only [Nat.cast_ofNat]
  have hg1 : 0 < g + 1 := by linarith
  rw [show g + (2 : ℝ) = (g + 1) + 1 by ring]
  rw [_root_.GD.N0235.d004039 (by linarith : 0 < g + 1 + 1) hg]
  rw [_root_.GD.N0235.d004038 hg1 hg]
  rw [_root_.GD.N0235.d004038 hg hg]
  field_simp [hg.ne', hg1.ne', (add_pos hg hg).ne',
    (by linarith : g + 1 + g ≠ 0),
    (by linarith : g + 2 + g ≠ 0),
    (beta_pos hg hg).ne']
  ring


theorem d004060
    {g : ℝ} (hg : 0 < g) :
    (∫ p : ℝ, p ^ 3 * (1 - p) ^ 1 ∂betaMeasure g g) =
      g * (g + 2) / (4 * (2 * g + 1) * (2 * g + 3)) := by
  rw [_root_.GD.N0235.d004044 hg hg 3 1]
  norm_num only [Nat.cast_ofNat]
  have hg1 : 0 < g + 1 := by linarith
  have hg2 : 0 < g + 2 := by linarith
  rw [show g + (3 : ℝ) = ((g + 2) + 1) by ring]
  rw [_root_.GD.N0235.d004039 (by linarith : 0 < g + 2 + 1) hg]
  rw [_root_.GD.N0235.d004038 hg2 hg]
  have hstep : beta (g + 2) g =
      (g + 1) / (g + 1 + g) * beta (g + 1) g := by
    rw [show g + 2 = (g + 1) + 1 by ring]
    exact _root_.GD.N0235.d004038 hg1 hg
  rw [hstep]
  rw [_root_.GD.N0235.d004038 hg hg]
  field_simp [hg.ne', hg1.ne', hg2.ne', (add_pos hg hg).ne',
    (by linarith : g + 1 + g ≠ 0),
    (by linarith : g + 2 + g ≠ 0),
    (by linarith : g + 3 + g ≠ 0),
    (beta_pos hg hg).ne']
  ring





def d004061 (g : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
      (∫ p : ℝ, p ^ 1 * (1 - p) ^ 1 ∂betaMeasure g g) -
    (2 * g + 2) *
      ((∫ p : ℝ, p ^ 3 * (1 - p) ^ 1 ∂betaMeasure g g) -
        (1 / 2 : ℝ) *
          (∫ p : ℝ, p ^ 2 * (1 - p) ^ 1 ∂betaMeasure g g))


theorem d004062
    {g : ℝ} (hg : 0 < g) :
    _root_.GD.N0232.N0720.N1443.d004061 g =
      g / (8 * (2 * g + 1) * (2 * g + 3)) := by
  unfold _root_.GD.N0232.N0720.N1443.d004061
  rw [_root_.GD.N0232.N0720.N1443.d004058 hg,
    _root_.GD.N0232.N0720.N1443.d004059 hg,
    _root_.GD.N0232.N0720.N1443.d004060 hg]
  field_simp [hg.ne', (by linarith : 2 * g + 1 ≠ 0),
    (by linarith : 2 * g + 3 ≠ 0)]
  ring

theorem d004063
    {g : ℝ} (hg : 0 < g) :
    0 < _root_.GD.N0232.N0720.N1443.d004061 g := by
  rw [_root_.GD.N0232.N0720.N1443.d004062 hg]
  positivity










theorem d004064
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hshiftedMean :
      (_root_.GD.N0232.N0720.N1443.d004050 a b + 1) /
          (_root_.GD.N0232.N0720.N1443.d004045 a b + 1) = b / (a + b))
    (hsymmetricDerivative :
      a = b →
        _root_.GD.N0232.N0720.N1443.d004061
            ((_root_.GD.N0232.N0720.N1443.d004045 a b - 1) / 2) = 0) :
    False := by
  by_cases hab : a = b
  · have hg : 0 < (_root_.GD.N0232.N0720.N1443.d004045 a b - 1) / 2 :=
      div_pos (_root_.GD.N0232.N0720.N1443.d004052 ha hb) (by norm_num)
    have hpos := _root_.GD.N0232.N0720.N1443.d004063 hg
    have hzero := hsymmetricDerivative hab
    linarith
  · exact
      (_root_.GD.N0232.N0720.N1443.d004057 ha hb hab) hshiftedMean





theorem d004065
    {linear energy eta epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hlinear : linear ≤ -eta)
    (hsmall : epsilon * energy < 2 * eta) :
    2 * epsilon * linear + epsilon ^ 2 * energy < 0 := by
  have hinside : 2 * linear + epsilon * energy < 0 := by
    linarith
  calc
    2 * epsilon * linear + epsilon ^ 2 * energy =
        epsilon * (2 * linear + epsilon * energy) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hepsilon hinside



theorem d004066
    {weight linear energy eta epsilon : ℝ}
    (hweight : 0 < weight)
    (hepsilon : 0 < epsilon) (hlinear : linear ≤ -eta)
    (hsmall : epsilon * energy < 2 * eta) :
    weight * (2 * epsilon * linear + epsilon ^ 2 * energy) < 0 :=
  mul_neg_of_pos_of_neg hweight
    (_root_.GD.N0232.N0720.N1443.d004065 hepsilon hlinear hsmall)

end

end N1443
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1443.d004048
#print axioms _root_.GD.N0232.N0720.N1443.d004057
#print axioms _root_.GD.N0232.N0720.N1443.d004063
#print axioms _root_.GD.N0232.N0720.N1443.d004064
#print axioms _root_.GD.N0232.N0720.N1443.d004065
