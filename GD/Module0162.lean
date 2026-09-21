























import Mathlib

namespace GD
namespace N0232
namespace N0720
namespace N1044

noncomputable section


def d001852 (rho : ℝ) : ℝ :=
  rho / (1 + rho)


def d001853 (rho : ℝ) : ℝ :=
  rho / (2 * (1 + rho) ^ 2)


def d001854 (rho : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1044.d001853 rho + _root_.GD.N0232.N0720.N1044.d001852 rho ^ 2


def d001855 (rho : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1044.d001853 rho + (1 - _root_.GD.N0232.N0720.N1044.d001852 rho) ^ 2


def d001856 (rho : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1044.d001852 rho - _root_.GD.N0232.N0720.N1044.d001854 rho


def d001857 (rho : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1044.d001856 rho - _root_.GD.N0232.N0720.N1044.d001852 rho * (1 - _root_.GD.N0232.N0720.N1044.d001852 rho)



def d001858 (rho : ℝ) : ℝ :=
  (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1044.d001854 rho +
    (rho ^ 2 / 2) * _root_.GD.N0232.N0720.N1044.d001855 rho

private theorem d001859
    {rho : ℝ} (hrho : rho ≠ -1) :
    1 + rho ≠ 0 := by
  intro hzero
  apply hrho
  linarith

private theorem d001860
    {rho : ℝ} (hrho : rho ≠ -1) :
    rho + 1 ≠ 0 := by
  simpa [add_comm] using _root_.GD.N0232.N0720.N1044.d001859 hrho

private theorem d001861
    {rho : ℝ} (hrho : rho ≠ -1) :
    1 + rho * 2 + rho ^ 2 ≠ 0 := by
  rw [show 1 + rho * 2 + rho ^ 2 = (1 + rho) ^ 2 by ring]
  exact pow_ne_zero 2 (_root_.GD.N0232.N0720.N1044.d001859 hrho)


theorem d001862
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001854 rho =
      rho * (2 * rho + 1) / (2 * (1 + rho) ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1044.d001854 _root_.GD.N0232.N0720.N1044.d001853 _root_.GD.N0232.N0720.N1044.d001852
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001863
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001855 rho =
      (rho + 2) / (2 * (1 + rho) ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1044.d001855 _root_.GD.N0232.N0720.N1044.d001853 _root_.GD.N0232.N0720.N1044.d001852
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001864
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001856 rho = _root_.GD.N0232.N0720.N1044.d001853 rho := by
  unfold _root_.GD.N0232.N0720.N1044.d001856 _root_.GD.N0232.N0720.N1044.d001854 _root_.GD.N0232.N0720.N1044.d001853 _root_.GD.N0232.N0720.N1044.d001852
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring



theorem d001865
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001857 rho = -_root_.GD.N0232.N0720.N1044.d001853 rho := by
  unfold _root_.GD.N0232.N0720.N1044.d001857
  rw [_root_.GD.N0232.N0720.N1044.d001864 hrho]
  unfold _root_.GD.N0232.N0720.N1044.d001853 _root_.GD.N0232.N0720.N1044.d001852
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001866
    {rho : ℝ} (hrho : rho ≠ 0) (hrhoNeg : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001853 (1 / rho) = _root_.GD.N0232.N0720.N1044.d001853 rho := by
  unfold _root_.GD.N0232.N0720.N1044.d001853
  have hone : 1 + 1 / rho = (rho + 1) / rho := by
    field_simp [hrho]
  have hpoly := _root_.GD.N0232.N0720.N1044.d001861 hrhoNeg
  rw [hone]
  field_simp [hrho, _root_.GD.N0232.N0720.N1044.d001860 hrhoNeg]
  conv_lhs => rw [← inv_mul_cancel₀ hpoly]
  ring


theorem d001867
    {rho : ℝ} (hrho : rho ≠ -1) :
    (1 / 8 : ℝ) - _root_.GD.N0232.N0720.N1044.d001853 rho =
      (rho - 1) ^ 2 / (8 * (1 + rho) ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1044.d001853
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring



theorem d001868
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001858 rho =
      rho * (rho ^ 2 + 4 * rho + 1) / (4 * (rho + 1) ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1044.d001858
  rw [_root_.GD.N0232.N0720.N1044.d001862 hrho, _root_.GD.N0232.N0720.N1044.d001863 hrho]
  rw [show 1 + rho = rho + 1 by ring]
  field_simp [_root_.GD.N0232.N0720.N1044.d001860 hrho]
  ring



theorem d001869
    {rho mean variance second complement risk : ℝ}
    (hrho : rho ≠ -1)
    (hmean : mean = rho / (1 + rho))
    (hvariance : variance = rho / (2 * (1 + rho) ^ 2))
    (hsecond : second = variance + mean ^ 2)
    (hcomplement : complement = variance + (1 - mean) ^ 2)
    (hrisk : risk = (1 / 2 : ℝ) * second + (rho ^ 2 / 2) * complement) :
    risk = rho * (rho ^ 2 + 4 * rho + 1) / (4 * (rho + 1) ^ 2) := by
  subst mean
  subst variance
  subst second
  subst complement
  rw [hrisk]
  field_simp [_root_.GD.N0232.N0720.N1044.d001859 hrho,
    _root_.GD.N0232.N0720.N1044.d001860 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring



theorem d001870
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001858 rho =
      rho / 4 + rho ^ 2 / (2 * (rho + 1) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 hrho]
  field_simp [_root_.GD.N0232.N0720.N1044.d001860 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001871
    {rho : ℝ} (hrho : 0 < rho) :
    0 < _root_.GD.N0232.N0720.N1044.d001858 rho := by
  rw [_root_.GD.N0232.N0720.N1044.d001870 (by linarith)]
  positivity


theorem d001872
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1044.d001858 rho = rho ^ 2 * _root_.GD.N0232.N0720.N1044.d001858 (1 / rho) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 (by linarith),
    _root_.GD.N0232.N0720.N1044.d001868 (by
      intro h
      have : 1 / rho = -1 := h
      field_simp [hrho.ne'] at this
      linarith)]
  field_simp [hrho.ne', _root_.GD.N0232.N0720.N1044.d001860 (by linarith : rho ≠ -1),
    _root_.GD.N0232.N0720.N1044.d001861 (by linarith : rho ≠ -1)]
  ring


theorem d001873 :
    _root_.GD.N0232.N0720.N1044.d001858 1 = 3 / 8 := by
  norm_num [_root_.GD.N0232.N0720.N1044.d001858, _root_.GD.N0232.N0720.N1044.d001854, _root_.GD.N0232.N0720.N1044.d001855,
    _root_.GD.N0232.N0720.N1044.d001853, _root_.GD.N0232.N0720.N1044.d001852]


theorem d001874
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001858 rho - 3 / 8 =
      (rho - 1) * (rho + 3) * (2 * rho + 1) /
        (8 * (rho + 1) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 hrho]
  field_simp [_root_.GD.N0232.N0720.N1044.d001860 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001875
    {x y : ℝ} (hx : x ≠ -1) (hy : y ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001858 y - _root_.GD.N0232.N0720.N1044.d001858 x =
      (y - x) *
        (x ^ 2 * y ^ 2 + 2 * x ^ 2 * y + x ^ 2 +
          2 * x * y ^ 2 + 8 * x * y + 4 * x +
          y ^ 2 + 4 * y + 1) /
        (4 * (x + 1) ^ 2 * (y + 1) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 hx, _root_.GD.N0232.N0720.N1044.d001868 hy]
  field_simp [_root_.GD.N0232.N0720.N1044.d001860 hx, _root_.GD.N0232.N0720.N1044.d001860 hy,
    _root_.GD.N0232.N0720.N1044.d001861 hx, _root_.GD.N0232.N0720.N1044.d001861 hy]
  ring



theorem d001876
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    _root_.GD.N0232.N0720.N1044.d001858 x < _root_.GD.N0232.N0720.N1044.d001858 y := by
  rw [sub_pos.symm,
    _root_.GD.N0232.N0720.N1044.d001875 (by linarith) (by linarith)]
  have hy : 0 < y := lt_trans hx hxy
  have hpoly :
      0 < x ^ 2 * y ^ 2 + 2 * x ^ 2 * y + x ^ 2 +
        2 * x * y ^ 2 + 8 * x * y + 4 * x +
        y ^ 2 + 4 * y + 1 := by positivity
  exact div_pos (mul_pos (sub_pos.mpr hxy) hpoly) (by positivity)




theorem d001877
    {rho : ℝ} (hrho : rho ≠ -1) :
    _root_.GD.N0232.N0720.N1044.d001858 rho - (1 + rho ^ 2) / 8 =
      (4 * rho ^ 2 - (rho ^ 2 - 1) ^ 2) /
        (8 * (rho + 1) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 hrho]
  field_simp [_root_.GD.N0232.N0720.N1044.d001860 hrho, _root_.GD.N0232.N0720.N1044.d001861 hrho]
  ring


theorem d001878
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1044.d001858 rho - rho ^ 2 / (2 * (1 + rho ^ 2)) =
      rho * ((rho ^ 2 - 1) ^ 2 + 2 * rho * (rho ^ 2 + 1)) /
        (4 * (rho + 1) ^ 2 * (rho ^ 2 + 1)) := by
  rw [_root_.GD.N0232.N0720.N1044.d001868 (by linarith)]
  field_simp [show rho + 1 ≠ 0 by linarith,
    show rho ^ 2 + 1 ≠ 0 by positivity]
  ring

theorem d001879
    {rho : ℝ} (hrho : 0 < rho) :
    rho ^ 2 / (2 * (1 + rho ^ 2)) < _root_.GD.N0232.N0720.N1044.d001858 rho := by
  rw [← sub_pos,
    _root_.GD.N0232.N0720.N1044.d001878 hrho]
  positivity



#print axioms _root_.GD.N0232.N0720.N1044.d001862
#print axioms _root_.GD.N0232.N0720.N1044.d001864
#print axioms _root_.GD.N0232.N0720.N1044.d001865
#print axioms _root_.GD.N0232.N0720.N1044.d001869
#print axioms _root_.GD.N0232.N0720.N1044.d001868
#print axioms _root_.GD.N0232.N0720.N1044.d001872
#print axioms _root_.GD.N0232.N0720.N1044.d001876
#print axioms _root_.GD.N0232.N0720.N1044.d001877
#print axioms _root_.GD.N0232.N0720.N1044.d001879

end


end N1044
end N0720
end N0232
end GD
