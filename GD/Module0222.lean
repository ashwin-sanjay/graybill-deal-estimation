import GD.Module0221

























namespace GD
namespace N0232
namespace N0720
namespace N1049

noncomputable section

open _root_.GD.N0232.N0720.N1463
open _root_.GD.N0232.N0720.N1462


def d003146 (alpha beta : ℝ) : ℝ :=
  2 ^ (3 / 2 : ℝ) * Real.Gamma (3 / 2) *
    Real.Gamma (alpha + beta) /
      Real.Gamma (alpha + beta + 3 / 2)



def d003147 (alpha beta l : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1049.d003146 alpha beta *
    l ^ (beta - 1) * (1 - l) ^ (alpha - 1) *
      (beta * l) ^ (-(alpha + beta))



def d003148 (alpha beta l : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1049.d003146 alpha beta *
    l ^ (beta - 1) * (1 - l) ^ (alpha - 1) *
      (alpha * (1 - l)) ^ (-(alpha + beta))



def d003149 (alpha beta l : ℝ) : ℝ :=
  2 ^ (3 / 2 : ℝ) * Real.Gamma (3 / 2) *
    Real.Gamma alpha * Real.Gamma beta /
      Real.Gamma (alpha + beta + 3 / 2) *
    alpha ^ (-alpha) * beta ^ (-beta) *
    l ^ (-alpha - 1) * (1 - l) ^ (-beta - 1)

theorem d003150
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1049.d003146 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1049.d003146
  have hr : 0 < alpha + beta := add_pos halpha hbeta
  have hnu : 0 < alpha + beta + 3 / 2 := by linarith
  positivity

theorem d003151
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1049.d003149 alpha beta l := by
  unfold _root_.GD.N0232.N0720.N1049.d003149
  have hnu : 0 < alpha + beta + 3 / 2 := by linarith
  have h1l : 0 < 1 - l := sub_pos.mpr hl.2
  have htwo : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hGthreeHalves : 0 < Real.Gamma (3 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hGa : 0 < Real.Gamma alpha := Real.Gamma_pos_of_pos halpha
  have hGb : 0 < Real.Gamma beta := Real.Gamma_pos_of_pos hbeta
  have hGnu : 0 < Real.Gamma (alpha + beta + 3 / 2) :=
    Real.Gamma_pos_of_pos hnu
  have hhead :
      0 < 2 ^ (3 / 2 : ℝ) * Real.Gamma (3 / 2) *
          Real.Gamma alpha * Real.Gamma beta /
            Real.Gamma (alpha + beta + 3 / 2) := by
    exact div_pos
      (mul_pos (mul_pos (mul_pos htwo hGthreeHalves) hGa) hGb) hGnu
  exact mul_pos
    (mul_pos
      (mul_pos (mul_pos hhead (Real.rpow_pos_of_pos halpha _))
        (Real.rpow_pos_of_pos hbeta _))
      (Real.rpow_pos_of_pos hl.1 _))
    (Real.rpow_pos_of_pos h1l _)



private theorem d003152
    {x a : ℝ} (hx : 0 < x) :
    x ^ (-a) * x ^ a = 1 := by
  rw [← Real.rpow_add hx]
  simp


private theorem d003153
    {x a b c : ℝ} (hx : 0 < x) :
    x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]



theorem d003154
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1049.d003147 alpha beta l =
      _root_.GD.N0232.N0720.N1049.d003149 alpha beta l *
        (_root_.GD.N0232.N0720.N1463.d003059 alpha beta * (1 - l) ^ (alpha + beta)) := by
  have h1l : 0 < 1 - l := sub_pos.mpr hl.2
  have hGa : Real.Gamma alpha ≠ 0 :=
    (Real.Gamma_pos_of_pos halpha).ne'
  have hGb : Real.Gamma beta ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hGr : Real.Gamma (alpha + beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos halpha hbeta)).ne'
  have hGnu : Real.Gamma (alpha + beta + 3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have haPow : alpha ^ alpha ≠ 0 :=
    (Real.rpow_pos_of_pos halpha alpha).ne'
  have hbPow : beta ^ alpha ≠ 0 :=
    (Real.rpow_pos_of_pos hbeta alpha).ne'
  rw [_root_.GD.N0232.N0720.N1049.d003147, _root_.GD.N0232.N0720.N1049.d003149,
    _root_.GD.N0232.N0720.N1049.d003146, _root_.GD.N0232.N0720.N1463.d003059,
    Real.mul_rpow hbeta.le hl.1.le,
    Real.div_rpow halpha.le hbeta.le]
  have hlpow :
      l ^ (beta - 1) * l ^ (-(alpha + beta)) =
        l ^ (-alpha - 1) := by
    rw [← Real.rpow_add hl.1]
    congr 1 <;> ring
  have h1lpow :
      (1 - l) ^ (-beta - 1) * (1 - l) ^ (alpha + beta) =
        (1 - l) ^ (alpha - 1) := by
    rw [← Real.rpow_add h1l]
    congr 1 <;> ring
  have hbetaPow :
      beta ^ (-(alpha + beta)) * beta ^ alpha = beta ^ (-beta) := by
    rw [← Real.rpow_add hbeta]
    congr 1 <;> ring
  have halphaPow : alpha ^ (-alpha) * alpha ^ alpha = 1 :=
    _root_.GD.N0232.N0720.N1049.d003152 halpha
  field_simp [hGa, hGb, hGr, hGnu, haPow, hbPow]
  calc
    _ = (beta ^ (-(alpha + beta)) * beta ^ alpha) *
          (l ^ (beta - 1) * l ^ (-(alpha + beta))) *
          (1 - l) ^ (alpha - 1) := by ring
    _ = beta ^ (-beta) * l ^ (-alpha - 1) *
          (1 - l) ^ (alpha - 1) := by rw [hbetaPow, hlpow]
    _ = (alpha ^ (-alpha) * alpha ^ alpha) * beta ^ (-beta) *
          l ^ (-alpha - 1) *
          ((1 - l) ^ (-beta - 1) * (1 - l) ^ (alpha + beta)) := by
      rw [halphaPow, h1lpow]
      ring
    _ = _ := by ring



theorem d003155
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1049.d003148 alpha beta l =
      _root_.GD.N0232.N0720.N1049.d003149 alpha beta l *
        (_root_.GD.N0232.N0720.N1463.d003060 alpha beta * l ^ (alpha + beta)) := by
  have h1l : 0 < 1 - l := sub_pos.mpr hl.2
  have hGa : Real.Gamma alpha ≠ 0 :=
    (Real.Gamma_pos_of_pos halpha).ne'
  have hGb : Real.Gamma beta ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hGr : Real.Gamma (alpha + beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos halpha hbeta)).ne'
  have hGnu : Real.Gamma (alpha + beta + 3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have haPow : alpha ^ beta ≠ 0 :=
    (Real.rpow_pos_of_pos halpha beta).ne'
  have hbPow : beta ^ beta ≠ 0 :=
    (Real.rpow_pos_of_pos hbeta beta).ne'
  rw [_root_.GD.N0232.N0720.N1049.d003148, _root_.GD.N0232.N0720.N1049.d003149,
    _root_.GD.N0232.N0720.N1049.d003146, _root_.GD.N0232.N0720.N1463.d003060,
    Real.mul_rpow halpha.le h1l.le,
    Real.div_rpow hbeta.le halpha.le]
  have hlpow :
      l ^ (-alpha - 1) * l ^ (alpha + beta) =
        l ^ (beta - 1) := by
    rw [← Real.rpow_add hl.1]
    congr 1 <;> ring
  have h1lpow :
      (1 - l) ^ (alpha - 1) *
          (1 - l) ^ (-(alpha + beta)) =
        (1 - l) ^ (-beta - 1) := by
    rw [← Real.rpow_add h1l]
    congr 1 <;> ring
  have halphaPow :
      alpha ^ (-(alpha + beta)) * alpha ^ beta =
        alpha ^ (-alpha) := by
    rw [← Real.rpow_add halpha]
    congr 1 <;> ring
  have hbetaPow : beta ^ (-beta) * beta ^ beta = 1 :=
    _root_.GD.N0232.N0720.N1049.d003152 hbeta
  field_simp [hGa, hGb, hGr, hGnu, haPow, hbPow]
  calc
    _ = (alpha ^ (-(alpha + beta)) * alpha ^ beta) *
          l ^ (beta - 1) *
          ((1 - l) ^ (alpha - 1) *
            (1 - l) ^ (-(alpha + beta))) := by ring
    _ = alpha ^ (-alpha) * l ^ (beta - 1) *
          (1 - l) ^ (-beta - 1) := by rw [halphaPow, h1lpow]
    _ = alpha ^ (-alpha) * (beta ^ (-beta) * beta ^ beta) *
          (l ^ (-alpha - 1) * l ^ (alpha + beta)) *
          (1 - l) ^ (-beta - 1) := by
      rw [hbetaPow, hlpow]
      ring
    _ = _ := by ring



theorem d003156
    {alpha beta l : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1049.d003148 alpha beta l /
        (_root_.GD.N0232.N0720.N1049.d003147 alpha beta l +
          _root_.GD.N0232.N0720.N1049.d003148 alpha beta l) =
      _root_.GD.N0232.N0720.N1463.d003066 alpha beta l := by
  rw [_root_.GD.N0232.N0720.N1049.d003154 halpha hbeta hl,
    _root_.GD.N0232.N0720.N1049.d003155 halpha hbeta hl]
  unfold _root_.GD.N0232.N0720.N1463.d003066 _root_.GD.N0232.N0720.N1463.d003053
  have hcommon : _root_.GD.N0232.N0720.N1049.d003149 alpha beta l ≠ 0 :=
    (_root_.GD.N0232.N0720.N1049.d003151 halpha hbeta hl).ne'
  have hleft :
      0 < _root_.GD.N0232.N0720.N1463.d003059 alpha beta * (1 - l) ^ (alpha + beta) :=
    mul_pos (_root_.GD.N0232.N0720.N1463.d003061 halpha hbeta)
      (Real.rpow_pos_of_pos (sub_pos.mpr hl.2) _)
  have hright :
      0 < _root_.GD.N0232.N0720.N1463.d003060 alpha beta * l ^ (alpha + beta) :=
    mul_pos (_root_.GD.N0232.N0720.N1463.d003062 halpha hbeta)
      (Real.rpow_pos_of_pos hl.1 _)
  field_simp [hcommon, (add_pos hleft hright).ne']

end

end N1049
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1049.d003154
#print axioms _root_.GD.N0232.N0720.N1049.d003155
#print axioms _root_.GD.N0232.N0720.N1049.d003156
