import GD.Module1807
import GD.Module0849

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0005.N0250

open _root_.GD.N0228.N0547
open _root_.GD.N0232.N0719
open _root_.GD.N0228.N0547.N0793 _root_.GD.N0228.N0547.N0792
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0897
open _root_.GD.N0005.N0252

noncomputable section

def d030028 (nullContrast : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  (u.mean 0 - u.mean 1 - nullContrast) /
    Real.sqrt (u.meanVariance 0 + u.meanVariance 1)

@[fun_prop] theorem d030029 (nullContrast : ℝ) :
    Measurable (_root_.GD.N0005.N0250.d030028 nullContrast) := by
  unfold _root_.GD.N0005.N0250.d030028
  fun_prop

def d030030 (r s : ℕ) (muX muY sigmaX sigmaY nullContrast : ℝ) : ℝ :=
  (muX - muY - nullContrast) / Real.sqrt (_root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY)

theorem d030031 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (d delta nullContrast vX vY : ℝ) :
    _root_.GD.N0005.N0252.d030008 r s (A / (A + B)) ((delta - nullContrast) / Real.sqrt (A + B))
      ((d - delta) / Real.sqrt (A + B), ((r : ℝ) / A * vX, (s : ℝ) / B * vY)) =
      (d - nullContrast) / Real.sqrt (vX + vY) := by
  have hS : 0 < A + B := add_pos hA hB
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hden : _root_.GD.N0005.N0252.d030007 r s (A / (A + B))
      ((r : ℝ) / A * vX, (s : ℝ) / B * vY) = (vX + vY) / (A + B) := by
    unfold _root_.GD.N0005.N0252.d030007
    field_simp
    ring
  have hnum : (d - delta) / Real.sqrt (A + B) +
      (delta - nullContrast) / Real.sqrt (A + B) =
      (d - nullContrast) / Real.sqrt (A + B) := by ring
  rw [_root_.GD.N0005.N0252.d030008, hden, hnum, Real.sqrt_div' _ hS.le]
  exact div_div_div_cancel_right₀ (Real.sqrt_pos.mpr hS).ne' _ _

theorem d030032 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) (nullContrast : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0005.N0250.d030028 nullContrast u =
      _root_.GD.N0005.N0252.d030008 r s (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
        (_root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast)
        (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY u) := by
  have hA : 0 < _root_.GD.N0228.N0547.N0793.d012956 r sigmaX := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hB : 0 < _root_.GD.N0228.N0547.N0793.d012957 s sigmaY := by
    unfold _root_.GD.N0228.N0547.N0793.d012957
    positivity
  exact (_root_.GD.N0005.N0250.d030031 hr hs hA hB
    (u.mean 0 - u.mean 1) (muX - muY) nullContrast
    (u.meanVariance 0) (u.meanVariance 1)).symm

theorem d030033 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) (nullContrast : ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009340 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map (_root_.GD.N0005.N0250.d030028 nullContrast) =
      _root_.GD.N0005.N0252.d030010 r s (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
        (_root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast) := by
  have hfun : _root_.GD.N0005.N0250.d030028 nullContrast =
      _root_.GD.N0005.N0252.d030008 r s (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
        (_root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast) ∘
      _root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY := by
    funext u
    exact _root_.GD.N0005.N0250.d030032 hr hs muX muY hX hY nullContrast u
  rw [hfun, ← Measure.map_map (_root_.GD.N0005.N0252.d030012 _ _ _ _)
    (_root_.GD.N0228.N0547.N0792.d013002 _ _ _ _ _ _),
    _root_.GD.N0228.N0547.N0792.d013005 hr hs muX muY hX hY]
  rfl

theorem d030034 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009340 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map (_root_.GD.N0005.N0250.d030028 (muX - muY)) =
      _root_.GD.N0005.N0252.d030010 r s (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) 0 := by
  simpa only [_root_.GD.N0005.N0250.d030030, sub_self, zero_div] using
    _root_.GD.N0005.N0250.d030033 hr hs muX muY hX hY (muX - muY)

theorem d030035 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) (nullContrast : ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009332 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
        (_root_.GD.N0005.N0250.d030028 nullContrast ∘ _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0005.N0252.d030010 r s (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
        (_root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast) := by
  rw [← Measure.map_map (_root_.GD.N0005.N0250.d030029 nullContrast)
    (_root_.GD.N0232.N0719.N0900.d009115 _ _),
    _root_.GD.N0232.N0719.N0897.d009341 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
      (_root_.GD.N0228.N0547.N0793.d012972 hr hs) (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)]
  exact _root_.GD.N0005.N0250.d030033 hr hs muX muY hX hY nullContrast

theorem d030036 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) (nullContrast x : ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009332 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))
        {ω | _root_.GD.N0005.N0250.d030028 nullContrast (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) ω) ≤ x} =
      ∫⁻ q, (gaussianReal 0 1)
        (Iic (x * Real.sqrt (_root_.GD.N0005.N0252.d030007 r s
          (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) q) -
            _root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast))
        ∂(_root_.GD.N0228.N0547.N0778.d009365 r).prod
          (_root_.GD.N0228.N0547.N0778.d009365 s) := by
  have hmap := _root_.GD.N0005.N0250.d030035 hr hs muX muY hX hY nullContrast
  have hm := (_root_.GD.N0005.N0250.d030029 nullContrast).comp (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))
  have heq := congrArg (fun μ : Measure ℝ => μ (Iic x)) hmap
  rw [Measure.map_apply hm measurableSet_Iic] at heq
  exact heq.trans (_root_.GD.N0005.N0252.d030027 hr hs
    (_root_.GD.N0228.N0547.N0793.d012979 hX hY) (_root_.GD.N0228.N0547.N0793.d012980 hX hY) _ x)

end
end GD.N0005.N0250

#print axioms _root_.GD.N0005.N0250.d030031
#print axioms _root_.GD.N0005.N0250.d030033
#print axioms _root_.GD.N0005.N0250.d030034
#print axioms _root_.GD.N0005.N0250.d030035
#print axioms _root_.GD.N0005.N0250.d030036
