import GD.Module1807
import GD.Module0701

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace GD.N0005.N0251

open _root_.GD.N0228.N0547
open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0790
open _root_.GD.N0005.N0252
open _root_.GD.N0232.N0719.N0875
open _root_.GD.N0235.N0744

noncomputable section

theorem d030037 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift : ℝ) :
    NoAtoms (_root_.GD.N0005.N0252.d030010 r s rho shift) := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  constructor
  intro x
  rw [_root_.GD.N0005.N0252.d030010, Measure.map_apply (_root_.GD.N0005.N0252.d030012 r s rho shift)
    (measurableSet_singleton x), _root_.GD.N0228.N0547.N0790.d012894,
    Measure.prod_apply_symm ((measurableSet_singleton x).preimage
      (_root_.GD.N0005.N0252.d030012 r s rho shift))]
  calc
    _ = ∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞)
        ∂(_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s) := by
      apply lintegral_congr_ae
      filter_upwards [_root_.GD.N0005.N0252.d030019 hr hs] with q hq
      have hsqrt := (Real.sqrt_pos.mpr
        (_root_.GD.N0005.N0252.d030016 hr hs h0 h1 hq.1 hq.2)).ne'
      have hpre : (fun z : ℝ => (z, q)) ⁻¹'
          (_root_.GD.N0005.N0252.d030008 r s rho shift ⁻¹' {x}) =
          {x * Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) - shift} := by
        ext z
        change (z + shift) / Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) = x ↔
          z = x * Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) - shift
        rw [div_eq_iff hsqrt]
        exact eq_sub_iff_add_eq.symm
      rw [hpre, measure_singleton]
    _ = 0 := by simp

theorem d030038 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift : ℝ) :
    Continuous (cdf (_root_.GD.N0005.N0252.d030010 r s rho shift)) := by
  letI := _root_.GD.N0005.N0252.d030021 hr hs rho shift
  letI := _root_.GD.N0005.N0251.d030037 hr hs h0 h1 shift
  exact _root_.GD.N0232.N0719.N0875.d010325 _

theorem d030039 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0005.N0252.d030010 r s rho shift
      (Iic (_root_.GD.N0235.N0744.d004268 (_root_.GD.N0005.N0252.d030010 r s rho shift) p)) = ENNReal.ofReal p := by
  letI := _root_.GD.N0005.N0252.d030021 hr hs rho shift
  letI := _root_.GD.N0005.N0251.d030037 hr hs h0 h1 shift
  rw [← ofReal_cdf, _root_.GD.N0232.N0719.N0875.d010327 _ hp0 hp1]

end
end GD.N0005.N0251

#print axioms _root_.GD.N0005.N0251.d030037
#print axioms _root_.GD.N0005.N0251.d030038
#print axioms _root_.GD.N0005.N0251.d030039
