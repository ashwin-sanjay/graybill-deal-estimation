import GD.Module1633
import GD.Module1731

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0492
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0990
open _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0213.N0491 _root_.GD.N0213.N0528
open _root_.GD.N0213.N0477 _root_.GD.N0213.N0484 _root_.GD.N0213.N0499

variable {k : ℕ} (sizes : Fin k → ℕ)

theorem d028815 [NeZero k]
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) {d : ℕ} (hdim : (∑ i, sizes i) = d + 2)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s)
    (hvanish : _root_.GD.N0213.N0528.d028808 sizes s) : False := by
  have hdim' : (∑ i, sizes i) = (d + 1) + 1 := by omega
  obtain ⟨pi, hpi⟩ := _root_.GD.N0213.N0491.N0775.d027941 sizes hdim hn hs
  obtain ⟨nu, hmom, hlim⟩ := _root_.GD.N0213.N0491.N0776.d027944
    sizes hn hdim' s hs
  let F := fun x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) =>
    _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d) x.1 x.2 (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
  have hrep : ∀ᵐ x ∂(volume : Measure
      (_root_.GD.N0232.N0720.N1341.d004414 (d + 1))),
      s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim').symm x) = F (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim' x) := by
    apply _root_.GD.N0213.N0500.d027915 sizes hdim' (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [_root_.GD.N0232.N0719.N0990.d020512, MeasurableEquiv.symm_apply_apply, F,
      _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0996.d019935, _root_.GD.N0232.N0719.N0986.d020362, Filter.EventuallyEq] using
      hpi (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  have hmarginal := _root_.GD.N0213.N0499.d022042 sizes hdim' hn nu hmom
    (fun x => s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim').symm x)) hlim F
    (_root_.GD.N0213.N0484.d022035 (_root_.GD.N0213.N0477.d020391 d) (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)))
    (hrep.mono (fun _ hx _ => hx))
  have hq : _root_.GD.N0213.N0477.d020391 d = ((d + 3 : ℕ) : ℝ) / 2 := by
    simp [_root_.GD.N0213.N0477.d020391, Nat.cast_add]
  have hnot := _root_.GD.N0213.N0528.d028814 sizes hk hn (d + 3) (by omega)
    (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) s hs.1
    (fun sigma hsigma => _root_.GD.N0156.N0444.d020670
      sizes s hs.1 ⟨0, sigma, hsigma⟩ (hs.2.2.1 _)) hvanish
    (by simpa only [hq, _root_.GD.N0232.N0719.N0859.d010812, Filter.EventuallyEq] using
      hpi ⟨0, fun _ => 1, fun _ => zero_lt_one⟩)
  apply hnot
  simpa only [F, hq, Nat.add_assoc] using hmarginal

theorem d028816 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ¬ _root_.GD.N0213.N0528.d028808 sizes s := by
  letI : NeZero k := ⟨by omega⟩
  have hsum : 2 ≤ ∑ i, sizes i := (hn 0).trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ 0))
  exact _root_.GD.N0213.N0492.d028815 sizes hk hn
    (d := (∑ i, sizes i) - 2) (by omega) hs

theorem d028817
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s)
    (C : ℝ) (hC : 0 ≤ C) : ¬ _root_.GD.N0213.N0528.d028811 sizes C s := by
  intro hcap
  exact _root_.GD.N0213.N0492.d028816 sizes hk hn hs
    (_root_.GD.N0213.N0528.d028813 sizes (fun i => by have := hn i; omega) C hC s hs.1 hcap)

theorem d028818
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes s = ⊤ := by
  by_contra hfinite
  let C := (_root_.GD.N0232.N0719.N0962.d012187 k sizes s).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  apply _root_.GD.N0213.N0492.d028817 sizes hk hn hs C hC
  intro theta
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
    (fun i => by have := hn i; omega) C hC theta s).mp
  rw [show ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 k sizes s from ENNReal.ofReal_toReal hfinite]
  exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0962.d012186 k sizes theta s) theta

theorem d028819 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes) (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes s) :
    _root_.GD.N0213.N0491.d027933 k sizes s := by
  refine ⟨hs.1.1, ?_, hs.2, ht⟩
  intro g z
  change s (_root_.GD.N0232.N0719.N0900.d009095 k sizes g.shift g.d009239 z) =
    g.shift + g.d009239 * s z
  exact hs.1.2 g.shift g.d009239 (Real.exp_pos _) z

theorem d028820
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) (hfinite : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (hvalue : _root_.GD.N0232.N0719.N0962.d012187 k sizes s = _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes s := by
  intro ht
  exact hfinite (hvalue.symm.trans (_root_.GD.N0213.N0492.d028818 sizes hk hn
    (_root_.GD.N0213.N0492.d028819 sizes hs ht)))

theorem d028821
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) (hfinite : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤) :
    _root_.GD.N0232.N0719.N0970.d012322 k sizes hk hn ∉ _root_.GD.N0232.N0719.N0962.d012185 k sizes := by
  intro ha
  exact _root_.GD.N0213.N0492.d028820 sizes hk hn hfinite
    ⟨ha, (_root_.GD.N0232.N0719.N0970.d012323 k sizes hk hn).2⟩
    (_root_.GD.N0232.N0719.N0970.d012325 k sizes hk hn)
    (_root_.GD.N0232.N0719.N0970.d012326 k sizes hk hn)

theorem d028822
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0213.N0491.d027933 k sizes s) :
    ¬ (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta s ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) := by
  intro hcap
  apply _root_.GD.N0213.N0492.d028816 sizes hk hn hs
  intro j
  have hbound (n : ℕ) : (∫ z, s z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0213.N0528.d028806 j n)) ≤
      ∫ z, _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0213.N0528.d028806 j n) := by
    let theta : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨0, _root_.GD.N0213.N0528.d028806 j n, _root_.GD.N0213.N0528.d028807 j n⟩
    have hbase : MemLp (_root_.GD.N0232.N0719.N0859.d010815 k sizes) 2
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
      simpa only [_root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812,
        theta, sub_zero] using _root_.GD.N0232.N0719.N0910.d010294 sizes (by omega) hn
          0 (_root_.GD.N0213.N0528.d028806 j n)
    have h := hcap theta
    rw [_root_.GD.N0156.N0444.d020671 sizes s theta
      (_root_.GD.N0156.N0444.d020670 sizes s hs.1 theta (hs.2.2.1 theta)),
      _root_.GD.N0156.N0444.d020671 sizes _ theta hbase] at h
    have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp h
    simpa only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010815,
      theta, sub_zero] using hr
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound
  exact _root_.GD.N0232.N0719.N0915.d010404 sizes hn j
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    (fun n => (div_le_one (by positivity)).mpr (by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith))
    tendsto_one_div_add_atTop_nhds_zero_nat

end
end GD.N0213.N0492

#print axioms _root_.GD.N0213.N0492.d028816
#print axioms _root_.GD.N0213.N0492.d028817
#print axioms _root_.GD.N0213.N0492.d028818
#print axioms _root_.GD.N0213.N0492.d028820
#print axioms _root_.GD.N0213.N0492.d028821
#print axioms _root_.GD.N0213.N0492.d028822
