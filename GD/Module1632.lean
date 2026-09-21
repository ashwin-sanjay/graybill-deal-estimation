import GD.Module1266
import GD.Module1219
import GD.Module1367
import GD.Module1631
import GD.Module0964

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0478

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0975 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0997
open _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1314 (d019720
  d019721 d019722)
open _root_.GD.N0230.N0556
open _root_.GD.N0213.N0476
open _root_.GD.N0213.N0481
open _root_.GD.N0213.N0480
open _root_.GD.N0213.N0477
open _root_.GD.N0213.N0479
open _root_.GD.N0213.N0483

variable {k d : ℕ} [NeZero k] (sizes : Fin k → ℕ)
  (hdim : (∑ i, sizes i) = d + 2)

def d027923 (v : Fin k → Ioo (0 : ℝ) 1) : _root_.GD.N0213.N0477.d020377 k :=
  ⟨fun i => (v i).1⁻¹, fun i => inv_pos.mpr (v i).2.1⟩

theorem d027924 (hn : ∀ i, 2 ≤ sizes i)
    (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (fun v : Fin k → Ioo (0 : ℝ) 1 =>
      _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0213.N0480.d020446 (_root_.GD.N0213.N0480.d020447 sizes hdim v)) h) :
    ∃ pi : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      (fun u => _root_.GD.N0232.N0719.N0976.d019748 _root_.GD.N0213.N0480.d020446 u (h u)) =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u =>
        _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  let ref := _root_.GD.N0213.N0480.d020449 (k := k)
  let tau := _root_.GD.N0213.N0480.d020447 sizes hdim
  have href : tau ref = _root_.GD.N0213.N0480.d020446 := _root_.GD.N0213.N0480.d020450 sizes hdim
  have hadm : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0975.d019769 tau ref) h := by
    change _root_.GD.N0230.N0556.d000031 (fun v => _root_.GD.N0232.N0719.N0976.d019747 (tau ref) (tau v)) h
    rw [href]
    exact hadmissible
  obtain ⟨w, ns, hw, _hns, hlim⟩ := _root_.GD.N0232.N0719.N0975.d019776 tau
    (_root_.GD.N0213.N0480.d020448 sizes hdim) ref h hadm
  let a : ∀ j, Option (Fin (ns j)) → _root_.GD.N0213.N0477.d020377 k := fun j i =>
    _root_.GD.N0213.N0478.d027923 (i.elim ref (fun i => _root_.GD.N0232.N0719.N0975.d019770 ref i))
  have hprec (j : ℕ) (i : Option (Fin (ns j))) :
      _root_.GD.N0213.N0477.d020380 sizes hdim (a j i) =
        _root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0975.d019770 ref i) i := by
    cases i <;> rfl
  apply _root_.GD.N0213.N0477.d020402 sizes hdim a
    (fun j => _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) (fun i => by have := hn i; omega)
    (fun j => _root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j)))
    (fun j => _root_.GD.N0232.N0720.N1314.d019722 (w (ns j)))
    (fun u => _root_.GD.N0232.N0719.N0976.d019748 _root_.GD.N0213.N0480.d020446 u (h u))
    (_root_.GD.N0213.N0481.d020442 sizes hdim hn)
  filter_upwards [hlim] with u hu
  simpa only [_root_.GD.N0232.N0719.N0975.d019765, _root_.GD.N0232.N0719.N0975.d019764, ← hprec, href,
    _root_.GD.N0232.N0719.N0976.d019734, _root_.GD.N0213.N0477.d020393, _root_.GD.N0232.N0719.N0976.d019735] using hu

omit [NeZero k] in
theorem d027925 (hn : ∀ i, 2 ≤ sizes i)
    (c a : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) i =
      c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i := by
  rw [_root_.GD.N0232.N0719.N0986.d020363, _root_.GD.N0232.N0719.N0986.d020363]
  exact _root_.GD.N0232.N0719.N0900.d009137 (k := k) (sizes := sizes)
    (fun i => by have := hn i; omega) c a (_root_.GD.N0213.N0477.d020379 sizes hdim z) i

include hdim in
theorem d027926 (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ pi : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        s =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] fun omega =>
          _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d) (_root_.GD.N0232.N0719.N0986.d020360 sizes omega) (_root_.GD.N0232.N0719.N0986.d020361 sizes omega)
            (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  obtain ⟨h, hadm, heq⟩ := _root_.GD.N0213.N0480.d020463 sizes hdim hs
  obtain ⟨pi, hpi⟩ := _root_.GD.N0213.N0478.d027924 sizes hdim hn h hadm
  refine ⟨pi, ?_⟩
  let P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop := fun z =>
    (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i) ∧
      _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h z =
        _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
  have hinvariant : ∀ c a, 0 < a → ∀ z, P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z := by
    intro c a ha z
    have hr : (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) i) ↔
        (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i) := by
      simp_rw [_root_.GD.N0213.N0481.d020440 sizes hdim hn c a z]
      exact forall_congr' (fun i => mul_pos_iff_of_pos_left (sq_pos_of_pos ha))
    constructor
    · rintro ⟨hpos, he⟩
      have hz := hr.mp hpos
      refine ⟨hz, ?_⟩
      have hm := _root_.GD.N0213.N0483.d022032 (_root_.GD.N0213.N0477.d020391 d) c a ha.ne'
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) hz (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
      simp_rw [← _root_.GD.N0213.N0478.d027925 sizes hdim hn c a z,
        ← _root_.GD.N0213.N0481.d020440 sizes hdim hn c a z] at hm
      rw [_root_.GD.N0213.N0476.d020413 _root_.GD.N0213.N0480.d020446 h c a ha z, hm] at he
      nlinarith
    · rintro ⟨hpos, he⟩
      refine ⟨hr.mpr hpos, ?_⟩
      have hm := _root_.GD.N0213.N0483.d022032 (_root_.GD.N0213.N0477.d020391 d) c a ha.ne'
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) hpos (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
      simp_rw [← _root_.GD.N0213.N0478.d027925 sizes hdim hn c a z,
        ← _root_.GD.N0213.N0481.d020440 sizes hdim hn c a z] at hm
      rw [_root_.GD.N0213.N0476.d020413 _root_.GD.N0213.N0480.d020446 h c a ha z, hm, he]
  have hraw : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z := by
    apply _root_.GD.N0213.N0479.d009790 P hinvariant
    filter_upwards [hpi, _root_.GD.N0213.N0481.d020442 sizes hdim hn] with u hu hr
    exact ⟨hr, by simpa only [_root_.GD.N0213.N0476.d020414] using hu⟩
  have hcoordinate : _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h =ᵐ[volume] fun z =>
      _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d) (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
    filter_upwards [hraw] with z hz
    exact hz.2
  intro theta
  have htoLp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (d + 2))).quasiMeasurePreserving.ae_eq_comp hcoordinate
  have hphysical := _root_.GD.N0232.N0719.N0996.d019943 sizes hdim htoLp theta
  apply (heq theta).symm.trans
  filter_upwards [hphysical] with omega homega
  have hcoord : _root_.GD.N0213.N0477.d020379 sizes hdim
      ((MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) = omega :=
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm_apply_apply omega
  change _root_.GD.N0213.N0476.d020410 _root_.GD.N0213.N0480.d020446 h
    ((MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) = _
  simpa only [Function.comp_apply, hcoord] using homega

end
end GD.N0213.N0478

#print axioms _root_.GD.N0213.N0478.d027924
#print axioms _root_.GD.N0213.N0478.d027925
#print axioms _root_.GD.N0213.N0478.d027926

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0490

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0991
open _root_.GD.N0232.N0719.N0990
open _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0213.N0478
open _root_.GD.N0213.N0477
open _root_.GD.N0213.N0484
open _root_.GD.N0213.N0499
open _root_.GD.N0156.N0444

variable {k : ℕ} (sizes : Fin k → ℕ)

theorem d027927 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp s 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
  _root_.GD.N0156.N0444.d020670 sizes s hs.1 theta (ne_top_of_lt (hs.2.2.1 theta))

theorem d027928 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) :
    (∫ z, s z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 sigma) ≤
      ∫ z, _root_.GD.N0232.N0719.N0900.d009111 k sizes z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 sigma := by
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨0, sigma, hsigma⟩
  have hbase : MemLp (_root_.GD.N0232.N0719.N0859.d010815 k sizes) 2
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    simpa only [_root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812,
      theta, sub_zero] using _root_.GD.N0232.N0719.N0910.d010294 sizes (by omega) hn 0 sigma
  have hle := (hs.2.2.1 theta).le
  rw [_root_.GD.N0156.N0444.d020671 sizes s theta (_root_.GD.N0213.N0490.d027927 sizes hs theta),
    _root_.GD.N0156.N0444.d020671 sizes _ theta hbase] at hle
  have hnonneg : 0 ≤ ∫ z, (_root_.GD.N0232.N0719.N0859.d010815 k sizes z - theta.location) ^ 2
      ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta := integral_nonneg (fun _ => sq_nonneg _)
  simpa only [_root_.GD.N0232.N0719.N0859.d010815, _root_.GD.N0232.N0719.N0859.d010812,
    theta, sub_zero] using (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hle

theorem d027929 (hn : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta, ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
  have hh := ae_all_iff.mpr (fun i =>
    _root_.GD.N0232.N0719.N0832.d012011 k sizes hn theta i)
  filter_upwards [hh] with z hz
  intro i
  rw [_root_.GD.N0232.N0719.N0986.d020364]
  apply div_pos (hz i)
  have hnpos : 0 < (sizes i : ℝ) := Nat.cast_pos.mpr (by have := hn i; omega)
  positivity

theorem d027930 [NeZero k] (hk : 3 ≤ k)
    (hn : ∀ i, 2 ≤ sizes i) {d : ℕ} (hdim : (∑ i, sizes i) = d + 2)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) : False := by
  have hdim' : (∑ i, sizes i) = (d + 1) + 1 := by omega
  obtain ⟨pi, hpi⟩ := _root_.GD.N0213.N0478.d027926 sizes hdim hn hs
  obtain ⟨nu, hmom, hlim⟩ := _root_.GD.N0213.N0501.d027922
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
  have hnot := _root_.GD.N0213.N0484.d022037 hk sizes hn (d + 3) (by omega)
    (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (_root_.GD.N0213.N0490.d027929 sizes hn ⟨0, fun _ => 1, fun _ => zero_lt_one⟩) s hs.1
    (fun sigma hsigma => _root_.GD.N0213.N0490.d027927 sizes hs ⟨0, sigma, hsigma⟩)
    (_root_.GD.N0213.N0490.d027928 sizes hk hn hs)
    (by simpa only [hq, _root_.GD.N0232.N0719.N0859.d010812, Filter.EventuallyEq] using
      hpi ⟨0, fun _ => 1, fun _ => zero_lt_one⟩)
  apply hnot
  simpa only [F, hq, Nat.add_assoc] using hmarginal

theorem d027931 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  letI : NeZero k := ⟨by omega⟩
  have hsum : 2 ≤ ∑ i, sizes i := by
    have hsingle := Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i))
      (Finset.mem_univ (0 : Fin k))
    have hsize := hn (0 : Fin k)
    omega
  rintro ⟨s, hs⟩
  exact _root_.GD.N0213.N0490.d027930 sizes hk hn (d := (∑ i, sizes i) - 2)
    (by omega) hs

theorem d027932 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∀ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
      _root_.GD.N0230.N0608.d000675
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
        (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hn) →
      0 < _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s := by
  exact (_root_.GD.N0232.N0719.N1022.d015195
    k sizes hk hn).mp (_root_.GD.N0213.N0490.d027931 sizes hk hn)

end
end GD.N0213.N0490

#print axioms _root_.GD.N0213.N0490.d027927
#print axioms _root_.GD.N0213.N0490.d027928
#print axioms _root_.GD.N0213.N0490.d027929
#print axioms _root_.GD.N0213.N0490.d027930
#print axioms _root_.GD.N0213.N0490.d027931
#print axioms _root_.GD.N0213.N0490.d027932
