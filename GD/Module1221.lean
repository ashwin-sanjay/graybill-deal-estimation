import GD.Module1220










open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0975

open _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0622

noncomputable section

variable {k : ℕ} {I : Type*} [Fintype I]

def d019759 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) :=
  ∑ i, w i • _root_.GD.N0232.N0719.N0976.d019745 ref (tau i)

def d019760 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1341.d004415 k, ℝ) :=
  ∑ i, w i • _root_.GD.N0232.N0719.N0976.d019746 ref (tau i)

theorem d019761 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    0 < _root_.GD.N0232.N0719.N0975.d019759 ref tau w u := by
  simp only [_root_.GD.N0232.N0719.N0975.d019759, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  obtain ⟨j, hj⟩ := hpos
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (_root_.GD.N0232.N0719.N0976.d019749 ref (tau i) u).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0719.N0976.d019749 ref (tau j) u)⟩

theorem d019762 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    (∑ i, w i * _root_.GD.N0232.N0719.N0976.d019747 ref (tau i) h) =
      _root_.GD.N0232.N0720.N1314.d019689 (_root_.GD.N0232.N0719.N0975.d019759 ref tau w) (_root_.GD.N0232.N0719.N0975.d019760 ref tau w) h := by
  unfold _root_.GD.N0232.N0720.N1314.d019689 _root_.GD.N0232.N0719.N0976.d019747
  simp_rw [_root_.GD.N0232.N0720.N1314.d019689]
  rw [← _root_.GD.N0232.N0720.N1314.d019696, ← _root_.GD.N0232.N0720.N1314.d019697, _root_.GD.N0232.N0719.N0975.d019759, _root_.GD.N0232.N0719.N0975.d019760,
    map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, _root_.GD.N0232.N0720.N1314.d019696, _root_.GD.N0232.N0720.N1314.d019697]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem d019763 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1341.d004417 k)
    (hmin : ∀ z, (∑ i, w i * _root_.GD.N0232.N0719.N0976.d019747 ref (tau i) h) ≤
      ∑ i, w i * _root_.GD.N0232.N0719.N0976.d019747 ref (tau i) z) :
    h = _root_.GD.N0232.N0720.N1314.d019686 (_root_.GD.N0232.N0719.N0975.d019759 ref tau w) (_root_.GD.N0232.N0719.N0975.d019760 ref tau w) (_root_.GD.N0232.N0719.N0975.d019761 ref tau w hw hpos) := by
  apply _root_.GD.N0232.N0720.N1314.d019693
  simpa only [_root_.GD.N0232.N0719.N0975.d019762] using hmin
    (_root_.GD.N0232.N0720.N1314.d019686 (_root_.GD.N0232.N0719.N0975.d019759 ref tau w) (_root_.GD.N0232.N0719.N0975.d019760 ref tau w) (_root_.GD.N0232.N0719.N0975.d019761 ref tau w hw hpos))

def d019764 (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0719.N0976.d019735 (tau i) u

def d019765 (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0719.N0976.d019735 (tau i) u * _root_.GD.N0232.N0719.N0976.d019734 (tau i) u

theorem d019766 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0719.N0975.d019759 ref tau w u = _root_.GD.N0232.N0719.N0975.d019764 tau w u / _root_.GD.N0232.N0719.N0976.d019735 ref u := by
  simp [_root_.GD.N0232.N0719.N0975.d019759, _root_.GD.N0232.N0719.N0976.d019745, _root_.GD.N0232.N0719.N0975.d019764, Finset.sum_div, mul_div_assoc]

theorem d019767 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0719.N0975.d019760 ref tau w u = Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) / _root_.GD.N0232.N0719.N0976.d019735 ref u *
      (_root_.GD.N0232.N0719.N0975.d019765 tau w u - _root_.GD.N0232.N0719.N0976.d019734 ref u * _root_.GD.N0232.N0719.N0975.d019764 tau w u) := by
  simp only [_root_.GD.N0232.N0719.N0975.d019760, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    _root_.GD.N0232.N0719.N0976.d019746, _root_.GD.N0232.N0719.N0976.d019745, ContinuousMap.coe_mk, _root_.GD.N0232.N0719.N0975.d019765, _root_.GD.N0232.N0719.N0975.d019764]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring



theorem d019768 (ref : _root_.GD.N0232.N0719.N0976.d019733 k) (tau : I → _root_.GD.N0232.N0719.N0976.d019733 k)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0719.N0976.d019748 ref u (_root_.GD.N0232.N0719.N0975.d019760 ref tau w u / _root_.GD.N0232.N0719.N0975.d019759 ref tau w u) =
      _root_.GD.N0232.N0719.N0975.d019765 tau w u / _root_.GD.N0232.N0719.N0975.d019764 tau w u := by
  have hA := _root_.GD.N0232.N0719.N0975.d019761 ref tau w hw hpos u
  rw [_root_.GD.N0232.N0719.N0975.d019766] at hA
  have hD : _root_.GD.N0232.N0719.N0975.d019764 tau w u ≠ 0 := by
    intro hz
    simp [hz] at hA
  have hc := (_root_.GD.N0232.N0719.N0976.d019736 ref u).ne'
  have hs := (Real.sqrt_pos.2 (_root_.GD.N0232.N0719.N0976.d019736 ref u)).ne'
  rw [_root_.GD.N0232.N0719.N0975.d019766, _root_.GD.N0232.N0719.N0975.d019767]
  unfold _root_.GD.N0232.N0719.N0976.d019748
  field_simp
  ring

section ParameterFamily

variable {Θ : Type*} [TopologicalSpace Θ] [SecondCountableTopology Θ]
variable (tau : Θ → _root_.GD.N0232.N0719.N0976.d019733 k) (htau : Continuous tau) (ref : Θ)

def d019769 (q : Θ) (h : _root_.GD.N0232.N0720.N1341.d004417 k) : ℝ := _root_.GD.N0232.N0719.N0976.d019747 (tau ref) (tau q) h

def d019770 : ℕ → Θ := by
  letI : Nonempty Θ := ⟨ref⟩
  exact TopologicalSpace.denseSeq Θ

theorem d019771 : DenseRange (_root_.GD.N0232.N0719.N0975.d019770 ref) := by
  letI : Nonempty Θ := ⟨ref⟩
  exact TopologicalSpace.denseRange_denseSeq Θ

def d019772 (q : I → Θ) : Option I → _root_.GD.N0232.N0719.N0976.d019733 k
  | none => tau ref
  | some i => tau (q i)

omit [TopologicalSpace Θ] [SecondCountableTopology Θ] in
theorem d019773 (q : I → Θ) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    (∑ i, _root_.GD.N0232.N0720.N1314.d019720 w i * _root_.GD.N0232.N0719.N0976.d019747 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref q i) h) =
      _root_.GD.N0232.N0719.N0975.d019769 tau ref ref h + ∑ i, w i * _root_.GD.N0232.N0719.N0975.d019769 tau ref (q i) h := by
  simp [Fintype.sum_option, _root_.GD.N0232.N0719.N0975.d019772, _root_.GD.N0232.N0720.N1314.d019720, _root_.GD.N0232.N0719.N0975.d019769]

omit [TopologicalSpace Θ] [SecondCountableTopology Θ] in
theorem d019774 (q : I → Θ) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 k)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ (_root_.GD.N0232.N0719.N0975.d019769 tau ref) ref q w h) :
    h = _root_.GD.N0232.N0720.N1314.d019686 (_root_.GD.N0232.N0719.N0975.d019759 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref q) (_root_.GD.N0232.N0720.N1314.d019720 w))
      (_root_.GD.N0232.N0719.N0975.d019760 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref q) (_root_.GD.N0232.N0720.N1314.d019720 w))
      (_root_.GD.N0232.N0719.N0975.d019761 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref q) (_root_.GD.N0232.N0720.N1314.d019720 w)
        (_root_.GD.N0232.N0720.N1314.d019721 w hbayes.1) (_root_.GD.N0232.N0720.N1314.d019722 w)) := by
  apply _root_.GD.N0232.N0719.N0975.d019763 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref q) (_root_.GD.N0232.N0720.N1314.d019720 w)
    (_root_.GD.N0232.N0720.N1314.d019721 w hbayes.1) (_root_.GD.N0232.N0720.N1314.d019722 w)
  intro z
  rw [_root_.GD.N0232.N0719.N0975.d019773, _root_.GD.N0232.N0719.N0975.d019773]
  exact hbayes.2 z (mem_univ z)

include htau in
set_option maxHeartbeats 800000 in
theorem d019775 (h : _root_.GD.N0232.N0720.N1341.d004417 k)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0975.d019769 tau ref) h) :
    ∃ (p : ℕ → _root_.GD.N0232.N0720.N1341.d004417 k) (w : ∀ j, Fin j → ℝ),
      Tendsto p atTop (𝓝 h) ∧ (∀ j i, 0 ≤ w j i) ∧ ∀ j,
        p j =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 k] fun u =>
          _root_.GD.N0232.N0719.N0975.d019760 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin j => _root_.GD.N0232.N0719.N0975.d019770 ref i)) (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u /
            _root_.GD.N0232.N0719.N0975.d019759 (tau ref) (_root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin j => _root_.GD.N0232.N0719.N0975.d019770 ref i)) (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u := by
  have ha : _root_.GD.N0230.N0556.d000031
      (fun q (z : (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 k))) => _root_.GD.N0232.N0719.N0975.d019769 tau ref q z)
      ⟨h, mem_univ h⟩ := by
    rintro ⟨z, hweak, q, hstrict⟩
    exact hadmissible ⟨z.1, hweak, q, hstrict⟩
  obtain ⟨p, w, hlimit, hcert⟩ := _root_.GD.N0230.N0622.d000623
    (H := _root_.GD.N0232.N0720.N1341.d004417 k) (Θ := Θ) (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 k)) (_root_.GD.N0232.N0719.N0975.d019769 tau ref)
    (_root_.GD.N0232.N0719.N0975.d019770 ref) ref h (mem_univ h) isClosed_univ convex_univ
    (fun q => _root_.GD.N0232.N0719.N0976.d019756 (tau ref) (tau q))
    (fun q => _root_.GD.N0232.N0719.N0976.d019758 (tau ref) (tau q))
    (fun z _ => (_root_.GD.N0232.N0719.N0976.d019757 (tau ref) z).comp htau)
    (_root_.GD.N0232.N0719.N0975.d019771 ref) 1 0 zero_lt_one
    (fun z _ => by simpa [_root_.GD.N0232.N0719.N0975.d019769] using _root_.GD.N0232.N0719.N0976.d019753 (tau ref) z)
    ha _root_.GD.N0232.N0720.N1314.d019727 _root_.GD.N0232.N0720.N1314.d019728 _root_.GD.N0232.N0720.N1314.d019729 _root_.GD.N0232.N0720.N1314.d019730
  refine ⟨p, w, hlimit, fun j => (hcert j).2.1, fun j => ?_⟩
  rw [_root_.GD.N0232.N0719.N0975.d019774 tau ref _ _ _ (hcert j).2]
  exact _root_.GD.N0232.N0720.N1314.d019687 _ _ _

include htau in



theorem d019776 (h : _root_.GD.N0232.N0720.N1341.d004417 k)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0975.d019769 tau ref) h) :
    ∃ (w : ∀ j, Fin j → ℝ) (ns : ℕ → ℕ),
      (∀ j i, 0 ≤ w j i) ∧ StrictMono ns ∧ ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 k,
        Tendsto (fun j => _root_.GD.N0232.N0719.N0975.d019765
          (_root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0975.d019770 ref i)) (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u /
          _root_.GD.N0232.N0719.N0975.d019764 (_root_.GD.N0232.N0719.N0975.d019772 tau ref (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0975.d019770 ref i))
            (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u) atTop (𝓝 (_root_.GD.N0232.N0719.N0976.d019748 (tau ref) u (h u))) := by
  obtain ⟨p, w, hlimit, hw, hratio⟩ := _root_.GD.N0232.N0719.N0975.d019775 tau htau ref h hadmissible
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlimit).exists_seq_tendsto_ae
  refine ⟨w, ns, hw, hns, ?_⟩
  have hall := ae_all_iff.mpr hratio
  filter_upwards [hpoint, hall] with u hu heq
  have hcont : Continuous (_root_.GD.N0232.N0719.N0976.d019748 (tau ref) u) := by unfold _root_.GD.N0232.N0719.N0976.d019748; fun_prop
  have ht := hcont.continuousAt.tendsto.comp hu
  convert ht using 1
  ext j
  rw [Function.comp_apply, heq (ns j)]
  exact (_root_.GD.N0232.N0719.N0975.d019768 (tau ref) _ _
    (_root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))) (_root_.GD.N0232.N0720.N1314.d019722 _) u).symm

end ParameterFamily
end
end GD.N0232.N0719.N0975

#print axioms _root_.GD.N0232.N0719.N0975.d019768
#print axioms _root_.GD.N0232.N0719.N0975.d019775
#print axioms _root_.GD.N0232.N0719.N0975.d019776
