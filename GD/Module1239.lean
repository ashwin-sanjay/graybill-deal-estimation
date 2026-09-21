import GD.Module0886
import GD.Module1238
import GD.Module0048














open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1267

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1400
open _root_.GD.N0232.N0720.N1272
open _root_.GD.N0230.N0622

def d020128 (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem d020129 (n : ℕ) : 0 < _root_.GD.N0232.N0720.N1267.d020128 n := by
  unfold _root_.GD.N0232.N0720.N1267.d020128
  positivity

theorem d020130 : Antitone _root_.GD.N0232.N0720.N1267.d020128 := by
  intro n m hnm
  unfold _root_.GD.N0232.N0720.N1267.d020128
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem d020131 : Tendsto _root_.GD.N0232.N0720.N1267.d020128 atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem d020132 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    _root_.GD.N0230.N0556.d000031
      (fun t (h : (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 2 2))) ↦ _root_.GD.N0232.N0720.N1272.d013752 t h.1)
      ⟨_root_.GD.N0232.N0720.N1400.d020124 hd, mem_univ _⟩ := by
  rintro ⟨h, hdom, t, hstrict⟩
  have heq : h.1 = _root_.GD.N0232.N0720.N1400.d020124 hd :=
    _root_.GD.N0232.N0720.N1400.d020127 hd h.1 (fun t ↦ by
      rw [_root_.GD.N0232.N0720.N1272.d013759, _root_.GD.N0232.N0720.N1272.d013759]
      exact ENNReal.ofReal_le_ofReal (hdom t))
  exact (lt_irrefl (_root_.GD.N0232.N0720.N1272.d013752 t (_root_.GD.N0232.N0720.N1400.d020124 hd))) (heq ▸ hstrict)

set_option maxHeartbeats 2400000 in



theorem d020133 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ (sample : ℕ → _root_.GD.N0232.N0720.N1441.d013676) (p : ℕ → _root_.GD.N0232.N0720.N1441.d013681 2 2)
      (weight : ∀ n, Fin n → ℝ),
      DenseRange sample ∧ Tendsto p atTop (𝓝 (_root_.GD.N0232.N0720.N1400.d020124 hd)) ∧
      ∀ n, _root_.GD.N0230.N0622.d000607 univ _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1441.d013677
        (fun i : Fin n ↦ sample i) (weight n) (p n) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1441.d013676 := ⟨_root_.GD.N0232.N0720.N1441.d013677⟩
  obtain ⟨sample, hdense⟩ := TopologicalSpace.exists_dense_seq _root_.GD.N0232.N0720.N1441.d013676
  have hdecision (t : _root_.GD.N0232.N0720.N1441.d013676) : Continuous (_root_.GD.N0232.N0720.N1272.d013752 t) := by
    simpa only [Function.comp_def] using!
      _root_.GD.N0232.N0720.N1272.d013753.comp (continuous_const.prodMk continuous_id)
  have hparameter (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) (_hh : h ∈ (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 2 2))) :
      Continuous (fun t ↦ _root_.GD.N0232.N0720.N1272.d013752 t h) := by
    simpa only [Function.comp_def] using!
      _root_.GD.N0232.N0720.N1272.d013753.comp (continuous_id.prodMk continuous_const)
  have hreference (h : _root_.GD.N0232.N0720.N1441.d013681 2 2) (_hh : h ∈ (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 2 2))) :
      _root_.GD.N0232.N0720.N1272.d013752 _root_.GD.N0232.N0720.N1441.d013677 h = 1 * ‖h‖ ^ 2 + 0 := by
    simpa only [one_mul, add_zero] using _root_.GD.N0232.N0720.N1272.d013763 h
  obtain ⟨p, weight, hlim, hbayes⟩ := _root_.GD.N0230.N0622.d000623
    (H := _root_.GD.N0232.N0720.N1441.d013681 2 2) (Θ := _root_.GD.N0232.N0720.N1441.d013676)
    (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 2 2)) _root_.GD.N0232.N0720.N1272.d013752 sample _root_.GD.N0232.N0720.N1441.d013677 (_root_.GD.N0232.N0720.N1400.d020124 hd) (mem_univ _)
    isClosed_univ convex_univ
    hdecision _root_.GD.N0232.N0720.N1272.d013760 hparameter
    hdense 1 0 (by norm_num)
    hreference
    (_root_.GD.N0232.N0720.N1267.d020132 hd) _root_.GD.N0232.N0720.N1267.d020128 _root_.GD.N0232.N0720.N1267.d020129 _root_.GD.N0232.N0720.N1267.d020130
    _root_.GD.N0232.N0720.N1267.d020131
  exact ⟨sample, p, weight, hdense, hlim, fun n ↦ (hbayes n).2⟩

end
end GD.N0232.N0720.N1267

#print axioms _root_.GD.N0232.N0720.N1267.d020132
#print axioms _root_.GD.N0232.N0720.N1267.d020133
