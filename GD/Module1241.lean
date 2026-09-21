import GD.Module1234
import GD.Module1239









open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1305

open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1337
open _root_.GD.N0232.N0720.N1335
open _root_.GD.N0230.N0622
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0720.N1267
  (d020128 d020129 d020130 d020131)

noncomputable section

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d020143 (H : _root_.GD.N0232.N0720.N1441.d013681 m n) (hadm : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H) :
    _root_.GD.N0230.N0556.d000031 (fun t (h : (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 m n))) ↦ _root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h.1)
      ⟨H, mem_univ _⟩ := by
  rintro ⟨h, hdom, t, hstrict⟩
  exact hadm ⟨h.1, hdom, t, hstrict⟩

set_option maxHeartbeats 2400000 in
theorem d020144 (H : _root_.GD.N0232.N0720.N1441.d013681 m n)
    (hadm : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H) :
    ∃ (sample : ℕ → _root_.GD.N0232.N0720.N1441.d013676) (p : ℕ → _root_.GD.N0232.N0720.N1441.d013681 m n)
      (weight : ∀ k, Fin k → ℝ),
      DenseRange sample ∧ Tendsto p atTop (𝓝 H) ∧
      ∀ k, _root_.GD.N0230.N0622.d000607 univ (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) _root_.GD.N0232.N0720.N1441.d013677
        (fun i : Fin k ↦ sample i) (weight k) (p k) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1441.d013676 := ⟨_root_.GD.N0232.N0720.N1441.d013677⟩
  obtain ⟨sample, hdense⟩ := TopologicalSpace.exists_dense_seq _root_.GD.N0232.N0720.N1441.d013676
  have hdecision (t : _root_.GD.N0232.N0720.N1441.d013676) : Continuous (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn t) := by
    simpa only [Function.comp_def] using!
      (_root_.GD.N0232.N0720.N1337.d013827 m n hm hn).comp (continuous_const.prodMk continuous_id)
  have hparameter (h : _root_.GD.N0232.N0720.N1441.d013681 m n) (_hh : h ∈ (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 m n))) :
      Continuous (fun t ↦ _root_.GD.N0232.N0720.N1337.d013826 m n hm hn t h) := by
    simpa only [Function.comp_def] using!
      (_root_.GD.N0232.N0720.N1337.d013827 m n hm hn).comp (continuous_id.prodMk continuous_const)
  have hreference (h : _root_.GD.N0232.N0720.N1441.d013681 m n) (_hh : h ∈ (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 m n))) :
      _root_.GD.N0232.N0720.N1337.d013826 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 h = 1 * ‖h‖ ^ 2 + 0 := by
    simpa only [one_mul, add_zero] using _root_.GD.N0232.N0720.N1337.d013836 m n hm hn h
  obtain ⟨p, weight, hlim, hbayes⟩ := _root_.GD.N0230.N0622.d000623
    (H := _root_.GD.N0232.N0720.N1441.d013681 m n) (Θ := _root_.GD.N0232.N0720.N1441.d013676)
    (univ : Set (_root_.GD.N0232.N0720.N1441.d013681 m n)) (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) sample _root_.GD.N0232.N0720.N1441.d013677 H (mem_univ _)
    isClosed_univ convex_univ hdecision (_root_.GD.N0232.N0720.N1337.d013834 m n hm hn) hparameter
    hdense 1 0 (by norm_num) hreference (_root_.GD.N0232.N0720.N1305.d020143 m n hm hn H hadm)
    _root_.GD.N0232.N0720.N1267.d020128 _root_.GD.N0232.N0720.N1267.d020129 _root_.GD.N0232.N0720.N1267.d020130 _root_.GD.N0232.N0720.N1267.d020131
  exact ⟨sample, p, weight, hdense, hlim, fun k ↦ (hbayes k).2⟩

end
end GD.N0232.N0720.N1305

#print axioms _root_.GD.N0232.N0720.N1305.d020143
#print axioms _root_.GD.N0232.N0720.N1305.d020144
