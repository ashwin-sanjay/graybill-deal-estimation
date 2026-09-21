import GD.Module0961
import Mathlib.MeasureTheory.Function.UniformIntegrable











open Filter MeasureTheory Topology

namespace GD
namespace N0232
namespace N0720
namespace N1215

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015113 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance




theorem d015114
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  exact (_root_.GD.N0232.N0720.N1214.d014267 m n
    (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp)).trans
      (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp).coeFn_toLp



theorem d015115
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1214.d014265 m n
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)).1 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g
        (_root_.GD.N0232.N0720.N1214.d014265 m n
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1) := by
  change
    _root_.GD.N0232.N0720.N1214.d014265 m n
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g
        (_root_.GD.N0232.N0720.N1214.d014265 m n
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1)
  exact _root_.GD.N0232.N0720.N1215.d015114 m n hm hn g
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2







theorem d015116
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit)) :
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn (gSeq j) q)).1)
      atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn
            (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) q)).1) := by
  have hraw := _root_.GD.N0232.N0720.N1484.d015110 m n hm hn q
    gSeq limit hcoordinate
  exact (hraw.congr_left (fun j ↦
      (_root_.GD.N0232.N0720.N1215.d015115
        m n hm hn (gSeq j) q).symm)).congr_right
    (_root_.GD.N0232.N0720.N1215.d015115 m n hm hn
      (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) q).symm






theorem d015117
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds (g.shift, g.logScale))) :
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn (gSeq j) q)).1)
      atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)).1) := by
  simpa using _root_.GD.N0232.N0720.N1215.d015116
    m n hm hn q gSeq (g.shift, g.logScale) hcoordinate

#print axioms _root_.GD.N0232.N0720.N1215.d015115
#print axioms _root_.GD.N0232.N0720.N1215.d015116
#print axioms _root_.GD.N0232.N0720.N1215.d015117

end
end N1215
end N0720
end N0232
end GD
