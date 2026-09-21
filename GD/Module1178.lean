import GD.Module1025
import GD.Module1167




















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1468

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1354
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1501

variable (m n : ℕ)


theorem d018951
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) =
      _root_.GD.N0232.N0720.N1501.d016291 m n e := by
  haveI : Fact (_root_.GD.N0232.N0720.N1501.d016287 m n ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0720.N1080.d014170 m n))) :=
    ⟨_root_.GD.N0232.N0720.N1501.d016290 m n⟩
  rw [_root_.GD.N0232.N0720.N1501.d016292, _root_.GD.N0232.N0720.N1501.d016292]
  congr 1
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (condExpL2 ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016290 m n) e)



theorem d018952
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖d‖ ^ 2 = ‖_root_.GD.N0232.N0720.N1501.d016291 m n d‖ ^ 2 +
      ‖d - _root_.GD.N0232.N0720.N1501.d016291 m n d‖ ^ 2 := by
  let S := lpMeas ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016287 m n) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)
  letI : Fact (_root_.GD.N0232.N0720.N1501.d016287 m n ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0720.N1080.d014170 m n))) :=
    ⟨_root_.GD.N0232.N0720.N1501.d016290 m n⟩
  have h := S.norm_sq_eq_add_norm_sq_starProjection d
  simpa [S, _root_.GD.N0232.N0720.N1501.d016291, condExpL2] using h


def d018953
    (e d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d ∧
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014182 m n theta e < _root_.GD.N0232.N0720.N1080.d014182 m n theta d


def d018954 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018953 m n e d


def d018955 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  _root_.GD.N0232.N0720.N1501.d016291 m n d = d


def d018956 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {e | _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d}



theorem d018957
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (he : e ∈ _root_.GD.N0232.N0720.N1468.d018956 m n d) :
    _root_.GD.N0232.N0720.N1501.d016291 m n e ∈ _root_.GD.N0232.N0720.N1468.d018956 m n d := by
  intro theta
  exact (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta e).trans (he theta)



theorem d018958
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1501.d016291 m n '' _root_.GD.N0232.N0720.N1468.d018956 m n d =
      {e | _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ e ∈ _root_.GD.N0232.N0720.N1468.d018956 m n d} := by
  ext e
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_root_.GD.N0232.N0720.N1468.d018951 m n q,
      _root_.GD.N0232.N0720.N1468.d018957 m n hm hn hq⟩
  · rintro ⟨heFixed, heLower⟩
    exact ⟨e, heLower, heFixed⟩


theorem d018959
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (he : _root_.GD.N0232.N0720.N1468.d018953 m n e d) :
    _root_.GD.N0232.N0720.N1468.d018953 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) d := by
  refine ⟨?_, ?_⟩
  · intro theta
    exact (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta e).trans (he.1 theta)
  · obtain ⟨theta, htheta⟩ := he.2
    exact ⟨theta,
      lt_of_le_of_lt (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta e) htheta⟩




theorem d018960
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    (∃ e, _root_.GD.N0232.N0720.N1468.d018953 m n e d) ↔
      ∃ e, _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e d := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨_root_.GD.N0232.N0720.N1501.d016291 m n e,
      _root_.GD.N0232.N0720.N1468.d018951 m n e,
      _root_.GD.N0232.N0720.N1468.d018959 m n hm hn he⟩
  · rintro ⟨e, _heFixed, he⟩
    exact ⟨e, he⟩



theorem d018961
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1468.d018954 m n d ↔
      ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e d := by
  unfold _root_.GD.N0232.N0720.N1468.d018954
  rw [_root_.GD.N0232.N0720.N1468.d018960 m n hm hn d]



theorem d018962
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : ¬ _root_.GD.N0232.N0720.N1468.d018955 m n d) :
    _root_.GD.N0232.N0720.N1468.d018953 m n (_root_.GD.N0232.N0720.N1501.d016291 m n d) d := by
  have hweak : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n d) d :=
    fun theta => _root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta d
  refine ⟨hweak, ⟨_root_.GD.N0232.N0720.N1080.d014169, ?_⟩⟩
  have hresidual_ne : d - _root_.GD.N0232.N0720.N1501.d016291 m n d ≠ 0 := by
    intro hzero
    have hfixed : d = _root_.GD.N0232.N0720.N1501.d016291 m n d := sub_eq_zero.mp hzero
    exact hd hfixed.symm
  have hresidual_pos : 0 < ‖d - _root_.GD.N0232.N0720.N1501.d016291 m n d‖ :=
    (norm_pos_iff.mpr hresidual_ne)
  have hsq_lt : ‖_root_.GD.N0232.N0720.N1501.d016291 m n d‖ ^ 2 < ‖d‖ ^ 2 := by
    rw [_root_.GD.N0232.N0720.N1468.d018952 m n d]
    nlinarith [sq_pos_of_pos hresidual_pos]
  have hd_sq_pos : 0 < ‖d‖ ^ 2 :=
    lt_of_le_of_lt (sq_nonneg ‖_root_.GD.N0232.N0720.N1501.d016291 m n d‖) hsq_lt
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n (_root_.GD.N0232.N0720.N1501.d016291 m n d), _root_.GD.N0232.N0720.N1080.d014190 m n d]
  simp only [zero_sub, norm_neg]
  exact (ENNReal.ofReal_lt_ofReal_iff hd_sq_pos).2 hsq_lt



theorem d018963
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hd : _root_.GD.N0232.N0720.N1468.d018954 m n d) :
    _root_.GD.N0232.N0720.N1468.d018955 m n d := by
  by_contra hnot
  exact hd ⟨_root_.GD.N0232.N0720.N1501.d016291 m n d,
    _root_.GD.N0232.N0720.N1468.d018962 m n hm hn d hnot⟩




theorem d018964
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1468.d018954 m n d ↔
      _root_.GD.N0232.N0720.N1468.d018955 m n d ∧
        ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e d := by
  constructor
  · intro hd
    exact ⟨_root_.GD.N0232.N0720.N1468.d018963 m n hm hn hd,
      (_root_.GD.N0232.N0720.N1468.d018961
        m n hm hn d).1 hd⟩
  · rintro ⟨_hdFixed, hd⟩
    exact (_root_.GD.N0232.N0720.N1468.d018961
      m n hm hn d).2 hd






theorem d018965
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1468.d018954 m n s.value ↔ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  constructor
  · intro hadmissible
    apply (_root_.GD.N0232.N0720.N1354.d018748
      s.value s.finiteRisk).1
    intro e heverywhere
    apply hadmissible
    exact ⟨e, (fun theta ↦ (heverywhere theta).le),
      ⟨_root_.GD.N0232.N0720.N1080.d014169, heverywhere _root_.GD.N0232.N0720.N1080.d014169⟩⟩
  · intro hterminal
    rintro ⟨e, heweak, theta, hstrict⟩
    have heq : e = s.value := hterminal e heweak
    subst e
    exact (lt_irrefl (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)) hstrict


theorem d018966
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value ↔
      _root_.GD.N0232.N0720.N1468.d018955 m n s.value ∧
        ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e s.value := by
  exact (_root_.GD.N0232.N0720.N1468.d018965 m n s).symm.trans
    (_root_.GD.N0232.N0720.N1468.d018964 m n hm hn s.value)



theorem d018967
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1468.d018955 m n s.value ∧
            ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hterminal⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1468.d018966
        m n hm hn s).1 hterminal⟩
  · rintro ⟨s, hstrict, hsummary⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1468.d018966
        m n hm hn s).2 hsummary⟩

end

end N1468
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1468.d018958
#print axioms _root_.GD.N0232.N0720.N1468.d018960
#print axioms _root_.GD.N0232.N0720.N1468.d018962
#print axioms _root_.GD.N0232.N0720.N1468.d018963
#print axioms _root_.GD.N0232.N0720.N1468.d018964
#print axioms _root_.GD.N0232.N0720.N1468.d018965
#print axioms _root_.GD.N0232.N0720.N1468.d018966
#print axioms _root_.GD.N0232.N0720.N1468.d018967
