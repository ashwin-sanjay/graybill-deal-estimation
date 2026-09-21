import GD.Module0778
import GD.Module0732
import GD.Module0784


















open Filter MeasureTheory
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0719
namespace N0835

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0839
open _root_.GD.N0232.N0719.N0819
open _root_.GD.N0232.N0719.N0833
open _root_.GD.N0232.N0719.N0959
open _root_.GD.N0230.N0655

variable
  {k : ℕ} {sizes : Fin k → ℕ}
  {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}



def d011953
    (g : _root_.GD.N0230.N0655.d000349) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 g.1 g.2) (g.2 : ℝ)⁻¹
    (inv_pos.mpr g.2.2) (_root_.GD.N0232.N0719.N0859.d010810 k)


theorem d011954
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0845.d010881 g.1 g.2 g.2.2
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) = _root_.GD.N0232.N0719.N0859.d010810 k := by
  exact _root_.GD.N0232.N0719.N0842.d010919 g.1 g.2 g.2.2 (_root_.GD.N0232.N0719.N0859.d010810 k)



theorem d011955
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  by_cases hk0 : k = 0
  · subst k
    exact Subsingleton.elim _ _
  · unfold _root_.GD.N0232.N0719.N0835.d011953
    exact _root_.GD.N0232.N0719.N0819.d011731 (Nat.pos_of_ne_zero hk0)
      (_root_.GD.N0232.N0719.N0842.d010906 g.1 g.2) (g.2 : ℝ)⁻¹ (inv_pos.mpr g.2.2)
      (_root_.GD.N0232.N0719.N0859.d010810 k)



theorem d011956
    (hkpos : 0 < k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0859.d010810 k) i = 1 / (k : ℝ) := by
  simp [_root_.GD.N0232.N0719.N0819.d011729, _root_.GD.N0232.N0719.N0815.d010926, _root_.GD.N0232.N0719.N0815.d010924,
    _root_.GD.N0232.N0719.N0859.d010810, Nat.cast_ne_zero.mpr hkpos.ne']



theorem d011957
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i = 1 / (k : ℝ) := by
  rw [_root_.GD.N0232.N0719.N0835.d011955]
  exact _root_.GD.N0232.N0719.N0835.d011956
    (Nat.zero_lt_of_lt i.isLt) i



theorem d011958
    (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) i := by
  rw [_root_.GD.N0232.N0719.N0835.d011955]
  exact _root_.GD.N0232.N0719.N0959.d011926
    (Nat.zero_lt_of_lt i.isLt) (_root_.GD.N0232.N0719.N0859.d010810 k) i


theorem d011959
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0819.d011733
        (_root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g)) =
      (Finset.univ : Finset (Fin k)) := by
  ext i
  simp only [_root_.GD.N0232.N0719.N0819.d011734, Finset.mem_univ, iff_true]
  exact _root_.GD.N0232.N0719.N0835.d011958 g i



theorem d011960
    (g : ℕ → _root_.GD.N0230.N0655.d000349) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) (g n)))
      atTop (nhds (_root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0859.d010810 k))) := by
  simpa only [_root_.GD.N0232.N0719.N0835.d011955] using
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0859.d010810 k))
      atTop (nhds (_root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0859.d010810 k))))





theorem d011961
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
        data.p (data.d011843 g) =
      _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) data.p data.q := by
  have htransport := _root_.GD.N0232.N0719.N0839.d011008
    k sizes hk hsizes g.1 g.2 g.2.2
    (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) data.p data.q
    data.p_measurable data.q_measurable
  rw [_root_.GD.N0232.N0719.N0835.d011954] at htransport
  rw [data.p_fixed g.1 g.2 g.2.2] at htransport
  exact htransport




theorem d011962
    (data : _root_.GD.N0232.N0719.N0833.d011835 k sizes hk hsizes)
    (g : ℕ → _root_.GD.N0230.N0655.d000349)
    (hzero : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0859.d010810 k) data.p (data.d011843 (g n)))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) (g n)) data.p data.q)
      atTop (nhds 0) := by
  simpa only [_root_.GD.N0232.N0719.N0835.d011961] using hzero

end

end N0835
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0835.d011955
#print axioms _root_.GD.N0232.N0719.N0835.d011959
#print axioms _root_.GD.N0232.N0719.N0835.d011961
#print axioms _root_.GD.N0232.N0719.N0835.d011962
