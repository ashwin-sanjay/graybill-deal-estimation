import GD.Module0094
import GD.Module0736

















open Set MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N0850

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0703
open _root_.GD.N0230.N0709

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)



def d011063 : Set
    (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))) :=
  toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) ''
    _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes



theorem d011064 :
    (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))).symm ''
        _root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes =
      _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  ext d
  constructor
  · rintro ⟨w, ⟨e, he, rfl⟩, rfl⟩
    simpa using he
  · intro hd
    exact ⟨toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) d,
      ⟨d, hd, rfl⟩, by simp⟩



theorem d011065 :
    (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))).symm ''
        _root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes ⊆
      Metric.closedBall 0 (_root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes) := by
  rw [_root_.GD.N0232.N0719.N0850.d011064 k sizes hk hsizes]
  intro d hd
  simpa [Metric.mem_closedBall, dist_eq_norm] using
    _root_.GD.N0232.N0719.N0858.d011034 k sizes hk hsizes d hd



theorem d011066 :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes) := by
  exact (Metric.isBounded_closedBall.subset
    (_root_.GD.N0232.N0719.N0850.d011065 k sizes hk hsizes))


theorem d011067 :
    IsCompact (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes) := by
  exact _root_.GD.N0232.N0719.N0858.d011035 k sizes hk hsizes


theorem d011068 :
    Convex ℝ (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes) := by
  exact (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes).linear_image
    (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))).toLinearMap


theorem d011069 :
    (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes).Nonempty := by
  exact (_root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes).image
    (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)))







theorem d011070
    {T A : Type*}
    (inner : T →
      (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) →ᴬ[ℝ]
        WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))))
    (outer : A →
      (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) →ᴬ[ℝ]
        WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))))
    (hinnerC : ∀ t, MapsTo (inner t)
      (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes))
    (hinnerCommutes : _root_.GD.N0230.N0703.d001148 (fun t ↦ inner t))
    (hnormal : _root_.GD.N0230.N0703.d001147 (fun a ↦ outer a) (fun t ↦ inner t))
    (houterC : ∀ a, MapsTo (outer a)
      (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes))
    (houterCommutes : _root_.GD.N0230.N0703.d001148 (fun a ↦ outer a)) :
    ∃ x, x ∈ _root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes ∧
      (∀ t, inner t x = x) ∧ ∀ a, outer a x = x := by
  exact _root_.GD.N0230.N0709.d001231
    inner outer (_root_.GD.N0232.N0719.N0850.d011063 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0850.d011067 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0850.d011068 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0850.d011069 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0850.d011066 k sizes hk hsizes)
    hinnerC hinnerCommutes hnormal houterC houterCommutes

#print axioms _root_.GD.N0232.N0719.N0850.d011066
#print axioms _root_.GD.N0232.N0719.N0850.d011065
#print axioms _root_.GD.N0232.N0719.N0850.d011070

end
end N0850
end N0719
end N0232
end GD
