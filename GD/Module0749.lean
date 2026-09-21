import GD.Module0015
import GD.Module0047
import GD.Module0725
import GD.Module0632
import GD.Module0748

















open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0719
namespace N0865

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1024
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0571
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0598
open _root_.GD.N0230.N0685

variable (k : ℕ) (sizes : Fin k → ℕ)
variable (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)



def d011214 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0932.d009224 k :=
  (theta.location, fun i ↦ ⟨theta.scale i, theta.scale_pos i⟩)

@[fun_prop]
theorem d011215 :
    Continuous (_root_.GD.N0232.N0719.N0865.d011214 k) := by
  apply Continuous.prodMk (_root_.GD.N0232.N0719.N0859.d011201 k)
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact _root_.GD.N0232.N0719.N0859.d011203 k i



def d011216
    (eta : _root_.GD.N0232.N0719.N0932.d009224 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009219
    k sizes eta.1 (fun i ↦ eta.2 i) omega


def d011217
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0865.d011216 k sizes
    (_root_.GD.N0232.N0719.N0865.d011214 k theta) omega

@[fun_prop]
theorem d011218 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta) := by
  change Measurable
    (_root_.GD.N0232.N0719.N0932.d009219
      k sizes theta.location theta.scale)
  exact _root_.GD.N0232.N0719.N0932.d009220
    k sizes theta.location theta.scale

theorem d011219
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega := by
  change 0 ≤ _root_.GD.N0232.N0719.N0932.d009219
    k sizes theta.location theta.scale omega
  exact _root_.GD.N0232.N0719.N0932.d009221
    k sizes theta.location theta.scale omega


theorem d011220 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes theta =
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes).withDensity
        (fun omega ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega)) := by
  change _root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale =
    (_root_.GD.N0232.N0719.d009182 k sizes).withDensity
      (fun omega ↦ ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0932.d009219
          k sizes theta.location theta.scale omega))
  exact _root_.GD.N0232.N0719.N0932.d009223
    k sizes theta.location theta.scale theta.scale_pos



theorem d011221 (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    Continuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega) := by
  change Continuous
    ((fun eta : _root_.GD.N0232.N0719.N0932.d009224 k ↦
        _root_.GD.N0232.N0719.N0865.d011216 k sizes eta omega) ∘
      _root_.GD.N0232.N0719.N0865.d011214 k)
  exact (_root_.GD.N0232.N0719.N0932.d009227
    k sizes omega).comp
      (_root_.GD.N0232.N0719.N0865.d011215 k)




theorem d011222
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    LowerSemicontinuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d) := by
  exact _root_.GD.N0230.N0591.d000131
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011217 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010809.location (k := k)) d
    (_root_.GD.N0232.N0719.N0865.d011220 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011218 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011219 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011221 k sizes)
    (_root_.GD.N0232.N0719.N0859.d011201 k)



theorem d011223
    (hcap : Continuous (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes)) :
    UpperSemicontinuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) := by
  have hcontinuous : Continuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) := by
    exact ENNReal.continuous_ofReal.comp hcap
  exact hcontinuous.upperSemicontinuous




theorem d011224
    (hbaseline : Continuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega ↦
          _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
            theta.location)))
    (hcross : Continuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale)) :
    Continuous (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0858.d010851
  exact hbaseline.add (continuous_const.mul hcross)



theorem d011225
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hcap : UpperSemicontinuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)) :
    (∀ n,
        _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d011211 k n) d ≤
          _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d011211 k n)) ↔
      _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d := by
  exact _root_.GD.N0230.N0598.d000594
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d011211 k) (_root_.GD.N0232.N0719.N0859.d011212 k) d
    hcap (_root_.GD.N0232.N0719.N0865.d011222 k sizes d)



theorem d011226
    (hcap : UpperSemicontinuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)) :
    _root_.GD.N0230.N0598.d000587
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d011211 k) =
      _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  ext d
  exact _root_.GD.N0232.N0719.N0865.d011225
    k sizes hk hsizes d hcap



theorem d011227
    (hcap : UpperSemicontinuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)) :
    (⋂ N,
        _root_.GD.N0230.N0598.d000588
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
          (_root_.GD.N0232.N0719.N0859.d011211 k) N) =
      _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  rw [_root_.GD.N0230.N0598.d000598]
  exact _root_.GD.N0232.N0719.N0865.d011226 k sizes hk hsizes hcap



theorem d011228 :
    _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) 0
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) := by
  constructor
  · exact _root_.GD.N0232.N0719.N0858.d010864 k sizes hk hsizes
  · intro d hd
    change _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes) d at hd
    simpa [_root_.GD.N0232.N0719.N0858.d010863] using
      (_root_.GD.N0230.N0571.d000694
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d010810 k)
        (0 : _root_.GD.N0230.N0602.d000116
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
        (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes)
        (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
        (by simpa [_root_.GD.N0232.N0719.N0858.d010858] using _root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d010829 k sizes) hd)





theorem d011229
    (hcap : UpperSemicontinuous (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes))
    (p : ℕ → _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hclosed : ∀ N, IsClosed
      (_root_.GD.N0230.N0598.d000588
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d011211 k) N))
    (hp : ∀ N, _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0230.N0598.d000588
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d011211 k) N)
      0 (p N)) :
    Tendsto p atTop
      (nhds (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)) := by
  apply _root_.GD.N0230.N0598.d000602
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0859.d011211 k) (_root_.GD.N0232.N0719.N0859.d011212 k)
    p (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) hcap
  · intro d hd
    exact _root_.GD.N0232.N0719.N0865.d011222 k sizes d
  · exact hclosed
  · exact hp
  · simpa [_root_.GD.N0230.N0598.d000586, _root_.GD.N0232.N0719.N0858.d010858, _root_.GD.N0230.N0571.d000684] using
      _root_.GD.N0232.N0719.N0865.d011228 k sizes hk hsizes



theorem d011230
    (hbaseline : Continuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega ↦
          _root_.GD.N0232.N0719.N0859.d010815 k sizes omega -
            theta.location)))
    (hcross : Continuous (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
      _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale)) :
    _root_.GD.N0230.N0598.d000587
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0859.d011211 k) =
      _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  apply _root_.GD.N0232.N0719.N0865.d011226 k sizes hk hsizes
  apply _root_.GD.N0232.N0719.N0865.d011223
  exact _root_.GD.N0232.N0719.N0865.d011224
    k sizes hk hsizes hbaseline hcross

end

end N0865
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0865.d011220
#print axioms _root_.GD.N0232.N0719.N0865.d011222
#print axioms _root_.GD.N0232.N0719.N0865.d011226
#print axioms _root_.GD.N0232.N0719.N0865.d011227
#print axioms _root_.GD.N0232.N0719.N0865.d011228
#print axioms _root_.GD.N0232.N0719.N0865.d011229
