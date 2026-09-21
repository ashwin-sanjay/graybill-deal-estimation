import GD.Module0966





























open Filter Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1027

noncomputable section

open _root_.GD.N0230.N0645
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0232.N0720.N1200



variable {G Theta Rule : Type*} [Group G] [MulAction G Theta]


def d015301
    (risk : Theta → Rule → ℝ) (character : G → ℝ) (d : Rule) : Prop :=
  ∀ (g : G) (theta : Theta),
    risk (g • theta) d = character g * risk theta d


def d015302
    (risk : Theta → Rule → ℝ) (seed candidate : Rule) (theta : Theta) : ℝ :=
  risk theta seed - risk theta candidate







theorem d015303
    (risk : Theta → Rule → ℝ) (character : G → ℝ)
    (seed candidate : Rule)
    (hseed : _root_.GD.N0232.N0720.N1027.d015301 risk character seed) :
    _root_.GD.N0232.N0720.N1027.d015301 risk character candidate ↔
      ∀ (g : G) (theta : Theta),
        _root_.GD.N0232.N0720.N1027.d015302 risk seed candidate (g • theta) =
          character g * _root_.GD.N0232.N0720.N1027.d015302 risk seed candidate theta := by
  constructor
  · intro hcandidate g theta
    simp only [_root_.GD.N0232.N0720.N1027.d015302, hseed g theta, hcandidate g theta]
    ring
  · intro hgain g theta
    have h := hgain g theta
    simp only [_root_.GD.N0232.N0720.N1027.d015302, hseed g theta] at h
    linarith



theorem d015304
    (risk : Theta → Rule → ℝ) (seed candidate baseline : Rule)
    (hle : ∀ theta, risk theta candidate ≤ risk theta seed)
    (hstrict : ∀ theta, risk theta seed < risk theta baseline) :
    ∀ theta, risk theta candidate < risk theta baseline := by
  intro theta
  exact lt_of_le_of_lt (hle theta) (hstrict theta)



variable {X : Type*}




theorem d015305
    (generator average terminalize : X → X) (seed : X)
    (haverageFixed : ∀ x, generator (average x) = average x)
    (hcommutes : terminalize (average seed) = average (terminalize seed)) :
    generator (terminalize (average seed)) =
      terminalize (average seed) := by
  rw [hcommutes, haverageFixed]




theorem d015306
    (generatorOne generatorTwo average terminalize : X → X) (seed : X)
    (haverageFixedOne : ∀ x, generatorOne (average x) = average x)
    (haverageFixedTwo : ∀ x, generatorTwo (average x) = average x)
    (hcommutes : terminalize (average seed) = average (terminalize seed)) :
    generatorOne (terminalize (average seed)) = terminalize (average seed) ∧
      generatorTwo (terminalize (average seed)) = terminalize (average seed) := by
  exact ⟨_root_.GD.N0232.N0720.N1027.d015305
      generatorOne average terminalize seed haverageFixedOne hcommutes,
    _root_.GD.N0232.N0720.N1027.d015305
      generatorTwo average terminalize seed haverageFixedTwo hcommutes⟩




def d015307 (_x : _root_.GD.N0230.N0645.d000855) : _root_.GD.N0230.N0645.d000855 :=
  _root_.GD.N0230.N0645.d000860



theorem d015308 (x : _root_.GD.N0230.N0645.d000855) :
    (_root_.GD.N0232.N0720.N1027.d015307 x).1 =
      (x.1 + (_root_.GD.N0230.N0645.d000856 x).1) / 2 := by
  simp [_root_.GD.N0232.N0720.N1027.d015307, _root_.GD.N0230.N0645.d000860, _root_.GD.N0230.N0645.d000856]


theorem d015309 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000856 (_root_.GD.N0232.N0720.N1027.d015307 x) = _root_.GD.N0232.N0720.N1027.d015307 x := by
  simp [_root_.GD.N0232.N0720.N1027.d015307, _root_.GD.N0230.N0645.d000869]



theorem d015310 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015276 (_root_.GD.N0232.N0720.N1027.d015307 x) := by
  exact (_root_.GD.N0232.N0720.N1200.d015277
    (_root_.GD.N0232.N0720.N1027.d015307 x)).2 rfl



theorem d015311 :
    _root_.GD.N0232.N0720.N1200.d015278
        (_root_.GD.N0232.N0720.N1027.d015307 _root_.GD.N0230.N0645.d000860) ≠
      _root_.GD.N0232.N0720.N1027.d015307
        (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860) := by
  intro h
  have hvalue := congrArg Subtype.val h
  norm_num [_root_.GD.N0232.N0720.N1200.d015278, _root_.GD.N0232.N0720.N1027.d015307,
    _root_.GD.N0230.N0645.d000858, _root_.GD.N0230.N0645.d000860] at hvalue



theorem d015312
    (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015278 (_root_.GD.N0232.N0720.N1027.d015307 x) =
      _root_.GD.N0230.N0645.d000858 := rfl



theorem d015313 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015283 (_root_.GD.N0232.N0720.N1027.d015307 x) = 2 := by
  exact _root_.GD.N0232.N0720.N1200.d015284 _



def d015314 (_j : ℕ) : _root_.GD.N0230.N0645.d000855 :=
  _root_.GD.N0232.N0720.N1027.d015307
    (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860)

@[simp] theorem d015315 (j : ℕ) :
    _root_.GD.N0232.N0720.N1027.d015314 j = _root_.GD.N0230.N0645.d000860 := rfl

@[simp] theorem d015316 (j : ℕ) :
    _root_.GD.N0232.N0720.N1200.d015283
      (_root_.GD.N0232.N0720.N1027.d015314 j) = 2 := by
  exact _root_.GD.N0232.N0720.N1200.d015284 _



theorem d015317 :
    ¬ Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1200.d015283
        (_root_.GD.N0232.N0720.N1027.d015314 j)) atTop (nhds 0) := by
  intro hzero
  have htwo : Tendsto
      (fun _j : ℕ ↦ (2 : ℝ)) atTop (nhds (2 : ℝ)) :=
    tendsto_const_nhds
  have heq : (0 : ℝ) = 2 := tendsto_nhds_unique
    (by simpa only [_root_.GD.N0232.N0720.N1027.d015316] using hzero)
    htwo
  norm_num at heq






theorem d015318 :
    _root_.GD.N0232.N0720.N1200.d015276
        (_root_.GD.N0232.N0720.N1027.d015307
          (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860)) ∧
      _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266
        (_root_.GD.N0232.N0720.N1027.d015307
          (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860))
        (_root_.GD.N0232.N0720.N1200.d015278
          (_root_.GD.N0232.N0720.N1027.d015307
            (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860))) ∧
      _root_.GD.N0230.N0630.d000786 _root_.GD.N0232.N0720.N1200.d015266
        (_root_.GD.N0232.N0720.N1200.d015278
          (_root_.GD.N0232.N0720.N1027.d015307
            (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860))) ∧
      _root_.GD.N0232.N0720.N1200.d015278
          (_root_.GD.N0232.N0720.N1027.d015307 _root_.GD.N0230.N0645.d000860) ≠
        _root_.GD.N0232.N0720.N1027.d015307
          (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860) ∧
      _root_.GD.N0232.N0720.N1200.d015283
        (_root_.GD.N0232.N0720.N1027.d015307
          (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860)) = 2 := by
  let averaged : _root_.GD.N0230.N0645.d000855 :=
    _root_.GD.N0232.N0720.N1027.d015307
      (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860)
  have heligible : _root_.GD.N0232.N0720.N1200.d015276 averaged :=
    _root_.GD.N0232.N0720.N1027.d015310 _
  have hspec := _root_.GD.N0232.N0720.N1200.d015279 averaged heligible
  exact ⟨heligible, hspec.1, hspec.2,
    _root_.GD.N0232.N0720.N1027.d015311,
    _root_.GD.N0232.N0720.N1027.d015313 _⟩

end


end N1027
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1027.d015303
#print axioms _root_.GD.N0232.N0720.N1027.d015306
#print axioms _root_.GD.N0232.N0720.N1027.d015311
#print axioms _root_.GD.N0232.N0720.N1027.d015317
#print axioms _root_.GD.N0232.N0720.N1027.d015318
