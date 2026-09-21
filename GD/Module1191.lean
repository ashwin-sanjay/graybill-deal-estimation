import GD.Module1190
import GD.Module1139



























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1096

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1097
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}




theorem d019218
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hgap : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1097.d019207 hm hn c hs
  have hupper := hgap.const_mul 2
  rw [mul_zero] at hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun k ↦ _root_.GD.N0232.N0720.N1482.d015170 (c.seed k))
    (fun k ↦ _root_.GD.N0232.N0720.N1201.d015336
      m n (c.seed k))





theorem d019219
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k))
          atTop (nhds 0) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hs, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 s, hs, ?_⟩
    show Tendsto (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1201.d015333 m n s)
      atTop (nhds 0)
    rw [hgap]
    exact tendsto_const_nhds
  · rintro ⟨c, hs, hgap⟩
    exact _root_.GD.N0232.N0720.N1096.d019218
      hm hn c hs hgap


theorem d019220
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto (fun k ↦
      _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (c.seed k).value) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k))
      atTop (nhds 0) := by
  exact squeeze_zero
    (fun k ↦ _root_.GD.N0232.N0720.N1201.d015334 m n (c.seed k))
    (fun k ↦ _root_.GD.N0232.N0720.N1135.d018316
      (c.seed k) (candidate k))
    hcalibration


theorem d019221
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto (fun k ↦
      _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (c.seed k).value) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1096.d019218 hm hn c hs
    (_root_.GD.N0232.N0720.N1096.d019220 c candidate hcalibration)



theorem d019222
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
        (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074),
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
          m n (candidate k) (c.seed k).value) atTop (nhds 0) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hs, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 :=
      fun k ↦
        (_root_.GD.N0232.N0720.N1103.d018292
          s).candidate k
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 s, candidate, hs, ?_⟩
    have hlimit := _root_.GD.N0232.N0720.N1135.d018319 s
    rw [hgap] at hlimit
    simpa only [candidate, _root_.GD.N0232.N0720.N1097.d019214] using hlimit
  · rintro ⟨c, candidate, hs, hcalibration⟩
    exact _root_.GD.N0232.N0720.N1096.d019221
      hm hn c hs candidate hcalibration



def d019223 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : Prop :=
  ∀ k : ℕ, ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
    _root_.GD.N0232.N0720.N1131.d017154
      m n candidate (c.seed k).value ≤ 1 / ((k : ℝ) + 1)



theorem d019224
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (h : _root_.GD.N0232.N0720.N1096.d019223 c) :
    ∃ candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (c.seed k).value) atTop (nhds 0) := by
  let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 :=
    fun k ↦ Classical.choose (h k)
  refine ⟨candidate, ?_⟩
  apply squeeze_zero
    (fun k ↦ _root_.GD.N0232.N0720.N1131.d017156
      m n (candidate k) (c.seed k).value)
    (fun k ↦ Classical.choose_spec (h k))
  exact tendsto_one_div_add_atTop_nhds_zero_nat


theorem d019225
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1096.d019223 c := by
  constructor
  · intro hendpoint
    obtain ⟨s, hs, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 s, hs, ?_⟩
    intro k
    have hpositive : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨candidate, hcandidate⟩ :=
      _root_.GD.N0232.N0720.N1135.d018325 s
        (1 / ((k : ℝ) + 1)) hpositive
    rw [hgap, zero_add] at hcandidate
    exact ⟨candidate, hcandidate.le⟩
  · rintro ⟨c, hs, hharmonic⟩
    obtain ⟨candidate, hcalibration⟩ :=
      _root_.GD.N0232.N0720.N1096.d019224 c hharmonic
    exact _root_.GD.N0232.N0720.N1096.d019221
      hm hn c hs candidate hcalibration






def d019226 (c : _root_.GD.N0232.N0720.N1097.d019167 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (k : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      _root_.GD.N0232.N0720.N1131.d017154
        m n candidate (c.seed k).value < epsilon




theorem d019227
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : _root_.GD.N0232.N0720.N1096.d019226 c) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  by_contra hno
  obtain ⟨epsilon, hepsilon, hgapFloor⟩ :=
    _root_.GD.N0232.N0720.N1102.d015440
      m n hm hn hno c.seed c.descending hs
  obtain ⟨k, candidate, hcalibration⟩ := hsmall epsilon hepsilon
  have hfloor :
      epsilon ≤ _root_.GD.N0232.N0720.N1131.d017154
        m n candidate (c.seed k).value :=
    (hgapFloor k).trans
      (_root_.GD.N0232.N0720.N1135.d018316
        (c.seed k) candidate)
  exact (not_lt_of_ge hfloor) hcalibration




theorem d019228
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1096.d019226 c := by
  constructor
  · intro hendpoint
    obtain ⟨s, hs, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 s, hs, ?_⟩
    intro epsilon hepsilon
    obtain ⟨candidate, hcandidate⟩ :=
      _root_.GD.N0232.N0720.N1135.d018325 s epsilon hepsilon
    rw [hgap, zero_add] at hcandidate
    exact ⟨0, candidate, hcandidate⟩
  · rintro ⟨c, hs, hsmall⟩
    exact _root_.GD.N0232.N0720.N1096.d019227
      hm hn c hs hsmall




theorem d019229
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (¬ _root_.GD.N0232.N0720.N1159.d014661 m n) ↔
      ∀ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
            (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          ∃ epsilon : ℝ, 0 < epsilon ∧
            ∀ (k : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
              epsilon ≤ _root_.GD.N0232.N0720.N1131.d017154
                m n candidate (c.seed k).value := by
  constructor
  · intro hno c hs
    obtain ⟨epsilon, hepsilon, hgapFloor⟩ :=
      _root_.GD.N0232.N0720.N1102.d015440
        m n hm hn hno c.seed c.descending hs
    exact ⟨epsilon, hepsilon, fun k candidate ↦
      (hgapFloor k).trans
        (_root_.GD.N0232.N0720.N1135.d018316
          (c.seed k) candidate)⟩
  · intro hfloor hendpoint
    obtain ⟨c, hs, hsmall⟩ :=
      (_root_.GD.N0232.N0720.N1096.d019228
        hm hn).1 hendpoint
    obtain ⟨epsilon, hepsilon, hbound⟩ := hfloor c hs
    obtain ⟨k, candidate, hlt⟩ := hsmall epsilon hepsilon
    exact (not_lt_of_ge (hbound k candidate)) hlt



theorem d019230
    {I : Type*}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdirected : ∀ i j, ∃ r,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value (seed r).value ∧
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed r).value)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
        _root_.GD.N0232.N0720.N1131.d017154
          m n candidate (seed i).value < epsilon) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hgap : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨i, candidate, hcandidate⟩ := hsmall epsilon hepsilon
    exact ⟨i, lt_of_le_of_lt
      (_root_.GD.N0232.N0720.N1135.d018316
        (seed i) candidate) hcandidate⟩
  exact _root_.GD.N0232.N0720.N1102.d015438
    m n hm hn seed hdirected hgap iStrict hstrict

end

end N1096
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1096.d019218
#print axioms _root_.GD.N0232.N0720.N1096.d019219
#print axioms _root_.GD.N0232.N0720.N1096.d019220
#print axioms _root_.GD.N0232.N0720.N1096.d019222
#print axioms _root_.GD.N0232.N0720.N1096.d019225
#print axioms _root_.GD.N0232.N0720.N1096.d019228
#print axioms _root_.GD.N0232.N0720.N1096.d019229
#print axioms _root_.GD.N0232.N0720.N1096.d019230
