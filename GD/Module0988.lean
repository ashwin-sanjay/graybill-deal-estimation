import GD.Module0986
import GD.Module0965
import GD.Module0973
import GD.Module0082

































open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1412

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0698
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}





theorem d015646
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖(seed j).value -
        _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖)
      atTop (nhds 0) := by
  have hsqrt : Tendsto
      (fun j ↦ Real.sqrt (_root_.GD.N0232.N0720.N1201.d015333 m n (seed j)))
      atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hgap
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  apply squeeze_zero
    (fun j ↦ norm_nonneg
      ((seed j).value - _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value))
    (fun j ↦ ?_) hsqrt
  have hsq := _root_.GD.N0232.N0720.N1288.d015626 m n (seed j)
  have hnonneg := _root_.GD.N0232.N0720.N1201.d015334 m n (seed j)
  have hsqrtNonneg :
      0 ≤ Real.sqrt (_root_.GD.N0232.N0720.N1201.d015333 m n (seed j)) :=
    Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt hnonneg,
    norm_nonneg ((seed j).value -
      _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)]




theorem d015647
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
      atTop (nhds d) := by
  have hprojectionSeed : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value -
        (seed j).value‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using
      _root_.GD.N0232.N0720.N1412.d015646 seed hgap
  have hseedLimit : Tendsto (fun j ↦ ‖(seed j).value - d‖)
      atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hvalue
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
    (fun j ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value - d))
    (fun j ↦ norm_sub_le_norm_sub_add_norm_sub
      (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value) (seed j).value d)
  simpa only [zero_add] using hprojectionSeed.add hseedLimit




theorem d015648
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hcauchy : CauchySeq (fun j ↦ (seed j).value))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      Tendsto (fun j ↦ (seed j).value) atTop (nhds d) ∧
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
        atTop (nhds d) := by
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨d, hd,
    _root_.GD.N0232.N0720.N1412.d015647
      seed d hd hgap⟩





theorem d015649
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (seed j).value -
        (seed j).value‖) atTop (nhds 0) := by
  have hmajor : Tendsto
      (fun j ↦ Real.sqrt
        (4 * _root_.GD.N0232.N0720.N1201.d015333 m n (seed j)))
      atTop (nhds 0) := by
    have hfour : Tendsto
        (fun j ↦ 4 * _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hgap.const_mul 4
    have h := (Real.continuous_sqrt.tendsto 0).comp hfour
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  apply squeeze_zero
    (fun j ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate (seed j).value -
        (seed j).value))
    (fun j ↦ ?_) hmajor
  rw [_root_.GD.N0232.N0720.N1146.d015218
    m n certificate (seed j).value (seed j).finiteRisk]
  have hsq :=
    _root_.GD.N0232.N0720.N1288.d015628
      m n (seed j) g
  have hgapNonneg := _root_.GD.N0232.N0720.N1201.d015334 m n (seed j)
  have hfourNonneg :
      0 ≤ 4 * _root_.GD.N0232.N0720.N1201.d015333 m n (seed j) := by positivity
  nlinarith [Real.sq_sqrt hfourNonneg,
    Real.sqrt_nonneg (4 * _root_.GD.N0232.N0720.N1201.d015333 m n (seed j)),
    norm_nonneg
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (seed j).value (seed j).finiteRisk -
        (seed j).value)]



theorem d015650
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1146.d015212 m n certificate d = d := by
  have htransport : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1146.d015212 m n certificate (seed j).value)
      atTop (nhds (_root_.GD.N0232.N0720.N1146.d015212 m n certificate d)) :=
    (_root_.GD.N0232.N0720.N1146.d015216 m n certificate).continuous
      |>.continuousAt.tendsto.comp hvalue
  have hnorm : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (seed j).value -
        (seed j).value‖) atTop
      (nhds ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate d - d‖) :=
    (htransport.sub hvalue).norm
  have hzero :
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate d - d‖ = 0 :=
    tendsto_nhds_unique hnorm
      (_root_.GD.N0232.N0720.N1412.d015649
        certificate seed hgap)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)





theorem d015651
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hdFinite : _root_.GD.N0232.N0720.N1159.d014637 m n d) :
    _root_.GD.N0232.N0720.N1159.d014652 m n d := by
  have hTwoRef : _root_.GD.N0232.N0720.N1146.d015228 m n d = d :=
    _root_.GD.N0232.N0720.N1412.d015650
      (_root_.GD.N0232.N0720.N1146.d015221 m n) seed d hvalue hgap
  have hThreeRef :
      _root_.GD.N0232.N0720.N1146.d015229 m n d = d :=
    _root_.GD.N0232.N0720.N1412.d015650
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      seed d hvalue hgap
  have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 d hdFinite = d := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) d hdFinite]
    exact hTwoRef
  have hThree :
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 d hdFinite = d := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) d hdFinite]
    exact hThreeRef
  have hall : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite = d :=
    _root_.GD.N0232.N0720.N1482.d015167 (m := m) (n := n)
      d hdFinite hTwo hThree
  exact (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn d hdFinite).1 hall




def d015652 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d}






def d015653
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∃ (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
      (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
    Tendsto (fun j ↦ (seed j).value) atTop (nhds d) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
        atTop (nhds 0) ∧
      IsClosed (_root_.GD.N0232.N0720.N1412.d015652 (m := m) (n := n)) ∧
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) d
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)




def d015654
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∃ (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
      (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
      (checkpoint : ℕ → ℕ),
    Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
        atTop (nhds 0) ∧
      Tendsto checkpoint atTop atTop ∧
      (∀ k, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed (checkpoint k)).value d) ∧
      ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) p d



def d015655
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  _root_.GD.N0232.N0720.N1412.d015653 m n hm hn ∨
    _root_.GD.N0232.N0720.N1412.d015654 m n hm hn





theorem d015656
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hclosed : IsClosed (_root_.GD.N0232.N0720.N1412.d015652 (m := m) (n := n)))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) d
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hprojection :=
    _root_.GD.N0232.N0720.N1412.d015647
      seed d hvalue hgap
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d := by
    apply hclosed.mem_of_tendsto hprojection
    exact Eventually.of_forall fun j ↦
      (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).2.1
  have hdFinite : _root_.GD.N0232.N0720.N1159.d014637 m n d :=
    _root_.GD.N0232.N0720.N1159.d014640
      m n d (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict
  have hrep := _root_.GD.N0232.N0720.N1412.d015651
    hm hn seed d hvalue hgap hdFinite
  exact (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2 ⟨d, hrep, hstrict, hterminal⟩


theorem d015657
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : _root_.GD.N0232.N0720.N1412.d015653 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rcases h with ⟨seed, d, hvalue, hgap, hclosed, hstrict⟩
  exact _root_.GD.N0232.N0720.N1412.d015656
    hm hn seed d hvalue hgap hclosed hstrict



theorem d015658
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hclosed : IsClosed (_root_.GD.N0232.N0720.N1412.d015652 (m := m) (n := n)))
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hanchor : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed iStrict).value d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1412.d015656
    hm hn seed d hvalue hgap hclosed
  intro theta
  exact lt_of_le_of_lt (hanchor theta) (hstrict theta)





theorem d015659
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {I : Type*}
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hanchor : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) p d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨hterminal, hrep⟩ :=
    _root_.GD.N0232.N0720.N1102.d015432
      m n hm hn seed d hsmall hbelow
  apply (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2
  refine ⟨d, hrep, ?_, hterminal⟩
  intro theta
  exact lt_of_le_of_lt (hanchor theta) (hstrict theta)



theorem d015660
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (checkpoint : ℕ → ℕ)
    (hcheckpoint : Tendsto checkpoint atTop atTop)
    (hbelow : ∀ k, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed (checkpoint k)).value d)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hanchor : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) p d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let selected : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n :=
    fun k ↦ seed (checkpoint k)
  have hselectedGap : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (selected k))
      atTop (nhds 0) := hgap.comp hcheckpoint
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ k, _root_.GD.N0232.N0720.N1201.d015333 m n (selected k) < ε := by
    intro ε hε
    rw [Metric.tendsto_atTop] at hselectedGap
    obtain ⟨K, hK⟩ := hselectedGap ε hε
    refine ⟨K, ?_⟩
    have h := hK K le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (_root_.GD.N0232.N0720.N1201.d015334 m n (selected K))]
      at h
    exact h
  exact _root_.GD.N0232.N0720.N1412.d015659
    (m := m) (n := n) hm hn selected d hsmall (fun k ↦ hbelow k)
      p hstrict hanchor


theorem d015661
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : _root_.GD.N0232.N0720.N1412.d015654 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rcases h with
    ⟨seed, d, checkpoint, hgap, hcheckpoint, hbelow,
      p, hstrict, hanchor⟩
  exact _root_.GD.N0232.N0720.N1412.d015660
    hm hn seed hgap d checkpoint hcheckpoint hbelow p hstrict hanchor






theorem d015662
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hendpoint : _root_.GD.N0232.N0720.N1159.d014661 m n) :
    _root_.GD.N0232.N0720.N1412.d015654 m n hm hn := by
  obtain ⟨s, hstrict, hgap⟩ :=
    (_root_.GD.N0232.N0720.N1201.d015341
      m n hm hn).1 hendpoint
  refine ⟨fun _ ↦ s, s.value, id, ?_, tendsto_id, ?_, s.value, hstrict, ?_⟩
  · simpa only [hgap] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · intro k
    exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
  · exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value



theorem d015663
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1412.d015654 m n hm hn := by
  constructor
  · exact
      _root_.GD.N0232.N0720.N1412.d015662
        hm hn
  · exact
      _root_.GD.N0232.N0720.N1412.d015661
        hm hn



theorem d015664
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1412.d015654 m n hm hn :=
  not_congr
    (_root_.GD.N0232.N0720.N1412.d015663
      hm hn)





theorem d015665
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1412.d015655 m n hm hn := by
  constructor
  · intro hendpoint
    exact Or.inr
      (_root_.GD.N0232.N0720.N1412.d015662
        hm hn hendpoint)
  · rintro (hclosed | hcofinal)
    · exact
        _root_.GD.N0232.N0720.N1412.d015657
          hm hn hclosed
    · exact
        _root_.GD.N0232.N0720.N1412.d015661
          hm hn hcofinal


theorem d015666
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1412.d015655 m n hm hn :=
  not_congr
    (_root_.GD.N0232.N0720.N1412.d015665 hm hn)




theorem d015667
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (checkpoint : ℕ → ℕ)
    (hcheckpoint : Tendsto checkpoint atTop atTop)
    (hbelow : ∀ k, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed (checkpoint k)).value d)
    (hdominator : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1412.d015660
    (m := m) (n := n) hm hn seed hgap d checkpoint hcheckpoint hbelow
      (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn) hdominator






theorem d015668
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (checkpoint : ℕ → ℕ)
    (hcheckpoint : Tendsto checkpoint atTop atTop)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed (checkpoint 0)).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hbelow : ∀ k, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed (checkpoint k)).value d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1412.d015660
    (m := m) (n := n) hm hn seed hgap d checkpoint hcheckpoint hbelow
      (seed (checkpoint 0)).value hstrict (hbelow 0)



theorem d015669
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ᶠ j in atTop,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value d)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hanchor : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) p d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbelow
  let checkpoint : ℕ → ℕ := fun k ↦ N + k
  have hcheckpoint : Tendsto checkpoint atTop atTop := by
    apply tendsto_atTop.2
    intro b
    apply eventually_atTop.2
    refine ⟨b, ?_⟩
    intro a ha
    exact ha.trans (Nat.le_add_left a N)
  exact _root_.GD.N0232.N0720.N1412.d015660
    (m := m) (n := n) hm hn seed hgap d checkpoint hcheckpoint
      (fun k ↦ hN (N + k) (Nat.le_add_right N k)) p hstrict hanchor




theorem d015670
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hstrict : ∀ j, _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed j).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ᶠ j in atTop,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value d) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbelow
  exact _root_.GD.N0232.N0720.N1412.d015669
    (m := m) (n := n) hm hn seed hgap d hbelow (seed N).value (hstrict N)
      (hN N le_rfl)







theorem d015671
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdominator : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) d) :
    ∀ N : ℕ, ∃ j, N ≤ j ∧
      ¬ _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value d := by
  intro N
  by_contra hnone
  apply hno
  exact _root_.GD.N0232.N0720.N1412.d015669
    (m := m) (n := n) hm hn seed hgap d
      (by
        filter_upwards [eventually_ge_atTop N] with j hj
        by_contra hnot
        exact hnone ⟨j, hj, hnot⟩)
      (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn) hdominator




theorem d015672
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hstrict : ∀ j, _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed j).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∀ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), ∀ N : ℕ,
      ∃ j, N ≤ j ∧ ¬ _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value d := by
  intro d N
  by_contra hnone
  apply hno
  apply _root_.GD.N0232.N0720.N1412.d015670
    hm hn seed hgap hstrict d
  filter_upwards [eventually_ge_atTop N] with j hj
  by_contra hnot
  exact hnone ⟨j, hj, hnot⟩




theorem d015673
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hvalue : Tendsto (fun j ↦ (seed j).value) atTop (nhds d))
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) d
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ¬ IsClosed (_root_.GD.N0232.N0720.N1412.d015652 (m := m) (n := n)) := by
  intro hclosed
  exact hno
    (_root_.GD.N0232.N0720.N1412.d015656
      hm hn seed d hvalue hgap hclosed hstrict)



open _root_.GD.N0230.N0698



def d015674 (k : ℕ) (x : _root_.GD.N0230.N0698.d001089) : ℝ :=
  let a : ℝ := 1 / ((k : ℝ) + 1)
  (x.1 - a) ^ 2 / ((x.1 - a) ^ 2 + x.1)

theorem d015675 (k : ℕ) (x : _root_.GD.N0230.N0698.d001089) :
    0 < (x.1 - 1 / ((k : ℝ) + 1)) ^ 2 + x.1 := by
  have hx : 0 ≤ x.1 := x.2.1
  have ha : 0 < 1 / ((k : ℝ) + 1) := by positivity
  by_cases hx0 : x.1 = 0
  · rw [hx0]
    simpa using sq_pos_of_pos ha
  · have hxpos : 0 < x.1 := lt_of_le_of_ne hx (Ne.symm hx0)
    nlinarith [sq_nonneg (x.1 - 1 / ((k : ℝ) + 1))]



theorem d015676 (k : ℕ) :
    Continuous (_root_.GD.N0232.N0720.N1412.d015674 k) := by
  have hval : Continuous (fun x : _root_.GD.N0230.N0698.d001089 ↦ x.1) :=
    continuous_subtype_val
  have hnum : Continuous
      (fun x : _root_.GD.N0230.N0698.d001089 ↦
        (x.1 - 1 / ((k : ℝ) + 1)) ^ 2) :=
    (hval.sub continuous_const).pow 2
  exact hnum.div (hnum.add hval) fun x ↦
    (_root_.GD.N0232.N0720.N1412.d015675 k x).ne'


theorem d015677 (k : ℕ) :
    _root_.GD.N0232.N0720.N1412.d015674 k _root_.GD.N0230.N0698.d001092 = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [_root_.GD.N0232.N0720.N1412.d015674, _root_.GD.N0230.N0698.d001092, zero_sub, add_zero]
  exact div_self (pow_ne_zero 2
    (neg_ne_zero.mpr (one_div_ne_zero hk.ne')))



theorem d015678
    (k : ℕ) (x : _root_.GD.N0230.N0698.d001089) (hx : 0 < x.1) :
    _root_.GD.N0232.N0720.N1412.d015674 k x < _root_.GD.N0232.N0720.N1412.d015674 k _root_.GD.N0230.N0698.d001092 := by
  rw [_root_.GD.N0232.N0720.N1412.d015677]
  unfold _root_.GD.N0232.N0720.N1412.d015674
  exact (div_lt_one (_root_.GD.N0232.N0720.N1412.d015675 k x)).2 (by linarith)



theorem d015679 (j : ℕ) :
    _root_.GD.N0230.N0630.d000786
      _root_.GD.N0232.N0720.N1412.d015674 (_root_.GD.N0230.N0698.d001091 j) := by
  intro e he
  have hj := he j
  have hnonneg : 0 ≤ _root_.GD.N0232.N0720.N1412.d015674 j e := by
    unfold _root_.GD.N0232.N0720.N1412.d015674
    exact div_nonneg (sq_nonneg _)
      (_root_.GD.N0232.N0720.N1412.d015675 j e).le
  have hzero : _root_.GD.N0232.N0720.N1412.d015674 j e = 0 := by
    apply le_antisymm
    · simpa [_root_.GD.N0232.N0720.N1412.d015674, _root_.GD.N0230.N0698.d001091] using hj
    · exact hnonneg
  have hnum :
      (e.1 - 1 / ((j : ℝ) + 1)) ^ 2 = 0 := by
    unfold _root_.GD.N0232.N0720.N1412.d015674 at hzero
    exact (div_eq_zero_iff.mp hzero).resolve_right
      (_root_.GD.N0232.N0720.N1412.d015675 j e).ne'
  apply Subtype.ext
  dsimp [_root_.GD.N0230.N0698.d001091]
  nlinarith



theorem d015680
    (j : ℕ) :
    _root_.GD.N0230.N0630.d000785
      _root_.GD.N0232.N0720.N1412.d015674
      (_root_.GD.N0230.N0698.d001091 j) _root_.GD.N0230.N0698.d001092 := by
  intro k
  apply _root_.GD.N0232.N0720.N1412.d015678
  dsimp [_root_.GD.N0230.N0698.d001091]
  positivity



theorem d015681 :
    ¬ _root_.GD.N0230.N0630.d000786
      _root_.GD.N0232.N0720.N1412.d015674 _root_.GD.N0230.N0698.d001092 := by
  intro hterminal
  have heq := hterminal (_root_.GD.N0230.N0698.d001091 0)
    (fun k ↦
      (_root_.GD.N0232.N0720.N1412.d015680
        0 k).le)
  have hne : _root_.GD.N0230.N0698.d001091 0 ≠ _root_.GD.N0230.N0698.d001092 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [_root_.GD.N0230.N0698.d001091, _root_.GD.N0230.N0698.d001092] at this
  exact hne heq






theorem d015682 :
    (∀ k, Continuous (_root_.GD.N0232.N0720.N1412.d015674 k)) ∧
      (∀ j, _root_.GD.N0230.N0630.d000786
        _root_.GD.N0232.N0720.N1412.d015674 (_root_.GD.N0230.N0698.d001091 j)) ∧
      (∀ j,
        _root_.GD.N0230.N0630.d000785
        _root_.GD.N0232.N0720.N1412.d015674
        (_root_.GD.N0230.N0698.d001091 j) _root_.GD.N0230.N0698.d001092) ∧
      Tendsto _root_.GD.N0230.N0698.d001091 atTop (nhds _root_.GD.N0230.N0698.d001092) ∧
      ¬ _root_.GD.N0230.N0630.d000786
        _root_.GD.N0232.N0720.N1412.d015674 _root_.GD.N0230.N0698.d001092 := by
  exact ⟨_root_.GD.N0232.N0720.N1412.d015676,
    _root_.GD.N0232.N0720.N1412.d015679,
    _root_.GD.N0232.N0720.N1412.d015680,
    _root_.GD.N0230.N0698.d001099,
    _root_.GD.N0232.N0720.N1412.d015681⟩

end

end N1412
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1412.d015647
#print axioms _root_.GD.N0232.N0720.N1412.d015648
#print axioms _root_.GD.N0232.N0720.N1412.d015651
#print axioms _root_.GD.N0232.N0720.N1412.d015658
#print axioms _root_.GD.N0232.N0720.N1412.d015659
#print axioms _root_.GD.N0232.N0720.N1412.d015662
#print axioms _root_.GD.N0232.N0720.N1412.d015663
#print axioms _root_.GD.N0232.N0720.N1412.d015664
#print axioms _root_.GD.N0232.N0720.N1412.d015665
#print axioms _root_.GD.N0232.N0720.N1412.d015666
#print axioms _root_.GD.N0232.N0720.N1412.d015667
#print axioms _root_.GD.N0232.N0720.N1412.d015670
#print axioms _root_.GD.N0232.N0720.N1412.d015671
#print axioms _root_.GD.N0232.N0720.N1412.d015672
#print axioms _root_.GD.N0232.N0720.N1412.d015673
#print axioms _root_.GD.N0232.N0720.N1412.d015682
