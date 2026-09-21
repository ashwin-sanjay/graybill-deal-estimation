import GD.Module0974
import GD.Module0963
import GD.Module0012





















open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1100

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0685
open _root_.GD.N0230.N0593
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1110
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

abbrev d015486 :=
  _root_.GD.N0232.N0719.N0946.d009229





theorem d015487
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1159.d014630 m n s) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s) := by
  let C : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := _root_.GD.N0232.N0720.N1159.d014630 m n s
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hpC : p ∈ C := (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  letI : Nonempty C := ⟨⟨p, hpC⟩⟩
  have hnormMin : ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) - p‖ =
      ⨅ w : C, ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) - (w :
        _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      have hrisk := (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.2 (w :
        _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) w.property
      rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hrisk
      simp only [zero_sub, norm_neg] at hrisk ⊢
      have hsq : ‖p‖ ^ 2 ≤ ‖(w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖ ^ 2 :=
        (ENNReal.ofReal_le_ofReal_iff
          (sq_nonneg ‖(w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖)).mp hrisk
      nlinarith [norm_nonneg p,
        norm_nonneg (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))]
    · have hbdd : BddBelow
          (Set.range (fun w : C ↦
            ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) -
              (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖)) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      exact ciInf_le hbdd ⟨p, hpC⟩
  refine ⟨hpC, ?_⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero
    (_root_.GD.N0232.N0720.N1159.d014632 m n s) hpC).1 hnormMin





theorem d015488
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) :
    ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      (∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d) ∧
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
        atTop (nhds d) := by
  let C : ℕ → Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
    fun j ↦ _root_.GD.N0232.N0720.N1159.d014630 m n (seed j).value
  let p : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value
  have hanti : Antitone C := by
    intro i j hij d hd
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hd
      (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc hij)
  have hp : ∀ j, _root_.GD.N0230.N0685.d000511 (C j) 0 (p j) := by
    intro j
    exact _root_.GD.N0232.N0720.N1100.d015487 m n (seed j).value
  have hbound : ∀ j, ‖p j‖ ^ 2 ≤ ‖(seed 0).value‖ ^ 2 := by
    intro j
    have hpBelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed 0).value (p j) :=
      _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
        (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc (Nat.zero_le j))
    have href := hpBelow _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
    simp only [zero_sub, norm_neg] at href
    exact (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖(seed 0).value‖)).mp href
  have hpCauchy : CauchySeq p :=
    _root_.GD.N0232.N0720.N1110.d015455
      C p hanti hp (‖(seed 0).value‖ ^ 2) hbound
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hpCauchy
  refine ⟨d, ?_, hd⟩
  intro i
  apply (_root_.GD.N0232.N0720.N1159.d014631 m n (seed i).value).mem_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with j hij
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
    (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc hij)




theorem d015489
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (hlim : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
      atTop (nhds d)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d := by
  intro e hed
  have heBelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value e := by
    intro i
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hed (hbelow i)
  have htax : ∀ i,
      ‖e - _root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value‖ ^ 2 ≤
        ‖e‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value‖ ^ 2 := by
    intro i
    exact _root_.GD.N0232.N0720.N1159.d014648
      m n (seed i).value e (heBelow i)
  have hleft : Tendsto
      (fun i ↦ ‖e - _root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value‖ ^ 2)
      atTop (nhds (‖e - d‖ ^ 2)) :=
    ((continuous_const.sub continuous_id).norm.pow 2).tendsto d |>.comp hlim
  have hnormSq : Tendsto
      (fun x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖x‖ ^ 2)
      (nhds d) (nhds (‖d‖ ^ 2)) :=
    (continuous_norm.pow 2).tendsto d
  have hright : Tendsto
      (fun i ↦ ‖e‖ ^ 2 -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value‖ ^ 2)
      atTop (nhds (‖e‖ ^ 2 - ‖d‖ ^ 2)) :=
    (tendsto_const_nhds.sub hnormSq).comp hlim
  have hineq : ‖e - d‖ ^ 2 ≤ ‖e‖ ^ 2 - ‖d‖ ^ 2 :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall htax)
  have href := hed _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖d‖)).mp href
  have hzero : ‖e - d‖ = 0 := by
    nlinarith [sq_nonneg ‖e - d‖, norm_nonneg (e - d)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)







theorem d015490
    {Alpha : Type*} [MeasurableSpace Alpha]
    {mu : Measure Alpha} [IsFiniteMeasure mu]
    {f : ℕ → Alpha → ℝ} {g : Alpha → ℝ} {psi : ℝ → ℝ}
    (hf : ∀ j, AEStronglyMeasurable (f j) mu)
    (hpsi : Continuous psi)
    (hfg : TendstoInMeasure mu f atTop g) :
    TendstoInMeasure mu (fun j x ↦ psi (f j x)) atTop
      (fun x ↦ psi (g x)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff
    (fun j ↦ hpsi.comp_aestronglyMeasurable (hf j))]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hf).1 hfg ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with x hx
  exact hpsi.continuousAt.tendsto.comp hx




theorem d015491
    (g : _root_.GD.N0232.N0720.N1100.d015486)
    (pseq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hpseq : ∀ j, _root_.GD.N0232.N0720.N1159.d014637 m n (pseq j))
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hlim : Tendsto pseq atTop (nhds p))
    (htransport : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j))
      atTop (nhds q)) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = q := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let mu := _root_.GD.N0232.N0720.N1080.d014172 m n
  let nu := mu.map (_root_.GD.N0232.N0720.N1484.d015094 m n g)
  have hclassP : TendstoInMeasure mu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (pseq j)) atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
    have hclass := tendstoInMeasure_of_tendsto_Lp hlim
    exact TendstoInMeasure.congr
      (fun j ↦ (_root_.GD.N0232.N0720.N1214.d014267 m n (pseq j)).symm)
      (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm hclass
  have hnuAc : nu ≪ mu := by
    rw [show nu = _root_.GD.N0232.N0720.N1080.d014171 m n
      (_root_.GD.N0232.N0720.N1484.d015099 g) by
        exact _root_.GD.N0232.N0720.N1484.d015101
          m n g]
    exact _root_.GD.N0232.N0720.N1080.d014173 m n _
  have hclassNu : TendstoInMeasure nu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (pseq j)) atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n p) :=
    _root_.GD.N0230.N0593.d000108 hnuAc
      (fun j ↦ (_root_.GD.N0232.N0720.N1214.d014266 m n (pseq j)).aestronglyMeasurable)
      hclassP
  have hpullback : TendstoInMeasure mu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (pseq j) ∘
        _root_.GD.N0232.N0720.N1484.d015094 m n g)
      atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n p ∘
        _root_.GD.N0232.N0720.N1484.d015094 m n g) := by
    exact _root_.GD.N0230.N0593.d000111
      (_root_.GD.N0232.N0720.N1484.d015095 m n g)
      (fun j ↦
        (_root_.GD.N0232.N0720.N1214.d014266 m n (pseq j)).aestronglyMeasurable)
      hclassNu
  have hrawTransport : TendstoInMeasure mu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (pseq j))) atTop
      (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) := by
    change TendstoInMeasure mu
      (fun j x ↦ g • _root_.GD.N0232.N0720.N1214.d014265 m n (pseq j)
        (_root_.GD.N0232.N0720.N1484.d015094 m n g x))
      atTop
      (fun x ↦ g • _root_.GD.N0232.N0720.N1214.d014265 m n p
        (_root_.GD.N0232.N0720.N1484.d015094 m n g x))
    let psi : ℝ → ℝ := fun x ↦ g • x
    have hpsi : Continuous psi := by
      change Continuous (fun x : ℝ ↦ g.shift + g.d009239 * x)
      exact continuous_const.add (continuous_const.mul continuous_id)
    have hpost := _root_.GD.N0232.N0720.N1100.d015490
      (fun j ↦ ((_root_.GD.N0232.N0720.N1214.d014266 m n (pseq j)).comp
        (_root_.GD.N0232.N0720.N1484.d015095
          m n g)).aestronglyMeasurable)
      hpsi hpullback
    simpa only [psi, Function.comp_apply] using hpost
  have htransportRawLimit : TendstoInMeasure mu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n
        (_root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j))) atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp)) := by
    exact TendstoInMeasure.congr
      (fun j ↦ (_root_.GD.N0232.N0720.N1482.d015160
        (m := m) (n := n) g (pseq j) (hpseq j)).symm)
      (_root_.GD.N0232.N0720.N1482.d015160
        (m := m) (n := n) g p hp).symm hrawTransport
  have htransportClass : TendstoInMeasure mu
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n
        (_root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j))) atTop
      (_root_.GD.N0232.N0720.N1214.d014265 m n q) := by
    have hclass := tendstoInMeasure_of_tendsto_Lp htransport
    exact TendstoInMeasure.congr
      (fun j ↦ (_root_.GD.N0232.N0720.N1214.d014267 m n
        (_root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j))).symm)
      (_root_.GD.N0232.N0720.N1214.d014267 m n q).symm hclass
  have hae : _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp) =ᵐ[mu]
      _root_.GD.N0232.N0720.N1214.d014265 m n q :=
    tendstoInMeasure_ae_unique htransportRawLimit htransportClass
  calc
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hp =
        MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp))
          (_root_.GD.N0232.N0720.N1214.d014268 m n
            (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp)) :=
      (_root_.GD.N0232.N0720.N1214.d014269 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp)).symm
    _ = MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n q)
          (_root_.GD.N0232.N0720.N1214.d014268 m n q) :=
      MemLp.toLp_congr _ _ hae
    _ = q := _root_.GD.N0232.N0720.N1214.d014269 m n q





theorem d015492
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0720.N1100.d015486)
    (hg : g = _root_.GD.N0232.N0720.N1482.d015130 ∨ g = _root_.GD.N0232.N0720.N1482.d015131)
    (hmaster : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖(_root_.GD.N0232.N0720.N1159.d014645 m n (seed j) g
          (_root_.GD.N0232.N0720.N1159.d014646 m n (seed j))).1 -
        _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖)
      atTop (nhds 0) := by
  have hupper : ∀ j,
      ‖(_root_.GD.N0232.N0720.N1159.d014645 m n (seed j) g
          (_root_.GD.N0232.N0720.N1159.d014646 m n (seed j))).1 -
        _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j) := by
    intro j
    refine (_root_.GD.N0232.N0720.N1159.d014649 m n (seed j) g).trans ?_
    rcases hg with rfl | rfl
    · exact le_add_of_nonneg_right
        (_root_.GD.N0232.N0720.N1159.d014650 m n (seed j)
          _root_.GD.N0232.N0720.N1482.d015131)
    · exact le_add_of_nonneg_left
        (_root_.GD.N0232.N0720.N1159.d014650 m n (seed j) _root_.GD.N0232.N0720.N1482.d015130)
  have hsquare : Tendsto
      (fun j ↦ ‖(_root_.GD.N0232.N0720.N1159.d014645 m n (seed j) g
          (_root_.GD.N0232.N0720.N1159.d014646 m n (seed j))).1 -
        _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ sq_nonneg ‖(_root_.GD.N0232.N0720.N1159.d014645 m n (seed j) g
        (_root_.GD.N0232.N0720.N1159.d014646 m n (seed j))).1 -
          _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖)
      hupper hmaster
  have hsqrt := hsquare.sqrt
  simpa [Real.sqrt_sq_eq_abs] using hsqrt



theorem d015493
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hmaster : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j))
      atTop (nhds 0))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨d, hbelow, hlim⟩ :=
    _root_.GD.N0232.N0720.N1100.d015488 m n seed hdesc
  let pseq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value
  have hpseq : ∀ j, _root_.GD.N0232.N0720.N1159.d014637 m n (pseq j) := by
    intro j
    exact _root_.GD.N0232.N0720.N1159.d014644 m n (seed j) (pseq j)
      (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
  have hdFinite : _root_.GD.N0232.N0720.N1159.d014637 m n d :=
    _root_.GD.N0232.N0720.N1159.d014644 m n (seed 0) d (hbelow 0)
  have fixedGenerator (g : _root_.GD.N0232.N0720.N1100.d015486)
      (hg : g = _root_.GD.N0232.N0720.N1482.d015130 ∨ g = _root_.GD.N0232.N0720.N1482.d015131) :
      _root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite = d := by
    have hdisp := _root_.GD.N0232.N0720.N1100.d015492
      m n seed g hg hmaster
    have hdisp' : Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j) - pseq j‖)
        atTop (nhds 0) := by
      simpa only [pseq, _root_.GD.N0232.N0720.N1159.d014645, _root_.GD.N0232.N0720.N1159.d014646] using hdisp
    have hdiff : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j) - pseq j)
        atTop (nhds 0) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      simpa only [sub_zero] using hdisp'
    have hpseqLim : Tendsto pseq atTop (nhds d) := by
      simpa only [pseq] using hlim
    have htransport : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1159.d014642 m n g (pseq j) (hpseq j))
        atTop (nhds d) := by
      have hadd := hdiff.add hpseqLim
      simpa only [zero_add, sub_add_cancel] using hadd
    exact _root_.GD.N0232.N0720.N1100.d015491
      m n g pseq hpseq d d hdFinite hlim htransport
  have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 d hdFinite = d :=
    fixedGenerator _root_.GD.N0232.N0720.N1482.d015130 (Or.inl rfl)
  have hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 d hdFinite = d :=
    fixedGenerator _root_.GD.N0232.N0720.N1482.d015131 (Or.inr rfl)
  have hall : ∀ g : _root_.GD.N0232.N0720.N1100.d015486,
      _root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite = d :=
    _root_.GD.N0232.N0720.N1482.d015167 (m := m) (n := n)
      d hdFinite hTwo hThree
  have hrep : _root_.GD.N0232.N0720.N1159.d014652 m n d :=
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn d hdFinite).1 hall
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d :=
    _root_.GD.N0232.N0720.N1100.d015489
      m n seed d hbelow hlim
  apply (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2
  refine ⟨d, hrep, ?_, hterminal⟩
  intro theta
  exact lt_of_le_of_lt (hbelow 0 theta) (hstrict theta)




theorem d015494
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j))
          atTop (nhds 0) ∧
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).1 hendpoint
    refine ⟨fun _ ↦ s, ?_, ?_, hstrict⟩
    · intro j
      exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    · simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · rintro ⟨seed, hdesc, hmaster, hstrict⟩
    exact _root_.GD.N0232.N0720.N1100.d015493
      m n hm hn seed hdesc hmaster hstrict





theorem d015495
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j))
          atTop (nhds 0) ∧
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1100.d015494
    m n hm hn]

end
end N1100
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1100.d015487
#print axioms _root_.GD.N0232.N0720.N1100.d015488
#print axioms _root_.GD.N0232.N0720.N1100.d015489
#print axioms _root_.GD.N0232.N0720.N1100.d015491
#print axioms _root_.GD.N0232.N0720.N1100.d015492
#print axioms _root_.GD.N0232.N0720.N1100.d015493
#print axioms _root_.GD.N0232.N0720.N1100.d015494
#print axioms _root_.GD.N0232.N0720.N1100.d015495
