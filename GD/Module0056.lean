import GD.Module0014
import GD.Module0055



























open Set

namespace GD
namespace N0230
namespace N0571

open _root_.GD.N0230.N0608

variable {Theta H : Type*}


def d000684
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal) (d : H) : Prop :=
  ∀ theta, risk theta d ≤ cap theta



theorem d000685
    (risk : Theta → H → ENNReal) (bar d : H) :
    _root_.GD.N0230.N0571.d000684 risk (fun theta ↦ risk theta bar) d ↔
      _root_.GD.N0230.N0608.d000673 risk bar d := by
  rfl

theorem d000686
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    {d e : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d)
    (hed : _root_.GD.N0230.N0608.d000672 risk e d) :
    _root_.GD.N0230.N0571.d000684 risk cap e := by
  intro theta
  exact (hed theta).trans (hd theta)

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]








theorem d000687
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    ∃ p,
      _root_.GD.N0230.N0571.d000684 risk cap p ∧
      ‖target - p‖ =
        ⨅ w : {d : H // _root_.GD.N0230.N0571.d000684 risk cap d},
          ‖target - (w : H)‖ ∧
      _root_.GD.N0230.N0608.d000674 risk p ∧
      (∀ d, _root_.GD.N0230.N0571.d000684 risk cap d →
        risk theta0 p ≤ risk theta0 d) ∧
      (∀ d, _root_.GD.N0230.N0571.d000684 risk cap d →
        ‖d - p‖ ^ 2 ≤
          ‖target - d‖ ^ 2 - ‖target - p‖ ^ 2) := by
  let C : Set H := {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}
  obtain ⟨p, hpC, hpMin⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hnonempty hclosed.isComplete hconvex target
  letI : Nonempty C := ⟨⟨p, hpC⟩⟩

  have hdist_le : ∀ d, d ∈ C → ‖target - p‖ ≤ ‖target - d‖ := by
    intro d hd
    rw [hpMin]
    have hbdd :
        BddBelow (Set.range (fun w : C ↦ ‖target - (w : H)‖)) := by
      refine ⟨(0 : ℝ), ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg (target - (w : H))
    exact ciInf_le hbdd ⟨d, hd⟩

  have hriskMin :
      ∀ d, _root_.GD.N0230.N0571.d000684 risk cap d → risk theta0 p ≤ risk theta0 d := by
    intro d hd
    rw [href p, href d]
    have hsq : ‖target - p‖ ^ 2 ≤ ‖target - d‖ ^ 2 := by
      nlinarith [hdist_le d hd, norm_nonneg (target - p),
        norm_nonneg (target - d)]
    exact ENNReal.ofReal_le_ofReal hsq

  have hprojection :
      ∀ d, d ∈ C → inner ℝ (target - p) (d - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hpC).1 hpMin

  have htax :
      ∀ d, _root_.GD.N0230.N0571.d000684 risk cap d →
        ‖d - p‖ ^ 2 ≤
          ‖target - d‖ ^ 2 - ‖target - p‖ ^ 2 := by
    intro d hd
    have hgap :=
      _root_.GD.N0230.N0693.d000669
        target p d (hprojection d hd)
    simpa [_root_.GD.N0230.N0693.d000667] using hgap

  have hunbeatable : _root_.GD.N0230.N0608.d000674 risk p := by
    intro e he
    have heC : _root_.GD.N0230.N0571.d000684 risk cap e :=
      _root_.GD.N0230.N0571.d000686 risk cap hpC he
    have hriskWeak := he theta0
    rw [href e, href p] at hriskWeak
    have hsqWeak : ‖target - e‖ ^ 2 ≤ ‖target - p‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (sq_nonneg ‖target - p‖)).mp hriskWeak
    have htaxe := htax e heC
    have hnormZero : ‖e - p‖ = 0 := by
      nlinarith [norm_nonneg (e - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)

  exact ⟨p, hpC, hpMin, hunbeatable, hriskMin, htax⟩


noncomputable def d000688
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2)) : H :=
  Classical.choose
    (_root_.GD.N0230.N0571.d000687
      risk cap theta0 target hnonempty hclosed hconvex href)


theorem d000689
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    let p :=
      _root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href
    _root_.GD.N0230.N0571.d000684 risk cap p ∧
      ‖target - p‖ =
        ⨅ w : {d : H // _root_.GD.N0230.N0571.d000684 risk cap d},
          ‖target - (w : H)‖ ∧
      _root_.GD.N0230.N0608.d000674 risk p ∧
      (∀ d, _root_.GD.N0230.N0571.d000684 risk cap d →
        risk theta0 p ≤ risk theta0 d) ∧
      (∀ d, _root_.GD.N0230.N0571.d000684 risk cap d →
        ‖d - p‖ ^ 2 ≤
          ‖target - d‖ ^ 2 - ‖target - p‖ ^ 2) :=
  Classical.choose_spec
    (_root_.GD.N0230.N0571.d000687
      risk cap theta0 target hnonempty hclosed hconvex href)

theorem d000690
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    _root_.GD.N0230.N0571.d000684 risk cap
      (_root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href) :=
  (_root_.GD.N0230.N0571.d000689
    risk cap theta0 target hnonempty hclosed hconvex href).1

theorem d000691
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    _root_.GD.N0230.N0608.d000674 risk
      (_root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href) :=
  (_root_.GD.N0230.N0571.d000689
    risk cap theta0 target hnonempty hclosed hconvex href).2.2.1

theorem d000692
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    {d : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) :
    risk theta0
        (_root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href) ≤
      risk theta0 d :=
  (_root_.GD.N0230.N0571.d000689
    risk cap theta0 target hnonempty hclosed hconvex href).2.2.2.1 d hd


theorem d000693
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    {d : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) :
    ‖target - _root_.GD.N0230.N0571.d000688
        risk cap theta0 target hnonempty hclosed hconvex href‖ ≤
      ‖target - d‖ := by
  have hrisk := _root_.GD.N0230.N0571.d000692
    risk cap theta0 target hnonempty hclosed hconvex href hd
  rw [href, href] at hrisk
  have hsq :
      ‖target - _root_.GD.N0230.N0571.d000688
          risk cap theta0 target hnonempty hclosed hconvex href‖ ^ 2 ≤
        ‖target - d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖target - d‖)).mp hrisk
  nlinarith [norm_nonneg
    (target - _root_.GD.N0230.N0571.d000688
      risk cap theta0 target hnonempty hclosed hconvex href),
    norm_nonneg (target - d)]







theorem d000694
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    {d : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) :
    let p :=
      _root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href
    inner ℝ (target - p) (d - p) ≤ 0 := by
  dsimp only
  let p := _root_.GD.N0230.N0571.d000688 risk cap theta0 target
    hnonempty hclosed hconvex href
  have hpC : _root_.GD.N0230.N0571.d000684 risk cap p :=
    _root_.GD.N0230.N0571.d000690 risk cap theta0 target
      hnonempty hclosed hconvex href
  have hpMin :
      ‖target - p‖ =
        ⨅ w : {e : H // _root_.GD.N0230.N0571.d000684 risk cap e},
          ‖target - (w : H)‖ :=
    (_root_.GD.N0230.N0571.d000689 risk cap theta0 target
      hnonempty hclosed hconvex href).2.1
  exact
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hpC).1 hpMin d hd


theorem d000695
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    {d : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) :
    let p :=
      _root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href
    ‖d - p‖ ^ 2 ≤
      ‖target - d‖ ^ 2 - ‖target - p‖ ^ 2 :=
  (_root_.GD.N0230.N0571.d000689
    risk cap theta0 target hnonempty hclosed hconvex href).2.2.2.2 d hd


theorem d000696
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    {d : H} (hd : _root_.GD.N0230.N0571.d000684 risk cap d) :
    let p :=
      _root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href
    risk theta0 p + ENNReal.ofReal (‖d - p‖ ^ 2) ≤ risk theta0 d := by
  dsimp only
  let p := _root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href
  have htax := _root_.GD.N0230.N0571.d000695
    risk cap theta0 target hnonempty hclosed hconvex href hd
  have hadd :
      ‖target - p‖ ^ 2 + ‖d - p‖ ^ 2 ≤ ‖target - d‖ ^ 2 := by
    nlinarith
  rw [href p, href d]
  rw [← ENNReal.ofReal_add
    (sq_nonneg ‖target - p‖) (sq_nonneg ‖d - p‖)]
  exact ENNReal.ofReal_le_ofReal hadd


theorem d000697
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (theta0 : Theta) (target base : H)
    (hnonempty : {d : H | _root_.GD.N0230.N0571.d000684 risk cap d}.Nonempty)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d})
    (href :
      ∀ d, risk theta0 d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hcap : ∀ theta, cap theta < risk theta base) :
    _root_.GD.N0230.N0608.d000675 risk
      (_root_.GD.N0230.N0571.d000688 risk cap theta0 target hnonempty hclosed hconvex href)
      base := by
  intro theta
  exact lt_of_le_of_lt
    (_root_.GD.N0230.N0571.d000690
      risk cap theta0 target hnonempty hclosed hconvex href theta)
    (hcap theta)

omit [CompleteSpace H] in




theorem d000698
    (risk : Theta → H → ENNReal) (cap : Theta → ENNReal)
    (hclosed : ∀ theta, IsClosed {d : H | risk theta d ≤ cap theta})
    (hconvex : ∀ theta, Convex ℝ {d : H | risk theta d ≤ cap theta}) :
    IsClosed {d : H | _root_.GD.N0230.N0571.d000684 risk cap d} ∧
      Convex ℝ {d : H | _root_.GD.N0230.N0571.d000684 risk cap d} := by
  constructor
  · simpa only [_root_.GD.N0230.N0571.d000684, Set.setOf_forall] using isClosed_iInter hclosed
  · simpa only [_root_.GD.N0230.N0571.d000684, Set.setOf_forall] using convex_iInter hconvex

section ConcreteQuadratic

open _root_.GD.N0230.N0602
open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]



theorem d000699
    (mu0 : MeasureTheory.Measure Omega)
    (mu : Theta → MeasureTheory.Measure Omega)
    (statTarget : Theta → ℝ) (cap : Theta → ENNReal)
    (hmu : ∀ theta, mu theta ≪ mu0) :
    IsClosed
        {d : _root_.GD.N0230.N0602.d000116 mu0 |
          _root_.GD.N0230.N0571.d000684
            (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
              (mu theta) (statTarget theta) e)
            cap d} ∧
      Convex ℝ
        {d : _root_.GD.N0230.N0602.d000116 mu0 |
          _root_.GD.N0230.N0571.d000684
            (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
              (mu theta) (statTarget theta) e)
            cap d} := by
  constructor
  · simpa only [_root_.GD.N0230.N0571.d000684, _root_.GD.N0230.N0602.d000118] using
      _root_.GD.N0230.N0602.d000122 mu0 mu statTarget cap hmu
  · simpa only [_root_.GD.N0230.N0571.d000684, _root_.GD.N0230.N0602.d000118] using
      _root_.GD.N0230.N0602.d000123 mu0 mu statTarget cap hmu






theorem d000700
    (mu0 : MeasureTheory.Measure Omega)
    (mu : Theta → MeasureTheory.Measure Omega)
    (statTarget : Theta → ℝ) (cap : Theta → ENNReal)
    (hmu : ∀ theta, mu theta ≪ mu0)
    (theta0 : Theta)
    (hmu0 : mu theta0 = mu0)
    (htarget0 : statTarget theta0 = 0)
    (hnonempty :
      {d : _root_.GD.N0230.N0602.d000116 mu0 |
        _root_.GD.N0230.N0571.d000684
          (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
            (mu theta) (statTarget theta) e)
          cap d}.Nonempty) :
    ∃ p : _root_.GD.N0230.N0602.d000116 mu0,
      _root_.GD.N0230.N0571.d000684
          (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
            (mu theta) (statTarget theta) e)
          cap p ∧
      ‖(0 : _root_.GD.N0230.N0602.d000116 mu0) - p‖ =
        ⨅ w :
            {d : _root_.GD.N0230.N0602.d000116 mu0 //
              _root_.GD.N0230.N0571.d000684
                (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
                  (mu theta) (statTarget theta) e)
                cap d},
          ‖(0 : _root_.GD.N0230.N0602.d000116 mu0) - (w : _root_.GD.N0230.N0602.d000116 mu0)‖ ∧
      _root_.GD.N0230.N0608.d000674
          (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
            (mu theta) (statTarget theta) e)
          p ∧
      (∀ d,
        _root_.GD.N0230.N0571.d000684
            (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
              (mu theta) (statTarget theta) e)
            cap d →
        _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) (mu theta0) (statTarget theta0) p ≤
          _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) (mu theta0) (statTarget theta0) d) ∧
      (∀ d,
        _root_.GD.N0230.N0571.d000684
            (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
              (mu theta) (statTarget theta) e)
            cap d →
        ‖d - p‖ ^ 2 ≤ ‖(0 : _root_.GD.N0230.N0602.d000116 mu0) - d‖ ^ 2 -
          ‖(0 : _root_.GD.N0230.N0602.d000116 mu0) - p‖ ^ 2) := by
  have hgeometry :=
    _root_.GD.N0230.N0571.d000699 mu0 mu statTarget cap hmu
  apply _root_.GD.N0230.N0571.d000687
    (fun theta e ↦ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0)
      (mu theta) (statTarget theta) e)
    cap theta0 (0 : _root_.GD.N0230.N0602.d000116 mu0) hnonempty hgeometry.1 hgeometry.2
  intro d
  rw [hmu0, htarget0]
  exact _root_.GD.N0230.N0602.d000124 mu0 d

end ConcreteQuadratic

end N0571
end N0230
end GD

#print axioms _root_.GD.N0230.N0571.d000687
#print axioms _root_.GD.N0230.N0571.d000691
#print axioms _root_.GD.N0230.N0571.d000694
#print axioms _root_.GD.N0230.N0571.d000695
#print axioms _root_.GD.N0230.N0571.d000697
#print axioms _root_.GD.N0230.N0571.d000700
