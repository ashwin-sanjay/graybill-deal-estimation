import GD.Module0068
import Mathlib.Analysis.Normed.Operator.Basic



























open Set

namespace GD
namespace N0230
namespace N0573

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630

variable {Theta H : Type*}


def d000832
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (charge : H →L[ℝ] ℝ) (eta : ℝ) : Set H :=
  {d | charge d ≤ -eta}


def d000833
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ) : Set H :=
  {d | _root_.GD.N0230.N0556.d000030 risk bar d} ∩ _root_.GD.N0230.N0573.d000832 charge eta





def d000834
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ)
    (charge : H →L[ℝ] ℝ) (eta : ℝ) : Prop :=
  ∀ {e d : H}, _root_.GD.N0230.N0556.d000028 risk e d →
    d ∈ _root_.GD.N0230.N0573.d000832 charge eta →
    e ∈ _root_.GD.N0230.N0573.d000832 charge eta

@[simp]
theorem d000835
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (charge : H →L[ℝ] ℝ) (eta : ℝ) (d : H) :
    d ∈ _root_.GD.N0230.N0573.d000832 charge eta ↔ charge d ≤ -eta :=
  Iff.rfl

@[simp]
theorem d000836
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ) (d : H) :
    d ∈ _root_.GD.N0230.N0573.d000833 risk bar charge eta ↔
      _root_.GD.N0230.N0556.d000030 risk bar d ∧ charge d ≤ -eta :=
  Iff.rfl


theorem d000837
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (charge : H →L[ℝ] ℝ) (eta : ℝ) :
    IsClosed (_root_.GD.N0230.N0573.d000832 charge eta) := by
  exact isClosed_le charge.continuous continuous_const


theorem d000838
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (charge : H →L[ℝ] ℝ) (eta : ℝ) :
    Convex ℝ (_root_.GD.N0230.N0573.d000832 charge eta) := by
  intro x hx y hy a b ha hb hab
  change charge (a • x + b • y) ≤ -eta
  rw [map_add, map_smul, map_smul]
  calc
    a * charge x + b * charge y ≤ a * (-eta) + b * (-eta) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = -eta := by rw [← add_mul, hab, one_mul]


theorem d000839
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0556.d000030 risk bar d}) :
    IsClosed (_root_.GD.N0230.N0573.d000833 risk bar charge eta) :=
  hclosed.inter (_root_.GD.N0230.N0573.d000837 charge eta)


theorem d000840
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d}) :
    Convex ℝ (_root_.GD.N0230.N0573.d000833 risk bar charge eta) :=
  hconvex.inter (_root_.GD.N0230.N0573.d000838 charge eta)


theorem d000841
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hbarCharge : charge bar ≤ -eta) :
    (_root_.GD.N0230.N0573.d000833 risk bar charge eta).Nonempty := by
  exact ⟨bar, _root_.GD.N0230.N0556.d000032 risk bar, hbarCharge⟩





theorem d000842
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ) (bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hcharge : _root_.GD.N0230.N0573.d000834 risk charge eta)
    {d e : H}
    (hd : d ∈ _root_.GD.N0230.N0573.d000833 risk bar charge eta)
    (hed : _root_.GD.N0230.N0556.d000028 risk e d) :
    e ∈ _root_.GD.N0230.N0573.d000833 risk bar charge eta := by
  exact ⟨_root_.GD.N0230.N0556.d000034 risk hd.1 hed, hcharge hed hd.2⟩





theorem d000843
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (risk : Theta → H → ℝ)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hmono : ∀ {e d : H}, _root_.GD.N0230.N0556.d000028 risk e d → charge e ≤ charge d) :
    _root_.GD.N0230.N0573.d000834 risk charge eta := by
  intro e d hed hd
  exact (hmono hed).trans hd

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]











theorem d000844
    (risk : Theta → H → ℝ)
    (theta0 : Theta) (target : H) (C : Set H)
    (hCne : C.Nonempty)
    (hCcomplete : IsComplete C)
    (hCconvex : Convex ℝ C)
    (hChereditary :
      ∀ {d e : H}, d ∈ C → _root_.GD.N0230.N0556.d000028 risk e d → e ∈ C)
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2) :
    ∃ star,
      star ∈ C ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, d ∈ C → risk theta0 star ≤ risk theta0 d) ∧
      (∀ d, d ∈ C →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  obtain ⟨star, hstarC, hstarMin⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hCne hCcomplete hCconvex target
  have hprojection :
      ∀ d, d ∈ C → inner ℝ (target - star) (d - star) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hCconvex hstarC).1 hstarMin
  have htax :
      ∀ d, d ∈ C →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star := by
    intro d hd
    have hgap :=
      _root_.GD.N0230.N0693.d000669
        target star d (hprojection d hd)
    simpa [_root_.GD.N0230.N0693.d000667, href] using hgap
  have hmin :
      ∀ d, d ∈ C → risk theta0 star ≤ risk theta0 d := by
    intro d hd
    have h := htax d hd
    nlinarith [sq_nonneg ‖d - star‖]
  have hterminal : _root_.GD.N0230.N0630.d000786 risk star := by
    intro e he
    have heC : e ∈ C := hChereditary hstarC he
    have htaxe := htax e heC
    have hrefle := he theta0
    have hzero : ‖e - star‖ = 0 := by
      nlinarith [norm_nonneg (e - star)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨star, hstarC, hterminal,
    _root_.GD.N0230.N0630.d000788 risk hterminal, hmin, htax⟩

variable [CompleteSpace H]










theorem d000845
    (risk : Theta → H → ℝ)
    (theta0 : Theta) (target base bar : H)
    (charge : H → ℝ) (eta : ℝ)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hchargeClosed : IsClosed {d : H | charge d ≤ -eta})
    (hchargeConvex : Convex ℝ {d : H | charge d ≤ -eta})
    (hbarCharge : charge bar ≤ -eta)
    (hchargeHereditary : ∀ {e d : H},
      _root_.GD.N0230.N0556.d000028 risk e d → charge d ≤ -eta → charge e ≤ -eta)
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      charge star ≤ -eta ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → charge d ≤ -eta →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  let C : Set H := {d : H | _root_.GD.N0230.N0556.d000030 risk bar d} ∩ {d : H | charge d ≤ -eta}
  have hCclosed : IsClosed C := hclosed.inter hchargeClosed
  have hCcomplete : IsComplete C := hCclosed.isComplete
  have hCconvex : Convex ℝ C := hconvex.inter hchargeConvex
  have hCne : C.Nonempty :=
    ⟨bar, _root_.GD.N0230.N0556.d000032 risk bar, hbarCharge⟩
  have hChereditary :
      ∀ {d e : H}, d ∈ C → _root_.GD.N0230.N0556.d000028 risk e d → e ∈ C := by
    intro d e hd hed
    exact ⟨_root_.GD.N0230.N0556.d000034 risk hd.1 hed,
      hchargeHereditary hed hd.2⟩
  obtain ⟨star, hstarC, hterminal, hadmissible, _hmin, htax⟩ :=
    _root_.GD.N0230.N0573.d000844
      risk theta0 target C hCne hCcomplete hCconvex hChereditary href
  exact ⟨star, hstarC.1,
    _root_.GD.N0230.N0630.d000790 risk hstarC.1 hbarStrict,
    hstarC.2, hterminal, hadmissible,
    fun d hd hdc ↦ htax d ⟨hd, hdc⟩⟩









theorem d000846
    (risk : Theta → H → ℝ)
    (theta0 : Theta) (target bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hbarCharge : charge bar ≤ -eta)
    (hcharge : _root_.GD.N0230.N0573.d000834 risk charge eta)
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      charge star ≤ -eta ∧
      eta ≤ |charge star| ∧
      eta ≤ ‖charge‖ * ‖star‖ ∧
      star ≠ 0 ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → charge d ≤ -eta →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  let C : Set H := _root_.GD.N0230.N0573.d000833 risk bar charge eta
  have hCclosed : IsClosed C :=
    _root_.GD.N0230.N0573.d000839 risk bar charge eta hclosed
  have hCcomplete : IsComplete C := hCclosed.isComplete
  have hCconvex : Convex ℝ C :=
    _root_.GD.N0230.N0573.d000840 risk bar charge eta hconvex
  have hCne : C.Nonempty :=
    _root_.GD.N0230.N0573.d000841 risk bar charge eta hbarCharge
  obtain ⟨star, hstarC, hterminal, hadmissible, _hmin, htax⟩ :=
    _root_.GD.N0230.N0573.d000844
      risk theta0 target C hCne hCcomplete hCconvex
      (fun hd hed ↦
        _root_.GD.N0230.N0573.d000842
          risk bar charge eta hcharge hd hed)
      href
  have hstarCharge : charge star ≤ -eta := hstarC.2
  have hchargeNonpos : charge star ≤ 0 := by linarith
  have habs : eta ≤ |charge star| := by
    rw [abs_of_nonpos hchargeNonpos]
    linarith
  have hop : |charge star| ≤ ‖charge‖ * ‖star‖ := by
    simpa [Real.norm_eq_abs] using charge.le_opNorm star
  have hnormCharge : eta ≤ ‖charge‖ * ‖star‖ := habs.trans hop
  have hstarNe : star ≠ 0 := by
    intro hzero
    subst star
    have hbad : 0 ≤ -eta := by simpa using hstarCharge
    linarith
  refine ⟨star, hstarC.1, hstarCharge, habs, hnormCharge, hstarNe,
    hterminal, hadmissible, ?_⟩
  intro d hd hdc
  exact htax d ⟨hd, hdc⟩





theorem d000847
    (risk : Theta → H → ℝ)
    (theta0 : Theta) (target base bar : H)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hbarCharge : charge bar ≤ -eta)
    (hcharge : _root_.GD.N0230.N0573.d000834 risk charge eta)
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      charge star ≤ -eta ∧
      eta ≤ |charge star| ∧
      eta ≤ ‖charge‖ * ‖star‖ ∧
      star ≠ 0 ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  obtain ⟨star, hstar, hstarCharge, habs, hnormCharge, hstarNe,
      hterminal, hadmissible, _htax⟩ :=
    _root_.GD.N0230.N0573.d000846
      risk theta0 target bar charge eta heta hclosed hconvex
      hbarCharge hcharge href
  exact ⟨star, hstar,
    _root_.GD.N0230.N0630.d000790 risk hstar hbarStrict,
    hstarCharge, habs, hnormCharge, hstarNe, hterminal, hadmissible⟩

end N0573
end N0230
end GD

#print axioms _root_.GD.N0230.N0573.d000837
#print axioms _root_.GD.N0230.N0573.d000838
#print axioms _root_.GD.N0230.N0573.d000844
#print axioms _root_.GD.N0230.N0573.d000845
#print axioms _root_.GD.N0230.N0573.d000846
#print axioms _root_.GD.N0230.N0573.d000847
