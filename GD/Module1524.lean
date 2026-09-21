import GD.Module1523













noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Finset
open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1510

open _root_.GD.N0106.N0428.N0765.N1509 _root_.GD.N0106.N0428.N0765.N1634 _root_.GD.N0106.N0428.N0765.N1616
  _root_.GD.N0106.N0428.N0765.N1619 _root_.GD.N0106.N0428.N0765.N1562 _root_.GD.N0106.N0428.N0765.N1569 _root_.GD.N0106.N0428.N0765.N1568


def d023684 (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) (ε τ₀ : ℝ) : ℝ :=
  max ((S₁.lo : ℝ) / (1 + ε) / (((S₀.hi : ℝ) + τ₀) / (1 - ε))) 0


def d023685 (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) (ε τ₁ : ℝ) : ℝ :=
  min ((((S₁.hi : ℝ) + τ₁) / (1 - ε)) / ((S₀.lo : ℝ) / (1 + ε))) 1

def d023686 (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) (ε τ₀ τ₁ : ℝ) : Set ℝ :=
  Set.Icc (_root_.GD.N0106.N0428.N0765.N1510.d023684 S₀ S₁ ε τ₀) (_root_.GD.N0106.N0428.N0765.N1510.d023685 S₀ S₁ ε τ₁)



theorem d023687 (h B : ℚ) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) (ε τ₀ : ℝ)
    (hS₁ : 0 ≤ S₁.lo) :
    _root_.GD.N0106.N0428.N0765.N1510.d023684 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₀ =
      _root_.GD.N0106.N0428.N0765.N1510.d023684 S₀ S₁ ε τ₀ := by
  simp only [_root_.GD.N0106.N0428.N0765.N1510.d023684, _root_.GD.N0106.N0428.N0765.N1509.d023675, _root_.GD.N0106.N0428.N0765.N1509.d023676, max_eq_right hS₁]



theorem d023688 (h B : ℚ) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) {ε τ₁ : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hS₀ : 0 < S₀.lo)
    (hnum : 0 ≤ (S₁.hi : ℝ) + τ₁) :
    _root_.GD.N0106.N0428.N0765.N1510.d023685 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₁ ≤
      _root_.GD.N0106.N0428.N0765.N1510.d023685 S₀ S₁ ε τ₁ := by
  have hplus : 0 < 1 + ε := by linarith
  have hminus : 0 < 1 - ε := sub_pos.mpr hε₁
  have hS₀R : (0 : ℝ) < (S₀.lo : ℝ) := by exact_mod_cast hS₀
  have hden : (S₀.lo : ℝ) / (1 + ε) ≤
      ((_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀).lo : ℝ) / (1 + ε) := by
    apply div_le_div_of_nonneg_right _ hplus.le
    change (S₀.lo : ℝ) ≤ ((max (_root_.GD.N0106.N0428.N0765.N1509.d023672 h B) S₀.lo : ℚ) : ℝ)
    rw [Rat.cast_max]
    exact le_max_right _ _
  apply min_le_min _ le_rfl
  exact div_le_div_of_nonneg_left (div_nonneg hnum hminus.le)
    (div_pos hS₀R hplus) hden



theorem d023689 (h B : ℚ) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) {ε τ₀ τ₁ : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hS₀ : 0 < S₀.lo) (hS₁ : 0 ≤ S₁.lo)
    (hnum : 0 ≤ (S₁.hi : ℝ) + τ₁) :
    _root_.GD.N0106.N0428.N0765.N1510.d023686 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₀ τ₁ ⊆
      _root_.GD.N0106.N0428.N0765.N1510.d023686 S₀ S₁ ε τ₀ τ₁ := by
  intro x hx
  refine ⟨?_, hx.2.trans (_root_.GD.N0106.N0428.N0765.N1510.d023688 h B S₀ S₁ hε₀ hε₁ hS₀ hnum)⟩
  rw [← _root_.GD.N0106.N0428.N0765.N1510.d023687 h B S₀ S₁ ε τ₀ hS₁]
  exact hx.1



theorem d023690 (h B : ℚ) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809) {ε τ₀ τ₁ : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hS₀ : 0 < S₀.lo) (hS₁ : 0 ≤ S₁.lo)
    (hnum : 0 ≤ (S₁.hi : ℝ) + τ₁) :
    _root_.GD.N0106.N0428.N0765.N1510.d023685 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₁ -
        _root_.GD.N0106.N0428.N0765.N1510.d023684 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₀ ≤
      _root_.GD.N0106.N0428.N0765.N1510.d023685 S₀ S₁ ε τ₁ - _root_.GD.N0106.N0428.N0765.N1510.d023684 S₀ S₁ ε τ₀ := by
  rw [_root_.GD.N0106.N0428.N0765.N1510.d023687 h B S₀ S₁ ε τ₀ hS₁]
  exact sub_le_sub_right (_root_.GD.N0106.N0428.N0765.N1510.d023688 h B S₀ S₁ hε₀ hε₁ hS₀ hnum) _



theorem d023691 {eta v w h : ℝ}
    (heta : 0 < eta) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (c₀ : ℝ) (N : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1619.d021057 eta v w c₀ h N := by
  have hd13 : 0 < 1 - Real.exp (-((13 / 2 : ℝ) * h)) :=
    sub_pos.mpr (_root_.GD.N0106.N0428.N0765.N1568.d005515 (by norm_num) hh)
  have hd11 : 0 < 1 - Real.exp (-((11 / 2 : ℝ) * h)) :=
    sub_pos.mpr (_root_.GD.N0106.N0428.N0765.N1568.d005515 (by norm_num) hh)
  have hvp : 0 ≤ v ^ (-((21 : ℝ) / 2)) := Real.rpow_nonneg hv.le _
  have hewp : 0 ≤ (eta * w) ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_nonneg (mul_pos heta hw).le _
  unfold _root_.GD.N0106.N0428.N0765.N1619.d021057 _root_.GD.N0106.N0428.N0765.N1568.d005509 _root_.GD.N0106.N0428.N0765.N1568.d005510
  exact add_nonneg (div_nonneg (by positivity) hd13.le)
    (div_nonneg (by positivity) hd11.le)




theorem d023692
    {eta a b c₀ d : ℝ} {N j : ℕ}
    (heta : 0 < eta) (hd : 0 < d) (hdpi : d < Real.pi / 2)
    (h B : ℚ) (hh : 0 < h) (hB : 1 ≤ B)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ) < 1)
    (hPB : _root_.GD.N0106.N0428.N0765.N1634.d023651 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 0 ≤ (B : ℝ))
    (hj : j < N) (hcenter : c₀ + (j : ℝ) * (h : ℝ) = 0)
    (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809)
    (hS₀ : S₀.d006810 (∑ i ∈ range N,
      (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * (h : ℝ))))
    (hS₁ : S₁.d006810 (∑ i ∈ range N,
      (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * (h : ℝ))))
    (hOld₀ : 0 < S₀.lo) (hOld₁ : 0 ≤ S₁.lo) :
    let ε := _root_.GD.N0106.N0428.N0765.N1562.d021061 d (h : ℝ)
    let τ₀ := _root_.GD.N0106.N0428.N0765.N1619.d021056 eta (Real.exp b) 1 c₀ (h : ℝ) N
    let τ₁ := _root_.GD.N0106.N0428.N0765.N1619.d021057 eta (Real.exp b) 1 c₀ (h : ℝ) N
    let refined := _root_.GD.N0106.N0428.N0765.N1510.d023686 (_root_.GD.N0106.N0428.N0765.N1509.d023675 h B S₀) (_root_.GD.N0106.N0428.N0765.N1509.d023676 S₁) ε τ₀ τ₁
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ∈ refined ∧
      refined ⊆ _root_.GD.N0106.N0428.N0765.N1510.d023686 S₀ S₁ ε τ₀ τ₁ := by
  dsimp only
  constructor
  · simpa only [_root_.GD.N0106.N0428.N0765.N1510.d023686, Set.mem_Icc, _root_.GD.N0106.N0428.N0765.N1510.d023684, _root_.GD.N0106.N0428.N0765.N1510.d023685] using
      _root_.GD.N0106.N0428.N0765.N1509.d023683
        heta hd hdpi h B hh hB hε hPB hj hcenter S₀ S₁ hS₀ hS₁
  · have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
    have hhi : (0 : ℝ) ≤ (S₁.hi : ℝ) :=
      (show (0 : ℝ) ≤ (S₁.lo : ℝ) by exact_mod_cast hOld₁).trans
        (hS₁.1.trans hS₁.2)
    exact _root_.GD.N0106.N0428.N0765.N1510.d023689 h B S₀ S₁ (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hhR)
      hε hOld₀ hOld₁ (add_nonneg hhi
        (_root_.GD.N0106.N0428.N0765.N1510.d023691 heta (Real.exp_pos b) one_pos hhR c₀ N))

end GD.N0106.N0428.N0765.N1510

#print axioms _root_.GD.N0106.N0428.N0765.N1510.d023689
#print axioms _root_.GD.N0106.N0428.N0765.N1510.d023690
#print axioms _root_.GD.N0106.N0428.N0765.N1510.d023692
