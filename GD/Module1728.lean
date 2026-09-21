import GD.Module1727
import GD.Module0835











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory ProbabilityTheory

namespace GD.N0106.N0428.N0766.N1689
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0106.N0428.N0766.N1694 _root_.GD.N0106.N0428.N0766.N1692


def d028780 (m n : ℕ) (q : ℝ × ℝ → ℝ)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  q (_root_.GD.N0107.d009091 m n (_root_.GD.N0107.d009085 omega.1)
      (_root_.GD.N0107.d009085 omega.2), _root_.GD.N0107.d009093 m n omega)


abbrev d028781 (m n : ℕ) (epsilon : ℝ) (q : ℝ × ℝ → ℝ) :=
  _root_.GD.N0107.d012734 m n epsilon (_root_.GD.N0106.N0428.N0766.N1689.d028780 m n q)

theorem d028782 (m n : ℕ) (q : ℝ × ℝ → ℝ)
    (hq : Measurable q) : Measurable (_root_.GD.N0106.N0428.N0766.N1689.d028780 m n q) := by
  apply hq.comp
  unfold _root_.GD.N0107.d009091 _root_.GD.N0107.d009093 _root_.GD.N0107.d009092
    _root_.GD.N0107.d009090 _root_.GD.N0107.d009085 _root_.GD.N0107.d009084
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420
  fun_prop

theorem d028783 (m n : ℕ) (epsilon : ℝ)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) :
    Measurable (_root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon q) := by
  have hprofile := _root_.GD.N0106.N0428.N0766.N1689.d028782 m n q hq
  unfold _root_.GD.N0106.N0428.N0766.N1689.d028781 _root_.GD.N0107.d012734 _root_.GD.N0107.d012733 _root_.GD.N0107.d009091
    _root_.GD.N0107.d009085 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420
  fun_prop


theorem d028784
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau epsilon : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    {B : ℝ} (hB : 0 ≤ B) (hqBound : ∀ x, |q x| ≤ B) :
    MemLp (fun omega => _root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon q omega - mu)
        2 (_root_.GD.N0107.d009030 m n mu sigma tau) ∧
      MemLp (fun omega => _root_.GD.N0107.d012733 m n omega - mu)
        2 (_root_.GD.N0107.d009030 m n mu sigma tau) := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  have hU := _root_.GD.N0107.d012747 m n hm hn mu sigma tau hsigma htau
  have hL2 := _root_.GD.N0107.d012749
    m n hm hn mu sigma tau hsigma htau q hq hB hqBound
  have hbase := hU.add hL2.1
  have hcorrected := hbase.add (hL2.2.const_mul epsilon)
  constructor
  · apply (memLp_congr_ae (ae_of_all _ fun omega => ?_)).2 hcorrected
    simp only [Pi.add_apply, Pi.mul_apply]
    unfold _root_.GD.N0106.N0428.N0766.N1689.d028781 _root_.GD.N0107.d012734 _root_.GD.N0107.d012733 _root_.GD.N0106.N0428.N0766.N1689.d028780
      _root_.GD.N0107.d012732
    ring
  · apply (memLp_congr_ae (ae_of_all _ fun omega => ?_)).2 hbase
    simp only [Pi.add_apply]
    unfold _root_.GD.N0107.d012733 _root_.GD.N0107.d012732
    ring


theorem d028785
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau epsilon : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    {B : ℝ} (hB : 0 ≤ B) (hqBound : ∀ x, |q x| ≤ B) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega => _root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon q omega - mu) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega => _root_.GD.N0107.d012733 m n omega - mu) =
      _root_.GD.N0107.d009045 m n sigma tau *
        (2 * epsilon * _root_.GD.N0120.d008814
            (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
            (_root_.GD.N0107.d009046 m n sigma tau) q +
          epsilon ^ 2 * _root_.GD.N0120.d008815
            (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
            (_root_.GD.N0107.d009046 m n sigma tau) q) := by
  let P := _root_.GD.N0107.d009030 m n mu sigma tau
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  let U := _root_.GD.N0107.d012732 m n mu e
  let D := _root_.GD.N0107.d009038 m n mu sigma tau e Sigma
  let L := _root_.GD.N0107.d009039 m n mu sigma tau e
  let F := _root_.GD.N0107.d009040 m n mu sigma tau e
  have hL2 := _root_.GD.N0107.d012748
    m n hm hn mu sigma tau hsigma htau q hq hB hqBound
  have hLaw := _root_.GD.N0107.d009052 m n hm hn mu sigma tau hsigma htau
  have hRisk := _root_.GD.N0144.d006723
    (P := P) (U := U) (D := D) (L := L)
    (Sobs := fun omega => (L omega, F omega))
    (q := fun p : ℝ × (ℝ × ℝ) => q p.2) (e := e) (ε := epsilon)
    (hq.comp measurable_snd)
    (_root_.GD.N0107.d012747 m n hm hn mu sigma tau hsigma htau)
    hL2.1 hL2.2
    (_root_.GD.N0107.d012745 m n hm hn mu sigma tau hsigma htau)
    (_root_.GD.N0107.d012746 m n hm hn mu sigma tau hsigma htau)
  have hAbstract :
      (fun omega => _root_.GD.N0141.d006685 U D L e omega + epsilon *
        _root_.GD.N0144.d006721 D
          (fun omega => (L omega, F omega))
          (fun p : ℝ × (ℝ × ℝ) => q p.2) omega) =
      _root_.GD.N0141.d006686 U D L (fun omega => q (L omega, F omega)) e epsilon := by
    funext omega
    unfold _root_.GD.N0141.d006686 _root_.GD.N0144.d006721
    ring
  rw [hAbstract, hLaw.d008877 q hq, hLaw.d008878 q hq] at hRisk
  have hD : D = _root_.GD.N0107.d009090 m n := by
    funext omega
    exact _root_.GD.N0107.d012724 m n hm hn mu sigma tau hsigma htau omega
  have hL : L = fun omega => _root_.GD.N0107.d009091 m n
      (_root_.GD.N0107.d009085 omega.1) (_root_.GD.N0107.d009085 omega.2) := by
    funext omega
    exact _root_.GD.N0107.d012729 m n hm hn mu sigma tau hsigma htau omega
  have hF : F = _root_.GD.N0107.d009093 m n := by
    funext omega
    exact _root_.GD.N0107.d012731 m n hm hn mu sigma tau hsigma htau omega
  have hCorrected :
      (fun omega => _root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon q omega - mu) =
      _root_.GD.N0141.d006686 U D L (fun omega => q (L omega, F omega)) e epsilon := by
    funext omega
    rw [hD, hL, hF]
    exact _root_.GD.N0107.d012736
      m n mu e epsilon (_root_.GD.N0106.N0428.N0766.N1689.d028780 m n q) omega
  have hBase : (fun omega => _root_.GD.N0107.d012733 m n omega - mu) =
      _root_.GD.N0141.d006685 U D L e := by
    funext omega
    rw [hD, hL]
    exact _root_.GD.N0107.d012735 m n mu e omega
  rw [hCorrected, hBase]
  calc
    _ = 2 * epsilon * (Sigma * _root_.GD.N0120.d008814
          (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2) e q) +
        epsilon ^ 2 * (Sigma * _root_.GD.N0120.d008815
          (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2) e q) := hRisk
    _ = _ := by ring



theorem d028786
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    0 < _root_.GD.N0107.d009045 m n sigma tau *
      _root_.GD.N0106.N0428.N0766.N1694.d028769 (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
        (_root_.GD.N0107.d009046 m n sigma tau) := by
  exact mul_pos (_root_.GD.N0107.d009049 (m := m) (n := n) (by omega) (by omega) hsigma htau)
    (_root_.GD.N0106.N0428.N0766.N1694.d028771 (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hn)
      (_root_.GD.N0107.d009050 (m := m) (n := n) (by omega) (by omega) hsigma htau)
      (_root_.GD.N0107.d009051 (m := m) (n := n) (by omega) (by omega) hsigma htau))




theorem d028787
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau epsilon : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    {C : ℝ} (hC : ∀ x, |q x| ≤ C)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsupport : Function.support q ⊆ K) (hOmega : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega => _root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon q omega - mu) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega => _root_.GD.N0107.d012733 m n omega - mu) =
      (_root_.GD.N0107.d009045 m n sigma tau *
        _root_.GD.N0106.N0428.N0766.N1694.d028769 (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
          (_root_.GD.N0107.d009046 m n sigma tau)) *
        (2 * epsilon * _root_.GD.N0106.N0428.N0766.d028738
            (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2) q
            (_root_.GD.N0107.d009046 m n sigma tau) +
          epsilon ^ 2 * _root_.GD.N0106.N0428.N0766.d028739
            (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2) q
            (_root_.GD.N0107.d009046 m n sigma tau)) := by
  have hC0 : 0 ≤ C := (abs_nonneg (q (0, 0))).trans (hC (0, 0))
  rw [_root_.GD.N0106.N0428.N0766.N1689.d028785
    m n hm hn mu sigma tau epsilon hsigma htau q hq hC0 hC]
  obtain ⟨hTrace, hEnergy⟩ := _root_.GD.N0106.N0428.N0766.N1694.d028775
    (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hn)
    (_root_.GD.N0107.d009050 (m := m) (n := n) (by omega) (by omega) hsigma htau)
    (_root_.GD.N0107.d009051 (m := m) (n := n) (by omega) (by omega) hsigma htau)
    q hq hC hK hsupport hOmega
  rw [hTrace, hEnergy]
  ring


def d028788 (n : ℕ) (hn : 2 ≤ n) : _root_.GD.N0106.N0428.N0766.N1692.d007794 :=
  ⟨(((n - 1 : ℕ) : ℝ) / 2), _root_.GD.N0137.d008900 hn⟩




theorem d028789
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ epsilon > 0,
      Measurable (_root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon
        (_root_.GD.N0106.N0428.N0766.N1694.d028776 (_root_.GD.N0106.N0428.N0766.N1689.d028788 m hm) (_root_.GD.N0106.N0428.N0766.N1689.d028788 n hn))) ∧
      ∀ (mu sigma tau : ℝ), 0 < sigma → 0 < tau →
        Integrable (fun omega =>
          (_root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon
            (_root_.GD.N0106.N0428.N0766.N1694.d028776 (_root_.GD.N0106.N0428.N0766.N1689.d028788 m hm) (_root_.GD.N0106.N0428.N0766.N1689.d028788 n hn)) omega - mu) ^ 2)
          (_root_.GD.N0107.d009030 m n mu sigma tau) ∧
        Integrable (fun omega => (_root_.GD.N0107.d012733 m n omega - mu) ^ 2)
          (_root_.GD.N0107.d009030 m n mu sigma tau) ∧
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
            (fun omega => _root_.GD.N0106.N0428.N0766.N1689.d028781 m n epsilon
              (_root_.GD.N0106.N0428.N0766.N1694.d028776 (_root_.GD.N0106.N0428.N0766.N1689.d028788 m hm) (_root_.GD.N0106.N0428.N0766.N1689.d028788 n hn)) omega - mu) <
          _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
            (fun omega => _root_.GD.N0107.d012733 m n omega - mu) := by
  let a := _root_.GD.N0106.N0428.N0766.N1689.d028788 m hm
  let b := _root_.GD.N0106.N0428.N0766.N1689.d028788 n hn
  let q := _root_.GD.N0106.N0428.N0766.N1694.d028776 a b
  have hp := _root_.GD.N0106.N0428.N0766.d028760 a b
  have hq : Measurable q := hp.continuous.measurable
  obtain ⟨B, hB, hqBound⟩ := hp.bounded
  obtain ⟨epsilon, hepsilon, hnegative⟩ := _root_.GD.N0106.N0428.N0766.N1694.d028778 a b
  refine ⟨epsilon, hepsilon, _root_.GD.N0106.N0428.N0766.N1689.d028783 m n epsilon q hq, ?_⟩
  intro mu sigma tau hsigma htau
  have hmem := _root_.GD.N0106.N0428.N0766.N1689.d028784
    m n hm hn mu sigma tau epsilon hsigma htau q hq hB.le hqBound
  refine ⟨hmem.1.integrable_sq, hmem.2.integrable_sq, ?_⟩
  apply sub_neg.mp
  rw [_root_.GD.N0106.N0428.N0766.N1689.d028785
    m n hm hn mu sigma tau epsilon hsigma htau q hq hB.le hqBound]
  exact mul_neg_of_pos_of_neg
    (_root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau)
    (hnegative (_root_.GD.N0107.d009046 m n sigma tau)
      ⟨_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau,
        _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau⟩)

end
end GD.N0106.N0428.N0766.N1689

#print axioms _root_.GD.N0106.N0428.N0766.N1689.d028786
#print axioms _root_.GD.N0106.N0428.N0766.N1689.d028787
#print axioms _root_.GD.N0106.N0428.N0766.N1689.d028789
