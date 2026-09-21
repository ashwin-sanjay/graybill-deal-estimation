import GD.Module1460
import GD.Module1732
import GD.Module0813

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0003.N0239
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 (d012190 d012191)
open _root_.GD.N0232.N0719.N0970 (d012309 d012310)
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0844
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0686
open _root_.GD.N0213.N0515
open _root_.GD.N0213.N0492

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)

abbrev d028829 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) θ d

theorem d028830 :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
      (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn ∧
      ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
  obtain ⟨a, ha, haf, haD, _, ha1⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 k sizes hk hn
  have habase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ a ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
    intro θ
    have hab := (le_iSup (fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ a) θ).trans ha1
    have hr := (_root_.GD.N0232.N0719.N0844.d012250 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) (by omega) (fun i => by have := hn i; omega)
      1 zero_le_one θ a).mp (by simpa only [ENNReal.ofReal_one] using hab)
    simpa only [_root_.GD.N0232.N0719.N0972.d012343, one_mul, _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn] using hr
  have hant : ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes a := by
    intro ht
    exact _root_.GD.N0213.N0492.d028822 sizes hk hn
      (_root_.GD.N0213.N0492.d028819 sizes ha ht) habase
  obtain ⟨e, he, het, hes⟩ := (_root_.GD.N0213.N0515.d023050 k sizes haf).mp hant
  have hrel (θ) : _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0003.N0239.d028829 k sizes hk hn θ a :=
    ENNReal.div_lt_div_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn θ)))
      ENNReal.ofReal_ne_top (hes θ)
  have hecap (θ) : _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
    exact (hrel θ).trans_le ((le_iSup (fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ a) θ).trans_eq haD)
  refine ⟨e, he, het, fun θ => (hes θ).trans_le (habase θ), ?_, hecap⟩
  exact le_antisymm (iSup_le fun θ => (hecap θ).le)
    (_root_.GD.N0230.N0611.d003520 _ he)

theorem d028831 : 0 < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
  obtain ⟨e, _, _, _, _, hstrict⟩ := _root_.GD.N0003.N0239.d028830 k sizes hk hn
  exact bot_le.trans_lt (hstrict (_root_.GD.N0232.N0719.N0859.d010810 k))

theorem d028832 :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
      _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn e =
        _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn e =
        _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012191 k sizes) ∧
      ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
  letI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩
  obtain ⟨e, he, het, hes, hev, hecap⟩ :=
    _root_.GD.N0003.N0239.d028830 k sizes hk hn
  have hgain : _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn e =
      ((1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal : ℝ) : EReal) := by
    have hfinite : _root_.GD.N0230.N0611.d003516 (_root_.GD.N0003.N0239.d028829 k sizes hk hn) e ≠ ⊤ := by
      change (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) ≠ ⊤
      rw [hev]
      exact _root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn
    exact (_root_.GD.N0230.N0686.d003548 (_root_.GD.N0003.N0239.d028829 k sizes hk hn) e hfinite).trans
      (congrArg (fun x : ℝ≥0∞ => ((1 - x.toReal : ℝ) : EReal)) hev)
  obtain ⟨_, _, _, hD, hE, _⟩ := _root_.GD.N0232.N0719.N0973.d012380 k sizes hk hn
  exact ⟨e, he, het, hes, hgain.trans hD.symm, hgain.trans hE.symm, hecap⟩

theorem d028833
    {e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hev : (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn)
    (hecap : ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn) :
    (∀ F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k), ∃ c : ℝ≥0∞,
      c < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn ∧ ∀ θ ∈ F, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e ≤ c) ∧
    (∀ c : ℝ≥0∞, c < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn →
      ∃ θ, c < _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) := by
  constructor
  · intro F
    refine ⟨F.sup (fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e), ?_, ?_⟩
    · exact (Finset.sup_lt_iff (_root_.GD.N0003.N0239.d028831 k sizes hk hn)).mpr (fun θ _ => hecap θ)
    · intro θ hθ
      exact Finset.le_sup (f := fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) hθ
  · intro c hc
    apply lt_iSup_iff.mp
    exact hc.trans_eq hev.symm

theorem d028834 :
    0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ↔
      ∃ c : ℝ≥0∞, c < 1 ∧
        ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
          _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
          ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e ≤ c := by
  rw [_root_.GD.N0232.N0719.N0973.d012382 k sizes hk hn]
  constructor
  · intro hB
    obtain ⟨e, he, het, hes, _, hecap⟩ :=
      _root_.GD.N0003.N0239.d028830 k sizes hk hn
    exact ⟨_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn, hB, e, he, het, hes, fun θ => (hecap θ).le⟩
  · rintro ⟨c, hc, e, he, _, _, hecap⟩
    exact ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0003.N0239.d028829 k sizes hk hn) he).trans
      (iSup_le hecap)).trans_lt hc

include hk hn in
theorem d028835
    {e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (het : _root_.GD.N0232.N0719.N0970.d012309 k sizes e) (hes : _root_.GD.N0232.N0719.N0970.d012310 k sizes e) :
    e ∉ _root_.GD.N0232.N0719.N0962.d012191 k sizes := by
  intro ha
  exact _root_.GD.N0213.N0492.d028822 sizes hk hn
    (_root_.GD.N0213.N0492.d028819 sizes ha het) (fun θ => (hes θ).le)

theorem d028836
    {e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hev : (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn)
    (hecap : ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞)
    (hw : ∑ θ ∈ F, w θ = 1) :
    (∑ θ ∈ F, w θ * _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
  obtain ⟨c, hc, hcap⟩ := (_root_.GD.N0003.N0239.d028833 k sizes hk hn hev hecap).1 F
  apply lt_of_le_of_lt ?_ hc
  calc
    (∑ θ ∈ F, w θ * _root_.GD.N0003.N0239.d028829 k sizes hk hn θ e) ≤ ∑ θ ∈ F, w θ * c := by
      apply Finset.sum_le_sum
      intro θ hθ
      exact mul_le_mul' le_rfl (hcap θ hθ)
    _ = (∑ θ ∈ F, w θ) * c := (Finset.sum_mul F w c).symm
    _ = c := by rw [hw, one_mul]

end
end GD.N0003.N0239

#print axioms _root_.GD.N0003.N0239.d028830
#print axioms _root_.GD.N0003.N0239.d028831
#print axioms _root_.GD.N0003.N0239.d028832
#print axioms _root_.GD.N0003.N0239.d028833
#print axioms _root_.GD.N0003.N0239.d028834
#print axioms _root_.GD.N0003.N0239.d028835
#print axioms _root_.GD.N0003.N0239.d028836
