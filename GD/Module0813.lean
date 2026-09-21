import GD.Module0811
import GD.Module0246







set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal
namespace GD.N0232.N0719.N0973
noncomputable section
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0844 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0232.N0719.N0962 (d012190 d012191)
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0686

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)

def d012375 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : EReal :=
  _root_.GD.N0230.N0686.d003544 (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes)) d

def d012376 (C : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ)) : EReal :=
  _root_.GD.N0230.N0686.d003545 (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes)) C

def d012377 : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes))
    (_root_.GD.N0232.N0719.N0962.d012190 k sizes)



theorem d012378 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (1 : EReal) -
      (_root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) theta d : EReal) =
    (((_root_.GD.N0232.N0719.N0972.d012340 k sizes theta - (_root_.GD.N0232.N0719.N0859.d010840 k sizes theta d).toReal) /
      _root_.GD.N0232.N0719.N0972.d012340 k sizes theta : ℝ) : EReal) := by
  have hb := _root_.GD.N0232.N0719.N0972.d012342 k sizes hk hsizes theta
  have hp : _root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) theta d ≠ ⊤ :=
    ENNReal.div_ne_top (hd.2 theta) (ne_of_gt (ENNReal.ofReal_pos.mpr hb))
  rw [_root_.GD.N0230.N0686.d003546 hp, ← EReal.coe_one, ← EReal.coe_sub]
  apply congrArg (fun x : ℝ => (x : EReal))
  simp only [_root_.GD.N0232.N0719.N0844.d012246, _root_.GD.N0232.N0719.N0972.d012343, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hb.le]
  field_simp [hb.ne']

theorem d012379 : _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes ≠ ⊤ := by
  unfold _root_.GD.N0232.N0719.N0973.d012377
  rw [← _root_.GD.N0232.N0719.N0844.d012256 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) hk hsizes]
  exact ne_top_of_le_ne_top (by simp) (_root_.GD.N0232.N0719.N0972.d012349 k sizes hk hsizes)



theorem d012380 :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012190 k sizes) =
        ((1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal : ℝ) : EReal) ∧
      _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012191 k sizes) =
        ((1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal : ℝ) : EReal) ∧
      _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hsizes e =
        _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hsizes e =
        _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012191 k sizes) := by
  letI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩
  let r := _root_.GD.N0232.N0719.N0844.d012246 k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes)
  obtain ⟨e, he, hD, hvD, hvE, _⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 k sizes hk hsizes
  have hp : ∀ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, ∀ theta, r theta d ≠ ⊤ := by
    intro d hd theta
    exact ENNReal.div_ne_top (hd.2 theta)
      (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hsizes theta)))
  have hv := _root_.GD.N0232.N0719.N0844.d012257 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) hk hsizes
  have hfD := _root_.GD.N0232.N0719.N0973.d012379 k sizes hk hsizes
  have hfE : _root_.GD.N0230.N0611.d003517 r (_root_.GD.N0232.N0719.N0962.d012191 k sizes) ≠ ⊤ := by
    rw [← hv]
    exact hfD
  have hDresult := _root_.GD.N0230.N0686.d003549 r (_root_.GD.N0232.N0719.N0962.d012190 k sizes)
    hp e hD hvD hfD
  have hEresult := _root_.GD.N0230.N0686.d003549 r (_root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (fun d hd => hp d ⟨hd.1.1, hd.2⟩) e he hvE hfE
  refine ⟨e, he, hD, hDresult.1, ?_, hDresult.2, hEresult.2⟩
  simpa only [r, _root_.GD.N0232.N0719.N0973.d012376, _root_.GD.N0232.N0719.N0973.d012377, ← hv] using hEresult.1

theorem d012381 :
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012190 k sizes) =
      ((1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal : ℝ) : EReal) := by
  obtain ⟨_, _, _, h, _⟩ := _root_.GD.N0232.N0719.N0973.d012380 k sizes hk hsizes
  exact h

theorem d012382 :
    0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hsizes (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ↔
      _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes < 1 := by
  rw [_root_.GD.N0232.N0719.N0973.d012381 k sizes hk hsizes]
  have hfinite := _root_.GD.N0232.N0719.N0973.d012379 k sizes hk hsizes
  have hreal : (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal < 1 ↔
      _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hfinite (by simp : (1 : ℝ≥0∞) ≠ ⊤))
  constructor
  · intro h
    have hR : (0 : ℝ) < 1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal := by
      exact_mod_cast h
    exact hreal.mp (by linarith)
  · intro h
    have hR : (0 : ℝ) < 1 - (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hsizes).toReal := by
      have := hreal.mpr h
      linarith
    exact_mod_cast hR
end
end GD.N0232.N0719.N0973
#print axioms _root_.GD.N0232.N0719.N0973.d012380
#print axioms _root_.GD.N0232.N0719.N0973.d012382
