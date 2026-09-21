import GD.Module0359
import GD.Module0699













open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1611

noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0107

abbrev d012588 := _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 11)

def d012589 (i : Fin 2) (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ := _root_.GD.N0107.d009084 (x i)

def d012590 (i : Fin 2) (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ :=
  @_root_.GD.N0126.d006422 (Fin 11) _ (x i)

def d012591 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ := _root_.GD.N0106.N0428.N0765.N1611.d012589 1 x - _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x

def d012592 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ × ℝ × ℝ × ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x, _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x, _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x)

def d012593 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005300 (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x)

def d012594 : Set _root_.GD.N0106.N0428.N0765.N1611.d012588 := {x | ∀ i, 0 < _root_.GD.N0106.N0428.N0765.N1611.d012590 i x}

def d012595 (location : ℝ) (scales : Fin 2 → ℝ) : Measure _root_.GD.N0106.N0428.N0765.N1611.d012588 :=
  _root_.GD.N0232.N0719.d009176 2 (fun _ => 11) location scales

@[fun_prop]
theorem d012596 (i : Fin 2) : Measurable (_root_.GD.N0106.N0428.N0765.N1611.d012589 i) := by
  unfold _root_.GD.N0106.N0428.N0765.N1611.d012589 _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  fun_prop

@[fun_prop]
theorem d012597 (i : Fin 2) : Measurable (_root_.GD.N0106.N0428.N0765.N1611.d012590 i) := by
  unfold _root_.GD.N0106.N0428.N0765.N1611.d012590 _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop

@[fun_prop]
theorem d012598 : Measurable _root_.GD.N0106.N0428.N0765.N1611.d012591 :=
  (_root_.GD.N0106.N0428.N0765.N1611.d012596 1).sub (_root_.GD.N0106.N0428.N0765.N1611.d012596 0)

@[fun_prop]
theorem d012599 : Measurable _root_.GD.N0106.N0428.N0765.N1611.d012592 := by
  unfold _root_.GD.N0106.N0428.N0765.N1611.d012592
  fun_prop

@[fun_prop]
theorem d012600 : Measurable _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  exact _root_.GD.N0106.N0428.N0765.N1534.d005351.comp _root_.GD.N0106.N0428.N0765.N1611.d012599

theorem d012601 : MeasurableSet _root_.GD.N0106.N0428.N0765.N1611.d012594 := by
  rw [show _root_.GD.N0106.N0428.N0765.N1611.d012594 = ⋂ i : Fin 2, {x : _root_.GD.N0106.N0428.N0765.N1611.d012588 | 0 < _root_.GD.N0106.N0428.N0765.N1611.d012590 i x} by
    ext x
    simp only [_root_.GD.N0106.N0428.N0765.N1611.d012594, mem_setOf_eq, mem_iInter]]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (_root_.GD.N0106.N0428.N0765.N1611.d012597 i)


theorem d012602 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) (i : Fin 2) :
    (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).2 i =
      _root_.GD.N0106.N0428.N0765.N1611.d012590 i x / 110 := by
  change (@_root_.GD.N0126.d006422 (Fin 11) _ (x i) / (11 - 1 : ℕ)) /
    (11 : ℝ) = _root_.GD.N0106.N0428.N0765.N1611.d012590 i x / 110
  norm_num [_root_.GD.N0106.N0428.N0765.N1611.d012590, div_div]

theorem d012603 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) (i : Fin 2) :
    (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11) x).1 i =
      _root_.GD.N0106.N0428.N0765.N1611.d012589 i x := rfl


theorem d012604 (location : ℝ) (scales : Fin 2 → ℝ) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009304 2 (fun _ => 11))
      (_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales)
      ((_root_.GD.N0232.N0719.N0933.d009300 2 (fun _ => 11) location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales)) := by
  refine ⟨_root_.GD.N0232.N0719.N0933.d009308 2 (fun _ => 11), ?_⟩
  exact _root_.GD.N0232.N0719.N0933.d009309
    2 (fun _ => 11) (by intro i; norm_num) location scales


theorem d012605 (location : ℝ) (scales : Fin 2 → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ∀ᵐ x ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales, x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594 := by
  have hpos :=
    (Measure.quasiMeasurePreserving_snd
      (μ := _root_.GD.N0232.N0719.N0933.d009300 2 (fun _ => 11) location scales)
      (ν := _root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales)).ae
      (_root_.GD.N0232.N0719.N0910.d010288
        (sizes := fun _ : Fin 2 => 11) (by intro i; norm_num) hscales)
  have hraw := (_root_.GD.N0106.N0428.N0765.N1611.d012604 location scales).quasiMeasurePreserving.ae hpos
  filter_upwards [hraw] with x hx
  intro i
  have hi := hx i
  rw [_root_.GD.N0106.N0428.N0765.N1611.d012602] at hi
  exact (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 110)).mp hi

theorem d012606 (location : ℝ) (scales : Fin 2 → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0106.N0428.N0765.N1611.d012595 location scales _root_.GD.N0106.N0428.N0765.N1611.d012594ᶜ = 0 := by
  exact (ae_iff).mp (_root_.GD.N0106.N0428.N0765.N1611.d012605 location scales hscales)

theorem d012607 (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1534.d005299 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) ∈ Ioo 0 1 :=
  _root_.GD.N0106.N0428.N0765.N1534.d005316 (hx 0) (hx 1)


theorem d012608 (location : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1611.d012588)
    (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2 ≤
      2 * (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x - location) ^ 2 + 2 * _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 :=
  _root_.GD.N0106.N0428.N0765.N1534.d005317 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) location

theorem d012609 (location : ℝ) (scales : Fin 2 → ℝ) (i : Fin 2) :
    MemLp (fun x : _root_.GD.N0106.N0428.N0765.N1611.d012588 => _root_.GD.N0106.N0428.N0765.N1611.d012589 i x - location) 2 (_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales) := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales) :=
    _root_.GD.N0232.N0719.N0910.d010289
      (fun _ => 11) (by intro i; norm_num) scales
  have h :=
    ((_root_.GD.N0232.N0719.N0910.d010290
      (fun _ : Fin 2 => 11) (by intro i; norm_num) location scales i).comp_fst
        (_root_.GD.N0232.N0719.N0933.d009301 2 (fun _ => 11) scales)).comp_measurePreserving
          (_root_.GD.N0106.N0428.N0765.N1611.d012604 location scales)
  simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0765.N1611.d012603] using h

theorem d012610 (location : ℝ) (scales : Fin 2 → ℝ) :
    MemLp _root_.GD.N0106.N0428.N0765.N1611.d012591 2 (_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1611.d012609 location scales 1).sub
    (_root_.GD.N0106.N0428.N0765.N1611.d012609 location scales 0)
  have heq : (fun x : _root_.GD.N0106.N0428.N0765.N1611.d012588 =>
      (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x - location) - (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x - location)) = _root_.GD.N0106.N0428.N0765.N1611.d012591 := by
    funext x
    dsimp [_root_.GD.N0106.N0428.N0765.N1611.d012591]
    ring
  change MemLp (fun x : _root_.GD.N0106.N0428.N0765.N1611.d012588 =>
    (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x - location) - (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x - location)) 2 (_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales) at h
  rw [heq] at h
  exact h


theorem d012611 (location : ℝ) (scales : Fin 2 → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    Integrable (fun x => (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2) (_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales) := by
  have hmajorant :=
    (((_root_.GD.N0106.N0428.N0765.N1611.d012609 location scales 0).integrable_sq).const_mul 2).add
      (((_root_.GD.N0106.N0428.N0765.N1611.d012610 location scales).integrable_sq).const_mul 2)
  apply hmajorant.mono'
  · exact ((_root_.GD.N0106.N0428.N0765.N1611.d012600.sub measurable_const).pow_const 2).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location scales hscales] with x hx
    change ‖(_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2‖ ≤
      2 * (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x - location) ^ 2 + 2 * _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location))]
    exact _root_.GD.N0106.N0428.N0765.N1611.d012608 location x hx

def d012612 (location : ℝ) (scales : Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2) ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales


theorem d012613 (location : ℝ) (scales : Fin 2 → ℝ)
    (hscales : ∀ i, 0 < scales i) : _root_.GD.N0106.N0428.N0765.N1611.d012612 location scales < ⊤ := by
  unfold _root_.GD.N0106.N0428.N0765.N1611.d012612
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0106.N0428.N0765.N1611.d012611 location scales hscales)
      (ae_of_all _ fun x => sq_nonneg _)]
  exact ENNReal.ofReal_lt_top


def d012614 (eta : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else Real.sqrt eta

theorem d012615 (eta : ℝ) (heta : 0 < eta) :
    ∀ i, 0 < _root_.GD.N0106.N0428.N0765.N1611.d012614 eta i := by
  intro i
  simp only [_root_.GD.N0106.N0428.N0765.N1611.d012614]
  split_ifs <;> positivity

theorem d012616 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0 ^ 2 = 1 ∧ _root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1 ^ 2 = eta := by
  simp [_root_.GD.N0106.N0428.N0765.N1611.d012614, Real.sq_sqrt heta.le]

theorem d012617 (location eta : ℝ) (heta : 0 < eta) :
    Measurable _root_.GD.N0106.N0428.N0765.N1611.d012593 ∧
    (∀ᵐ x ∂_root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta), x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) ∧
    _root_.GD.N0106.N0428.N0765.N1611.d012612 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta) < ⊤ :=
  ⟨_root_.GD.N0106.N0428.N0765.N1611.d012600,
    _root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta),
    _root_.GD.N0106.N0428.N0765.N1611.d012613 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)⟩

end
end GD.N0106.N0428.N0765.N1611

#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012600
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012605
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012606
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012609
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012611
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012613
#print axioms _root_.GD.N0106.N0428.N0765.N1611.d012617
