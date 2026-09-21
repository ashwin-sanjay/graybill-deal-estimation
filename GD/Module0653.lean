import GD.Module0651
import Mathlib.MeasureTheory.Integral.Prod




















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0955

noncomputable section


def d009607 (k : ℕ) :
    Set (_root_.GD.N0232.N0719.N0857.d009377 k) :=
  {q |
    (∀ j, 0 < q j) ∧
      0 < 1 - ∑ j, q j}

theorem d009608 (k : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  rw [show _root_.GD.N0232.N0719.N0955.d009607 k =
      (⋂ j : Fin (k - 1),
        {q : _root_.GD.N0232.N0719.N0857.d009377 k | 0 < q j}) ∩
        {q : _root_.GD.N0232.N0719.N0857.d009377 k |
          0 < 1 - ∑ j, q j} by
    ext q
    simp [_root_.GD.N0232.N0719.N0955.d009607]]
  exact
    (MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_const (measurable_pi_apply j)).inter
      (measurableSet_lt measurable_const
        (measurable_const.sub
          (Finset.measurable_fun_sum Finset.univ fun j _ =>
            measurable_pi_apply j)))



def d009609 (k : ℕ) :
    _root_.GD.N0232.N0719.N0953.d003306 (k - 1) ≃ᵐ
      _root_.GD.N0232.N0719.N0857.d009377 k × ℝ :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : _root_.GD.N0232.N0719.N0953.d003305 (k - 1) => ℝ)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (_root_.GD.N0232.N0719.N0857.d009377 k))
      (MeasurableEquiv.piUnique
        (fun _ : Fin 1 => ℝ)))

@[simp]
theorem d009610
    {k : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) :
    (_root_.GD.N0232.N0719.N0955.d009609 k x).1 =
      fun j => _root_.GD.N0232.N0719.N0953.d003307 x j := by
  rfl

@[simp]
theorem d009611
    {k : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) :
    (_root_.GD.N0232.N0719.N0955.d009609 k x).2 =
      _root_.GD.N0232.N0719.N0953.d003308 x := by
  rfl



def d009612
    {k : ℕ} (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003306 (k - 1) :=
  (_root_.GD.N0232.N0719.N0955.d009609 k).symm (q, ω)

@[simp]
theorem d009613
    {k : ℕ} (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ)
    (j : Fin (k - 1)) :
    _root_.GD.N0232.N0719.N0953.d003307 (_root_.GD.N0232.N0719.N0955.d009612 q ω) j = q j := by
  have h :=
    congrArg Prod.fst
      ((_root_.GD.N0232.N0719.N0955.d009609 k).apply_symm_apply (q, ω))
  exact congrFun h j

@[simp]
theorem d009614
    {k : ℕ} (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003308 (_root_.GD.N0232.N0719.N0955.d009612 q ω) = ω := by
  have h :=
    congrArg Prod.snd
      ((_root_.GD.N0232.N0719.N0955.d009609 k).apply_symm_apply (q, ω))
  exact h

@[simp]
theorem d009615
    {k : ℕ} (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003309 (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      1 - ∑ j, q j := by
  unfold _root_.GD.N0232.N0719.N0953.d003309
  simp

theorem d009616
    {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0953.d003334 (_root_.GD.N0232.N0719.N0955.d009612 q ω)
        ((_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i) =
      _root_.GD.N0232.N0719.N0853.d009567 hk q i := by
  cases hi : (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
  | inl j =>
      simp [_root_.GD.N0232.N0719.N0953.d003334, _root_.GD.N0232.N0719.N0853.d009567, hi]
  | inr j =>
      fin_cases j
      simp [_root_.GD.N0232.N0719.N0953.d003334, _root_.GD.N0232.N0719.N0853.d009567, hi]

theorem d009617
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0954.d009479 (_root_.GD.N0232.N0719.N0954.d009350 hk shape) =
      _root_.GD.N0232.N0719.N0954.d009503 shape := by
  unfold _root_.GD.N0232.N0719.N0954.d009479 _root_.GD.N0232.N0719.N0954.d009503
    _root_.GD.N0232.N0719.N0954.d009350
  exact
    Fintype.sum_equiv
      (_root_.GD.N0232.N0719.N0954.d009344 k hk) _ _ fun _ => rfl

theorem d009618
    {k : ℕ} (hk : 0 < k)
    (shape rate : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0954.d009481
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate) =
      _root_.GD.N0232.N0719.N0954.d009507 shape rate := by
  unfold _root_.GD.N0232.N0719.N0954.d009481 _root_.GD.N0232.N0719.N0954.d009507
    _root_.GD.N0232.N0719.N0954.d009350
  exact
    Fintype.prod_equiv
      (_root_.GD.N0232.N0719.N0954.d009344 k hk) _ _ fun _ => rfl

theorem d009619
    {k : ℕ} (hk : 0 < k)
    (rate : Fin k → ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0953.d003337
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
        (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      _root_.GD.N0232.N0719.N0951.d003587
        rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  unfold _root_.GD.N0232.N0719.N0953.d003337
    _root_.GD.N0232.N0719.N0951.d003587
  rw [show
      (∑ i : Fin k,
          rate i / _root_.GD.N0232.N0719.N0853.d009567 hk q i) =
        ∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          rate (e j) /
            _root_.GD.N0232.N0719.N0853.d009567 hk q (e j) by
    symm
    exact Fintype.sum_equiv e _ _ fun _ => rfl]
  rw [Fintype.sum_sum_type]
  simp only [_root_.GD.N0232.N0719.N0954.d009350, e]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp [_root_.GD.N0232.N0719.N0853.d009567,
    _root_.GD.N0232.N0719.N0955.d009613, _root_.GD.N0232.N0719.N0955.d009615, e]

theorem d009620
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0954.d009482
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      ∏ i,
        (_root_.GD.N0232.N0719.N0853.d009567 hk q i) ^
          (-(shape i + 1)) := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  unfold _root_.GD.N0232.N0719.N0954.d009482
  rw [show
      (∏ i : Fin k,
          (_root_.GD.N0232.N0719.N0853.d009567 hk q i) ^
            (-(shape i + 1))) =
        ∏ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          (_root_.GD.N0232.N0719.N0853.d009567 hk q (e j)) ^
            (-(shape (e j) + 1)) by
    symm
    exact Fintype.prod_equiv e _ _ fun _ => rfl]
  apply Finset.prod_congr rfl
  intro j _
  have hw :
      _root_.GD.N0232.N0719.N0953.d003334 (_root_.GD.N0232.N0719.N0955.d009612 q ω) j =
        _root_.GD.N0232.N0719.N0853.d009567 hk q (e j) := by
    simpa only [e, Equiv.symm_apply_apply] using
      (_root_.GD.N0232.N0719.N0955.d009616 hk q ω (e j))
  rw [hw]
  rfl





theorem d009621
    {k : ℕ} (hk : 0 < k)
    (shape rate : Fin k → ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k) (ω : ℝ) :
    _root_.GD.N0232.N0719.N0954.d009500
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
        (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      _root_.GD.N0232.N0719.N0954.d009508
        shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) := by
  unfold _root_.GD.N0232.N0719.N0954.d009500
    _root_.GD.N0232.N0719.N0954.d009508
  rw [_root_.GD.N0232.N0719.N0955.d009618,
    _root_.GD.N0232.N0719.N0955.d009617,
    _root_.GD.N0232.N0719.N0955.d009619,
    _root_.GD.N0232.N0719.N0955.d009620]






theorem d009622
    {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0853.d009581 hk ⊆ _root_.GD.N0232.N0719.N0955.d009607 k := by
  intro q hq
  constructor
  · intro j
    have hpos :=
      _root_.GD.N0232.N0719.N0951.d003590
        hk hq
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j))
    simpa using hpos
  · have hpos :=
      _root_.GD.N0232.N0719.N0951.d003590
        hk hq
        (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inr 0))
    simpa using hpos

theorem d009623
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k)
    {ω : ℝ} (hω : 0 < ω) :
    _root_.GD.N0232.N0719.N0954.d009483
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
        (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      _root_.GD.N0232.N0719.N0954.d009508
          shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
        gammaPDFReal
          (_root_.GD.N0232.N0719.N0954.d009503 shape)
          (_root_.GD.N0232.N0719.N0951.d003587
            rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) ω := by
  have hx :
      _root_.GD.N0232.N0719.N0955.d009612 q ω ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hω
    · intro j
      simpa using hq.1 j
    · simpa using hq.2
  have hfactor :=
    _root_.GD.N0232.N0719.N0954.d009501
      (shape := _root_.GD.N0232.N0719.N0954.d009350 hk shape)
      (rate := _root_.GD.N0232.N0719.N0954.d009350 hk rate)
      (x := _root_.GD.N0232.N0719.N0955.d009612 q ω)
      (fun i => hshape
        (_root_.GD.N0232.N0719.N0954.d009344 k hk i))
      (fun i => hrate
        (_root_.GD.N0232.N0719.N0954.d009344 k hk i))
      hx hω.le
  rw [_root_.GD.N0232.N0719.N0955.d009621,
    _root_.GD.N0232.N0719.N0955.d009617,
    _root_.GD.N0232.N0719.N0955.d009619] at hfactor
  exact hfactor



theorem d009624
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (F : ℝ → ℝ) :
    (∫ x in Set.Ioi 0,
        gammaPDFReal a r x * F x) =
      ∫ x, F x ∂gammaMeasure a r := by
  rw [_root_.GD.N0232.N0719.N0954.d009351
    ha hr]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx hnot
  have hxle : x ≤ 0 := le_of_not_gt hnot
  have hxlt : x < 0 := lt_of_le_of_ne hxle hx
  simp [gammaPDFReal, not_le.mpr hxlt]






theorem d009625
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k)
    (F : ℝ → ℝ) :
    (∫ ω in Set.Ioi 0,
        _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
            (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
          F ω) =
      _root_.GD.N0232.N0719.N0954.d009508
          shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
        ∫ ω, F ω
          ∂gammaMeasure
            (_root_.GD.N0232.N0719.N0954.d009503 shape)
            (_root_.GD.N0232.N0719.N0951.d003587
              rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) := by
  have hA :
      0 < _root_.GD.N0232.N0719.N0954.d009503 shape :=
    _root_.GD.N0232.N0719.N0954.d009504 hk hshape
  have hweightPos :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i := by
    intro i
    cases hi : (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
    | inl j =>
        have hj := hq.1 j
        simpa [_root_.GD.N0232.N0719.N0853.d009567, hi] using hj
    | inr j =>
        fin_cases j
        simpa [_root_.GD.N0232.N0719.N0853.d009567, hi] using hq.2
  have hR :
      0 <
        _root_.GD.N0232.N0719.N0951.d003587
          rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.sum_pos
      (fun i _ =>
        div_pos (hrate i) (hweightPos i))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  calc
    (∫ ω in Set.Ioi 0,
        _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
            (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
          F ω) =
        ∫ ω in Set.Ioi 0,
          _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (gammaPDFReal
              (_root_.GD.N0232.N0719.N0954.d009503 shape)
              (_root_.GD.N0232.N0719.N0951.d003587
                rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) ω *
              F ω) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ω hω
      change
        _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
              (_root_.GD.N0232.N0719.N0955.d009612 q ω) * F ω =
          _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (gammaPDFReal
                (_root_.GD.N0232.N0719.N0954.d009503 shape)
                (_root_.GD.N0232.N0719.N0951.d003587
                  rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) ω *
              F ω)
      rw [_root_.GD.N0232.N0719.N0955.d009623
        hk hshape hrate hq hω]
      ring
    _ =
        _root_.GD.N0232.N0719.N0954.d009508
            shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          ∫ ω in Set.Ioi 0,
            gammaPDFReal
                (_root_.GD.N0232.N0719.N0954.d009503 shape)
                (_root_.GD.N0232.N0719.N0951.d003587
                  rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) ω *
              F ω := by
      rw [integral_const_mul]
    _ =
        _root_.GD.N0232.N0719.N0954.d009508
            shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          ∫ ω, F ω
            ∂gammaMeasure
              (_root_.GD.N0232.N0719.N0954.d009503 shape)
              (_root_.GD.N0232.N0719.N0951.d003587
                rate (_root_.GD.N0232.N0719.N0853.d009567 hk q)) := by
      rw [_root_.GD.N0232.N0719.N0955.d009624 hA hR F]

theorem d009626
    (k : ℕ) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0955.d009609 k)
      (volume :
        Measure (_root_.GD.N0232.N0719.N0953.d003306 (k - 1)))
      (volume :
        Measure (_root_.GD.N0232.N0719.N0857.d009377 k × ℝ)) := by
  refine
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : _root_.GD.N0232.N0719.N0953.d003305 (k - 1) => ℝ)).trans ?_
  exact MeasurePreserving.prod
    (MeasurePreserving.id volume)
    (volume_preserving_piUnique
      (fun _ : Fin 1 => ℝ))

theorem d009627
    {k : ℕ}
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) :
    x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1) ↔
      _root_.GD.N0232.N0719.N0955.d009609 k x ∈
        _root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Set.Ioi 0 := by
  simp only [_root_.GD.N0232.N0719.N0953.d003311, _root_.GD.N0232.N0719.N0955.d009607,
    Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioi,
    _root_.GD.N0232.N0719.N0955.d009610,
    _root_.GD.N0232.N0719.N0955.d009611]
  simp only [_root_.GD.N0232.N0719.N0953.d003309]
  tauto

theorem d009628
    (k : ℕ) :
    _root_.GD.N0232.N0719.N0955.d009609 k ''
        _root_.GD.N0232.N0719.N0953.d003311 (k - 1) =
      _root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Set.Ioi 0 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (_root_.GD.N0232.N0719.N0955.d009627 x).1 hx
  · intro hz
    refine
      ⟨(_root_.GD.N0232.N0719.N0955.d009609 k).symm z, ?_,
        (_root_.GD.N0232.N0719.N0955.d009609 k).apply_symm_apply z⟩
    apply
      (_root_.GD.N0232.N0719.N0955.d009627
        ((_root_.GD.N0232.N0719.N0955.d009609 k).symm z)).2
    simpa using hz






theorem d009629
    {k : ℕ}
    (H : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ)
    (hH :
      IntegrableOn H (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    (∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1), H x) =
      ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
        ∫ ω in Set.Ioi 0,
          H (_root_.GD.N0232.N0719.N0955.d009612 q ω) := by
  let e := _root_.GD.N0232.N0719.N0955.d009609 k
  let K : _root_.GD.N0232.N0719.N0857.d009377 k × ℝ → ℝ :=
    fun z => H (e.symm z)
  have hImage :
      e '' _root_.GD.N0232.N0719.N0953.d003311 (k - 1) =
        _root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Set.Ioi 0 :=
    _root_.GD.N0232.N0719.N0955.d009628 k
  have htransport :
      (∫ z in e '' _root_.GD.N0232.N0719.N0953.d003311 (k - 1), K z) =
        ∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1), H x := by
    have h :=
      (_root_.GD.N0232.N0719.N0955.d009626 k).setIntegral_image_emb
        e.measurableEmbedding K (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))
    simpa [K, e] using h
  have hK :
      IntegrableOn K
        (_root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Set.Ioi 0) := by
    rw [← hImage]
    apply
      ((_root_.GD.N0232.N0719.N0955.d009626 k).integrableOn_image
        e.measurableEmbedding).2
    have hKe : K ∘ e = H := by
      funext x
      simp [K]
    rw [hKe]
    exact hH
  calc
    (∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1), H x) =
        ∫ z in
          _root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Set.Ioi 0,
          K z := by
      rw [← hImage, htransport]
    _ =
        ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
          ∫ ω in Set.Ioi 0, K (q, ω) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod K hK
    _ =
        ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
          ∫ ω in Set.Ioi 0,
            H (_root_.GD.N0232.N0719.N0955.d009612 q ω) := by
      rfl










theorem d009630
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (G : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ)
    (hG :
      IntegrableOn
        (fun x =>
          G x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    (∫ t, G (_root_.GD.N0232.N0719.N0954.d009347 hk t)
        ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) =
      ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
        ∫ ω in Set.Ioi 0,
          G (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
              (_root_.GD.N0232.N0719.N0955.d009612 q ω) := by
  rw [_root_.GD.N0232.N0719.N0954.d009491
    hk hshape hrate]
  exact _root_.GD.N0232.N0719.N0955.d009629 _ hG

end

end GD.N0232.N0719.N0955
