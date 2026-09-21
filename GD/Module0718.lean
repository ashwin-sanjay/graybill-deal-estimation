import GD.Module0717










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0232.N0719.N0872

noncomputable section

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0875
open _root_.GD.N0232.N0719.N1003
open _root_.GD.N0137 _root_.GD.N0232.N0719.N1009 _root_.GD.N0232.N0719.N0933


def d010692 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin k) (x : ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  ⟨Function.update s.mean j x, s.meanVariance⟩

theorem d010693 {n : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1))
    (j : Fin (n + 1)) (hmin : ∀ i, s.mean j ≤ s.mean i) :
    _root_.GD.N0232.N0719.N1003.d010646 s = s.mean j := by
  unfold _root_.GD.N0232.N0719.N1003.d010646
  have hle : Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (n + 1) => -s.mean i) ≤ -s.mean j := by
    apply Finset.sup'_le
    intro i _
    exact neg_le_neg (hmin i)
  have hge := Finset.le_sup' (fun i : Fin (n + 1) => -s.mean i)
    (Finset.mem_univ j)
  linarith




theorem d010694
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (j : Fin (n + 1)) :
    ∃ c : ℝ, ∀ x < c, _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) = x := by
  let l : Fin (n + 1) := j.succAbove ⟨0, hn⟩
  have hlj : l ≠ j := Fin.succAbove_ne j _
  let c := min (_root_.GD.N0232.N0719.N1003.d010646 s)
    (_root_.GD.N0232.N0719.N1003.d010642 sizes beta s l +
      _root_.GD.N0232.N0719.N0875.d010338 (sizes j) beta * Real.sqrt (s.meanVariance j))
  refine ⟨c, ?_⟩
  intro x hx
  have hxmean : ∀ i, x < s.mean i := by
    intro i
    have hmin : _root_.GD.N0232.N0719.N1003.d010646 s ≤ s.mean i := by
      unfold _root_.GD.N0232.N0719.N1003.d010646
      have hh := Finset.le_sup' (fun a : Fin (n + 1) => -s.mean a)
        (Finset.mem_univ i)
      linarith
    exact (hx.trans_le (min_le_left _ _)).trans_le hmin
  have hcenter : _root_.GD.N0232.N0719.N1003.d010646 (_root_.GD.N0232.N0719.N0872.d010692 s j x) = x := by
    have h := _root_.GD.N0232.N0719.N0872.d010693 (_root_.GD.N0232.N0719.N0872.d010692 s j x) j
      (by
        intro i
        by_cases hi : i = j
        · subst i; exact le_rfl
        · simpa [_root_.GD.N0232.N0719.N0872.d010692, Function.update_of_ne hi] using (hxmean i).le)
    simpa [_root_.GD.N0232.N0719.N0872.d010692] using h
  have hupper : _root_.GD.N0232.N0719.N1003.d010643 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) j =
      x - _root_.GD.N0232.N0719.N0875.d010338 (sizes j) beta * Real.sqrt (s.meanVariance j) := by
    simp [_root_.GD.N0232.N0719.N1003.d010643, _root_.GD.N0232.N0719.N0875.d010341, _root_.GD.N0232.N0719.N0872.d010692]
  have hlower : _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) l =
      _root_.GD.N0232.N0719.N1003.d010642 sizes beta s l := by
    simp [_root_.GD.N0232.N0719.N1003.d010642, _root_.GD.N0232.N0719.N0875.d010340, _root_.GD.N0232.N0719.N0872.d010692, hlj]
  have hgap : _root_.GD.N0232.N0719.N1003.d010645 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) <
      _root_.GD.N0232.N0719.N1003.d010644 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) := by
    calc
      _root_.GD.N0232.N0719.N1003.d010645 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) ≤
          _root_.GD.N0232.N0719.N1003.d010643 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) j :=
        _root_.GD.N0232.N0719.N1003.d010650 _ _ _ _
      _ < _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) l := by
        rw [hupper, hlower]
        have hh := hx.trans_le (min_le_right _ _)
        linarith
      _ ≤ _root_.GD.N0232.N0719.N1003.d010644 sizes beta (_root_.GD.N0232.N0719.N0872.d010692 s j x) :=
        _root_.GD.N0232.N0719.N1003.d010649 _ _ _ _
  simp [_root_.GD.N0232.N0719.N1003.d010647, not_le.mpr hgap, hcenter]



theorem d010695
    {mu : Measure ℝ} (hmu : volume ≪ mu) {f : ℝ → ℝ}
    (hf : ∃ c : ℝ, ∀ x < c, f x = x) (d : ℝ) :
    ¬ f =ᵐ[mu] fun _ => d := by
  intro h
  have hv := hmu.ae_eq h
  obtain ⟨c, hc⟩ := hf
  have hnull : volume {x | f x ≠ d} = 0 := by
    simpa only [Filter.EventuallyEq, ae_iff, mem_setOf_eq] using hv
  have hi : volume (Ioo (min c d - 1) (min c d)) = 0 := by
    apply measure_mono_null _ hnull
    intro x hx
    change f x ≠ d
    rw [hc x (hx.2.trans_le (min_le_left _ _))]
    exact (hx.2.trans_le (min_le_right _ _)).ne
  rw [Real.volume_Ioo] at hi
  simp at hi


def d010696 {k : ℕ} (z : Fin k → ℝ × ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  ⟨fun i => (z i).1, fun i => (z i).2⟩

@[fun_prop]
theorem d010697 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0872.d010696 : (Fin k → ℝ × ℝ) → _root_.GD.N0232.N0719.N0900.d009096 k) := by
  rw [measurable_comap_iff]
  change Measurable (fun z : Fin k → ℝ × ℝ =>
    ((fun i => (z i).1), (fun i => (z i).2)))
  fun_prop

theorem d010698 {n : ℕ} (j : Fin (n + 1))
    (z : Fin n → ℝ × ℝ) (v x : ℝ) :
    _root_.GD.N0232.N0719.N0872.d010696 (j.insertNth (x, v) z) =
      _root_.GD.N0232.N0719.N0872.d010692 (_root_.GD.N0232.N0719.N0872.d010696 (j.insertNth (0, v) z)) j x := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    apply j.forall_iff_succAbove.2
      ⟨by simp [_root_.GD.N0232.N0719.N0872.d010696, _root_.GD.N0232.N0719.N0872.d010692], ?_⟩ i
    intro a
    simp [_root_.GD.N0232.N0719.N0872.d010696, _root_.GD.N0232.N0719.N0872.d010692, Fin.succAbove_ne]
  · funext i
    apply j.forall_iff_succAbove.2
      ⟨by simp [_root_.GD.N0232.N0719.N0872.d010696, _root_.GD.N0232.N0719.N0872.d010692], ?_⟩ i
    intro a
    simp [_root_.GD.N0232.N0719.N0872.d010696, _root_.GD.N0232.N0719.N0872.d010692]

theorem d010699 {m : ℕ} (hm : 2 ≤ m) (scale : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009289 m scale) := by
  have hshape : 0 < (((m - 1 : ℕ) : ℝ) / 2) := by
    have hh : 0 < m - 1 := by omega
    positivity
  unfold _root_.GD.N0232.N0719.N0933.d009289
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2) (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape hshape
  exact Measure.isProbabilityMeasure_map
    (_root_.GD.N0232.N0719.N0933.d009294 m scale).aemeasurable

theorem d010700 {m : ℕ} (hm : 2 ≤ m)
    (location : ℝ) {scale : ℝ} (hscale : 0 < scale) :
    volume ≪ _root_.GD.N0232.N0719.N0933.d009288 m location scale := by
  rw [_root_.GD.N0232.N0719.N0933.d009297 (by omega : 0 < m)]
  apply gaussianReal_absolutelyContinuous'
  intro hzero
  have hh := congrArg (fun v : ℝ≥0 => (v : ℝ)) hzero
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hpos : 0 < scale ^ 2 / (m : ℝ) := div_pos (sq_pos_of_pos hscale) hmpos
  exact hpos.ne' hh




theorem d010701
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (beta location : ℝ)
    (scales : Fin (n + 1) → ℝ) (hscales : ∀ i, 0 < scales i)
    (j : Fin (n + 1)) (F : (Fin n → ℝ × ℝ) → ℝ) :
    ¬ (fun z => _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 z))
      =ᵐ[_root_.GD.N0232.N0719.N1009.d009283 (n + 1) sizes location scales]
        (fun z => F (fun i => z (j.succAbove i))) := by
  let mu (i : Fin (n + 1)) := _root_.GD.N0232.N0719.N1009.d009276 (sizes i) location (scales i)
  letI (i : Fin (n + 1)) : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i)) :=
    _root_.GD.N0232.N0719.N0872.d010699 (hsizes i) _
  letI (i : Fin (n + 1)) : IsProbabilityMeasure (mu i) := by
    dsimp [mu]
    rw [_root_.GD.N0232.N0719.N0933.d009298]
    infer_instance
  let rest := Measure.pi (fun i : Fin n => mu (j.succAbove i))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) j
  intro hfactor
  change (fun z => _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 z))
      =ᵐ[Measure.pi mu] (fun z => F (fun i => z (j.succAbove i))) at hfactor
  have hsplit := (MeasurePreserving.symm e (measurePreserving_piFinSuccAbove mu j)).quasiMeasurePreserving.ae
    hfactor
  have hpres : MeasurePreserving Prod.swap (rest.prod (mu j)) ((mu j).prod rest) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have hswap := hpres.quasiMeasurePreserving.ae hsplit
  obtain ⟨z, hz⟩ := (Measure.ae_ae_of_ae_prod hswap).exists
  change ∀ᵐ pair ∂mu j,
    _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 (e.symm (pair, z))) =
      F (fun i => (e.symm (pair, z)) (j.succAbove i)) at hz
  have hz' : ∀ᵐ pair ∂mu j,
      _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 (j.insertNth pair z)) = F z := by
    filter_upwards [hz] with pair hpair
    change _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 (j.insertNth pair z)) =
      F (fun i => j.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ)
        pair z (j.succAbove i)) at hpair
    simpa only [Fin.insertNth_apply_succAbove] using hpair
  rw [show mu j = (_root_.GD.N0232.N0719.N0933.d009288 (sizes j) location (scales j)).prod
    (_root_.GD.N0232.N0719.N0933.d009289 (sizes j) (scales j)) from _root_.GD.N0232.N0719.N0933.d009298 _ _ _] at hz'
  have hpres' : MeasurePreserving Prod.swap
      ((_root_.GD.N0232.N0719.N0933.d009289 (sizes j) (scales j)).prod
        (_root_.GD.N0232.N0719.N0933.d009288 (sizes j) location (scales j)))
      ((_root_.GD.N0232.N0719.N0933.d009288 (sizes j) location (scales j)).prod
        (_root_.GD.N0232.N0719.N0933.d009289 (sizes j) (scales j))) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have hswap' := hpres'.quasiMeasurePreserving.ae hz'
  obtain ⟨v, hv⟩ := (Measure.ae_ae_of_ae_prod hswap').exists
  have hv' : (fun x => _root_.GD.N0232.N0719.N1003.d010647 sizes beta
      (_root_.GD.N0232.N0719.N0872.d010692 (_root_.GD.N0232.N0719.N0872.d010696 (j.insertNth (0, v) z)) j x))
      =ᵐ[_root_.GD.N0232.N0719.N0933.d009288 (sizes j) location (scales j)] fun _ => F z := by
    filter_upwards [hv] with x hx
    change _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 (j.insertNth (x, v) z)) = F z at hx
    rw [_root_.GD.N0232.N0719.N0872.d010698] at hx
    exact hx
  exact _root_.GD.N0232.N0719.N0872.d010695
    (_root_.GD.N0232.N0719.N0872.d010700 (hsizes j) location (hscales j))
    (_root_.GD.N0232.N0719.N0872.d010694 hn sizes beta _ j) (F z) hv'


def d010702 {n : ℕ} (j : Fin (n + 1)) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : _root_.GD.N0232.N0719.N0900.d009096 n :=
  ⟨fun i => s.mean (j.succAbove i), fun i => s.meanVariance (j.succAbove i)⟩

@[fun_prop]
theorem d010703 {n : ℕ} (j : Fin (n + 1)) :
    Measurable (_root_.GD.N0232.N0719.N0872.d010702 j) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) =>
    ((fun i => s.mean (j.succAbove i)),
      (fun i => s.meanVariance (j.succAbove i))))
  fun_prop



theorem d010704
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (beta location : ℝ)
    (scales : Fin (n + 1) → ℝ) (hscales : ∀ i, 0 < scales i)
    (j : Fin (n + 1)) (F : _root_.GD.N0232.N0719.N0900.d009096 n → ℝ) (hF : Measurable F) :
    ¬ (fun omega => _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))
      =ᵐ[_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
        (fun omega => F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))) := by
  intro hraw
  have hset : MeasurableSet {z : Fin (n + 1) → ℝ × ℝ |
      _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 z) =
        F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0872.d010696 z))} :=
    measurableSet_eq_fun
      ((_root_.GD.N0232.N0719.N1003.d010659 sizes beta).comp _root_.GD.N0232.N0719.N0872.d010697)
      (hF.comp ((_root_.GD.N0232.N0719.N0872.d010703 j).comp _root_.GD.N0232.N0719.N0872.d010697))
  have hstat : ∀ᵐ z ∂_root_.GD.N0232.N0719.N1009.d009283 (n + 1) sizes location scales,
      _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0872.d010696 z) =
        F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0872.d010696 z)) := by
    rw [← _root_.GD.N0232.N0719.N1009.d009285
      (n + 1) sizes hsizes location scales]
    apply (ae_map_iff (_root_.GD.N0232.N0719.N1009.d009284 _ _).aemeasurable hset).2
    exact hraw
  exact _root_.GD.N0232.N0719.N0872.d010701 hn sizes hsizes
    beta location scales hscales j (F ∘ _root_.GD.N0232.N0719.N0872.d010696) hstat



theorem d010705
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (beta location : ℝ)
    (scales : Fin (n + 1) → ℝ) (hscales : ∀ i, 0 < scales i)
    (j : Fin (n + 1)) (F : _root_.GD.N0232.N0719.N0900.d009096 n → ℝ × ℝ) (hF : Measurable F) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
      {omega | (_root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega),
          _root_.GD.N0232.N0719.N1003.d010648 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =
        F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))} < 1 := by
  let mu := _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
  have hset : MeasurableSet {omega |
      (_root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega),
          _root_.GD.N0232.N0719.N1003.d010648 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =
        F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))} :=
    measurableSet_eq_fun
      (((_root_.GD.N0232.N0719.N1003.d010659 sizes beta).prodMk
        (_root_.GD.N0232.N0719.N1003.d010660 sizes beta)).comp (_root_.GD.N0232.N0719.N0900.d009115 _ _))
      (hF.comp ((_root_.GD.N0232.N0719.N0872.d010703 j).comp (_root_.GD.N0232.N0719.N0900.d009115 _ _)))
  by_contra h
  have hone : mu {omega |
      (_root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega),
          _root_.GD.N0232.N0719.N1003.d010648 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =
        F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))} = 1 :=
    le_antisymm (prob_le_one) (le_of_not_gt h)
  have hae := (mem_ae_iff_prob_eq_one hset).2 hone
  apply _root_.GD.N0232.N0719.N0872.d010704 hn sizes hsizes beta location scales hscales
    j (fun s => (F s).1) hF.fst
  filter_upwards [hae] with omega homega
  exact congrArg Prod.fst homega


def d010706 (k : ℕ) : Set (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  {s | ∀ i, 0 < s.meanVariance i}

theorem d010707 (k : ℕ) : MeasurableSet (_root_.GD.N0232.N0719.N0872.d010706 k) := by
  simp only [_root_.GD.N0232.N0719.N0872.d010706, setOf_forall]
  exact MeasurableSet.iInter (fun i =>
    measurableSet_lt measurable_const (_root_.GD.N0232.N0719.N0900.d009100 i))




theorem d010708
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (beta location : ℝ)
    (scales : Fin (n + 1) → ℝ) (hscales : ∀ i, 0 < scales i)
    (j : Fin (n + 1)) (F : _root_.GD.N0232.N0719.N0872.d010706 n → ℝ × ℝ) (hF : Measurable F) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
      {omega | ∃ hpos : _root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ∈ _root_.GD.N0232.N0719.N0872.d010706 n,
        (_root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega),
          _root_.GD.N0232.N0719.N1003.d010648 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =
          F ⟨_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega), hpos⟩} < 1 := by
  obtain ⟨G, hG, hext⟩ :=
    (MeasurableEmbedding.subtype_coe (_root_.GD.N0232.N0719.N0872.d010707 n)).exists_measurable_extend
      hF (fun _ => inferInstance)
  apply lt_of_le_of_lt (measure_mono ?_)
    (_root_.GD.N0232.N0719.N0872.d010705 hn sizes hsizes beta location
      scales hscales j G hG)
  rintro omega ⟨hpos, homega⟩
  have hh := congrFun hext ⟨_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega), hpos⟩
  exact homega.trans hh.symm




theorem d010709
    {n : ℕ} (hn : 1 ≤ n) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ L U : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) → ℝ,
      Measurable L ∧ Measurable U ∧ (∀ s, L s ≤ U s) ∧
      (∀ (location : ℝ) (scales : Fin (n + 1) → ℝ),
        (∀ i, 0 < scales i) →
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
          {omega | L (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤ location ∧
            location ≤ U (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} =
          ENNReal.ofReal (1 - alpha)) ∧
      (∀ (location : ℝ) (scales : Fin (n + 1) → ℝ),
        (∀ i, 0 < scales i) →
        ∀ (j : Fin (n + 1)) (F : _root_.GD.N0232.N0719.N0900.d009096 n → ℝ × ℝ), Measurable F →
          ¬ (fun omega => (L (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega),
              U (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)))
            =ᵐ[_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
              (fun omega => F (_root_.GD.N0232.N0719.N0872.d010702 j (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)))) := by
  let beta := _root_.GD.N0232.N0719.N1003.d010685 n alpha
  refine ⟨_root_.GD.N0232.N0719.N1003.d010647 sizes beta, _root_.GD.N0232.N0719.N1003.d010648 sizes beta,
    _root_.GD.N0232.N0719.N1003.d010659 _ _, _root_.GD.N0232.N0719.N1003.d010660 _ _,
    _root_.GD.N0232.N0719.N1003.d010654 _ _, ?_, ?_⟩
  · intro location scales hscales
    exact _root_.GD.N0232.N0719.N1003.d010690 sizes hsizes ha0 ha1 location scales hscales
  · intro location scales hscales j F hF hfactor
    apply _root_.GD.N0232.N0719.N0872.d010704 hn sizes hsizes beta location scales
      hscales j (fun s => (F s).1) hF.fst
    filter_upwards [hfactor] with omega homega
    exact congrArg Prod.fst homega

#print axioms _root_.GD.N0232.N0719.N0872.d010694
#print axioms _root_.GD.N0232.N0719.N0872.d010695
#print axioms _root_.GD.N0232.N0719.N0872.d010701
#print axioms _root_.GD.N0232.N0719.N0872.d010704
#print axioms _root_.GD.N0232.N0719.N0872.d010705
#print axioms _root_.GD.N0232.N0719.N0872.d010708
#print axioms _root_.GD.N0232.N0719.N0872.d010709

end

end GD.N0232.N0719.N0872
