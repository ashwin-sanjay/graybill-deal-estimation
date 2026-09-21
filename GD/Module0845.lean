import GD.Module0844

set_option autoImplicit false
set_option warningAsError true


















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0790

noncomputable section

open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0788
  _root_.GD.N0228.N0547.N0784
  _root_.GD.N0228.N0547.N0786
  _root_.GD.N0228.N0547.N0785
  _root_.GD.N0228.N0547.N0797
  _root_.GD.N0228.N0547.N0789

universe uα uβ uγ uδ


def d012884
    (α : Type uα) (β : Type uβ) (γ : Type uγ) (δ : Type uδ)
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] :
    ((α × β) × (γ × δ)) → ((α × γ) × (β × δ)) :=
  (MeasurableEquiv.prodAssoc.symm :
      (α × (γ × (β × δ))) ≃ᵐ ((α × γ) × (β × δ))) ∘
    Prod.map id (MeasurableEquiv.prodAssoc :
      ((γ × β) × δ) ≃ᵐ (γ × (β × δ))) ∘
    Prod.map id (Prod.map
      (MeasurableEquiv.prodComm : (β × γ) ≃ᵐ (γ × β)) id) ∘
    Prod.map id (MeasurableEquiv.prodAssoc.symm :
      (β × (γ × δ)) ≃ᵐ ((β × γ) × δ)) ∘
    (MeasurableEquiv.prodAssoc :
      ((α × β) × (γ × δ)) ≃ᵐ (α × (β × (γ × δ))))

@[fun_prop]
theorem d012885
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (_root_.GD.N0228.N0547.N0790.d012884 α β γ δ) := by
  unfold _root_.GD.N0228.N0547.N0790.d012884
  fun_prop


theorem d012886
    {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (muα : Measure α) (muβ : Measure β)
    (muγ : Measure γ) (muδ : Measure δ)
    [SFinite muα] [SFinite muβ] [SFinite muγ] [SFinite muδ] :
    MeasurePreserving (_root_.GD.N0228.N0547.N0790.d012884 α β γ δ)
      ((muα.prod muβ).prod (muγ.prod muδ))
      ((muα.prod muγ).prod (muβ.prod muδ)) := by
  let h₁ := measurePreserving_prodAssoc muα muβ (muγ.prod muδ)
  let h₂inner : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        (β × (γ × δ)) ≃ᵐ ((β × γ) × δ))
      (muβ.prod (muγ.prod muδ)) ((muβ.prod muγ).prod muδ) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc muβ muγ muδ)
  let h₂ := (MeasurePreserving.id muα).prod h₂inner
  let hswap : MeasurePreserving
      (MeasurableEquiv.prodComm : (β × γ) ≃ᵐ (γ × β))
      (muβ.prod muγ) (muγ.prod muβ) :=
    Measure.measurePreserving_swap
  let h₃inner := hswap.prod (MeasurePreserving.id muδ)
  let h₃ := (MeasurePreserving.id muα).prod h₃inner
  let h₄ := (MeasurePreserving.id muα).prod
    (measurePreserving_prodAssoc muγ muβ muδ)
  let h₅ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        (α × (γ × (β × δ))) ≃ᵐ ((α × γ) × (β × δ)))
      (muα.prod (muγ.prod (muβ.prod muδ)))
      ((muα.prod muγ).prod (muβ.prod muδ)) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc muα muγ (muβ.prod muδ))
  let hcomp := h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))
  simpa only [_root_.GD.N0228.N0547.N0790.d012884] using hcomp



def d012887 (d : ℕ) : Measure (ℝ × ℝ) :=
  if d = 1 then
    _root_.GD.N0228.N0547.N0788.d006356.prod (Measure.dirac (1 : ℝ))
  else
    _root_.GD.N0228.N0547.N0788.d006356.prod
      (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2))



theorem d012888
    {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 d) := by
  by_cases hboundary : d = 1
  · rw [_root_.GD.N0228.N0547.N0790.d012887, if_pos hboundary]
    infer_instance
  · have hdLarge : 1 < d := by omega
    have hshape : 0 < ((d : ℝ) - 1) / 2 := by
      have hdR : (1 : ℝ) < d := by exact_mod_cast hdLarge
      positivity
    rw [_root_.GD.N0228.N0547.N0790.d012887, if_neg hboundary]
    letI : IsProbabilityMeasure
        (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)) :=
      isProbabilityMeasureBeta (by norm_num) hshape
    infer_instance


theorem d012889
    {d : ℕ} (hd : 0 < d) : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d) := by
  unfold _root_.GD.N0228.N0547.N0778.d009365
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)


def d012890 (z : (ℝ × ℝ) × ℝ) : ℝ × (ℝ × ℝ) :=
  (z.1.1, (z.1.2, z.2))

@[fun_prop]
theorem d012891 : Measurable _root_.GD.N0228.N0547.N0790.d012890 := by
  unfold _root_.GD.N0228.N0547.N0790.d012890
  fun_prop



theorem d012892
    {d : ℕ} (hd : 0 < d) :
    ((_root_.GD.N0228.N0547.N0790.d012887 d).prod (_root_.GD.N0228.N0547.N0778.d009365 d)).map _root_.GD.N0228.N0547.N0790.d012890 =
      _root_.GD.N0228.N0547.N0785.d012843 d := by
  by_cases hboundary : d = 1
  · subst d
    letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) :=
      _root_.GD.N0228.N0547.N0790.d012889 (by norm_num)
    rw [_root_.GD.N0228.N0547.N0790.d012887, _root_.GD.N0228.N0547.N0785.d012843,
      if_pos rfl, if_pos rfl]
    unfold _root_.GD.N0228.N0547.N0785.d012840
    exact (measurePreserving_prodAssoc _root_.GD.N0228.N0547.N0788.d006356
      (Measure.dirac (1 : ℝ)) (_root_.GD.N0228.N0547.N0778.d009365 1)).map_eq
  · rw [_root_.GD.N0228.N0547.N0790.d012887, _root_.GD.N0228.N0547.N0785.d012843,
      if_neg hboundary, if_neg hboundary]
    have hdLarge : 1 < d := by omega
    have hshape : 0 < ((d : ℝ) - 1) / 2 := by
      have hdR : (1 : ℝ) < d := by exact_mod_cast hdLarge
      positivity
    letI : IsProbabilityMeasure
        (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2)) :=
      isProbabilityMeasureBeta (by norm_num) hshape
    letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 d) :=
      _root_.GD.N0228.N0547.N0790.d012889 hd
    unfold _root_.GD.N0228.N0547.N0786.d012835
    exact (measurePreserving_prodAssoc _root_.GD.N0228.N0547.N0788.d006356
      (betaMeasure (1 / 2) (((d : ℝ) - 1) / 2))
      (_root_.GD.N0228.N0547.N0778.d009365 d)).map_eq


def d012893 (r s : ℕ) :
    Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (_root_.GD.N0228.N0547.N0790.d012887 r).prod (_root_.GD.N0228.N0547.N0790.d012887 s)


def d012894 (r s : ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 1).prod ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))


def d012895 :
    ((ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) →
      ℝ × ((((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × ℝ))) :=
  Prod.map id (_root_.GD.N0228.N0547.N0790.d012884 (ℝ × ℝ) (ℝ × ℝ) ℝ ℝ) ∘
    Prod.map id Prod.swap ∘
    (MeasurableEquiv.prodAssoc :
      ((ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) ≃ᵐ
        ℝ × ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))))

@[fun_prop]
theorem d012896 : Measurable _root_.GD.N0228.N0547.N0790.d012895 := by
  unfold _root_.GD.N0228.N0547.N0790.d012895
  fun_prop


def d012897 :
    (ℝ × ((((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × ℝ)))) →
      ℝ × ((ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ))) :=
  Prod.map id (Prod.map _root_.GD.N0228.N0547.N0790.d012890 _root_.GD.N0228.N0547.N0790.d012890)

@[fun_prop]
theorem d012898 : Measurable _root_.GD.N0228.N0547.N0790.d012897 := by
  unfold _root_.GD.N0228.N0547.N0790.d012897
  fun_prop



def d012899 :
    ((ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) →
      ℝ × ((ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ))) :=
  _root_.GD.N0228.N0547.N0790.d012897 ∘ _root_.GD.N0228.N0547.N0790.d012895

@[fun_prop]
theorem d012900 : Measurable _root_.GD.N0228.N0547.N0790.d012899 := by
  unfold _root_.GD.N0228.N0547.N0790.d012899
  fun_prop



theorem d012901
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) :
    ((_root_.GD.N0228.N0547.N0790.d012894 r s).prod (_root_.GD.N0228.N0547.N0790.d012893 r s)).map
        _root_.GD.N0228.N0547.N0790.d012899 =
      (gaussianReal 0 1).prod
        ((_root_.GD.N0228.N0547.N0785.d012843 r).prod
          (_root_.GD.N0228.N0547.N0785.d012843 s)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hspos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hspos
  let h₁ := measurePreserving_prodAssoc (gaussianReal 0 1)
    ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))
    ((_root_.GD.N0228.N0547.N0790.d012887 r).prod (_root_.GD.N0228.N0547.N0790.d012887 s))
  let h₂ := (MeasurePreserving.id (gaussianReal 0 1)).prod
    (Measure.measurePreserving_swap : MeasurePreserving
      MeasurableEquiv.prodComm
      (((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)).prod
        ((_root_.GD.N0228.N0547.N0790.d012887 r).prod (_root_.GD.N0228.N0547.N0790.d012887 s)))
      (((_root_.GD.N0228.N0547.N0790.d012887 r).prod (_root_.GD.N0228.N0547.N0790.d012887 s)).prod
        ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))))
  let h₃ := (MeasurePreserving.id (gaussianReal 0 1)).prod
    (_root_.GD.N0228.N0547.N0790.d012886
      (_root_.GD.N0228.N0547.N0790.d012887 r) (_root_.GD.N0228.N0547.N0790.d012887 s)
      (_root_.GD.N0228.N0547.N0778.d009365 r) (_root_.GD.N0228.N0547.N0778.d009365 s))
  let hreorder := h₃.comp (h₂.comp h₁)
  let hr : MeasurePreserving _root_.GD.N0228.N0547.N0790.d012890
      ((_root_.GD.N0228.N0547.N0790.d012887 r).prod (_root_.GD.N0228.N0547.N0778.d009365 r))
      (_root_.GD.N0228.N0547.N0785.d012843 r) :=
    ⟨_root_.GD.N0228.N0547.N0790.d012891, _root_.GD.N0228.N0547.N0790.d012892 hrpos⟩
  let hs : MeasurePreserving _root_.GD.N0228.N0547.N0790.d012890
      ((_root_.GD.N0228.N0547.N0790.d012887 s).prod (_root_.GD.N0228.N0547.N0778.d009365 s))
      (_root_.GD.N0228.N0547.N0785.d012843 s) :=
    ⟨_root_.GD.N0228.N0547.N0790.d012891, _root_.GD.N0228.N0547.N0790.d012892 hspos⟩
  let hattach := (MeasurePreserving.id (gaussianReal 0 1)).prod (hr.prod hs)
  have hcomp := hattach.comp hreorder
  simpa only [_root_.GD.N0228.N0547.N0790.d012894, _root_.GD.N0228.N0547.N0790.d012893, _root_.GD.N0228.N0547.N0790.d012899,
    _root_.GD.N0228.N0547.N0790.d012897, _root_.GD.N0228.N0547.N0790.d012895] using hcomp.map_eq


def d012902 (rho p : ℝ) :
    Set (ℝ × ((ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ)))) :=
  {z | |z.1| ≤ _root_.GD.N0228.N0547.N0782.d003367 p *
    |_root_.GD.N0228.N0547.N0789.d012877 rho z.2|}

theorem d012903 (rho p : ℝ) :
    MeasurableSet (_root_.GD.N0228.N0547.N0790.d012902 rho p) := by
  change MeasurableSet
    ((_root_.GD.N0228.N0547.N0789.d012880 rho) ⁻¹'
      _root_.GD.N0228.N0547.N0782.d003372
        (_root_.GD.N0228.N0547.N0782.d003367 p))
  exact (_root_.GD.N0228.N0547.N0782.d003375 _).preimage
    (_root_.GD.N0228.N0547.N0789.d012881 rho)



def d012904 (rho p : ℝ) :
    Set ((ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
  _root_.GD.N0228.N0547.N0790.d012899 ⁻¹' _root_.GD.N0228.N0547.N0790.d012902 rho p

theorem d012905 (rho p : ℝ) :
    MeasurableSet (_root_.GD.N0228.N0547.N0790.d012904 rho p) :=
  (_root_.GD.N0228.N0547.N0790.d012903 rho p).preimage
    _root_.GD.N0228.N0547.N0790.d012900



def d012906 (r s : ℕ) (rho p : ℝ)
    (base : ℝ × (ℝ × ℝ)) : ℝ≥0∞ :=
  _root_.GD.N0228.N0547.N0790.d012893 r s
    (Prod.mk base ⁻¹' _root_.GD.N0228.N0547.N0790.d012904 rho p)



theorem d012907
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) :
    IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012893 r s) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hspos
  unfold _root_.GD.N0228.N0547.N0790.d012893
  infer_instance



theorem d012908
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (rho p : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0790.d012906 r s rho p) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hspos
  unfold _root_.GD.N0228.N0547.N0790.d012906 _root_.GD.N0228.N0547.N0790.d012893
  exact measurable_measure_prodMk_left
    (_root_.GD.N0228.N0547.N0790.d012905 rho p)


theorem d012909
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (rho p : ℝ)
    (base : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0228.N0547.N0790.d012906 r s rho p base ≤ 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012893 r s) :=
    _root_.GD.N0228.N0547.N0790.d012907 hrpos hspos
  calc
    _root_.GD.N0228.N0547.N0790.d012906 r s rho p base ≤
        _root_.GD.N0228.N0547.N0790.d012893 r s Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ


def d012910 (r s : ℕ) (rho p : ℝ)
    (base : ℝ × (ℝ × ℝ)) : ℝ :=
  (_root_.GD.N0228.N0547.N0790.d012906 r s rho p base).toReal


theorem d012911
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (rho p : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0790.d012910 r s rho p) :=
  (_root_.GD.N0228.N0547.N0790.d012908 hrpos hspos rho p).ennreal_toReal


theorem d012912
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (rho p : ℝ)
    (base : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0228.N0547.N0790.d012910 r s rho p base ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · rw [_root_.GD.N0228.N0547.N0790.d012910, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (_root_.GD.N0228.N0547.N0790.d012909 hrpos hspos rho p base)



theorem d012913
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s)
    {rho p : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ base, _root_.GD.N0228.N0547.N0790.d012906 r s rho p base
        ∂(_root_.GD.N0228.N0547.N0790.d012894 r s) = ENNReal.ofReal p := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hspos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012893 r s) :=
    _root_.GD.N0228.N0547.N0790.d012907 hrpos hspos
  calc
    ∫⁻ base, _root_.GD.N0228.N0547.N0790.d012906 r s rho p base
        ∂(_root_.GD.N0228.N0547.N0790.d012894 r s) =
        ((_root_.GD.N0228.N0547.N0790.d012894 r s).prod (_root_.GD.N0228.N0547.N0790.d012893 r s))
          (_root_.GD.N0228.N0547.N0790.d012904 rho p) := by
      rw [Measure.prod_apply
        (_root_.GD.N0228.N0547.N0790.d012905 rho p)]
      rfl
    _ = (((_root_.GD.N0228.N0547.N0790.d012894 r s).prod (_root_.GD.N0228.N0547.N0790.d012893 r s)).map
          _root_.GD.N0228.N0547.N0790.d012899) (_root_.GD.N0228.N0547.N0790.d012902 rho p) := by
      rw [Measure.map_apply _root_.GD.N0228.N0547.N0790.d012900
        (_root_.GD.N0228.N0547.N0790.d012903 rho p)]
      rfl
    _ = ((gaussianReal 0 1).prod
          ((_root_.GD.N0228.N0547.N0785.d012843 r).prod
            (_root_.GD.N0228.N0547.N0785.d012843 s)))
          (_root_.GD.N0228.N0547.N0790.d012902 rho p) := by
      rw [_root_.GD.N0228.N0547.N0790.d012901 hrpos hspos]
    _ = ENNReal.ofReal p := by
      simpa only [_root_.GD.N0228.N0547.N0790.d012902] using
        _root_.GD.N0228.N0547.N0789.d012883 hrpos hspos hrho0 hrho1 hp0 hp1



theorem d012914
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (rho p : ℝ)
    (base : ℝ × (ℝ × ℝ)) :
    ENNReal.ofReal (_root_.GD.N0228.N0547.N0790.d012910 r s rho p base) =
      _root_.GD.N0228.N0547.N0790.d012906 r s rho p base := by
  rw [_root_.GD.N0228.N0547.N0790.d012910, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (_root_.GD.N0228.N0547.N0790.d012909 hrpos hspos rho p base)



theorem d012915
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s)
    {rho p : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ base, ENNReal.ofReal (_root_.GD.N0228.N0547.N0790.d012910 r s rho p base)
        ∂(_root_.GD.N0228.N0547.N0790.d012894 r s) = ENNReal.ofReal p := by
  simp_rw [_root_.GD.N0228.N0547.N0790.d012914 hrpos hspos rho p]
  exact _root_.GD.N0228.N0547.N0790.d012913
    hrpos hspos hrho0 hrho1 hp0 hp1

end

end GD.N0228.N0547.N0790

#print axioms _root_.GD.N0228.N0547.N0790.d012886
#print axioms _root_.GD.N0228.N0547.N0790.d012892
#print axioms _root_.GD.N0228.N0547.N0790.d012901
#print axioms _root_.GD.N0228.N0547.N0790.d012911
#print axioms _root_.GD.N0228.N0547.N0790.d012912
#print axioms _root_.GD.N0228.N0547.N0790.d012913
#print axioms _root_.GD.N0228.N0547.N0790.d012915
