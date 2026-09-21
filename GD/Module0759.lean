import GD.Module0758
import GD.Module0634

















open MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N1010

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0946



private theorem d011413 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009101 0 1 s = s := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    change 0 + 1 * s.mean i = s.mean i
    ring
  · funext i
    change 1 ^ 2 * s.meanVariance i = s.meanVariance i
    ring

private theorem d011414 {k : ℕ}
    (g h : _root_.GD.N0232.N0719.N0946.d009229) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009101 (g * h).shift (g * h).d009239 s =
      _root_.GD.N0232.N0719.N0900.d009101 g.shift g.d009239
        (_root_.GD.N0232.N0719.N0900.d009101 h.shift h.d009239 s) := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    change
      (g * h).shift + (g * h).d009239 * s.mean i =
        g.shift + g.d009239 * (h.shift + h.d009239 * s.mean i)
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009235, _root_.GD.N0232.N0719.N0946.d009229.d009243]
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009239]
    ring
  · funext i
    change
      (g * h).d009239 ^ 2 * s.meanVariance i =
        g.d009239 ^ 2 * (h.d009239 ^ 2 * s.meanVariance i)
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009243]
    ring

instance d011415 {k : ℕ} :
    SemigroupAction _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0719.N0900.d009096 k) where
  smul g s := _root_.GD.N0232.N0719.N0900.d009101 g.shift g.d009239 s
  mul_smul := _root_.GD.N0232.N0719.N1010.d011414

@[simp] theorem d011416 {k : ℕ}
    (g : _root_.GD.N0232.N0719.N0946.d009229) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    g • s = _root_.GD.N0232.N0719.N0900.d009101 g.shift g.d009239 s := rfl

instance d011417 {k : ℕ} : MulAction _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0719.N0900.d009096 k) where
  one_smul s := by
    rw [_root_.GD.N0232.N0719.N1010.d011416]
    simpa using _root_.GD.N0232.N0719.N1010.d011413 s

instance {k : ℕ} : MeasurableSMul₂ _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0719.N0900.d009096 k) where
  measurable_smul := by
    rw [measurable_comap_iff]
    simp only [Function.comp_apply, _root_.GD.N0232.N0719.N1010.d011416, _root_.GD.N0232.N0719.N0900.d009097]
    change Measurable
      (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0900.d009096 k ↦
        ((fun i ↦ z.1.shift + z.1.d009239 * z.2.mean i),
          fun i ↦ z.1.d009239 ^ 2 * z.2.meanVariance i))
    have hmean : Measurable
        (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0900.d009096 k ↦
          fun i ↦ z.1.shift + z.1.d009239 * z.2.mean i) := by
      apply measurable_pi_lambda
      intro i
      exact (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
        ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul
          ((_root_.GD.N0232.N0719.N0900.d009099 i).comp measurable_snd))
    have hvariance : Measurable
        (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0900.d009096 k ↦
          fun i ↦ z.1.d009239 ^ 2 * z.2.meanVariance i) := by
      apply measurable_pi_lambda
      intro i
      exact ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).pow_const 2).mul
        ((_root_.GD.N0232.N0719.N0900.d009100 i).comp measurable_snd)
    exact hmean.prodMk hvariance



theorem d011418
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 0 < sizes i)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009104 k sizes (g • omega) = g • _root_.GD.N0232.N0719.N0900.d009104 k sizes omega := by
  simpa [_root_.GD.N0232.N0719.N0946.d009258,
    _root_.GD.N0232.N0719.N1010.d011416] using
    _root_.GD.N0232.N0719.N0900.d009139 hsizes g.shift g.d009239 omega



theorem d011419
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 0 < sizes i)
    (value : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (hvalue : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (s : _root_.GD.N0232.N0719.N0900.d009096 k) ↦ g • s)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) value) :
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
      (value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) := by
  intro g omega
  simp only [Function.comp_apply, _root_.GD.N0232.N0719.N1010.d011418 hsizes g omega]
  exact hvalue g (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)





noncomputable def d011420 (k : ℕ) (sizes : Fin k → ℕ) :
    Measure (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  (_root_.GD.N0232.N0719.d009182 k sizes).map (_root_.GD.N0232.N0719.N0900.d009104 k sizes)

instance (k : ℕ) (sizes : Fin k → ℕ) :
    SFinite (_root_.GD.N0232.N0719.N1010.d011420 k sizes) := by
  unfold _root_.GD.N0232.N0719.N1010.d011420
  infer_instance



theorem d011421
    {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (s : _root_.GD.N0232.N0719.N0900.d009096 k) ↦ g • s)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
      (_root_.GD.N0232.N0719.N0900.d009110 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  intro g s
  simpa [_root_.GD.N0232.N0719.N1010.d011416, _root_.GD.N0232.N0719.N0946.d009229.d009244] using
    _root_.GD.N0232.N0719.N0900.d009145 hk g.shift g.d009241 s



theorem d011422
    {k : ℕ} {sizes : Fin k → ℕ}
    (value : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
          value (g • _root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • value (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦ value (g • s)) =ᵐ[_root_.GD.N0232.N0719.N1010.d011420 k sizes]
        fun s ↦ g • value s := by
  intro g
  let E : Set (_root_.GD.N0232.N0719.N0900.d009096 k) :=
    {s | value (g • s) = g • value s}
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      (hvalue.comp (measurable_const.smul measurable_id))
      (measurable_const.smul hvalue)
  have hmap := (ae_map_iff
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes).aemeasurable hE).2 (hcov g)
  change ∀ᵐ s ∂_root_.GD.N0232.N0719.N1010.d011420 k sizes,
    value (_root_.GD.N0232.N0719.N0900.d009101 g.shift g.d009239 s) =
      g.shift + g.d009239 * value s
  simpa only [_root_.GD.N0232.N0719.N1010.d011420, _root_.GD.N0232.N0719.N1010.d011416,
    _root_.GD.N0232.N0719.N0946.d009229.d009244] using hmap







theorem d011423
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 0 < k)
    (value : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
          value (g • _root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • value (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        (repaired ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
          value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (s : _root_.GD.N0232.N0719.N0900.d009096 k) ↦ g • s)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  rcases
      _root_.GD.N0230.N0605.d000343
        (G := _root_.GD.N0232.N0719.N0946.d009229) (X := _root_.GD.N0232.N0719.N0900.d009096 k)
        (_root_.GD.N0232.N0719.N1010.d011420 k sizes) _root_.GD.N0232.N0719.N0946.d009229.d009254
        value _root_.GD.N0232.N0719.N0900.d009110 hvalue _root_.GD.N0232.N0719.N0900.d009121
        (_root_.GD.N0232.N0719.N1010.d011421 hk)
        (_root_.GD.N0232.N0719.N1010.d011422 value hvalue hcov)
        _root_.GD.N0232.N0719.N0946.d009229.d009257 with
    ⟨repaired, hrepaired, hrefSummary, hequiv⟩
  refine ⟨repaired, hrepaired, ?_, hequiv⟩
  intro theta
  have hrefRaw :
      (repaired ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
    have hset : MeasurableSet {s : _root_.GD.N0232.N0719.N0900.d009096 k | repaired s = value s} :=
      measurableSet_eq_fun hrepaired hvalue
    exact (ae_map_iff (_root_.GD.N0232.N0719.N0900.d009115 k sizes).aemeasurable hset).1
      hrefSummary
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le hrefRaw




theorem d011424
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (value : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
          value (g • _root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • value (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        (repaired ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
          value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
        (repaired ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) := by
  rcases _root_.GD.N0232.N0719.N1010.d011423 hk value hvalue hcov with
    ⟨repaired, hrepaired, hall, hequiv⟩
  exact ⟨repaired, hrepaired, hall,
    _root_.GD.N0232.N0719.N1010.d011419 hsizes repaired hequiv⟩

end

end N1010
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N1010.d011423
#print axioms _root_.GD.N0232.N0719.N1010.d011424
