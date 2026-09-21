import GD.Module0281
import GD.Module0643
















open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0719.N0983

open _root_.GD.N0232.N0720.N1290 (d004131)

noncomputable section

variable (k : ℕ)


def d009709 := {p : Fin k → _root_.GD.N0232.N0720.N1290.d004131 // ∑ i, (p i : ℝ) = 1}

instance : TopologicalSpace (_root_.GD.N0232.N0719.N0983.d009709 k) := inferInstanceAs (TopologicalSpace
  {p : Fin k → _root_.GD.N0232.N0720.N1290.d004131 // ∑ i, (p i : ℝ) = 1})

instance : MetricSpace (_root_.GD.N0232.N0719.N0983.d009709 k) := inferInstanceAs (MetricSpace
  {p : Fin k → _root_.GD.N0232.N0720.N1290.d004131 // ∑ i, (p i : ℝ) = 1})

instance : MeasurableSpace (_root_.GD.N0232.N0719.N0983.d009709 k) := borel (_root_.GD.N0232.N0719.N0983.d009709 k)
instance : BorelSpace (_root_.GD.N0232.N0719.N0983.d009709 k) := ⟨rfl⟩

instance : CompactSpace (_root_.GD.N0232.N0719.N0983.d009709 k) := by
  apply isCompact_iff_compactSpace.mp
  exact (isClosed_eq (continuous_finsetSum _ fun i _ =>
    continuous_subtype_val.comp (continuous_apply i)) continuous_const).isCompact

instance : SecondCountableTopology (_root_.GD.N0232.N0719.N0983.d009709 k) :=
  inferInstanceAs (SecondCountableTopology
    {p : Fin k → _root_.GD.N0232.N0720.N1290.d004131 // ∑ i, (p i : ℝ) = 1})

variable {k}

def d009710 (i : Fin k) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : _root_.GD.N0232.N0720.N1290.d004131 := p.val i

theorem d009711 (i : Fin k) : Continuous (_root_.GD.N0232.N0719.N0983.d009710 i) :=
  (continuous_apply i).comp continuous_subtype_val

theorem d009712 (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) = 1 := p.property

def d009713 (y : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ℝ :=
  ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i


def d009714 (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ℝ :=
  ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * r i +
    (1 / 2 : ℝ) * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2

theorem d009715 (y : Fin k → ℝ) : Continuous (_root_.GD.N0232.N0719.N0983.d009713 y) := by
  exact continuous_finsetSum _ fun i _ =>
    (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).mul continuous_const

theorem d009716 (y r : Fin k → ℝ) : Continuous (_root_.GD.N0232.N0719.N0983.d009714 y r) := by
  apply Continuous.add
  · exact continuous_finsetSum _ fun i _ =>
      (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).mul continuous_const
  · exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).mul
        ((continuous_const.sub (_root_.GD.N0232.N0719.N0983.d009715 y)).pow 2))

theorem d009717 (y r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    0 ≤ _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1 (hr i)
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1 (sq_nonneg _))

theorem d009718 (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    0 < _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  have hex : ∃ i, 0 < (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) := by
    by_contra! h
    have hz : ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) ≤ 0 := Finset.sum_nonpos fun i _ => h i
    rw [_root_.GD.N0232.N0719.N0983.d009712] at hz
    norm_num at hz
  obtain ⟨j, hj⟩ := hex
  have hfirst : 0 < ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * r i := by
    apply Finset.sum_pos'
    · exact fun i _ => mul_nonneg (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1 (hr i).le
    · exact ⟨j, Finset.mem_univ j, mul_pos hj (hr j)⟩
  exact add_pos_of_pos_of_nonneg hfirst (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ => mul_nonneg (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1 (sq_nonneg _)))


theorem d009719 (shape y t : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 y (fun i => shape i * t i) p =
      _root_.GD.N0232.N0719.N0928.d009407 shape
        (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)) y t := by
  unfold _root_.GD.N0232.N0719.N0983.d009714 _root_.GD.N0232.N0719.N0928.d009407
    _root_.GD.N0232.N0719.N0928.d009406
    _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0719.N0983.d009713
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def d009720 (q : ℝ) (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ℝ := _root_.GD.N0232.N0719.N0983.d009714 y r p ^ (-q)

theorem d009721 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) :
    Continuous (_root_.GD.N0232.N0719.N0983.d009720 q y r) :=
  (_root_.GD.N0232.N0719.N0983.d009716 y r).rpow_const (fun p => Or.inl (_root_.GD.N0232.N0719.N0983.d009718 y r hr p).ne')

theorem d009722 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    0 < _root_.GD.N0232.N0719.N0983.d009720 q y r p := Real.rpow_pos_of_pos (_root_.GD.N0232.N0719.N0983.d009718 y r hr p) _

def d009723 (q : ℝ) (y r : Fin k → ℝ) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) : ℝ :=
  ∫ p, _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂mu

def d009724 (q : ℝ) (y r : Fin k → ℝ) (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) : ℝ :=
  (∫ p, _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂mu) / _root_.GD.N0232.N0719.N0983.d009723 q y r mu

def d009725 (q : ℝ) (y r : Fin k → ℝ)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (i : Fin k) : ℝ :=
  (∫ p, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂mu) / _root_.GD.N0232.N0719.N0983.d009723 q y r mu

theorem d009726 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure mu] : Integrable (_root_.GD.N0232.N0719.N0983.d009720 q y r) mu :=
  (_root_.GD.N0232.N0719.N0983.d009721 q y r hr).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

theorem d009727 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure mu] (i : Fin k) :
    Integrable (fun p => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p) mu :=
  ((continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).mul
    (_root_.GD.N0232.N0719.N0983.d009721 q y r hr)).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

theorem d009728 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu] : 0 < _root_.GD.N0232.N0719.N0983.d009723 q y r mu := by
  have hs : Function.support (_root_.GD.N0232.N0719.N0983.d009720 q y r) = univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (_root_.GD.N0232.N0719.N0983.d009722 q y r hr p).ne'
  rw [_root_.GD.N0232.N0719.N0983.d009723, integral_pos_iff_support_of_nonneg
    (fun p => (_root_.GD.N0232.N0719.N0983.d009722 q y r hr p).le) (_root_.GD.N0232.N0719.N0983.d009726 q y r hr mu), hs]
  simp

theorem d009729 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu] :
    ∑ i, _root_.GD.N0232.N0719.N0983.d009725 q y r mu i = 1 := by
  unfold _root_.GD.N0232.N0719.N0983.d009725
  rw [← Finset.sum_div, ← integral_finsetSum _
    (fun i _ => _root_.GD.N0232.N0719.N0983.d009727 q y r hr mu i)]
  have h : (fun p : _root_.GD.N0232.N0719.N0983.d009709 k => ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p) =
      _root_.GD.N0232.N0719.N0983.d009720 q y r := by
    funext p
    rw [← Finset.sum_mul, _root_.GD.N0232.N0719.N0983.d009712, one_mul]
  rw [h]
  exact div_self (_root_.GD.N0232.N0719.N0983.d009728 q y r hr mu).ne'


theorem d009730 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsFiniteMeasure mu] :
    _root_.GD.N0232.N0719.N0983.d009724 q y r mu = ∑ i, _root_.GD.N0232.N0719.N0983.d009725 q y r mu i * y i := by
  unfold _root_.GD.N0232.N0719.N0983.d009724 _root_.GD.N0232.N0719.N0983.d009725 _root_.GD.N0232.N0719.N0983.d009713
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ =>
    ((_root_.GD.N0232.N0719.N0983.d009727 q y r hr mu i).mul_const (y i)).congr
      (ae_of_all _ fun _ => by ring))]
  simp_rw [show ∀ i, (fun p : _root_.GD.N0232.N0719.N0983.d009709 k => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i * _root_.GD.N0232.N0719.N0983.d009720 q y r p) =
      (fun p => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p * y i) by intro i; funext p; ring]
  simp_rw [integral_mul_const]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def d009731 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) : C(_root_.GD.N0232.N0719.N0983.d009709 k, ℝ) :=
  ⟨_root_.GD.N0232.N0719.N0983.d009720 q y r, _root_.GD.N0232.N0719.N0983.d009721 q y r hr⟩

private def d009732 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) : C(_root_.GD.N0232.N0719.N0983.d009709 k, ℝ) :=
  ⟨fun p => _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p,
    (_root_.GD.N0232.N0719.N0983.d009715 y).mul (_root_.GD.N0232.N0719.N0983.d009721 q y r hr)⟩

private def d009733 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (i : Fin k) : C(_root_.GD.N0232.N0719.N0983.d009709 k, ℝ) :=
  ⟨fun p => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p,
    (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).mul (_root_.GD.N0232.N0719.N0983.d009721 q y r hr)⟩

theorem d009734 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i) :
    Continuous (fun mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k) =>
      _root_.GD.N0232.N0719.N0983.d009724 q y r (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) := by
  exact (ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0719.N0983.d009732 q y r hr)).div
    (ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0719.N0983.d009731 q y r hr))
    (fun mu => (_root_.GD.N0232.N0719.N0983.d009728 q y r hr (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))).ne')

theorem d009735 (q : ℝ) (y r : Fin k → ℝ)
    (hr : ∀ i, 0 < r i) (i : Fin k) :
    Continuous (fun mu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k) =>
      _root_.GD.N0232.N0719.N0983.d009725 q y r (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) i) := by
  exact (ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0719.N0983.d009733 q y r hr i)).div
    (ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0719.N0983.d009731 q y r hr))
    (fun mu => (_root_.GD.N0232.N0719.N0983.d009728 q y r hr (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))).ne')



theorem d009736 (q : ℝ)
    (mu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k)) :
    ∃ (nu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k)) (psi : ℕ → ℕ), StrictMono psi ∧
      ∀ (y r : Fin k → ℝ), (∀ i, 0 < r i) →
        Tendsto (fun j => _root_.GD.N0232.N0719.N0983.d009724 q y r (mu (psi j) : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) atTop
          (𝓝 (_root_.GD.N0232.N0719.N0983.d009724 q y r (nu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)))) ∧
        ∀ i, Tendsto (fun j => _root_.GD.N0232.N0719.N0983.d009725 q y r (mu (psi j) : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) i)
          atTop (𝓝 (_root_.GD.N0232.N0719.N0983.d009725 q y r (nu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) i)) := by
  obtain ⟨nu, psi, hpsi, hweak⟩ := SeqCompactSpace.tendsto_subseq mu
  refine ⟨nu, psi, hpsi, ?_⟩
  intro y r hr
  exact ⟨((_root_.GD.N0232.N0719.N0983.d009734 q y r hr).tendsto nu).comp hweak,
    fun i => ((_root_.GD.N0232.N0719.N0983.d009735 q y r hr i).tendsto nu).comp hweak⟩



theorem d009737
    {X : Type*} [MeasurableSpace X] (rho : Measure X)
    (q : ℝ) (y r : X → Fin k → ℝ) (g : X → ℝ)
    (mu : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (hr : ∀ᵐ x ∂rho, ∀ i, 0 < r x i)
    (hlim : ∀ᵐ x ∂rho, Tendsto
      (fun j => _root_.GD.N0232.N0719.N0983.d009724 q (y x) (r x) (mu j : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) atTop (𝓝 (g x))) :
    ∃ nu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      g =ᵐ[rho] fun x => _root_.GD.N0232.N0719.N0983.d009724 q (y x) (r x) (nu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  obtain ⟨nu, psi, hpsi, hweak⟩ := _root_.GD.N0232.N0719.N0983.d009736 q mu
  refine ⟨nu, ?_⟩
  filter_upwards [hr, hlim] with x hrx hx
  exact tendsto_nhds_unique (hx.comp hpsi.tendsto_atTop) (hweak (y x) (r x) hrx).1

end

end GD.N0232.N0719.N0983

#print axioms _root_.GD.N0232.N0719.N0983.d009719
#print axioms _root_.GD.N0232.N0719.N0983.d009730
#print axioms _root_.GD.N0232.N0719.N0983.d009736
#print axioms _root_.GD.N0232.N0719.N0983.d009737
