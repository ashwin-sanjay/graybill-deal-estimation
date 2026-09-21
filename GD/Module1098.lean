import GD.Module0030
import GD.Module1095































open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1189

noncomputable section

open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1186
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0230.N0656

abbrev d017612 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017613 :=
  _root_.GD.N0232.N0720.N1173.d015936

abbrev d017614 := _root_.GD.N0232.N0720.N1189.d017612 → ℝ




theorem d017615
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1189.d017613 → ℝ) (x : _root_.GD.N0232.N0720.N1189.d017613) :
    _root_.GD.N0232.N0720.N1185.d017512 rho candidate (0 : _root_.GD.N0232.N0720.N1189.d017614) x = 0 := by
  simp [_root_.GD.N0232.N0720.N1185.d017512, _root_.GD.N0232.N0720.N1173.d015939]




theorem d017616
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1189.d017613 → ℝ)
    (c : ℝ) (weight : _root_.GD.N0232.N0720.N1189.d017614) (x : _root_.GD.N0232.N0720.N1189.d017613) :
    _root_.GD.N0232.N0720.N1185.d017512 rho candidate (c • weight) x =
      c * _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight x := by
  unfold _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1173.d015939
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with theta
  simp only [Pi.smul_apply, smul_eq_mul]
  ring











structure d017617
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1189.d017613 → ℝ)
    (base : _root_.GD.N0232.N0720.N1189.d017614) where
  Legal : _root_.GD.N0232.N0720.N1189.d017614 → Prop
  legal_zero : Legal 0
  legal_add : ∀ {w v}, Legal w → Legal v → Legal (w + v)
  legal_smul : ∀ {c : ℝ}, 0 ≤ c → ∀ {w}, Legal w → Legal (c • w)
  weight_nonnegative : ∀ {w}, Legal w → ∀ theta, 0 ≤ w theta
  current_integrable : ∀ {w}, Legal w → ∀ x,
    Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - candidate x) * _root_.GD.N0232.N0720.N1173.d015939 w theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)
  current_memLp : ∀ {w}, Legal w →
    MemLp (_root_.GD.N0232.N0720.N1185.d017512 rho candidate w) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)

variable {rho : Measure (Set.Ioo (0 : ℝ) 1)}
variable {candidate : _root_.GD.N0232.N0720.N1189.d017613 → ℝ}
variable {base : _root_.GD.N0232.N0720.N1189.d017614}


def d017618
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (w : _root_.GD.N0232.N0720.N1189.d017614) (hw : D.Legal w) :
    _root_.GD.N0232.N0720.N1186.d017590 rho base :=
  _root_.GD.N0232.N0720.N1186.d017591 rho candidate base w (D.current_memLp hw)


theorem d017619
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    _root_.GD.N0232.N0720.N1189.d017618 D 0 D.legal_zero = 0 := by
  apply Lp.ext
  filter_upwards
    [_root_.GD.N0232.N0720.N1186.d017592 rho candidate base 0
      (D.current_memLp D.legal_zero),
     Lp.coeFn_zero ℝ 2 (_root_.GD.N0232.N0720.N1186.d017589 rho base)] with x hx hzero
  simp only [_root_.GD.N0232.N0720.N1189.d017618]
  rw [hx, _root_.GD.N0232.N0720.N1189.d017615]
  exact hzero.symm



theorem d017620
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    {w v : _root_.GD.N0232.N0720.N1189.d017614} (hw : D.Legal w) (hv : D.Legal v) :
    _root_.GD.N0232.N0720.N1189.d017618 D (w + v) (D.legal_add hw hv) =
      _root_.GD.N0232.N0720.N1189.d017618 D w hw + _root_.GD.N0232.N0720.N1189.d017618 D v hv := by
  apply Lp.ext
  filter_upwards
    [_root_.GD.N0232.N0720.N1186.d017592 rho candidate base (w + v)
      (D.current_memLp (D.legal_add hw hv)),
     _root_.GD.N0232.N0720.N1186.d017592 rho candidate base w
      (D.current_memLp hw),
     _root_.GD.N0232.N0720.N1186.d017592 rho candidate base v
      (D.current_memLp hv),
     Lp.coeFn_add (_root_.GD.N0232.N0720.N1189.d017618 D w hw) (_root_.GD.N0232.N0720.N1189.d017618 D v hv)]
      with x hsum hwx hvx hadd
  simp only [_root_.GD.N0232.N0720.N1189.d017618] at hadd ⊢
  rw [hsum, hadd, Pi.add_apply, hwx, hvx]
  exact _root_.GD.N0232.N0720.N1185.d017520 rho candidate w v x
    (D.current_integrable hw x) (D.current_integrable hv x)



theorem d017621
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    {c : ℝ} (hc : 0 ≤ c) {w : _root_.GD.N0232.N0720.N1189.d017614} (hw : D.Legal w) :
    _root_.GD.N0232.N0720.N1189.d017618 D (c • w) (D.legal_smul hc hw) =
      c • _root_.GD.N0232.N0720.N1189.d017618 D w hw := by
  apply Lp.ext
  filter_upwards
    [_root_.GD.N0232.N0720.N1186.d017592 rho candidate base (c • w)
      (D.current_memLp (D.legal_smul hc hw)),
     _root_.GD.N0232.N0720.N1186.d017592 rho candidate base w
      (D.current_memLp hw),
     Lp.coeFn_smul c (_root_.GD.N0232.N0720.N1189.d017618 D w hw)] with x hscaled hwx hsmul
  simp only [_root_.GD.N0232.N0720.N1189.d017618] at hsmul ⊢
  rw [hscaled, hsmul, Pi.smul_apply, hwx,
    _root_.GD.N0232.N0720.N1189.d017616]
  rfl




def d017622
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    Set (_root_.GD.N0232.N0720.N1186.d017590 rho base) :=
  {z | ∃ w : _root_.GD.N0232.N0720.N1189.d017614, ∃ hw : D.Legal w, z = _root_.GD.N0232.N0720.N1189.d017618 D w hw}

theorem d017623
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    0 ∈ _root_.GD.N0232.N0720.N1189.d017622 D := by
  exact ⟨0, D.legal_zero, (_root_.GD.N0232.N0720.N1189.d017619 D).symm⟩



theorem d017624
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    {x y : _root_.GD.N0232.N0720.N1186.d017590 rho base}
    (hx : x ∈ _root_.GD.N0232.N0720.N1189.d017622 D) (hy : y ∈ _root_.GD.N0232.N0720.N1189.d017622 D)
    (a : ℝ) (ha : 0 ≤ a) (b : ℝ) (hb : 0 ≤ b) :
    a • x + b • y ∈ _root_.GD.N0232.N0720.N1189.d017622 D := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  let hwa : D.Legal (a • w) := D.legal_smul ha hw
  let hvb : D.Legal (b • v) := D.legal_smul hb hv
  let hab : D.Legal (a • w + b • v) := D.legal_add hwa hvb
  refine ⟨a • w + b • v, hab, ?_⟩
  rw [_root_.GD.N0232.N0720.N1189.d017620 D hwa hvb,
    _root_.GD.N0232.N0720.N1189.d017621 D ha hw, _root_.GD.N0232.N0720.N1189.d017621 D hb hv]




def d017625
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    PointedCone ℝ (_root_.GD.N0232.N0720.N1186.d017590 rho base) :=
  PointedCone.ofConeComb (_root_.GD.N0232.N0720.N1189.d017622 D)
    ⟨0, _root_.GD.N0232.N0720.N1189.d017623 D⟩
    (fun _x hx _y hy a ha b hb ↦
      _root_.GD.N0232.N0720.N1189.d017624 D hx hy a ha b hb)

@[simp]
theorem d017626
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (z : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    z ∈ _root_.GD.N0232.N0720.N1189.d017625 D ↔
      ∃ w : _root_.GD.N0232.N0720.N1189.d017614, ∃ hw : D.Legal w, z = _root_.GD.N0232.N0720.N1189.d017618 D w hw :=
  Iff.rfl



theorem d017627
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    PointedCone.hull ℝ (_root_.GD.N0232.N0720.N1189.d017622 D) = _root_.GD.N0232.N0720.N1189.d017625 D := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun z hz ↦ hz)
  · intro z hz
    exact PointedCone.subset_hull hz



theorem d017628
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    {ι : Type*} (s : Finset ι)
    (w : ι → _root_.GD.N0232.N0720.N1189.d017614) (hw : ∀ i, D.Legal (w i))
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∃ W : _root_.GD.N0232.N0720.N1189.d017614, ∃ hW : D.Legal W,
      _root_.GD.N0232.N0720.N1189.d017618 D W hW =
        ∑ i ∈ s, c i • _root_.GD.N0232.N0720.N1189.d017618 D (w i) (hw i) := by
  have hsum :
      (∑ i ∈ s, c i • _root_.GD.N0232.N0720.N1189.d017618 D (w i) (hw i)) ∈
        PointedCone.hull ℝ (_root_.GD.N0232.N0720.N1189.d017622 D) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        apply (PointedCone.hull ℝ (_root_.GD.N0232.N0720.N1189.d017622 D)).add_mem
        · apply (PointedCone.hull ℝ (_root_.GD.N0232.N0720.N1189.d017622 D)).smul_mem
            (hc i (Finset.mem_insert_self i s))
          exact PointedCone.subset_hull ⟨w i, hw i, rfl⟩
        · exact ih (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
  rw [_root_.GD.N0232.N0720.N1189.d017627 D] at hsum
  obtain ⟨W, hW, hEq⟩ :=
    (_root_.GD.N0232.N0720.N1189.d017626 D _).mp hsum
  exact ⟨W, hW, hEq.symm⟩


def d017629
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base) :
    ProperCone ℝ (_root_.GD.N0232.N0720.N1186.d017590 rho base) where
  toSubmodule := (_root_.GD.N0232.N0720.N1189.d017625 D).closure
  isClosed' := isClosed_closure

theorem d017630
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (z : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    z ∈ _root_.GD.N0232.N0720.N1189.d017629 D ↔ z ∈ closure (_root_.GD.N0232.N0720.N1189.d017622 D) :=
  Iff.rfl





theorem d017631
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (target : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    target ∈ _root_.GD.N0232.N0720.N1189.d017629 D ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ w : _root_.GD.N0232.N0720.N1189.d017614, ∃ hw : D.Legal w,
          ‖_root_.GD.N0232.N0720.N1189.d017618 D w hw - target‖ < ε := by
  rw [_root_.GD.N0232.N0720.N1189.d017630, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨z, hz, hdist⟩ := h ε hε
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, by simpa [dist_eq_norm, norm_sub_rev] using hdist⟩
  · intro h ε hε
    obtain ⟨w, hw, hnorm⟩ := h ε hε
    refine ⟨_root_.GD.N0232.N0720.N1189.d017618 D w hw, ⟨w, hw, rfl⟩, ?_⟩
    simpa [dist_eq_norm, norm_sub_rev] using hnorm



theorem d017632
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (target : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    target ∈ _root_.GD.N0232.N0720.N1189.d017629 D ↔
      ∀ f : StrongDual ℝ (_root_.GD.N0232.N0720.N1186.d017590 rho base),
        (∀ w : _root_.GD.N0232.N0720.N1189.d017614, ∀ hw : D.Legal w,
          0 ≤ f (_root_.GD.N0232.N0720.N1189.d017618 D w hw)) →
        0 ≤ f target := by
  constructor
  · intro htarget f hf
    have hhalf : IsClosed
        {z : _root_.GD.N0232.N0720.N1186.d017590 rho base | 0 ≤ f z} :=
      isClosed_Ici.preimage f.continuous
    have hgenerators : _root_.GD.N0232.N0720.N1189.d017622 D ⊆
        {z : _root_.GD.N0232.N0720.N1186.d017590 rho base | 0 ≤ f z} := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hf w hw
    have hclosure : closure (_root_.GD.N0232.N0720.N1189.d017622 D) ⊆
        {z : _root_.GD.N0232.N0720.N1186.d017590 rho base | 0 ≤ f z} :=
      hhalf.closure_subset_iff.mpr hgenerators
    exact hclosure ((_root_.GD.N0232.N0720.N1189.d017630 D target).mp htarget)
  · intro hdual
    rw [_root_.GD.N0230.N0656.d000355]
    intro f hfcone
    apply hdual f
    intro w hw
    apply hfcone (_root_.GD.N0232.N0720.N1189.d017618 D w hw)
    rw [_root_.GD.N0232.N0720.N1189.d017630]
    exact subset_closure ⟨w, hw, rfl⟩




theorem d017633
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (target : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    target ∈ _root_.GD.N0232.N0720.N1189.d017629 D ∨
      ∃ f : StrongDual ℝ (_root_.GD.N0232.N0720.N1186.d017590 rho base),
        (∀ w : _root_.GD.N0232.N0720.N1189.d017614, ∀ hw : D.Legal w,
          0 ≤ f (_root_.GD.N0232.N0720.N1189.d017618 D w hw)) ∧
        f target < 0 := by
  rcases _root_.GD.N0230.N0656.d000354
      (_root_.GD.N0232.N0720.N1189.d017629 D) target with hmem | ⟨f, hfcone, htarget⟩
  · exact Or.inl hmem
  · refine Or.inr ⟨f, ?_, htarget⟩
    intro w hw
    apply hfcone (_root_.GD.N0232.N0720.N1189.d017618 D w hw)
    rw [_root_.GD.N0232.N0720.N1189.d017630]
    exact subset_closure ⟨w, hw, rfl⟩





theorem d017634
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (eta : _root_.GD.N0232.N0720.N1186.d017590 rho base)
    (w : _root_.GD.N0232.N0720.N1189.d017614) (hw : D.Legal w) :
    inner ℝ eta (_root_.GD.N0232.N0720.N1189.d017618 D w hw) =
      ∫ x, eta x * _root_.GD.N0232.N0720.N1185.d017512 rho candidate w x
        ∂_root_.GD.N0232.N0720.N1186.d017589 rho base := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [_root_.GD.N0232.N0720.N1186.d017592 rho candidate base w
      (D.current_memLp hw)] with x hx
  simp only [_root_.GD.N0232.N0720.N1189.d017618, RCLike.inner_apply, conj_trivial, hx, mul_comm]





theorem d017635
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (target : _root_.GD.N0232.N0720.N1186.d017590 rho base) :
    target ∈ _root_.GD.N0232.N0720.N1189.d017629 D ∨
      ∃ eta : _root_.GD.N0232.N0720.N1186.d017590 rho base,
        (∀ w : _root_.GD.N0232.N0720.N1189.d017614, ∀ hw : D.Legal w,
          0 ≤ inner ℝ eta (_root_.GD.N0232.N0720.N1189.d017618 D w hw)) ∧
        inner ℝ eta target < 0 := by
  rcases _root_.GD.N0232.N0720.N1189.d017633 D target with
      hmem | ⟨f, hf, htarget⟩
  · exact Or.inl hmem
  · let eta : _root_.GD.N0232.N0720.N1186.d017590 rho base :=
      (InnerProductSpace.toDual ℝ
        (_root_.GD.N0232.N0720.N1186.d017590 rho base)).symm f
    refine Or.inr ⟨eta, ?_, ?_⟩
    · intro w hw
      simpa only [eta, InnerProductSpace.toDual_symm_apply] using hf w hw
    · simpa only [eta, InnerProductSpace.toDual_symm_apply] using htarget






theorem d017636
    (D : _root_.GD.N0232.N0720.N1189.d017617 rho candidate base)
    (hevidenceMeasurable : Measurable (_root_.GD.N0232.N0720.N1173.d015940 rho base))
    (hevidencePos : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2, 0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hbase : MemLp (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base) 2
      (_root_.GD.N0232.N0720.N1186.d017589 rho base)) :
    _root_.GD.N0232.N0720.N1186.d017593 rho candidate base hbase ∈ _root_.GD.N0232.N0720.N1189.d017629 D ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ w : _root_.GD.N0232.N0720.N1189.d017614, ∃ _hw : D.Legal w,
          _root_.GD.N0232.N0720.N1185.d017521 rho candidate base w < ε := by
  rw [_root_.GD.N0232.N0720.N1189.d017631]
  constructor
  · intro hclose ε hε
    obtain ⟨w, hw, hnorm⟩ := hclose (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨w, hw, ?_⟩
    have hnormSq := _root_.GD.N0232.N0720.N1186.d017596
      rho candidate base w hevidenceMeasurable hevidencePos hbase
      (D.current_memLp hw)
    have hsq :
        ‖_root_.GD.N0232.N0720.N1189.d017618 D w hw - _root_.GD.N0232.N0720.N1186.d017593 rho candidate base hbase‖ ^ 2 <
          (Real.sqrt ε) ^ 2 :=
      (sq_lt_sq₀
        (norm_nonneg
          (_root_.GD.N0232.N0720.N1189.d017618 D w hw - _root_.GD.N0232.N0720.N1186.d017593 rho candidate base hbase))
        (Real.sqrt_nonneg ε)).2 hnorm
    rw [Real.sq_sqrt hε.le] at hsq
    rw [← hnormSq]
    simpa only [_root_.GD.N0232.N0720.N1189.d017618] using hsq
  · intro hresidual ε hε
    obtain ⟨w, hw, hres⟩ := hresidual (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨w, hw, ?_⟩
    have hnormSq := _root_.GD.N0232.N0720.N1186.d017596
      rho candidate base w hevidenceMeasurable hevidencePos hbase
      (D.current_memLp hw)
    rw [← hnormSq] at hres
    apply (sq_lt_sq₀
      (norm_nonneg
        (_root_.GD.N0232.N0720.N1189.d017618 D w hw - _root_.GD.N0232.N0720.N1186.d017593 rho candidate base hbase))
      hε.le).mp
    simpa only [_root_.GD.N0232.N0720.N1189.d017618] using hres

#print axioms _root_.GD.N0232.N0720.N1189.d017616
#print axioms _root_.GD.N0232.N0720.N1189.d017628
#print axioms _root_.GD.N0232.N0720.N1189.d017632
#print axioms _root_.GD.N0232.N0720.N1189.d017635
#print axioms _root_.GD.N0232.N0720.N1189.d017636

end
end N1189
end N0720
end N0232
end GD
