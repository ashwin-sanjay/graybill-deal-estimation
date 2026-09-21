import GD.Module0228
import GD.Module0318























open Matrix Set
open scoped BigOperators MatrixOrder Topology

namespace GD
namespace N0234
namespace N0742

noncomputable section

variable {n X I : Type*} [Fintype n] [DecidableEq n]


def d004743 (P : Matrix n n ℝ) (v : n → ℝ) : ℝ :=
  v ⬝ᵥ (P *ᵥ v)


def d004744 (P : Matrix n n ℝ) : Set (n → ℝ) :=
  {v | P *ᵥ v = 0}






def d004745
    (P : Matrix n n ℝ) (residual : X → n → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → _root_.GD.N0234.N0742.d004743 P (residual x) = 0 → residual x = 0





theorem d004746
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (v : n → ℝ) :
    _root_.GD.N0234.N0742.d004743 P v = 0 ↔ P *ᵥ v = 0 := by
  simpa [_root_.GD.N0234.N0742.d004743] using hP.dotProduct_mulVec_zero_iff v


theorem d004747
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (v : n → ℝ) :
    0 ≤ _root_.GD.N0234.N0742.d004743 P v := by
  exact hP.dotProduct_mulVec_nonneg v





theorem d004748
    {P Q : Matrix n n ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (v : n → ℝ) :
    (P + Q) *ᵥ v = 0 ↔ P *ᵥ v = 0 ∧ Q *ᵥ v = 0 := by
  constructor
  · intro hsum
    have hquadSum : _root_.GD.N0234.N0742.d004743 (P + Q) v = 0 :=
      (_root_.GD.N0234.N0742.d004746 (hP.add hQ) v).2 hsum
    have hsplit :
        _root_.GD.N0234.N0742.d004743 (P + Q) v =
          _root_.GD.N0234.N0742.d004743 P v + _root_.GD.N0234.N0742.d004743 Q v := by
      simp [_root_.GD.N0234.N0742.d004743, add_mulVec, dotProduct_add]
    have hzero :
        _root_.GD.N0234.N0742.d004743 P v + _root_.GD.N0234.N0742.d004743 Q v = 0 := by
      simpa [hsplit] using hquadSum
    have hPzero : _root_.GD.N0234.N0742.d004743 P v = 0 := by
      linarith [_root_.GD.N0234.N0742.d004747 hP v,
        _root_.GD.N0234.N0742.d004747 hQ v]
    have hQzero : _root_.GD.N0234.N0742.d004743 Q v = 0 := by
      linarith [_root_.GD.N0234.N0742.d004747 hP v,
        _root_.GD.N0234.N0742.d004747 hQ v]
    exact
      ⟨(_root_.GD.N0234.N0742.d004746 hP v).1 hPzero,
        (_root_.GD.N0234.N0742.d004746 hQ v).1 hQzero⟩
  · rintro ⟨hPv, hQv⟩
    simp [add_mulVec, hPv, hQv]


theorem d004749
    {P Q : Matrix n n ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    _root_.GD.N0234.N0742.d004744 (P + Q) = _root_.GD.N0234.N0742.d004744 P ∩ _root_.GD.N0234.N0742.d004744 Q := by
  ext v
  exact _root_.GD.N0234.N0742.d004748 hP hQ v





theorem d004750
    {ι : Type*} (s : Finset ι) (P : ι → Matrix n n ℝ)
    (hP : ∀ i ∈ s, (P i).PosSemidef) (v : n → ℝ) :
    (∑ i ∈ s, P i) *ᵥ v = 0 ↔
      ∀ i ∈ s, P i *ᵥ v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hPi : (P i).PosSemidef :=
        hP i (Finset.mem_insert_self i s)
      have hPs : (∑ j ∈ s, P j).PosSemidef :=
        Matrix.posSemidef_sum s
          (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
      rw [_root_.GD.N0234.N0742.d004748 hPi hPs v]
      rw [ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))]
      simp [hi]


theorem d004751
    {ι : Type*} (s : Finset ι) (P : ι → Matrix n n ℝ)
    (hP : ∀ i ∈ s, (P i).PosSemidef) :
    _root_.GD.N0234.N0742.d004744 (∑ i ∈ s, P i) =
      {v | ∀ i ∈ s, v ∈ _root_.GD.N0234.N0742.d004744 (P i)} := by
  ext v
  exact _root_.GD.N0234.N0742.d004750 s P hP v


theorem d004752
    {a : ℝ} (ha : 0 < a) (P : Matrix n n ℝ) (v : n → ℝ) :
    (a • P) *ᵥ v = 0 ↔ P *ᵥ v = 0 := by
  simp [smul_mulVec, ha.ne']





theorem d004753
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (v : n → ℝ) :
    (∑ i ∈ s, weight i • P i) *ᵥ v = 0 ↔
      ∀ i ∈ s, P i *ᵥ v = 0 := by
  have hscaled :
      ∀ i ∈ s, (weight i • P i).PosSemidef :=
    fun i hi ↦ (hP i hi).smul (hweight i hi).le
  rw [_root_.GD.N0234.N0742.d004750 s
    (fun i ↦ weight i • P i) hscaled v]
  constructor
  · intro h i hi
    exact (_root_.GD.N0234.N0742.d004752 (hweight i hi) (P i) v).1 (h i hi)
  · intro h i hi
    exact (_root_.GD.N0234.N0742.d004752 (hweight i hi) (P i) v).2 (h i hi)


theorem d004754
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hP : ∀ i ∈ s, (P i).PosSemidef) :
    _root_.GD.N0234.N0742.d004744 (∑ i ∈ s, weight i • P i) =
      _root_.GD.N0234.N0742.d004744 (∑ i ∈ s, P i) := by
  ext v
  change
    ((∑ i ∈ s, weight i • P i) *ᵥ v = 0) ↔
      (∑ i ∈ s, P i) *ᵥ v = 0
  rw [_root_.GD.N0234.N0742.d004753
    s weight P hweight hP v]
  rw [_root_.GD.N0234.N0742.d004750 s P hP v]


theorem d004755
    {ι : Type*} (s : Finset ι) (P : ι → Matrix n n ℝ)
    (v : n → ℝ) :
    _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, P i) v =
      ∑ i ∈ s, _root_.GD.N0234.N0742.d004743 (P i) v := by
  classical
  unfold _root_.GD.N0234.N0742.d004743
  rw [Matrix.sum_mulVec, dotProduct_sum]


theorem d004756
    (a : ℝ) (P : Matrix n n ℝ) (v : n → ℝ) :
    _root_.GD.N0234.N0742.d004743 (a • P) v = a * _root_.GD.N0234.N0742.d004743 P v := by
  simp [_root_.GD.N0234.N0742.d004743, smul_mulVec, dotProduct_smul]





theorem d004757
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    {m : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i ∈ s, m ≤ weight i)
    (v : n → ℝ) :
    m * _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, P i) v ≤
      _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, weight i • P i) v := by
  rw [_root_.GD.N0234.N0742.d004755, _root_.GD.N0234.N0742.d004755]
  simp_rw [_root_.GD.N0234.N0742.d004756]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_right (hweight i hi)
      (_root_.GD.N0234.N0742.d004747 (hP i hi) v)





theorem d004758
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    {m δ : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i ∈ s, m ≤ weight i)
    (residual : X → n → ℝ) (S : Set X)
    (hmargin :
      ∀ x ∈ S, δ ≤ _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, P i) (residual x)) :
    ∀ x ∈ S,
      m * δ ≤
        _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, weight i • P i) (residual x) := by
  intro x hx
  calc
    m * δ ≤ m * _root_.GD.N0234.N0742.d004743 (∑ i ∈ s, P i) (residual x) :=
      mul_le_mul_of_nonneg_left (hmargin x hx) hm
    _ ≤ _root_.GD.N0234.N0742.d004743
        (∑ i ∈ s, weight i • P i) (residual x) :=
      _root_.GD.N0234.N0742.d004757
        s weight P hP hm hweight (residual x)





theorem d004759
    {P Q : Matrix n n ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (residual : X → n → ℝ) (S : Set X) :
    _root_.GD.N0234.N0742.d004745 (P + Q) residual S ↔
      ∀ ⦃x : X⦄, x ∈ S →
        P *ᵥ residual x = 0 →
        Q *ᵥ residual x = 0 →
        residual x = 0 := by
  constructor
  · intro hfaithful x hx hPx hQx
    apply hfaithful hx
    apply (_root_.GD.N0234.N0742.d004746 (hP.add hQ) _).2
    exact (_root_.GD.N0234.N0742.d004748 hP hQ _).2 ⟨hPx, hQx⟩
  · intro hcommon x hx henergy
    have hsum :
        (P + Q) *ᵥ residual x = 0 :=
      (_root_.GD.N0234.N0742.d004746 (hP.add hQ) _).1 henergy
    exact hcommon hx
      ((_root_.GD.N0234.N0742.d004748 hP hQ _).1 hsum).1
      ((_root_.GD.N0234.N0742.d004748 hP hQ _).1 hsum).2





theorem d004745.d004760
    {P Q : Matrix n n ℝ}
    {residual : X → n → ℝ} {S : Set X}
    (hfaithful : _root_.GD.N0234.N0742.d004745 P residual S)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    _root_.GD.N0234.N0742.d004745 (P + Q) residual S := by
  rw [_root_.GD.N0234.N0742.d004759 hP hQ residual S]
  intro x hx hPx hQx
  apply hfaithful hx
  exact (_root_.GD.N0234.N0742.d004746 hP _).2 hPx






theorem d004761
    {ι : Type*} (s : Finset ι) (P : ι → Matrix n n ℝ)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X) :
    _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, P i) residual S ↔
      ∀ ⦃x : X⦄, x ∈ S →
        (∀ i ∈ s, P i *ᵥ residual x = 0) →
        residual x = 0 := by
  let Psum : Matrix n n ℝ := ∑ i ∈ s, P i
  have hPsum : Psum.PosSemidef :=
    Matrix.posSemidef_sum s hP
  constructor
  · intro hfaithful x hx hall
    apply hfaithful hx
    apply (_root_.GD.N0234.N0742.d004746 hPsum _).2
    exact (_root_.GD.N0234.N0742.d004750 s P hP _).2 hall
  · intro hcommon x hx henergy
    have hsum : Psum *ᵥ residual x = 0 :=
      (_root_.GD.N0234.N0742.d004746 hPsum _).1 henergy
    exact hcommon hx
      ((_root_.GD.N0234.N0742.d004750 s P hP _).1 hsum)





theorem d004762
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X) :
    _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, weight i • P i) residual S ↔
      ∀ ⦃x : X⦄, x ∈ S →
        (∀ i ∈ s, P i *ᵥ residual x = 0) →
        residual x = 0 := by
  let Psum : Matrix n n ℝ := ∑ i ∈ s, weight i • P i
  have hscaled :
      ∀ i ∈ s, (weight i • P i).PosSemidef :=
    fun i hi ↦ (hP i hi).smul (hweight i hi).le
  have hPsum : Psum.PosSemidef :=
    Matrix.posSemidef_sum s hscaled
  constructor
  · intro hfaithful x hx hall
    apply hfaithful hx
    apply (_root_.GD.N0234.N0742.d004746 hPsum _).2
    exact
      (_root_.GD.N0234.N0742.d004753
        s weight P hweight hP _).2 hall
  · intro hcommon x hx henergy
    have hsum : Psum *ᵥ residual x = 0 :=
      (_root_.GD.N0234.N0742.d004746 hPsum _).1 henergy
    exact hcommon hx
      ((_root_.GD.N0234.N0742.d004753
        s weight P hweight hP _).1 hsum)





theorem d004763
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ) (P : ι → Matrix n n ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X) :
    _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, weight i • P i) residual S ↔
      _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, P i) residual S := by
  rw [_root_.GD.N0234.N0742.d004762
    s weight P hweight hP residual S]
  rw [_root_.GD.N0234.N0742.d004761 s P hP residual S]






theorem d004764
    {ι : Type*} (s : Finset ι)
    (P : ι → Matrix n n ℝ) (region : ι → Set X)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X)
    (hcover : ∀ x ∈ S, ∃ i ∈ s, x ∈ region i)
    (hfaithful :
      ∀ i ∈ s, _root_.GD.N0234.N0742.d004745 (P i) residual (region i)) :
    _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, P i) residual S := by
  rw [_root_.GD.N0234.N0742.d004761 s P hP residual S]
  intro x hx hall
  obtain ⟨i, hi, hxregion⟩ := hcover x hx
  apply hfaithful i hi hxregion
  exact (_root_.GD.N0234.N0742.d004746 (hP i hi) _).2
    (hall i hi)





theorem d004765
    {ι : Type*} (s : Finset ι)
    (weight : ι → ℝ)
    (P : ι → Matrix n n ℝ) (region : ι → Set X)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (residual : X → n → ℝ) (S : Set X)
    (hcover : ∀ x ∈ S, ∃ i ∈ s, x ∈ region i)
    (hfaithful :
      ∀ i ∈ s, _root_.GD.N0234.N0742.d004745 (P i) residual (region i)) :
    _root_.GD.N0234.N0742.d004745 (∑ i ∈ s, weight i • P i) residual S := by
  rw [_root_.GD.N0234.N0742.d004763
    s weight P hweight hP residual S]
  exact _root_.GD.N0234.N0742.d004764
    s P region hP residual S hcover hfaithful






theorem d004766
    {P Q : Matrix n n ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (residual : X → n → ℝ) (S U V : Set X)
    (hcover : S ⊆ U ∪ V)
    (hfaithfulP : _root_.GD.N0234.N0742.d004745 P residual U)
    (hfaithfulQ : _root_.GD.N0234.N0742.d004745 Q residual V) :
    _root_.GD.N0234.N0742.d004745 (P + Q) residual S := by
  rw [_root_.GD.N0234.N0742.d004759 hP hQ residual S]
  intro x hx hPx hQx
  rcases hcover hx with hxU | hxV
  · apply hfaithfulP hxU
    exact (_root_.GD.N0234.N0742.d004746 hP _).2 hPx
  · apply hfaithfulQ hxV
    exact (_root_.GD.N0234.N0742.d004746 hQ _).2 hQx





theorem d004767
    {P : Matrix n n ℝ} (hP : P.PosSemidef)
    (residual : X → n → ℝ) (S : Set X)
    {x : X} (hx : x ∈ S)
    (hkernel : P *ᵥ residual x = 0)
    (hne : residual x ≠ 0) :
    ¬ _root_.GD.N0234.N0742.d004745 P residual S := by
  intro hfaithful
  exact hne <| hfaithful hx <|
    (_root_.GD.N0234.N0742.d004746 hP _).2 hkernel





theorem d004768
    (P : Matrix n n ℝ) (v : n → ℝ) :
    ((0 : ℝ) • P) *ᵥ v = 0 := by
  simp





theorem d004769
    (v : n → ℝ) (hv : v ≠ 0) :
    (((1 : Matrix n n ℝ) + (-1 : Matrix n n ℝ)) *ᵥ v = 0) ∧
      ¬ ((1 : Matrix n n ℝ) *ᵥ v = 0 ∧
        (-1 : Matrix n n ℝ) *ᵥ v = 0) := by
  constructor
  · simp
  · simp [hv]





theorem d004770
    (v : n → ℝ) (hv : v ≠ 0) :
    (((0 : ℝ) • (1 : Matrix n n ℝ)) *ᵥ v = 0) ∧
      (1 : Matrix n n ℝ) *ᵥ v ≠ 0 := by
  simp [hv]

section CompactExtraction

variable [TopologicalSpace X]


def d004771
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ)
    (x : X) : ↥u → ℝ :=
  fun i ↦ obs i x - target i




def d004772 (u : Finset I) : Matrix ↥u ↥u ℝ := by
  classical
  exact 1


theorem d004773 (u : Finset I) :
    (_root_.GD.N0234.N0742.d004772 u).PosSemidef := by
  classical
  simpa [_root_.GD.N0234.N0742.d004772] using
    (Matrix.PosSemidef.one : (1 : Matrix ↥u ↥u ℝ).PosSemidef)





theorem d004774
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ) (x : X) :
    _root_.GD.N0238.N0755.d004732
        u obs target x =
      _root_.GD.N0234.N0742.d004743 (_root_.GD.N0234.N0742.d004772 u)
        (_root_.GD.N0234.N0742.d004771 u obs target x) := by
  classical
  simp only [_root_.GD.N0238.N0755.d004732,
    _root_.GD.N0234.N0742.d004743, _root_.GD.N0234.N0742.d004772, _root_.GD.N0234.N0742.d004771, one_mulVec,
    dotProduct]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro i hi
  ring








theorem d004775
    (boundary : Set X)
    (hboundary : IsCompact boundary)
    (obs : I → X → ℝ)
    (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (havoid : ∀ x ∈ boundary, ∃ i, obs i x ≠ target i) :
    ∃ u : Finset I, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x ∈ boundary,
        δ ≤ _root_.GD.N0234.N0742.d004743 (_root_.GD.N0234.N0742.d004772 u)
          (_root_.GD.N0234.N0742.d004771 u obs target x) := by
  obtain ⟨u, δ, hδ, hmargin⟩ :=
    _root_.GD.N0238.N0755.d004736
      boundary hboundary obs target hobs havoid
  refine ⟨u, δ, hδ, ?_⟩
  intro x hx
  rw [← _root_.GD.N0234.N0742.d004774]
  exact hmargin x hx

end CompactExtraction

end

end N0742
end N0234
end GD
