import GD.Module1362
import GD.Module0724
import GD.Module0701
import GD.Module0632
import GD.Module0744
import GD.Module0822
import GD.Module0625

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0076.N0311

noncomputable section

namespace N0760

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0107 _root_.GD.N0137

variable {k : ℕ} (sizes : Fin k → ℕ)

def d022078 (z : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : Prop :=
  ∀ i, 0 < (_root_.GD.N0232.N0719.N0900.d009104 k sizes z).meanVariance i

def d022079 (z : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  (∑ i, (sizes i : ℝ) * _root_.GD.N0107.d009084 (z i) / _root_.GD.N0107.d009085 (z i)) /
    (∑ i, (sizes i : ℝ) / _root_.GD.N0107.d009085 (z i))

theorem d022080 : Measurable (_root_.GD.N0076.N0311.N0760.d022079 sizes) := by
  unfold _root_.GD.N0076.N0311.N0760.d022079 _root_.GD.N0107.d009084 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop

theorem d022081 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i : Fin k ↦
      Measure.pi (fun _ : Fin (sizes i) ↦
        gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)))) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0932.d009211 _ _ _

theorem d022082 (z : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes z).mean i = (∑ j, z i j) / sizes i ∧
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes z).meanVariance i =
      _root_.GD.N0107.d009085 (z i) / sizes i := by
  constructor
  · simp [_root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0107.d009084,
      _root_.GD.N0126.d006420, _root_.GD.N0126.d006419]
  · rfl

theorem d022083 (hsizes : ∀ i, 0 < sizes i) :
    ∀ f : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable f →
      ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable g ∧
        (∀ z, g (_root_.GD.N0228.N0548.d009155 k sizes z) =
          f (_root_.GD.N0232.N0719.N0900.d009104 k sizes z)) ∧
        (∀ s, g (_root_.GD.N0228.N0548.d009148 sizes s) = f s) := by
  intro f hf
  refine ⟨f ∘ _root_.GD.N0228.N0548.d009149 sizes,
    hf.comp (_root_.GD.N0228.N0548.d009151 sizes),
    ?_, ?_⟩
  · intro z
    rfl
  · intro s
    simp [_root_.GD.N0228.N0548.d009152 sizes hsizes]

theorem d022084 (hsizes : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0076.N0311.N0760.d022078 sizes z :=
  _root_.GD.N0232.N0719.N0875.d010352
    sizes hsizes θ.location θ.scale θ.scale_pos

theorem d022085 (hk : 0 < k)
    (z : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (hz : _root_.GD.N0076.N0311.N0760.d022078 sizes z) :
    _root_.GD.N0232.N0719.N0859.d010815 k sizes z = _root_.GD.N0076.N0311.N0760.d022079 sizes z := by
  have hprecision (i : Fin k) :
      _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0900.d009104 k sizes z) i =
        (sizes i : ℝ) / _root_.GD.N0107.d009085 (z i) := by
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (hz i)]
    simp [_root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009103, inv_div]
  have htotal : 0 < _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0900.d009104 k sizes z) := by
    apply Finset.sum_pos
    · intro i _
      rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (hz i)]
      exact inv_pos.mpr (hz i)
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
  unfold _root_.GD.N0232.N0719.N0859.d010815 _root_.GD.N0232.N0719.N0900.d009111 _root_.GD.N0232.N0719.N0900.d009110
  simp only [_root_.GD.N0232.N0719.N0900.d009108, ne_of_gt htotal, ↓reduceIte]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp only [_root_.GD.N0232.N0719.N0900.d009107]
  simp_rw [hprecision]
  change (∑ i, ((sizes i : ℝ) / _root_.GD.N0107.d009085 (z i)) *
    _root_.GD.N0107.d009084 (z i)) / (∑ i, (sizes i : ℝ) / _root_.GD.N0107.d009085 (z i)) = _
  unfold _root_.GD.N0076.N0311.N0760.d022079
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d022086 (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0076.N0311.N0760.d022079 sizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0232.N0719.N0859.d010815 k sizes := by
  filter_upwards [_root_.GD.N0076.N0311.N0760.d022084 sizes hsizes θ] with z hz
  exact (_root_.GD.N0076.N0311.N0760.d022085 sizes hk z hz).symm

theorem d022087 (θ η : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f g : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :
    f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] g ↔ f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes η] g := by
  exact (_root_.GD.N0232.N0719.d009184 k sizes
    θ.location θ.scale θ.scale_pos).trans
      (_root_.GD.N0232.N0719.d009184 k sizes
        η.location η.scale η.scale_pos).symm

theorem d022088 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f g : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hfg : f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] g) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g := by
  apply lintegral_congr_ae
  filter_upwards [(_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_eq hfg] with z hz
  rw [hz]

theorem d022089 (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ z, _root_.GD.N0076.N0311.N0760.d022078 sizes z → f z = _root_.GD.N0076.N0311.N0760.d022079 sizes z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0076.N0311.N0760.d022084 sizes hsizes θ] with z hz
  rw [hf z hz, _root_.GD.N0076.N0311.N0760.d022085 sizes hk z hz]

theorem d022090 (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ z, _root_.GD.N0076.N0311.N0760.d022078 sizes z → f z = _root_.GD.N0076.N0311.N0760.d022079 sizes z) :
    ∀ d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable d →
      ((∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) ↔
        (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes))) ∧
      ((∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) ↔
        (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes))) := by
  intro d _
  simp only [_root_.GD.N0076.N0311.N0760.d022089 sizes hk hsizes f hf]
  exact ⟨True.intro, True.intro⟩

theorem d022091 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f =
      ∫⁻ z, ENNReal.ofReal ((f z - θ.location) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ := rfl

theorem d022092 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : Integrable (fun z ↦ (f z - θ.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f =
      ENNReal.ofReal (∫ z, (f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  exact (ofReal_integral_eq_lintegral_ofReal hf
    (ae_of_all _ fun z ↦ sq_nonneg (f z - θ.location))).symm

theorem d022093 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (MemLp.toLp f hf) :=
  _root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hf

theorem d022094
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) (hf : Measurable f)
    (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) f ≠ ⊤) :
    ∃ p : _root_.GD.N0230.N0602.d000116
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f = _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
  have hmem := _root_.GD.N0232.N0719.N0896.d011095
    k sizes f hf hfinite
  exact ⟨MemLp.toLp f hmem, fun θ ↦ _root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hmem⟩

theorem d022095
    (p : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ,
      Measurable f ∧ ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f = _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p :=
  ⟨_root_.GD.N0232.N0719.N0896.d011088 k sizes p,
    _root_.GD.N0232.N0719.N0896.d011089 k sizes p,
    fun θ ↦ _root_.GD.N0232.N0719.N0896.d011093
      k sizes θ p⟩

theorem d022096 (hk : 2 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Measurable (_root_.GD.N0076.N0311.N0760.d022079 sizes) ∧
    (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i : Fin k ↦
      Measure.pi (fun _ : Fin (sizes i) ↦
        gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i))))) ∧
    (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0076.N0311.N0760.d022079 sizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      _root_.GD.N0232.N0719.N0859.d010815 k sizes) ∧
    (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0076.N0311.N0760.d022079 sizes) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
    (∀ (θ η : _root_.GD.N0232.N0719.N0859.d010809 k) (f g : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ),
      f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] g ↔ f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes η] g) := by
  have hk0 : 0 < k := by omega
  exact ⟨_root_.GD.N0076.N0311.N0760.d022080 sizes, _root_.GD.N0076.N0311.N0760.d022081 sizes,
    _root_.GD.N0076.N0311.N0760.d022086 sizes hk0 hsizes,
    _root_.GD.N0076.N0311.N0760.d022089 sizes hk0 hsizes _ (fun _ _ ↦ rfl), _root_.GD.N0076.N0311.N0760.d022087 sizes⟩

end N0760

theorem d022097 (m n : ℕ) (μ σ υ : ℝ) :
    MeasurePreserving
      (_root_.GD.N0232.N0720.N1467.d012540 m n)
      (_root_.GD.N0232.N0719.d009176 2
        (_root_.GD.N0232.N0720.N1467.d012537 m n) μ ![σ, υ])
      (_root_.GD.N0107.d009030 m n μ σ υ) :=
  _root_.GD.N0232.N0720.N1497.d012550
    m n μ σ υ

theorem d022098 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Measurable (_root_.GD.N0096.N0341.d021956 m n) ∧
    ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0096.N0341.d021956 m n =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014171 m n θ]
        _root_.GD.N0232.N0720.N1080.d014175 m n ∧
      _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0096.N0341.d021956 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  refine ⟨_root_.GD.N0096.N0341.d021960 m n, fun θ ↦ ?_⟩
  exact ⟨_root_.GD.N0096.N0341.d021965 m n hm hn θ,
    _root_.GD.N0096.N0341.d021966
      m n hm hn θ⟩

end
end GD.N0076.N0311

#print axioms _root_.GD.N0076.N0311.N0760.d022096
#print axioms _root_.GD.N0076.N0311.d022098
#print axioms _root_.GD.N0076.N0311.N0760.d022090
#print axioms _root_.GD.N0076.N0311.N0760.d022093
#print axioms _root_.GD.N0076.N0311.N0760.d022092
#print axioms _root_.GD.N0076.N0311.N0760.d022083
#print axioms _root_.GD.N0076.N0311.N0760.d022094
#print axioms _root_.GD.N0076.N0311.N0760.d022095
#print axioms _root_.GD.N0076.N0311.d022097
