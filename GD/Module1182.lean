import GD.Module0065
import GD.Module1161






















open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1506

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0624
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0137
open _root_.GD.N0107

variable (m n : ℕ)




abbrev d018997 := Equiv.Perm (Fin m) × Equiv.Perm (Fin n)


def d018998 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1080.d014170 m n :=
  (ω.1 ∘ ⇑g.1, ω.2 ∘ ⇑g.2)

theorem d018999 : _root_.GD.N0232.N0720.N1506.d018998 m n 1 = id := by
  funext ω
  exact Prod.ext rfl rfl

theorem d019000 (g h : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0232.N0720.N1506.d018998 m n h ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g =
      _root_.GD.N0232.N0720.N1506.d018998 m n (g * h) := by
  funext ω
  exact Prod.ext rfl rfl

theorem d019001 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    Measurable (_root_.GD.N0232.N0720.N1506.d018998 m n g) := by
  unfold _root_.GD.N0232.N0720.N1506.d018998
  first
    | fun_prop
    | exact Measurable.prodMk
        (measurable_pi_lambda _ (fun i =>
          (measurable_pi_apply (g.1 i)).comp measurable_fst))
        (measurable_pi_lambda _ (fun j =>
          (measurable_pi_apply (g.2 j)).comp measurable_snd))


theorem d019002 {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun x : _root_.GD.N0137.d008894 k => x ∘ ⇑σ)
      (_root_.GD.N0137.d008895 k) (_root_.GD.N0137.d008895 k) := by
  have h := measurePreserving_arrowCongr'
    (fun _ : Fin k => gaussianReal 0 1) (fun _ : Fin k => gaussianReal 0 1)
    σ.symm (MeasurableEquiv.refl ℝ)
    (fun _ => by
      first
        | exact MeasurePreserving.id _
        | exact ⟨(MeasurableEquiv.refl ℝ).measurable, by simp⟩)
  have hfun :
      ⇑(MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)) =
        fun x : _root_.GD.N0137.d008894 k => x ∘ ⇑σ := by
    funext x i
    first
      | rfl
      | simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  unfold _root_.GD.N0137.d008895 _root_.GD.N0140.d006650
  rw [← hfun]
  exact h

theorem d019003 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1506.d018998 m n g)
      (_root_.GD.N0137.d008914 m n) (_root_.GD.N0137.d008914 m n) := by
  unfold _root_.GD.N0137.d008914
  exact (_root_.GD.N0232.N0720.N1506.d019002 g.1).prod (_root_.GD.N0232.N0720.N1506.d019002 g.2)

theorem d019004 (μ σ τ : ℝ) (g : _root_.GD.N0232.N0720.N1506.d018997 m n)
    (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0107.d009024 m n μ σ τ (_root_.GD.N0232.N0720.N1506.d018998 m n g ω) =
      _root_.GD.N0232.N0720.N1506.d018998 m n g (_root_.GD.N0107.d009024 m n μ σ τ ω) := by
  exact Prod.ext rfl rfl


theorem d019005 (θ : _root_.GD.N0232.N0720.N1080.d014168) (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1506.d018998 m n g) (_root_.GD.N0232.N0720.N1080.d014171 m n θ) (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
  refine ⟨_root_.GD.N0232.N0720.N1506.d019001 m n g, ?_⟩
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1506.d019001 m n g)
    (_root_.GD.N0107.d009026 m n _ _ _)]
  have hcomm :
      _root_.GD.N0232.N0720.N1506.d018998 m n g ∘ _root_.GD.N0107.d009024 m n θ.location θ.scale₁ θ.scale₂ =
        _root_.GD.N0107.d009024 m n θ.location θ.scale₁ θ.scale₂ ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g := by
    funext ω
    exact (_root_.GD.N0232.N0720.N1506.d019004 m n _ _ _ g ω).symm
  rw [hcomm, ← Measure.map_map (_root_.GD.N0107.d009026 m n _ _ _)
    (_root_.GD.N0232.N0720.N1506.d019001 m n g),
    (_root_.GD.N0232.N0720.N1506.d019003 m n g).map_eq]

theorem d019006 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1506.d018998 m n g)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1506.d019005 m n _root_.GD.N0232.N0720.N1080.d014169 g




def d019007 (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1506.d018998 m n g)
    (_root_.GD.N0232.N0720.N1506.d019006 m n g)

theorem d019008
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f f' : α → β} (h : f = f')
    (hf : MeasurePreserving f μ ν) (hf' : MeasurePreserving f' μ ν)
    (x : Lp ℝ 2 ν) :
    Lp.compMeasurePreserving f hf x = Lp.compMeasurePreserving f' hf' x := by
  subst h
  rfl

theorem d019009 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1506.d019007 m n 1 x = x := by
  unfold _root_.GD.N0232.N0720.N1506.d019007
  rw [_root_.GD.N0232.N0720.N1506.d019008 (_root_.GD.N0232.N0720.N1506.d018999 m n) _
    (MeasurePreserving.id _)]
  exact Lp.compMeasurePreserving_id_apply x

theorem d019010 (g h : _root_.GD.N0232.N0720.N1506.d018997 m n) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1506.d019007 m n h x) = _root_.GD.N0232.N0720.N1506.d019007 m n (g * h) x := by
  unfold _root_.GD.N0232.N0720.N1506.d019007
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact _root_.GD.N0232.N0720.N1506.d019008 (_root_.GD.N0232.N0720.N1506.d019000 m n g h) _ _ x


theorem d019011 (θ : _root_.GD.N0232.N0720.N1080.d014168) (g : _root_.GD.N0232.N0720.N1506.d018997 m n)
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1506.d019007 m n g x) = _root_.GD.N0232.N0720.N1080.d014182 m n θ x := by
  have hpres := _root_.GD.N0232.N0720.N1506.d019006 m n g
  have h1 : (fun ω => x ω) =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1506.d018998 m n g)]
      _root_.GD.N0232.N0720.N1214.d014265 m n x := by
    rw [hpres.map_eq]
    exact (_root_.GD.N0232.N0720.N1214.d014267 m n x).symm
  have h2 : (fun ω => x ω) ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014265 m n x ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g :=
    MeasureTheory.ae_eq_comp (_root_.GD.N0232.N0720.N1506.d019001 m n g).aemeasurable h1
  have hae : ⇑(_root_.GD.N0232.N0720.N1506.d019007 m n g x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014265 m n x ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g :=
    (Lp.coeFn_compMeasurePreserving x hpres).trans h2
  have hmem : MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n x ∘ _root_.GD.N0232.N0720.N1506.d018998 m n g) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1214.d014268 m n x).comp_measurePreserving hpres
  have heq : _root_.GD.N0232.N0720.N1506.d019007 m n g x = MemLp.toLp _ hmem :=
    Lp.ext (hae.trans hmem.coeFn_toLp.symm)
  rw [heq, ← _root_.GD.N0232.N0720.N1080.d014198 m n θ _ hmem,
    ← _root_.GD.N0232.N0720.N1215.d014286 m n θ x]
  unfold _root_.GD.N0232.N0720.N1080.d014197
  have hmeas :
      Measurable (fun ω => ENNReal.ofReal ((_root_.GD.N0232.N0720.N1214.d014265 m n x ω - θ.location) ^ 2)) :=
    (((_root_.GD.N0232.N0720.N1214.d014266 m n x).sub measurable_const).pow_const 2).ennreal_ofReal
  conv_rhs => rw [← (_root_.GD.N0232.N0720.N1506.d019005 m n θ g).map_eq]
  rw [lintegral_map hmeas (_root_.GD.N0232.N0720.N1506.d019001 m n g)]
  rfl



theorem d019012 {ι : Type*} (s : Finset ι)
    (x : ι → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ⇑(∑ i ∈ s, x i) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] fun ω => ∑ i ∈ s, x i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := _root_.GD.N0232.N0720.N1080.d014172 m n)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with ω hω
    simp only [Pi.add_apply, hω, Finset.sum_insert ha]



theorem d019013 {G : Type*} [Fintype G] [Nonempty G] (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (x : G → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ ((Fintype.card G : ℝ)⁻¹ • ∑ g, x g) ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g, _root_.GD.N0232.N0720.N1080.d014182 m n θ (x g) := by
  have hk : 0 < Fintype.card G := Fintype.card_pos
  have hkR : (0 : ℝ) < Fintype.card G := by exact_mod_cast hk
  have hk0 : (Fintype.card G : ℝ) ≠ 0 := hkR.ne'
  have hc : (0 : ℝ) < (Fintype.card G : ℝ)⁻¹ := inv_pos.mpr hkR
  have hac := _root_.GD.N0232.N0720.N1080.d014173 m n θ
  have hae : ⇑((Fintype.card G : ℝ)⁻¹ • ∑ g, x g) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun ω => (Fintype.card G : ℝ)⁻¹ * ∑ g, x g ω := by
    refine (Lp.coeFn_smul _ _).trans ?_
    filter_upwards [_root_.GD.N0232.N0720.N1506.d019012 m n Finset.univ x] with ω hω
    simp only [Pi.smul_apply, hω, smul_eq_mul]
  have haeθ := hac.ae_le hae
  unfold _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
  have hpt : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ,
      ENNReal.ofReal
          ((((Fintype.card G : ℝ)⁻¹ • ∑ g, x g) ω - θ.location) ^ 2) ≤
        ENNReal.ofReal ((Fintype.card G : ℝ)⁻¹) *
          ∑ g, ENNReal.ofReal ((x g ω - θ.location) ^ 2) := by
    filter_upwards [haeθ] with ω hω
    rw [hω]
    have hcenter :
        (Fintype.card G : ℝ)⁻¹ * ∑ g, x g ω - θ.location =
          (Fintype.card G : ℝ)⁻¹ * ∑ g, (x g ω - θ.location) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_sub, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]
    rw [hcenter, ← ENNReal.ofReal_sum_of_nonneg (fun g _ => sq_nonneg _),
      ← ENNReal.ofReal_mul hc.le]
    apply ENNReal.ofReal_le_ofReal
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset G))
      (f := fun g => x g ω - θ.location)
    rw [Finset.card_univ] at hcs
    rw [mul_pow]
    calc ((Fintype.card G : ℝ)⁻¹) ^ 2 *
          (∑ g, (x g ω - θ.location)) ^ 2
        ≤ ((Fintype.card G : ℝ)⁻¹) ^ 2 *
          ((Fintype.card G : ℝ) * ∑ g, (x g ω - θ.location) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (Fintype.card G : ℝ)⁻¹ *
            ((Fintype.card G : ℝ)⁻¹ * (Fintype.card G : ℝ)) *
            ∑ g, (x g ω - θ.location) ^ 2 := by ring
      _ = (Fintype.card G : ℝ)⁻¹ * ∑ g, (x g ω - θ.location) ^ 2 := by
          rw [inv_mul_cancel₀ hk0, mul_one]
  calc ∫⁻ ω, ENNReal.ofReal
          ((((Fintype.card G : ℝ)⁻¹ • ∑ g, x g) ω - θ.location) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ
      ≤ ∫⁻ ω, ENNReal.ofReal ((Fintype.card G : ℝ)⁻¹) *
          ∑ g, ENNReal.ofReal ((x g ω - θ.location) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((Fintype.card G : ℝ)⁻¹) *
          ∑ g, ∫⁻ ω, ENNReal.ofReal ((x g ω - θ.location) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro g _
        exact ((((Lp.aestronglyMeasurable (x g)).mono_ac hac).aemeasurable.sub
          aemeasurable_const).pow_const 2).ennreal_ofReal
    _ = (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g, _root_.GD.N0232.N0720.N1080.d014182 m n θ (x g) := by
        rw [ENNReal.ofReal_inv_of_pos hkR, ENNReal.ofReal_natCast]
        rfl





def d019014 :
    _root_.GD.N0230.N0624.d000770 (G := _root_.GD.N0232.N0720.N1506.d018997 m n) (_root_.GD.N0232.N0720.N1080.d014182 m n) _root_.GD.N0232.N0720.N1080.d014169 where
  act := _root_.GD.N0232.N0720.N1506.d019007 m n
  pact := fun _ θ => θ
  act_one := _root_.GD.N0232.N0720.N1506.d019009 m n
  act_mul := _root_.GD.N0232.N0720.N1506.d019010 m n
  map_add := fun g x y => map_add (Lp.compMeasurePreserving _ _) x y
  map_smul := fun g c x =>
    LinearMap.map_smul (Lp.compMeasurePreservingₗ ℝ (_root_.GD.N0232.N0720.N1506.d018998 m n g)
      (_root_.GD.N0232.N0720.N1506.d019006 m n g)) c x
  norm_map := fun g x => Lp.norm_compMeasurePreserving x _
  risk_map := fun g θ x => _root_.GD.N0232.N0720.N1506.d019011 m n θ g x
  href := fun d => by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    simp only [zero_sub, norm_neg]
  risk_avg := fun θ x => _root_.GD.N0232.N0720.N1506.d019013 m n θ x


theorem d019015
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d)
    (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g d = d :=
  _root_.GD.N0230.N0624.d000775 (_root_.GD.N0232.N0720.N1506.d019014 m n) d (fun _ _ => rfl) hd g



theorem d019016 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1506.d018997 m n) :
    _root_.GD.N0232.N0720.N1506.d019007 m n g (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) = _root_.GD.N0232.N0720.N1080.d014191 m n hm hn :=
  _root_.GD.N0232.N0720.N1506.d019015 m n _
    (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1 g


theorem d019017
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ↔
      (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g d = d) ∧
        ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) →
          _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d :=
  _root_.GD.N0230.N0624.d000784 (_root_.GD.N0232.N0720.N1506.d019014 m n) d
    (fun _ _ => rfl)





theorem d019018
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g s.value = s.value) ∧
          ∀ e, (∀ g, _root_.GD.N0232.N0720.N1506.d019007 m n g e = e) →
            _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e s.value → e = s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨hsym, hsu⟩ :=
      (_root_.GD.N0232.N0720.N1506.d019017 m n s.value).1 ht
    exact ⟨s, hs, hsym, hsu⟩
  · rintro ⟨s, hs, hsym, hsu⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1506.d019017 m n s.value).2
        ⟨hsym, hsu⟩⟩

end

end N1506
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1506.d019015
#print axioms _root_.GD.N0232.N0720.N1506.d019016
#print axioms _root_.GD.N0232.N0720.N1506.d019017
#print axioms _root_.GD.N0232.N0720.N1506.d019018
