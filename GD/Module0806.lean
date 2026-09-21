import GD.Module0805







set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0844
noncomputable section
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0843
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0586
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (k : ℕ) (sizes : Fin k → ℕ) (γ : _root_.GD.N0232.N0719.N0843.d012215 k)

def d012246 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d / ENNReal.ofReal (γ.value theta)

def d012247 (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) d

def d012248 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)

def d012249 : ℝ≥0∞ := _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012185 k sizes)

theorem d012250 (_hk : 0 < k) (_hsizes : ∀ i, 0 < sizes i) (C : ℝ) (hC : 0 ≤ C)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0844.d012246 k sizes γ theta d ≤ ENNReal.ofReal C ↔
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤ ENNReal.ofReal (C * γ.value theta) := by
  unfold _root_.GD.N0232.N0719.N0844.d012246
  rw [ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr
    (γ.positive theta))) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hC]



theorem d012251
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal C)).Nonempty) :
    (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012185 k sizes)
      (ENNReal.ofReal C)).Nonempty := by
  obtain ⟨d, hd, hb⟩ := hne
  have hraw : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * γ.value theta) :=
    fun theta => (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) C hC theta d).mp (hb theta)
  obtain ⟨e, he, heq, heRisk⟩ :=
    _root_.GD.N0232.N0719.N0843.d012245 k sizes γ hk hsizes C hC d hd hraw
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro b a ha omega
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
    have hg : g.d009239 = a := Real.exp_log ha
    have h := heq g omega
    simpa only [_root_.GD.N0232.N0719.N0946.d009258,
      _root_.GD.N0232.N0719.N0946.d009229.d009244, hg, show g.shift = b from rfl] using h
  · intro theta
    exact (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) C hC theta e).mpr (heRisk theta)



theorem d012252
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = _root_.GD.N0232.N0719.N0844.d012249 k sizes γ := by
  exact _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
    (_root_.GD.N0232.N0719.N0962.d012184 k sizes) (_root_.GD.N0232.N0719.N0962.d012185 k sizes) (fun _ hd => hd.1)
    (_root_.GD.N0232.N0719.N0844.d012251 k sizes γ hk hsizes)


theorem d012253
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0844.d012249 k sizes γ ≤ _root_.GD.N0232.N0719.N0844.d012247 k sizes γ d := by
  rw [← _root_.GD.N0232.N0719.N0844.d012252 k sizes γ hk hsizes]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) hd



theorem d012254
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0719.N0844.d012247 k sizes γ d ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes,
      _root_.GD.N0232.N0719.N0844.d012247 k sizes γ e ≤ _root_.GD.N0232.N0719.N0844.d012247 k sizes γ d := by
  let C := (_root_.GD.N0232.N0719.N0844.d012247 k sizes γ d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0719.N0844.d012247 k sizes γ d :=
    ENNReal.ofReal_toReal hfinite
  have hb : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal C)).Nonempty := by
    refine ⟨d, hd, ?_⟩
    intro theta
    rw [hval]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0844.d012246 k sizes γ theta d) theta
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0844.d012251 k sizes γ hk hsizes C hC hb
  refine ⟨e, he, ?_⟩
  rw [← hval]
  exact iSup_le heb



theorem d012255
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0844.d012246 k sizes γ theta d ≤ ENNReal.ofReal C) :
    ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≠ ⊤ := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((_root_.GD.N0232.N0719.N0844.d012250 k sizes γ hk hsizes C hC theta d).mp (hb theta))



theorem d012256 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
    (_root_.GD.N0232.N0719.N0962.d012184 k sizes) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) (fun _ hd => hd.1)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  exact ⟨d, ⟨hd, _root_.GD.N0232.N0719.N0844.d012255 k sizes γ (by omega) (fun i => by have := hsizes i; omega) C hC d hb⟩, hb⟩



theorem d012257
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012191 k sizes) := by
  apply _root_.GD.N0230.N0611.d003525 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
    (_root_.GD.N0232.N0719.N0962.d012190 k sizes) (_root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (fun _ hd => ⟨hd.1.1, hd.2⟩)
  intro C hC hne
  obtain ⟨d, hd, hb⟩ := hne
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0844.d012251 k sizes γ hk hsizes C hC ⟨d, hd.1, hb⟩
  exact ⟨e, ⟨he, _root_.GD.N0232.N0719.N0844.d012255 k sizes γ (by omega) (fun i => by have := hsizes i; omega) C hC e heb⟩, heb⟩


theorem d012258 : Monotone (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ) := by
  intro a b hab p hp theta
  exact (hp theta).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hab ((γ.positive theta).le)))

theorem d012259 : Monotone (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ) := by
  intro a b hab
  exact Set.image_mono (_root_.GD.N0232.N0719.N0844.d012258 k sizes γ hab)



theorem d012260 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hV : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ < ENNReal.ofReal C) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty := by
  change (⨅ d ∈ _root_.GD.N0232.N0719.N0962.d012184 k sizes, _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) d) <
    ENNReal.ofReal C at hV
  obtain ⟨d, hd⟩ := iInf_lt_iff.mp hV
  obtain ⟨hdBorel, hdRisk⟩ := iInf_lt_iff.mp hd
  have hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * γ.value theta) := by
    intro theta
    apply (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) C hC theta d).mp
    exact (le_iSup (fun theta => _root_.GD.N0232.N0719.N0844.d012246 k sizes γ theta d) theta).trans hdRisk.le
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0719.N0843.d012232 k sizes γ C d hdBorel hb
  exact ⟨p, hp⟩



theorem d012261 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfinite : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ≠ ⊤) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ (_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal).Nonempty := by
  let v := (_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0719.N0844.d012248 k sizes γ :=
    ENNReal.ofReal_toReal hfinite
  have hne : ∀ c : ℝ, v < c → (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ c).Nonempty := by
    intro c hc
    have hcpos : 0 < c := lt_of_le_of_lt hv hc
    have hlt : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ < ENNReal.ofReal c := by
      rw [← hV]
      exact (ENNReal.ofReal_lt_ofReal_iff hcpos).mpr hc
    exact (_root_.GD.N0232.N0719.N0844.d012260 k sizes γ hk hsizes c hcpos.le hlt).image _
  obtain ⟨x, hx⟩ := _root_.GD.N0230.N0586.d003514
    (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ) (_root_.GD.N0232.N0719.N0844.d012259 k sizes γ) v
    (fun c hc => _root_.GD.N0232.N0719.N0843.d012223 k sizes γ (le_trans hv hc.le)) hne
  let p := (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm x
  refine ⟨p, ?_⟩
  intro theta
  have hnorm : _root_.GD.N0232.N0719.N0844.d012246 k sizes γ theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal v := by
    apply _root_.GD.N0230.N0586.d003515 hv
    intro c hc
    apply (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) c (le_trans hv hc.le)
      theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)).mpr
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ c x).mp (hx c hc)) theta
  have hraw := (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) v hv theta
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)).mp hnorm
  simpa only [_root_.GD.N0232.N0719.N0896.d011093] using hraw


theorem d012262 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfinite : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ≠ ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0844.d012247 k sizes γ e = _root_.GD.N0232.N0719.N0844.d012248 k sizes γ := by
  let v := (_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0232.N0719.N0844.d012248 k sizes γ :=
    ENNReal.ofReal_toReal hfinite
  obtain ⟨p, hp⟩ := _root_.GD.N0232.N0719.N0844.d012261 k sizes γ hk hsizes hfinite
  have hraw : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≤
      ENNReal.ofReal (v * γ.value theta) := by
    intro theta
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact hp theta
  have hcap : (_root_.GD.N0230.N0611.d003518 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012184 k sizes)
      (ENNReal.ofReal v)).Nonempty := by
    refine ⟨_root_.GD.N0232.N0719.N0896.d011088 k sizes p, _root_.GD.N0232.N0719.N0896.d011089 k sizes p, ?_⟩
    intro theta
    exact (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ (by omega) (fun i => by have := hsizes i; omega) v hv theta _).mpr (hraw theta)
  obtain ⟨e, he, heb⟩ := _root_.GD.N0232.N0719.N0844.d012251 k sizes γ hk hsizes v hv hcap
  refine ⟨e, ⟨he, _root_.GD.N0232.N0719.N0844.d012255 k sizes γ (by omega) (fun i => by have := hsizes i; omega) v hv e heb⟩, ?_⟩
  apply le_antisymm
  · rw [← hV]
    exact iSup_le heb
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) he.1


theorem d012263 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0844.d012247 k sizes γ e = _root_.GD.N0232.N0719.N0844.d012248 k sizes γ := by
  by_cases htop : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = ⊤
  · obtain ⟨e, he⟩ := _root_.GD.N0232.N0719.N0968.d012202 k sizes hk hsizes
    refine ⟨e, he, le_antisymm ?_ (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) he.1.1)⟩
    rw [htop]
    exact le_top
  · exact _root_.GD.N0232.N0719.N0844.d012262 k sizes γ hk hsizes htop



theorem d012264 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      _root_.GD.N0232.N0719.N0844.d012247 k sizes γ e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012190 k sizes) ∧
      _root_.GD.N0232.N0719.N0844.d012247 k sizes γ e =
        _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ) (_root_.GD.N0232.N0719.N0962.d012191 k sizes) := by
  obtain ⟨e, he, hval⟩ := _root_.GD.N0232.N0719.N0844.d012263 k sizes γ hk hsizes
  have hD := _root_.GD.N0232.N0719.N0844.d012256 k sizes γ hk hsizes
  have hE := _root_.GD.N0232.N0719.N0844.d012257 k sizes γ hk hsizes
  exact ⟨e, he, ⟨he.1.1, he.2⟩, hval.trans hD, (hval.trans hD).trans hE⟩


end
end GD.N0232.N0719.N0844

#print axioms _root_.GD.N0232.N0719.N0844.d012257
#print axioms _root_.GD.N0232.N0719.N0844.d012261
#print axioms _root_.GD.N0232.N0719.N0844.d012264
