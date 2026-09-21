import GD.Module0527
import GD.Module1416
import GD.Module1851

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0065
noncomputable section
open _root_.GD.N0024 _root_.GD.N0024.N0277
open _root_.GD.N0023
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256

def d030413 (t : _root_.GD.N0024.N0277.d007878) : _root_.GD.N0024.N0277.d007878 := ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem d030414 (t : _root_.GD.N0024.N0277.d007878) : _root_.GD.N0065.d030413 (_root_.GD.N0065.d030413 t) = t := by
  apply Subtype.ext
  dsimp [_root_.GD.N0065.d030413]
  ring

@[simp] theorem d030415 (t : _root_.GD.N0024.N0277.d007878) : _root_.GD.N0024.N0277.d007879 (_root_.GD.N0065.d030413 t) = _root_.GD.N0024.N0277.d007879 t := by
  dsimp [_root_.GD.N0024.N0277.d007879, _root_.GD.N0065.d030413]
  ring

theorem d030416 {Ω : Type*} [MeasurableSpace Ω]
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) (g : Ω → ℝ) (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0024.N0277.d007882 (fun s => Q (_root_.GD.N0065.d030413 s)) (fun z => 1 - g z) t =
      _root_.GD.N0024.N0277.d007882 Q g (_root_.GD.N0065.d030413 t) := by
  unfold _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0277.d007881
  rw [_root_.GD.N0065.d030415]
  congr 1
  apply integral_congr_ae (ae_of_all _ fun z => ?_)
  dsimp [_root_.GD.N0065.d030413]
  ring

private theorem d030417 {Ω : Type*} (g : Ω → ℝ)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    ∀ z, 1 - g z ∈ Icc (0 : ℝ) 1 := by
  intro z
  constructor <;> linarith [(hb z).1, (hb z).2]


theorem d030418 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (hf : Measurable f)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (hfb : ∀ z, f z ∈ Icc (0 : ℝ) 1)
    (d V h H C : ℝ) (hd : 0 < d) (hdhalf : d < 1 / 2) (hh : 0 < h) (hH : 0 < H)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) g t ≤ V)
    (hgright : ∀ t : _root_.GD.N0024.N0277.d007878, 1 - d < t.1 →
      _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) g t ≤ V - h)
    (hfcap : ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) f t ≤ C)
    (hfleft : ∀ t : _root_.GD.N0024.N0277.d007878, t.1 < d →
      _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) f t ≤ V - H)
    (hminimax : ∀ u : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable u →
      (∀ z, u z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) u t) : False := by
  let Q := _root_.GD.N0023.N0261.d021897 m n hm hn
  let Q' := fun t => Q (_root_.GD.N0065.d030413 t)
  let g' := fun z => 1 - g z
  let f' := fun z => 1 - f z
  have hg' : Measurable g' := measurable_const.sub hg
  have hf' : Measurable f' := measurable_const.sub hf
  have hgb' : ∀ z, g' z ∈ Icc (0 : ℝ) 1 := _root_.GD.N0065.d030417 g hgb
  have hfb' : ∀ z, f' z ∈ Icc (0 : ℝ) 1 := _root_.GD.N0065.d030417 f hfb
  have hcap' : ∀ t, _root_.GD.N0024.N0277.d007882 Q' g' t ≤ V := fun t => by
    rw [_root_.GD.N0065.d030416]
    exact hcap (_root_.GD.N0065.d030413 t)
  let t₀ : _root_.GD.N0024.N0277.d007878 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hQ' : ∀ t : _root_.GD.N0024.N0277.d007878, Q' t ≪ Q' t₀ := fun t =>
    _root_.GD.N0232.N0720.N1436.d013292 hm hn (_root_.GD.N0065.d030413 t).2.1 (_root_.GD.N0065.d030413 t).2.2
      (_root_.GD.N0065.d030413 t₀).2.1 (_root_.GD.N0065.d030413 t₀).2.2
  have hlower := _root_.GD.N0024.N0277.d007894 Q' (Q' t₀) hQ' g' hg' hgb'
    (d / 2) V (by positivity) hcap'
  have hdomain : ∀ᵐ z ∂Q' t₀, z ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    (_root_.GD.N0023.N0261.d021899 m n hm hn (_root_.GD.N0065.d030413 t₀)).ae_le
      (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)
  have heq : Q' t₀ ({z | g' z < d / 2} ∩ _root_.GD.N0232.N0720.N1436.d013218) =
      Q' t₀ {z | g' z < d / 2} := by
    apply measure_congr
    filter_upwards [hdomain] with z hz
    exact propext (and_iff_left hz)
  have hinter : MeasurableSet ({z | g' z < d / 2} ∩ _root_.GD.N0232.N0720.N1436.d013218) :=
    (measurableSet_lt hg' measurable_const).inter _root_.GD.N0232.N0720.N1436.d013219
  have hpos : 0 < Q' t₀ ({z | g' z < d / 2} ∩ _root_.GD.N0232.N0720.N1436.d013218) := heq ▸ hlower
  obtain ⟨E, hEsub, hEc, hEpos⟩ :=
    hinter.exists_lt_isCompact_of_ne_top (measure_ne_top (Q' t₀) _) hpos
  have hEref : 0 < _root_.GD.N0232.N0720.N1436.d013288 E := by
    by_contra hnot
    have hz := _root_.GD.N0023.N0261.d021899 m n hm hn (_root_.GD.N0065.d030413 t₀)
      (le_antisymm (not_lt.mp hnot) bot_le)
    exact hEpos.ne' hz
  have hED : E ⊆ _root_.GD.N0232.N0720.N1436.d013218 := hEsub.trans inter_subset_right
  obtain ⟨M, k, hM, hk, hupper, hlower⟩ := _root_.GD.N0023.N0261.d021902
    m n hm hn E E hEc hED hEc.measurableSet (Subset.refl E) hEref d hd hdhalf
  apply _root_.GD.N0065.d007901 Q' E hEc.measurableSet g' f' hg' hf' hgb' hfb'
    d V h H k M C hd (by linarith) hh hH hk hM
    (fun z hz => (hEsub hz).1.le) hcap'
  · intro t ht
    rw [_root_.GD.N0065.d030416]
    exact hgright (_root_.GD.N0065.d030413 t) (by dsimp [_root_.GD.N0065.d030413]; linarith)
  · intro t
    rw [_root_.GD.N0065.d030416]
    exact hfcap (_root_.GD.N0065.d030413 t)
  · intro t ht
    rw [_root_.GD.N0065.d030416]
    exact hfleft (_root_.GD.N0065.d030413 t) (by dsimp [_root_.GD.N0065.d030413]; linarith)
  · intro t
    simpa only [_root_.GD.N0065.d030415] using hupper (_root_.GD.N0065.d030413 t)
  · intro t ht ht'
    have hh := hlower (_root_.GD.N0065.d030413 t) (by dsimp [_root_.GD.N0065.d030413]; linarith) (by dsimp [_root_.GD.N0065.d030413]; linarith)
    simpa only [_root_.GD.N0065.d030415] using hh
  · intro u hu hub ε hε
    obtain ⟨t, ht⟩ := hminimax (fun z => 1 - u z) (measurable_const.sub hu)
      (_root_.GD.N0065.d030417 u hub) ε hε
    refine ⟨_root_.GD.N0065.d030413 t, ?_⟩
    have he : _root_.GD.N0024.N0277.d007882 Q' u (_root_.GD.N0065.d030413 t) = _root_.GD.N0024.N0277.d007882 Q (fun z => 1 - u z) t := by
      have hh := _root_.GD.N0065.d030416 Q (fun z => 1 - u z) (_root_.GD.N0065.d030413 t)
      simpa only [_root_.GD.N0065.d030414, sub_sub_cancel] using hh
    rw [he]
    exact ht


theorem d030419 (m n : ℕ) (hm : 2 ≤ m) (hn : 4 ≤ n)
    (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hf : Measurable f)
    (hfb : ∀ z, f z ∈ Icc (0 : ℝ) 1) (C : ℝ)
    (hfcap : ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm (by omega)) f t ≤ C)
    (hfzero : ∀ t : ℕ → _root_.GD.N0024.N0277.d007878,
      Tendsto (fun j => (t j).1) atTop (𝓝 0) →
      Tendsto (fun j => _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm (by omega)) f (t j))
        atTop (𝓝 0)) :
    _root_.GD.N0046.N0305.d030202 m n hm (by omega) = ∅ := by
  have hfin : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply (_root_.GD.N0230.N0611.d003520
      (_root_.GD.N0232.N0720.N1256.d015547 m n)
      (_root_.GD.N0232.N0720.N1398.d019599 m n hf)).trans
    apply iSup_le
    intro θ
    rw [_root_.GD.N0023.N0262.d021911 m n hm (by omega) f hf hfb]
    exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl (hfcap _))
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hK
  let v := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal hfin).symm
  obtain ⟨g, hg, hgb, hbound⟩ := _root_.GD.N0024.N0270.d030252
    m n hm (by omega) v hv hvalue hK
  have hcap := _root_.GD.N0023.N0262.d021914 m n hm (by omega)
    g hg hgb v hv (fun θ => (hbound θ).1)
  have hbase := _root_.GD.N0023.N0262.d021920 m n hm (by omega)
    g hg hgb (fun θ => (hbound θ).2)
  have hQ : ∀ t : _root_.GD.N0024.N0277.d007878, _root_.GD.N0023.N0261.d021897 m n hm (by omega) t ≪
      _root_.GD.N0023.N0261.d021897 m n hm (by omega) _root_.GD.N0024.N0276.d007902 := fun t =>
    _root_.GD.N0232.N0720.N1436.d013292 hm (by omega) t.2.1 t.2.2
      _root_.GD.N0024.N0276.d007902.2.1 _root_.GD.N0024.N0276.d007902.2.2
  have hV := _root_.GD.N0024.N0276.d007903
    (_root_.GD.N0023.N0261.d021897 m n hm (by omega)) hQ g hg hgb (v - 1) hcap
  obtain ⟨d₁, hd₁, hleft⟩ := _root_.GD.N0023.N0258.d021877
    (_root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm (by omega)) f) hfzero ((v - 1) / 2) (by positivity)
  obtain ⟨d₂, hd₂, hright⟩ := _root_.GD.N0023.N0258.d021878
    (_root_.GD.N0023.N0258.d021868 m n) (_root_.GD.N0065.d022701 m n hm hn)
    ((v - 1) / 2) (by positivity)
  let d := min d₁ (min d₂ (1 / 4))
  have hd : 0 < d := lt_min hd₁ (lt_min hd₂ (by norm_num))
  have hdd₁ : d ≤ d₁ := min_le_left _ _
  have hdd₂ : d ≤ d₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hdhalf : d < 1 / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  apply _root_.GD.N0065.d030418 m n hm (by omega) g f hg hf hgb hfb
    d (v - 1) ((v - 1) / 2) ((v - 1) / 2) C hd hdhalf (by positivity) (by positivity) hcap
  · intro t ht
    have h := (hbase t).trans (hright t (by linarith))
    linarith
  · exact hfcap
  · intro t ht
    have h := hleft t (ht.trans_le hdd₁)
    linarith
  · exact _root_.GD.N0023.N0262.d021915 m n hm (by omega) v hvalue (by linarith)

end
end GD.N0065

#print axioms _root_.GD.N0065.d030416
#print axioms _root_.GD.N0065.d030418
#print axioms _root_.GD.N0065.d030419
