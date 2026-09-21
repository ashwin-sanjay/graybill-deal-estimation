import GD.Module1541
import GD.Module1458
import GD.Module0629
import GD.Module0982
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0086
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0719 (d009174)
open _root_.GD.N0137 _root_.GD.N0107


theorem d023900 {m M : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : Fin m → Fin M) (he : Function.Injective e) :
    MeasurePreserving (fun x : Fin M → ℝ => x ∘ e)
      (Measure.pi fun _ : Fin M => μ) (Measure.pi fun _ : Fin m => μ) := by
  have hi := (iIndepFun_pi (μ := fun _ : Fin M => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp he
  have hh := hi.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (e i)).aemeasurable)
  refine ⟨by fun_prop, ?_⟩
  change Measure.map (fun x i => x (e i)) (Measure.pi fun _ : Fin M => μ) = _
  rw [hh]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin M => μ) (e i)).map_eq


theorem d023901 {m M : ℕ} (e : Fin m → Fin M)
    (he : Function.Injective e) (location scale : ℝ) :
    MeasurePreserving (fun x : Fin M → ℝ => x ∘ e)
      (_root_.GD.N0232.N0719.d009174 M location scale) (_root_.GD.N0232.N0719.d009174 m location scale) := by
  have hs : MeasurePreserving (fun x : Fin M → ℝ => x ∘ e)
      (_root_.GD.N0137.d008895 M) (_root_.GD.N0137.d008895 m) :=
    _root_.GD.N0086.d023900 (gaussianReal 0 1) e he
  refine ⟨by fun_prop, ?_⟩
  unfold _root_.GD.N0232.N0719.d009174
  rw [Measure.map_map (by fun_prop) (_root_.GD.N0107.d009020 M location scale),
    ← hs.map_eq, Measure.map_map (_root_.GD.N0107.d009020 m location scale) hs.measurable]
  rfl


def d023902 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (x : _root_.GD.N0232.N0720.N1080.d014170 M N) : _root_.GD.N0232.N0720.N1080.d014170 m n :=
  (x.1 ∘ Fin.castLE hm, x.2 ∘ Fin.castLE hn)

theorem d023903 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N) :
    Measurable (_root_.GD.N0086.d023902 hm hn) := by unfold _root_.GD.N0086.d023902; fun_prop

theorem d023904 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    MeasurePreserving (_root_.GD.N0086.d023902 hm hn) (_root_.GD.N0232.N0720.N1080.d014171 M N θ) (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by
  have h₁ := _root_.GD.N0086.d023901 (Fin.castLE hm) (Fin.castLE_injective hm)
    θ.location θ.scale₁
  have h₂ := _root_.GD.N0086.d023901 (Fin.castLE hn) (Fin.castLE_injective hn)
    θ.location θ.scale₂
  change MeasurePreserving
    (Prod.map (fun x : Fin M → ℝ => x ∘ Fin.castLE hm)
      (fun x : Fin N → ℝ => x ∘ Fin.castLE hn)) _ _
  simpa only [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.d009061, _root_.GD.N0232.N0719.d009174]
    using h₁.prod h₂

def d023905 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : _root_.GD.N0232.N0720.N1080.d014170 M N → ℝ := d ∘ _root_.GD.N0086.d023902 hm hn

theorem d023906 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) : Measurable (_root_.GD.N0086.d023905 hm hn d) :=
  hd.comp (_root_.GD.N0086.d023903 hm hn)


theorem d023907 {m n M N : ℕ} (hm : m ≤ M) (hn : n ≤ N)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 M N θ (_root_.GD.N0086.d023905 hm hn d) = _root_.GD.N0232.N0720.N1080.d014197 m n θ d := by
  unfold _root_.GD.N0232.N0720.N1080.d014197
  rw [← (_root_.GD.N0086.d023904 hm hn θ).map_eq]
  exact (lintegral_map (show Measurable (fun x => ENNReal.ofReal ((d x - θ.location) ^ 2)) by fun_prop)
    (_root_.GD.N0086.d023903 hm hn)).symm

end
end GD.N0086

#print axioms _root_.GD.N0086.d023900
#print axioms _root_.GD.N0086.d023901
#print axioms _root_.GD.N0086.d023904
#print axioms _root_.GD.N0086.d023907


set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0086
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611


theorem d023908 {m n M N : ℕ} (hm : 1 ≤ m) (hM : 1 ≤ M)
    (K : ℝ) (_hK : 0 < K) (h₁ : (M : ℝ) ≤ K * m) (h₂ : (N : ℝ) ≤ K * n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1257.d015508 m n θ ≤ K * _root_.GD.N0232.N0720.N1257.d015508 M N θ := by
  have hp : 0 < (m : ℝ) / θ.scale₁ ^ 2 + (n : ℝ) / θ.scale₂ ^ 2 := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact add_pos_of_pos_of_nonneg (div_pos hm' (sq_pos_of_pos θ.scale₁_pos)) (by positivity)
  have hP : 0 < (M : ℝ) / θ.scale₁ ^ 2 + (N : ℝ) / θ.scale₂ ^ 2 := by
    have hM' : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    exact add_pos_of_pos_of_nonneg (div_pos hM' (sq_pos_of_pos θ.scale₁_pos)) (by positivity)
  have hprec : (M : ℝ) / θ.scale₁ ^ 2 + (N : ℝ) / θ.scale₂ ^ 2 ≤
      K * ((m : ℝ) / θ.scale₁ ^ 2 + (n : ℝ) / θ.scale₂ ^ 2) := by
    calc
      _ ≤ (K * m) / θ.scale₁ ^ 2 + (K * n) / θ.scale₂ ^ 2 :=
        add_le_add (div_le_div_of_nonneg_right h₁ (sq_nonneg _))
          (div_le_div_of_nonneg_right h₂ (sq_nonneg _))
      _ = _ := by ring
  have ho : (1 : ℝ) / ((m : ℝ) / θ.scale₁ ^ 2 + (n : ℝ) / θ.scale₂ ^ 2) ≤
      K / ((M : ℝ) / θ.scale₁ ^ 2 + (N : ℝ) / θ.scale₂ ^ 2) :=
    (div_le_div_iff₀ hp hP).mpr (by simpa only [one_mul] using hprec)
  simpa only [_root_.GD.N0232.N0720.N1257.d015508, one_div, div_eq_mul_inv, one_mul] using ho


theorem d023909 {m n M N : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hM : m ≤ M) (hN : n ≤ N)
    (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 m n θ d ≤ ENNReal.ofReal C) :
    Measurable (_root_.GD.N0086.d023905 hM hN d) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 M N θ (_root_.GD.N0086.d023905 hM hN d) ≤
        ENNReal.ofReal (C * ((M : ℝ) + N)) := by
  have hK : 0 < (M : ℝ) + N := by
    have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : (M : ℝ) ≤ ((M : ℝ) + N) * m := by
    have hh := mul_nonneg hK.le (sub_nonneg.mpr hm')
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h₂ : (N : ℝ) ≤ ((M : ℝ) + N) * n := by
    have hh := mul_nonneg hK.le (sub_nonneg.mpr hn')
    nlinarith [Nat.cast_nonneg (α := ℝ) M]
  refine ⟨_root_.GD.N0086.d023906 hM hN d hd, ?_⟩
  intro θ
  apply (_root_.GD.N0232.N0720.N1256.d015553 M N (by omega) _ (by positivity) θ _).mpr
  rw [_root_.GD.N0086.d023907 hM hN d hd θ]
  have hb := (_root_.GD.N0232.N0720.N1256.d015553 m n hm C hC θ d).mp (hcap θ)
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have ho := _root_.GD.N0086.d023908 hm (by omega) ((M : ℝ) + N) hK h₁ h₂ θ
  calc
    C * _root_.GD.N0232.N0720.N1257.d015508 m n θ ≤ C * (((M : ℝ) + N) * _root_.GD.N0232.N0720.N1257.d015508 M N θ) :=
      mul_le_mul_of_nonneg_left ho hC
    _ = _ := by ring


theorem d023910 {m n M N : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hM : m ≤ M) (hN : n ≤ N)
    (hf : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) : _root_.GD.N0232.N0720.N1256.d015549 M N ≠ ⊤ := by
  obtain ⟨d, hd, hv⟩ := _root_.GD.N0232.N0720.N1222.d015569 m n hm hn hf
  let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 m n θ d ≤ ENNReal.ofReal C := by
    intro θ
    rw [ENNReal.ofReal_toReal hf, ← hv]
    exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 m n θ d) θ
  obtain ⟨he, hb⟩ := _root_.GD.N0086.d023909 (by omega) (by omega) hM hN C hC d hd.1.1 hcap
  have hw : _root_.GD.N0232.N0720.N1256.d015548 M N (_root_.GD.N0086.d023905 hM hN d) ≤
      ENNReal.ofReal (C * ((M : ℝ) + N)) := iSup_le hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 M N) he).trans hw)


theorem d023911 {m n M N : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hM : m ≤ M) (hN : n ≤ N)
    (h : _root_.GD.N0232.N0720.N1256.d015549 M N = ⊤) : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤ := by
  by_contra hf
  exact _root_.GD.N0086.d023910 hm hn hM hN hf h

theorem d023912 (h : _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤) :
    _root_.GD.N0232.N0720.N1256.d015549 2 3 = ⊤ :=
  _root_.GD.N0086.d023911 (by decide) (by decide) (by decide) (by decide) h

end
end GD.N0086

#print axioms _root_.GD.N0086.d023908
#print axioms _root_.GD.N0086.d023909
#print axioms _root_.GD.N0086.d023910
#print axioms _root_.GD.N0086.d023911
#print axioms _root_.GD.N0086.d023912

namespace GD.N0086
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611

def d023913 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := θ.location
  scale₁ := θ.scale₂
  scale₂ := θ.scale₁
  scale₁_pos := θ.scale₂_pos
  scale₂_pos := θ.scale₁_pos

theorem d023914 (m n : ℕ) (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1256.d015547 n m θ (d ∘ Prod.swap) =
      _root_.GD.N0232.N0720.N1256.d015547 m n (_root_.GD.N0086.d023913 θ) d := by
  have hmp : MeasurePreserving Prod.swap (_root_.GD.N0232.N0720.N1080.d014171 n m θ) (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0086.d023913 θ)) := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.d009061, _root_.GD.N0086.d023913,
      _root_.GD.N0232.N0719.d009174] using
      (Measure.measurePreserving_swap (μ := _root_.GD.N0232.N0719.d009174 n θ.location θ.scale₁)
        (ν := _root_.GD.N0232.N0719.d009174 m θ.location θ.scale₂))
  have hr : _root_.GD.N0232.N0720.N1080.d014197 n m θ (d ∘ Prod.swap) =
      _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0086.d023913 θ) d := by
    unfold _root_.GD.N0232.N0720.N1080.d014197
    rw [← hmp.map_eq]
    exact (lintegral_map
      (show Measurable (fun x => ENNReal.ofReal ((d x - θ.location) ^ 2)) by fun_prop)
      measurable_swap).symm
  have ho : _root_.GD.N0232.N0720.N1257.d015508 n m θ = _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0086.d023913 θ) := by
    simp only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0086.d023913, add_comm]
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [hr, ho]

theorem d023915 (m n : ℕ) : _root_.GD.N0232.N0720.N1256.d015549 n m ≤ _root_.GD.N0232.N0720.N1256.d015549 m n := by
  change _ ≤ ⨅ d ∈ _root_.GD.N0232.N0720.N1256.d015545 m n, _root_.GD.N0232.N0720.N1256.d015548 m n d
  refine le_iInf fun d => le_iInf fun hd => ?_
  have hd' : Measurable d := hd
  have hmeas : Measurable (d ∘ Prod.swap) := hd'.comp measurable_swap
  apply (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 n m) hmeas).trans
  apply iSup_le
  intro θ
  rw [_root_.GD.N0086.d023914 m n θ d hd']
  exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 m n θ d) (_root_.GD.N0086.d023913 θ)


theorem d023916 (m n : ℕ) : _root_.GD.N0232.N0720.N1256.d015549 n m = _root_.GD.N0232.N0720.N1256.d015549 m n :=
  le_antisymm (_root_.GD.N0086.d023915 m n) (_root_.GD.N0086.d023915 n m)

end
end GD.N0086

#print axioms _root_.GD.N0086.d023914
#print axioms _root_.GD.N0086.d023916

namespace GD.N0086
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256

private theorem d023917 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : ¬ 4 ≤ (m - 1) * (n - 1)) :
    (m = 2 ∧ n ≤ 4) ∨ (n = 2 ∧ m ≤ 4) := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hn1 : 1 ≤ n - 1 := by omega
  have hm4 : m ≤ 4 := by
    by_contra h
    have : 4 ≤ m - 1 := by omega
    apply hp
    nlinarith
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 4 ≤ n - 1 := by omega
    apply hp
    nlinarith
  by_cases h : m = 2
  · exact Or.inl ⟨h, hn4⟩
  · right
    refine ⟨?_, hm4⟩
    by_contra hh
    have hm2 : 2 ≤ m - 1 := by omega
    have hn2 : 2 ≤ n - 1 := by omega
    apply hp
    nlinarith


theorem d023918
    (h24 : _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤) (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ ↔ 4 ≤ (m - 1) * (n - 1) := by
  constructor
  · intro hf
    by_contra hp
    have h42 : _root_.GD.N0232.N0720.N1256.d015549 4 2 = ⊤ := (_root_.GD.N0086.d023916 2 4).trans h24
    rcases _root_.GD.N0086.d023917 hm hn hp with ⟨hm2, hn4⟩ | ⟨hn2, hm4⟩
    · subst m
      exact hf (_root_.GD.N0086.d023911 hm hn le_rfl hn4 h24)
    · subst n
      exact hf (_root_.GD.N0086.d023911 hm hn hm4 le_rfl h42)
  · exact _root_.GD.N0030.d023896 m n hm hn


theorem d023919 :
    (∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
      (_root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ ↔ 4 ≤ (m - 1) * (n - 1))) ↔
      _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤ := by
  constructor
  · intro h
    by_contra hf
    have hh := (h 2 4 (by decide) (by decide)).mp hf
    norm_num at hh
  · exact _root_.GD.N0086.d023918


theorem d023920
    (h24 : _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤) {k : ℕ} (hk : 2 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔
      ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1) := by
  rw [_root_.GD.N0068.d023043 hk sizes hn]
  constructor
  · intro h i j hij
    exact (_root_.GD.N0086.d023918 h24 _ _ (hn i) (hn j)).mp (h i j hij)
  · intro h i j hij
    exact (_root_.GD.N0086.d023918 h24 _ _ (hn i) (hn j)).mpr (h i j hij)

end
end GD.N0086

#print axioms _root_.GD.N0086.d023918
#print axioms _root_.GD.N0086.d023919
#print axioms _root_.GD.N0086.d023920

namespace GD.N0086
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256


theorem d023921 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) :
    (∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1)) ↔
      (∀ i, 3 ≤ sizes i) ∨
        ∃ i₀ : Fin k, sizes i₀ = 2 ∧ ∀ i, i ≠ i₀ → 5 ≤ sizes i := by
  constructor
  · intro hp
    by_cases h : ∀ i, 3 ≤ sizes i
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨i₀, hi⟩ := h
      have hi2 : sizes i₀ = 2 := by have := hn i₀; omega
      refine ⟨i₀, hi2, ?_⟩
      intro i hii
      have hh := hp i₀ i (Ne.symm hii)
      rw [hi2] at hh
      norm_num at hh
      omega
  · rintro (h | ⟨i₀, hi, hh⟩)
    · intro i j _
      have hi : 2 ≤ sizes i - 1 := by have := h i; omega
      have hj : 2 ≤ sizes j - 1 := by have := h j; omega
      nlinarith
    · exact (_root_.GD.N0032.d023893
        sizes i₀ (by omega) hh).2


theorem d023922
    (h24 : _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤) {k : ℕ} (hk : 2 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔
      (∀ i, 3 ≤ sizes i) ∨
        ∃ i₀ : Fin k, sizes i₀ = 2 ∧ ∀ i, i ≠ i₀ → 5 ≤ sizes i :=
  (_root_.GD.N0086.d023920 h24 hk sizes hn).trans
    (_root_.GD.N0086.d023921 sizes hn)

end
end GD.N0086

#print axioms _root_.GD.N0086.d023921
#print axioms _root_.GD.N0086.d023922
