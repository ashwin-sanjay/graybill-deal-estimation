import GD.Module1061





































open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0232
namespace N0720
namespace N1479

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1418
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602

variable (m n : ℕ)



theorem d017055
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (s : ℝ) :
    ∫ ω, ((p + s • (e - p)) ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
      s ^ 2 * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  have h := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
    (Lp.coeFn_add p (s • (e - p)))
  have h2 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
    (Lp.coeFn_smul s (e - p))
  have h3 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le (Lp.coeFn_sub e p)
  filter_upwards [h, h2, h3] with ω h₁ h₂ h₃
  rw [h₁]
  simp only [Pi.add_apply]
  rw [h₂]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h₃]
  simp only [Pi.sub_apply]
  ring


theorem d017056
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (s : ℝ)
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤) (he : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≠ ⊤) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta (p + s • (e - p)) ≠ ⊤ := by
  apply _root_.GD.N0232.N0720.N1418.d017032
  have hpmem := _root_.GD.N0232.N0720.N1418.d017030 m n theta p hp
  have hemem := _root_.GD.N0232.N0720.N1418.d017030 m n theta e he
  have hvmem : MemLp (fun ω ↦ e ω - p ω) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have := hemem.sub hpmem
    simpa [_root_.GD.N0232.N0720.N1418.d017027, Pi.sub_def, sub_sub_sub_cancel_right] using this
  apply MemLp.ae_eq (f := fun ω ↦
    _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω + s * (e ω - p ω))
  · have h := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
      (Lp.coeFn_add p (s • (e - p)))
    have h2 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
      (Lp.coeFn_smul s (e - p))
    have h3 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le (Lp.coeFn_sub e p)
    filter_upwards [h, h2, h3] with ω h₁ h₂ h₃
    unfold _root_.GD.N0232.N0720.N1418.d017027
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₃]
    simp only [Pi.sub_apply]
    ring
  · exact hpmem.add (hvmem.const_mul s)




theorem d017057
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤)
    (hdom : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta p)
    (s : ℝ) (hs0 : 0 ≤ s) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (p + s • (e - p))).toReal ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
        s * (1 - s) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have he : _root_.GD.N0232.N0720.N1080.d014182 m n theta e ≠ ⊤ := ne_top_of_le_ne_top hp hdom
  have hs := _root_.GD.N0232.N0720.N1479.d017056 m n theta p e s hp he

  have hexp := _root_.GD.N0232.N0720.N1418.d017034 m n theta p e hp he

  have htrace : 2 * ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω * (e ω - p ω)
      ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≤
      -(1 : ℝ) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have hR : (_root_.GD.N0232.N0720.N1080.d014182 m n theta e).toReal ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal :=
      ENNReal.toReal_mono hp hdom
    linarith [hexp, hR]

  have hexp2 := _root_.GD.N0232.N0720.N1418.d017034 m n theta p (p + s • (e - p)) hp hs

  have hint1 : ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω *
      ((p + s • (e - p)) ω - p ω) ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
      s * ∫ ω, _root_.GD.N0232.N0720.N1418.d017027 m n theta p ω * (e ω - p ω)
        ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have h := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
      (Lp.coeFn_add p (s • (e - p)))
    have h2 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le
      (Lp.coeFn_smul s (e - p))
    have h3 := (_root_.GD.N0232.N0720.N1418.d017026 m n theta).ae_le (Lp.coeFn_sub e p)
    filter_upwards [h, h2, h3] with ω h₁ h₂ h₃
    rw [h₁]
    simp only [Pi.add_apply]
    rw [h₂]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₃]
    simp only [Pi.sub_apply]
    ring
  have hint2 := _root_.GD.N0232.N0720.N1479.d017055 m n theta p e s
  rw [hint1, hint2] at hexp2
  have hE : (0 : ℝ) ≤ ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    integral_nonneg fun ω ↦ sq_nonneg _
  nlinarith [hexp2, htrace, hE, mul_le_mul_of_nonneg_left htrace
    (mul_nonneg hs0 hs0)]




theorem d017058
    (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p) (hne : e ≠ p)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ b : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0232.N0720.N1159.d014637 m n b ∧ b ≠ p ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (_root_.GD.N0232.N0720.N1080.d014182 m n theta b).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal -
          δ * ∫ ω, (b ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        ∫ ω, (b ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
          (1 / (1 + δ)) ^ 2 * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  set s : ℝ := 1 / (1 + δ) with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by linarith)]
    linarith
  refine ⟨p + s • (e - p), ?_, ?_, ?_, ?_⟩
  · intro theta
    exact _root_.GD.N0232.N0720.N1479.d017056 m n theta p e s (hp theta)
      (ne_top_of_le_ne_top (hp theta) (hdom theta))
  · intro hcontra
    apply hne
    have h1 : s • (e - p) = 0 := by
      have := congrArg (fun x ↦ x - p) hcontra
      simpa [add_sub_cancel_left] using this
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h hs0.ne'
    · exact sub_eq_zero.1 h
  · intro theta
    have hstep := _root_.GD.N0232.N0720.N1479.d017057 m n theta p e (hp theta)
      (hdom theta) s hs0.le
    have hscale := _root_.GD.N0232.N0720.N1479.d017055 m n theta p e s
    rw [hscale]
    have halg : δ * (s ^ 2 * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) =
        s * (1 - s) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
      have hδs : δ * s = 1 - s := by
        rw [hs]
        field_simp
        ring
      calc δ * (s ^ 2 * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) =
          (δ * s) * s * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by ring
        _ = s * (1 - s) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
            rw [hδs]; ring
    rw [halg]
    exact hstep
  · intro theta
    exact _root_.GD.N0232.N0720.N1479.d017055 m n theta p e s





theorem d017059
    (p q e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p) (hne : e ≠ p)
    (hterm : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 4) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      c * (∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) <
        ∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  by_contra hcontra

  obtain ⟨b, hbfin, hbne, hbmargin, hbenergy⟩ :=
    _root_.GD.N0232.N0720.N1479.d017058 m n p e hp hdom hne 1 one_pos

  set t : ℝ := 1 - 4 * ((c + 1 / 4) / 2) with hts
  have hc' : c < (c + 1 / 4) / 2 := by linarith
  have hc'' : (c + 1 / 4) / 2 < 1 / 4 := by linarith
  have ht0 : 0 < t := by rw [hts]; linarith
  have ht1 : t ≤ 1 := by rw [hts]; linarith
  apply _root_.GD.N0232.N0720.N1418.d017039 m n p q b hp hq hbfin hbne
    1 t zero_le_one ht0 ht1 hbmargin ?_ hterm
  intro theta

  have hbenergy' : ∫ ω, (b ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
      (1 / 4) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have := hbenergy theta
    norm_num at this
    exact this
  rw [hbenergy']
  have hcon := not_lt.1 fun hlt ↦ hcontra ⟨theta, hlt⟩
  have hE : (0 : ℝ) ≤ ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    integral_nonneg fun ω ↦ sq_nonneg _
  have hgoal : (1 - t) * 1 * ((1 / 4) *
      ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) =
      ((c + 1 / 4) / 2) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    rw [hts]
    ring
  rw [hgoal]
  calc (∫ ω, (q ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta)) ≤
      c * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := hcon
    _ ≤ ((c + 1 / 4) / 2) * ∫ ω, (e ω - p ω) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
        apply mul_le_mul_of_nonneg_right hc'.le hE

end

end N1479
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1479.d017057
#print axioms _root_.GD.N0232.N0720.N1479.d017058
#print axioms _root_.GD.N0232.N0720.N1479.d017059
