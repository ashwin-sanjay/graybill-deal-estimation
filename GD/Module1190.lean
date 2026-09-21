import GD.Module0028
import GD.Module1174
import GD.Module0965
import GD.Module1189























open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1097

noncomputable section

open _root_.GD.N0230.N0647
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1369
open _root_.GD.N0232.N0720.N1453
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1107

local notation "PA" => _root_.GD.N0232.N0720.N1482.d015118

variable (m n : ℕ)




theorem d019162 (g : _root_.GD.N0232.N0720.N1477.d015740) {x y : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hx : _root_.GD.N0232.N0720.N1159.d014637 m n x) (hy : _root_.GD.N0232.N0720.N1159.d014637 m n y) (h : x = y) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g x hx = _root_.GD.N0232.N0720.N1159.d014642 m n g y hy := by
  subst h
  rfl


theorem d019163 (g : _root_.GD.N0232.N0720.N1477.d015740) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hx : _root_.GD.N0232.N0720.N1159.d014637 m n x) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n g x hx‖ ^ 2 =
      g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) x).toReal := by
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) =
      _root_.GD.N0232.N0720.N1080.d014169 := by simp
  have hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g x hx) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) x := by
    calc _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g x hx)
        = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169))
            (_root_.GD.N0232.N0720.N1159.d014642 m n g x hx) := by rw [heta]
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) x :=
        _root_.GD.N0232.N0720.N1159.d014643 m n g _ x hx
  have hnorm : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g x hx) =
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014642 m n g x hx‖ ^ 2) := by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    simp only [zero_sub, norm_neg]
  have hreal := congrArg ENNReal.toReal (hnorm.symm.trans hrisk)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)] at hreal
  exact hreal


theorem d019164 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖x‖ ^ 2 = (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 x).toReal := by
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
  simp only [zero_sub, norm_neg]
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]


theorem d019165 {x y : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (h : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 x ≤ _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 y)
    (hy : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 y ≠ ⊤) : ‖x‖ ≤ ‖y‖ := by
  have h2 : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [_root_.GD.N0232.N0720.N1097.d019164, _root_.GD.N0232.N0720.N1097.d019164]
    exact ENNReal.toReal_mono hy h
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3


theorem d019166 {K : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))} (hcv : Convex ℝ K)
    {p x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hp : p ∈ K) (hmin : ∀ w ∈ K, ‖p‖ ≤ ‖w‖)
    (hx : x ∈ K) (hle : ‖x‖ ≤ ‖p‖) : x = p := by
  have h := _root_.GD.N0230.N0647.d000345 hcv hp hmin hx
  have h2 : ‖x - p‖ ^ 2 ≤ 0 := by
    nlinarith [norm_nonneg x, norm_nonneg p,
      mul_nonneg (sub_nonneg.2 hle) (add_nonneg (norm_nonneg p) (norm_nonneg x))]
  have h4 : ‖x - p‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
  have h5 : ‖x - p‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h4
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)





structure d019167 where
  seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n
  descending : ∀ (k : ℕ) (θ : _root_.GD.N0232.N0720.N1080.d014168),
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (seed (k + 1)).value ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (seed k).value

variable {m n}

namespace d019167

variable (c : _root_.GD.N0232.N0720.N1097.d019167 m n)


def d019168 (k : ℕ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := _root_.GD.N0232.N0720.N1159.d014630 m n (c.seed k).value

theorem d019169 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    Antitone (fun k => _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed k).value) :=
  antitone_nat_of_succ_le (fun k => c.descending k θ)

theorem d019170 (k : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    d ∈ c.d019168 k ↔ ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (c.seed k).value :=
  Iff.rfl

theorem d019171 : Antitone c.d019168 := by
  intro i j hij d hd
  rw [_root_.GD.N0232.N0720.N1097.d019167.d019170] at hd ⊢
  intro θ
  exact le_trans (hd θ) (c.d019169 θ hij)


def d019172 (k : ℕ) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1159.d014633 m n (c.seed k).value

theorem d019173 (k : ℕ) : c.d019172 k ∈ c.d019168 k :=
  (_root_.GD.N0232.N0720.N1159.d014634 m n (c.seed k).value).1

theorem d019174 (k : ℕ) : _root_.GD.N0232.N0720.N1159.d014637 m n (c.d019172 k) :=
  _root_.GD.N0232.N0720.N1159.d014644 m n (c.seed k) _ (c.d019173 k)

theorem d019175 (k : ℕ) {w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hw : w ∈ c.d019168 k) :
    ‖c.d019172 k‖ ≤ ‖w‖ := by
  have h := (_root_.GD.N0232.N0720.N1159.d014634 m n (c.seed k).value).2.2 w hw
  exact _root_.GD.N0232.N0720.N1097.d019165 m n h
    (_root_.GD.N0232.N0720.N1159.d014644 m n (c.seed k) w hw _root_.GD.N0232.N0720.N1080.d014169)

theorem d019176 (k : ℕ) {w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hw : w ∈ c.d019168 k) :
    ‖w‖ ≤ Real.sqrt ((_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (c.seed 0).value).toReal) := by
  have hw0 : w ∈ c.d019168 0 := c.d019171 (Nat.zero_le k) hw
  rw [_root_.GD.N0232.N0720.N1097.d019167.d019170] at hw0
  have h2 : ‖w‖ ^ 2 ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (c.seed 0).value).toReal := by
    rw [_root_.GD.N0232.N0720.N1097.d019164]
    exact ENNReal.toReal_mono ((c.seed 0).finiteRisk _root_.GD.N0232.N0720.N1080.d014169) (hw0 _root_.GD.N0232.N0720.N1080.d014169)
  have := Real.abs_le_sqrt h2
  rwa [abs_of_nonneg (norm_nonneg _)] at this



theorem d019177 :
    ∃ x ∈ ⋂ k, c.d019168 k, (∀ w ∈ ⋂ k, c.d019168 k, ‖x‖ ≤ ‖w‖) ∧
      ‖x‖ ^ 2 = sSup (Set.range fun k => ‖c.d019172 k‖ ^ 2) :=
  _root_.GD.N0230.N0647.d000346 c.d019168
    (fun k => ⟨_, c.d019173 k⟩)
    (fun _ => _root_.GD.N0232.N0720.N1159.d014631 m n _)
    (fun _ => _root_.GD.N0232.N0720.N1159.d014632 m n _)
    (Real.sqrt ((_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (c.seed 0).value).toReal))
    (fun k _ hw => c.d019176 k hw)
    (fun i j => ⟨max i j, c.d019171 (le_max_left i j),
      c.d019171 (le_max_right i j)⟩)
    c.d019172 (fun k => c.d019173 k) (fun k _ hw => c.d019175 k hw)


def d019178 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := Classical.choose c.d019177

theorem d019179 :
    c.d019178 ∈ ⋂ k, c.d019168 k ∧ (∀ w ∈ ⋂ k, c.d019168 k, ‖c.d019178‖ ≤ ‖w‖) ∧
      ‖c.d019178‖ ^ 2 = sSup (Set.range fun k => ‖c.d019172 k‖ ^ 2) :=
  Classical.choose_spec c.d019177

theorem d019180 (k : ℕ) : c.d019178 ∈ c.d019168 k := Set.mem_iInter.1 c.d019179.1 k

theorem d019181 : _root_.GD.N0232.N0720.N1159.d014637 m n c.d019178 :=
  _root_.GD.N0232.N0720.N1159.d014644 m n (c.seed 0) _ (c.d019180 0)

theorem d019182 {w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hw : w ∈ ⋂ k, c.d019168 k) :
    ‖c.d019178‖ ≤ ‖w‖ :=
  c.d019179.2.1 w hw

theorem d019183 : Monotone (fun k => ‖c.d019172 k‖ ^ 2) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := c.d019175 k (c.d019171 (Nat.le_succ k) (c.d019173 (k + 1)))
  nlinarith [mul_self_le_mul_self (norm_nonneg _) h]

theorem d019184 (k : ℕ) : ‖c.d019172 k‖ ^ 2 ≤ ‖c.d019178‖ ^ 2 := by
  have h := c.d019175 k (c.d019180 k)
  nlinarith [mul_self_le_mul_self (norm_nonneg _) h]

theorem d019185 :
    Tendsto (fun k => ‖c.d019172 k‖ ^ 2) atTop (𝓝 (‖c.d019178‖ ^ 2)) := by
  have hbdd : BddAbove (Set.range fun k => ‖c.d019172 k‖ ^ 2) := by
    refine ⟨‖c.d019178‖ ^ 2, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact c.d019184 k
  have h := tendsto_atTop_ciSup c.d019183 hbdd
  have heq : (⨆ k, ‖c.d019172 k‖ ^ 2) = ‖c.d019178‖ ^ 2 := by
    rw [c.d019179.2.2]
    rfl
  rwa [heq] at h


theorem d019186 : Tendsto c.d019172 atTop (𝓝 c.d019178) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ k, ‖c.d019172 k - c.d019178‖ ≤
      Real.sqrt (2 * ‖c.d019178‖ ^ 2 - 2 * ‖c.d019172 k‖ ^ 2) := by
    intro k
    have h := _root_.GD.N0230.N0647.d000347 c.d019168 (fun k => _root_.GD.N0232.N0720.N1159.d014632 m n _)
      c.d019172 (fun k => c.d019173 k) (fun k _ hw => c.d019175 k hw)
      c.d019178 (fun k => c.d019180 k) k
    rw [norm_sub_rev] at h
    have := Real.abs_le_sqrt h
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hlim : Tendsto (fun k => Real.sqrt (2 * ‖c.d019178‖ ^ 2 - 2 * ‖c.d019172 k‖ ^ 2)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => 2 * ‖c.d019178‖ ^ 2 - 2 * ‖c.d019172 k‖ ^ 2) atTop
        (𝓝 (2 * ‖c.d019178‖ ^ 2 - 2 * ‖c.d019178‖ ^ 2)) :=
      tendsto_const_nhds.sub (c.d019185.const_mul 2)
    rw [sub_self] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  exact squeeze_zero (fun k => norm_nonneg _) hbound hlim





theorem d019187 (g : _root_.GD.N0232.N0720.N1477.d015740) (K : ℝ)
    (hlip : ∀ (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
      (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q),
      ‖_root_.GD.N0232.N0720.N1159.d014642 m n g p hp - _root_.GD.N0232.N0720.N1159.d014642 m n g q hq‖ ≤ K * ‖p - q‖)
    (hdisp : Tendsto (fun k => ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖) atTop (𝓝 0)) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 := by
  have hb : ∀ k, ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 - c.d019178‖ ≤
      (K + 1) * ‖c.d019172 k - c.d019178‖ +
        ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖ := by
    intro k
    have h1 := hlip c.d019178 (c.d019172 k) c.d019181 (c.d019174 k)
    have h2 : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (c.d019172 k) (c.d019174 k) - c.d019172 k‖ ≤
        ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖ := le_rfl
    have h3 : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 - c.d019178‖ ≤
        ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 -
            _root_.GD.N0232.N0720.N1159.d014642 m n g (c.d019172 k) (c.d019174 k)‖ +
          ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (c.d019172 k) (c.d019174 k) - c.d019172 k‖ +
          ‖c.d019172 k - c.d019178‖ := by
      have hsplit : _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 - c.d019178 =
          (_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 -
              _root_.GD.N0232.N0720.N1159.d014642 m n g (c.d019172 k) (c.d019174 k)) +
            (_root_.GD.N0232.N0720.N1159.d014642 m n g (c.d019172 k) (c.d019174 k) - c.d019172 k) +
            (c.d019172 k - c.d019178) := by abel
      rw [hsplit]
      exact norm_add₃_le
    rw [norm_sub_rev c.d019178 (c.d019172 k)] at h1
    linarith
  have hlim : Tendsto (fun k => (K + 1) * ‖c.d019172 k - c.d019178‖ +
      ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖) atTop (𝓝 0) := by
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 c.d019186).const_mul (K + 1)
    have h3 := h1.add hdisp
    simpa using h3
  have hle : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 - c.d019178‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb
  have h0 : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 - c.d019178‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)


theorem d019188 (k : ℕ) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖ ≤
      Real.sqrt (_root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k) g) := by
  have h : ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k) g :=
    _root_.GD.N0232.N0720.N1159.d014649 m n (c.seed k) g
  have h' := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _)] at h'


theorem d019189 (g : _root_.GD.N0232.N0720.N1477.d015740) (K : ℝ)
    (hlip : ∀ (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
      (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q),
      ‖_root_.GD.N0232.N0720.N1159.d014642 m n g p hp - _root_.GD.N0232.N0720.N1159.d014642 m n g q hq‖ ≤ K * ‖p - q‖)
    (hdef : Tendsto (fun k => _root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k) g) atTop (𝓝 0)) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 := by
  refine c.d019187 g K hlip ?_
  have hlim : Tendsto (fun k => Real.sqrt (_root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k) g)) atTop
      (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hdef
    rw [Real.sqrt_zero] at h
    exact h
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => c.d019188 k g) hlim


def d019190 : Subgroup _root_.GD.N0232.N0720.N1477.d015740 where
  carrier := {g | _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178}
  one_mem' := _root_.GD.N0232.N0720.N1482.d015159 (m := m) (n := n) _ _
  mul_mem' := by
    intro g h hg hh
    have hg' : _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 := hg
    have hh' : _root_.GD.N0232.N0720.N1159.d014642 m n h c.d019178 c.d019181 = c.d019178 := hh
    show _root_.GD.N0232.N0720.N1159.d014642 m n (g * h) c.d019178 c.d019181 = c.d019178
    have h1 := _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n)
      g h c.d019178 c.d019181
    simp only [hh'] at h1
    exact h1.symm.trans hg'
  inv_mem' := by
    intro g hg
    have hg' : _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 := hg
    show _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ c.d019178 c.d019181 = c.d019178
    have h1 := _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n)
      g⁻¹ g c.d019178 c.d019181
    rw [inv_mul_cancel, _root_.GD.N0232.N0720.N1482.d015159] at h1
    simp only [hg'] at h1
    exact h1

theorem d019191 (g : _root_.GD.N0232.N0720.N1477.d015740) :
    g ∈ c.d019190 ↔ _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 :=
  Iff.rfl


theorem d019192 (g : _root_.GD.N0232.N0720.N1477.d015740) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 ∈ ⋂ k, c.d019168 k := by
  rw [Set.mem_iInter]
  intro k
  exact (_root_.GD.N0232.N0720.N1159.d014645 m n (c.seed k) g ⟨c.d019178, c.d019180 k⟩).2



theorem d019193 (g : _root_.GD.N0232.N0720.N1477.d015740) :
    g ∈ c.d019190 ↔
      g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) c.d019178).toReal ≤
        ‖c.d019178‖ ^ 2 := by
  rw [← _root_.GD.N0232.N0720.N1097.d019163 m n g c.d019178 c.d019181,
    _root_.GD.N0232.N0720.N1097.d019167.d019191]
  constructor
  · intro h
    rw [h]
  · intro h
    have hle : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181‖ ≤ ‖c.d019178‖ := by
      have h' := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
    exact _root_.GD.N0232.N0720.N1097.d019166 m n (convex_iInter fun k => _root_.GD.N0232.N0720.N1159.d014632 m n _)
      c.d019179.1 c.d019179.2.1 (c.d019192 g) hle

theorem d019194 : IsClosed (c.d019190 : Set _root_.GD.N0232.N0720.N1477.d015740) := by
  have hset : (c.d019190 : Set _root_.GD.N0232.N0720.N1477.d015740) =
      {g | g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) c.d019178).toReal ≤ ‖c.d019178‖ ^ 2} := by
    ext g
    exact c.d019193 g
  rw [hset]
  exact isClosed_le ((_root_.GD.N0232.N0720.N1453.d018880.pow 2).mul
    ((_root_.GD.N0232.N0720.N1369.d018805 _ c.d019181).comp
      _root_.GD.N0232.N0720.N1453.d018883)) continuous_const



theorem d019195
    (h2 : _root_.GD.N0232.N0720.N1482.d015130 ∈ c.d019190)
    (h3 : _root_.GD.N0232.N0720.N1482.d015131 ∈ c.d019190) :
    c.d019190 = ⊤ := by
  have hle : _root_.GD.N0232.N0720.N1482.d015132 ≤ c.d019190 := by
    apply (Subgroup.closure_le _).2
    intro g hg
    rcases hg with (rfl | rfl)
    · exact h2
    · exact h3
  have hsub : closure (_root_.GD.N0232.N0720.N1482.d015132 : Set _root_.GD.N0232.N0720.N1477.d015740) ⊆
      (c.d019190 : Set _root_.GD.N0232.N0720.N1477.d015740) :=
    closure_minimal (SetLike.coe_subset_coe.2 hle) c.d019194
  rw [_root_.GD.N0232.N0720.N1482.d015157.closure_eq] at hsub
  exact (Subgroup.eq_top_iff' _).2 (fun g => hsub (Set.mem_univ g))

theorem d019196 (htop : c.d019190 = ⊤) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g c.d019178 c.d019181 = c.d019178 := by
  have : g ∈ c.d019190 := by
    rw [htop]
    exact Subgroup.mem_top g
  exact this



theorem d019197 (htop : c.d019190 = ⊤) :
    _root_.GD.N0232.N0720.N1159.d014638 m n c.d019178 := by
  intro g θ
  have := _root_.GD.N0232.N0720.N1159.d014643 m n g θ c.d019178 c.d019181
  rwa [c.d019196 htop g] at this


def d019198 (htop : c.d019190 = ⊤) : _root_.GD.N0232.N0720.N1159.d014639 m n :=
  ⟨c.d019178, c.d019181, c.d019197 htop⟩

theorem d019199 : c.d019178 ∈ _root_.GD.N0232.N0720.N1159.d014630 m n c.d019178 := fun _ => le_rfl

theorem d019200 : _root_.GD.N0232.N0720.N1159.d014630 m n c.d019178 ⊆ ⋂ k, c.d019168 k := by
  intro d hd
  rw [Set.mem_iInter]
  intro k
  rw [_root_.GD.N0232.N0720.N1097.d019167.d019170]
  intro θ
  have hlim := (c.d019170 k c.d019178).1 (c.d019180 k) θ
  exact le_trans (hd θ) hlim


theorem d019201 : _root_.GD.N0232.N0720.N1159.d014633 m n c.d019178 = c.d019178 := by
  have hPmem := (_root_.GD.N0232.N0720.N1159.d014634 m n c.d019178).1
  have hPmin : ∀ w ∈ _root_.GD.N0232.N0720.N1159.d014630 m n c.d019178, ‖_root_.GD.N0232.N0720.N1159.d014633 m n c.d019178‖ ≤ ‖w‖ := by
    intro w hw
    have hw0 : w ∈ c.d019168 0 := Set.mem_iInter.1 (c.d019200 hw) 0
    exact _root_.GD.N0232.N0720.N1097.d019165 m n
      ((_root_.GD.N0232.N0720.N1159.d014634 m n c.d019178).2.2 w hw)
      (_root_.GD.N0232.N0720.N1159.d014644 m n (c.seed 0) w hw0 _root_.GD.N0232.N0720.N1080.d014169)
  have hle : ‖c.d019178‖ ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n c.d019178‖ :=
    c.d019182 (c.d019200 hPmem)
  exact (_root_.GD.N0232.N0720.N1097.d019166 m n (_root_.GD.N0232.N0720.N1159.d014632 m n _) hPmem hPmin
    c.d019199 hle).symm


theorem d019202 (htop : c.d019190 = ⊤) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n)
      (c.d019198 htop) = 0 := by
  rw [_root_.GD.N0232.N0720.N1453.d018896, eq_top_iff]
  intro g _
  rw [_root_.GD.N0232.N0720.N1453.d018886]
  have hP : _root_.GD.N0232.N0720.N1159.d014633 m n (c.d019198 htop).value = c.d019178 :=
    c.d019201
  rw [_root_.GD.N0232.N0720.N1097.d019162 m n g _ c.d019181 hP,
    c.d019196 htop g, hP]


theorem d019203 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) c.d019178 (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := fun θ =>
  lt_of_le_of_lt ((c.d019170 0 c.d019178).1 (c.d019180 0) θ) (hs θ)

end d019167




theorem d019204 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (h2 : _root_.GD.N0232.N0720.N1482.d015130 ∈ c.d019190)
    (h3 : _root_.GD.N0232.N0720.N1482.d015131 ∈ c.d019190) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have htop := c.d019195 h2 h3
  rw [_root_.GD.N0232.N0720.N1482.d015173
    hm hn]
  exact ⟨c.d019198 htop, c.d019203 hm hn hs, c.d019202 htop⟩

theorem d019205 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) s := by
  unfold _root_.GD.N0232.N0720.N1477.d015749
  positivity




theorem d019206 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hE : Tendsto (fun k => _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) (c.seed k))
      atTop (𝓝 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hsqrt : Tendsto (fun k => Real.sqrt (_root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n)
      (c.seed k))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hE
    rw [Real.sqrt_zero] at h
    exact h
  have hD : ∀ g : _root_.GD.N0232.N0720.N1477.d015740, (∀ k, ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) (c.seed k)) →
      Tendsto (fun k => ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k) g‖) atTop (𝓝 0) := by
    intro g hg
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsqrt
    have := Real.abs_le_sqrt (hg k)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have h2 : _root_.GD.N0232.N0720.N1482.d015130 ∈ c.d019190 :=
    c.d019187 _ _
      (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015232 m n p q hp hq)
      (hD _ fun k => by
        unfold _root_.GD.N0232.N0720.N1477.d015749
        linarith [sq_nonneg ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k)
          _root_.GD.N0232.N0720.N1482.d015131‖])
  have h3 : _root_.GD.N0232.N0720.N1482.d015131 ∈ c.d019190 :=
    c.d019187 _ _
      (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015233 m n p q hp hq)
      (hD _ fun k => by
        unfold _root_.GD.N0232.N0720.N1477.d015749
        linarith [sq_nonneg ‖_root_.GD.N0232.N0720.N1477.d015744 m n (c.seed k)
          _root_.GD.N0232.N0720.N1482.d015130‖])
  exact _root_.GD.N0232.N0720.N1097.d019204 hm hn c hs h2 h3



theorem d019207 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hflat : Tendsto (fun k =>
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (c.seed k))
      atTop (𝓝 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  refine _root_.GD.N0232.N0720.N1097.d019206 hm hn c hs ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hflat
    (fun k => _root_.GD.N0232.N0720.N1097.d019205 _)
    (fun k => _root_.GD.N0232.N0720.N1477.d015753 (m := m) (n := n) (c.seed k))




theorem d019208 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k) (hlim : Tendsto ε atTop (𝓝 0))
    (happ : ∀ k, _root_.GD.N0232.N0720.N1107.d019158 m n (c.seed k) (ε k)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  refine _root_.GD.N0232.N0720.N1097.d019206 hm hn c hs ?_
  have h := hlim.const_mul (_root_.GD.N0232.N0720.N1107.d019159 m n)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun k => _root_.GD.N0232.N0720.N1097.d019205 _)
    (fun k => _root_.GD.N0232.N0720.N1107.d019160 m n (c.seed k) (hε k) (happ k))




theorem d019209 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  have hmem : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := fun _ => le_rfl
  have h := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2 s.value hmem
  have hle := _root_.GD.N0232.N0720.N1097.d019165 m n h (s.finiteRisk _root_.GD.N0232.N0720.N1080.d014169)
  nlinarith [mul_self_le_mul_self (norm_nonneg _) hle]




theorem d019210 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) (K : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
      (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q),
      ‖_root_.GD.N0232.N0720.N1159.d014642 m n g p hp - _root_.GD.N0232.N0720.N1159.d014642 m n g q hq‖ ≤ K * ‖p - q‖)
    (hfix : _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk = s.value) :
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n s g‖ ≤
      (K + 1) * Real.sqrt (‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hval : _root_.GD.N0232.N0720.N1477.d015744 m n s g =
      _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := rfl
  have hsplit : _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value =
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
          _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk) +
        (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk -
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by abel
  have h1 := hlip (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) s.value hP s.finiteRisk
  rw [norm_sub_rev (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) s.value] at h1
  have hgap : ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 :=
    _root_.GD.N0232.N0720.N1159.d014648 m n s.value s.value (fun _ => le_rfl)
  have hsqrt : ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤
      Real.sqrt (‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
    have := Real.abs_le_sqrt hgap
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hmul := mul_le_mul_of_nonneg_left hsqrt hK
  rw [hval]
  calc ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖
      = ‖(_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
            _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk) +
          (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value)‖ := by rw [hsplit]
    _ ≤ ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
            _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk‖ +
          ‖_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ := norm_add_le _ _
    _ = ‖_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP -
            _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk‖ +
          ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ := by rw [hfix]
    _ ≤ K * ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ +
          ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ := by linarith [h1]
    _ ≤ (K + 1) * Real.sqrt (‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
        linarith [hmul, hsqrt]


def d019211 : ℝ :=
  (2 * Real.sqrt ((2 : ℝ) ^ (m + n)) + 1) ^ 2 +
    (3 * Real.sqrt ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) + 1) ^ 2



theorem d019212 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h2 : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
      s.value s.finiteRisk = s.value)
    (h3 : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131
      s.value s.finiteRisk = s.value) :
    _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) s ≤
      _root_.GD.N0232.N0720.N1097.d019211 (m := m) (n := n) * (‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  have hg := _root_.GD.N0232.N0720.N1097.d019209 s
  have hd2 := _root_.GD.N0232.N0720.N1097.d019210 s _ _ (by positivity)
    (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015232 m n p q hp hq) h2
  have hd3 := _root_.GD.N0232.N0720.N1097.d019210 s _ _ (by positivity)
    (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015233 m n p q hp hq) h3
  have hs := Real.sq_sqrt hg
  have hsq0 := Real.sqrt_nonneg (‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)
  have hn2 := norm_nonneg (_root_.GD.N0232.N0720.N1477.d015744 m n s
    _root_.GD.N0232.N0720.N1482.d015130)
  have hn3 := norm_nonneg (_root_.GD.N0232.N0720.N1477.d015744 m n s
    _root_.GD.N0232.N0720.N1482.d015131)
  have hK2 : 0 ≤ 2 * Real.sqrt ((2 : ℝ) ^ (m + n)) + 1 := by positivity
  have hK3 : 0 ≤ 3 * Real.sqrt ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) + 1 := by positivity
  have e2 := mul_self_le_mul_self hn2 hd2
  have e3 := mul_self_le_mul_self hn3 hd3
  unfold _root_.GD.N0232.N0720.N1477.d015749 _root_.GD.N0232.N0720.N1097.d019211
  nlinarith [e2, e3, hs]




theorem d019213 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (h2 : ∀ k, _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
      (c.seed k).value (c.seed k).finiteRisk = (c.seed k).value)
    (h3 : ∀ k, _root_.GD.N0232.N0720.N1159.d014642 m n
      _root_.GD.N0232.N0720.N1482.d015131
      (c.seed k).value (c.seed k).finiteRisk = (c.seed k).value)
    (hgap : Tendsto (fun k => ‖(c.seed k).value‖ ^ 2 - ‖c.d019172 k‖ ^ 2) atTop (𝓝 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  refine _root_.GD.N0232.N0720.N1097.d019206 hm hn c hs ?_
  have h := hgap.const_mul (_root_.GD.N0232.N0720.N1097.d019211 (m := m) (n := n))
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun k => _root_.GD.N0232.N0720.N1097.d019205 _)
    (fun k => _root_.GD.N0232.N0720.N1097.d019212 (c.seed k) (h2 k) (h3 k))


def d019214 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : _root_.GD.N0232.N0720.N1097.d019167 m n :=
  ⟨fun _ => s, fun _ _ => le_rfl⟩




theorem d019215 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto (fun k =>
          _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n)
            (c.seed k)) atTop (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨s, hs, hflat⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015173
        hm hn).1 h
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 s, hs, ?_⟩
    show Tendsto (fun _ : ℕ =>
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s)
      atTop (𝓝 0)
    rw [hflat]
    exact tendsto_const_nhds
  · rintro ⟨c, hs, hflat⟩
    exact _root_.GD.N0232.N0720.N1097.d019207 hm hn c hs hflat


theorem d019216 (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto (fun k => _root_.GD.N0232.N0720.N1477.d015749 (m := m) (n := n) (c.seed k))
          atTop (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨c, hs, hflat⟩ := (_root_.GD.N0232.N0720.N1097.d019215 hm hn).1 h
    refine ⟨c, hs, ?_⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hflat
      (fun k => _root_.GD.N0232.N0720.N1097.d019205 _)
      (fun k => _root_.GD.N0232.N0720.N1477.d015753 (m := m) (n := n) (c.seed k))
  · rintro ⟨c, hs, hE⟩
    exact _root_.GD.N0232.N0720.N1097.d019206 hm hn c hs hE




theorem d019217 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1097.d019167 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        (∀ k, _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130
          (c.seed k).value (c.seed k).finiteRisk = (c.seed k).value) ∧
        (∀ k, _root_.GD.N0232.N0720.N1159.d014642 m n
          _root_.GD.N0232.N0720.N1482.d015131
          (c.seed k).value (c.seed k).finiteRisk = (c.seed k).value) ∧
        Tendsto (fun k => ‖(c.seed k).value‖ ^ 2 - ‖c.d019172 k‖ ^ 2) atTop (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨c, hs, hflat⟩ := (_root_.GD.N0232.N0720.N1097.d019215 hm hn).1 h
    have hδ2 : Tendsto (fun k => _root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k)
        _root_.GD.N0232.N0720.N1482.d015130) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hflat
        (fun k => _root_.GD.N0232.N0720.N1159.d014650 m n (c.seed k) _) (fun k => ?_)
      unfold _root_.GD.N0232.N0720.N1482.d015169
      linarith [_root_.GD.N0232.N0720.N1159.d014650 m n (c.seed k)
        _root_.GD.N0232.N0720.N1482.d015131]
    have hδ3 : Tendsto (fun k => _root_.GD.N0232.N0720.N1159.d014647 m n (c.seed k)
        _root_.GD.N0232.N0720.N1482.d015131) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hflat
        (fun k => _root_.GD.N0232.N0720.N1159.d014650 m n (c.seed k) _) (fun k => ?_)
      unfold _root_.GD.N0232.N0720.N1482.d015169
      linarith [_root_.GD.N0232.N0720.N1159.d014650 m n (c.seed k)
        _root_.GD.N0232.N0720.N1482.d015130]
    have hf2 : _root_.GD.N0232.N0720.N1482.d015130 ∈ c.d019190 :=
      c.d019189 _ _
        (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015232 m n p q hp hq) hδ2
    have hf3 : _root_.GD.N0232.N0720.N1482.d015131 ∈ c.d019190 :=
      c.d019189 _ _
        (fun p q hp hq => _root_.GD.N0232.N0720.N1146.d015233 m n p q hp hq)
        hδ3
    have htop := c.d019195 hf2 hf3
    refine ⟨_root_.GD.N0232.N0720.N1097.d019214 (c.d019198 htop), c.d019203 hm hn hs,
      fun _ => c.d019196 htop _, fun _ => c.d019196 htop _, ?_⟩
    show Tendsto (fun _ : ℕ => ‖c.d019178‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n c.d019178‖ ^ 2)
      atTop (𝓝 0)
    rw [c.d019201, sub_self]
    exact tendsto_const_nhds
  · rintro ⟨c, hs, h2, h3, hgap⟩
    exact _root_.GD.N0232.N0720.N1097.d019213 hm hn c hs h2 h3 hgap

end

end N1097
end N0720
end N0232
end GD
