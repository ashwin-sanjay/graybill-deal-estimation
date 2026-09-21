import GD.Module1193
import GD.Module1177













open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0720.N1411

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1295 _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1459 _root_.GD.N0232.N0720.N1458
open _root_.GD.N0232.N0720.N1437 _root_.GD.N0232.N0720.N1467
open _root_.GD.N0137 _root_.GD.N0107


def d019255 (u s : ℝ) : _root_.GD.N0137.d008894 2 :=
  ![u + Real.sqrt s, u - Real.sqrt s]

def d019256 (u v s t : ℝ) : _root_.GD.N0232.N0720.N1080.d014170 2 2 :=
  (_root_.GD.N0232.N0720.N1411.d019255 u s, _root_.GD.N0232.N0720.N1411.d019255 v t)

def d019257 (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (u v s t : ℝ) : ℝ :=
  d (_root_.GD.N0232.N0720.N1411.d019256 u v s t)

theorem d019258 (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009084 x = (x 0 + x 1) / 2 := by
  simp [_root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419, Fin.sum_univ_two]

theorem d019259 (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009085 x / 2 = ((x 0 - x 1) / 2) ^ 2 := by
  simp [_root_.GD.N0107.d009085, _root_.GD.N0126.d006422,
    _root_.GD.N0126.d006421, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419, Fin.sum_univ_two]
  ring


theorem d019260 (x : _root_.GD.N0137.d008894 2) :
    ∃ p : Equiv.Perm (Fin 2),
      _root_.GD.N0232.N0720.N1411.d019255 (_root_.GD.N0107.d009084 x) (_root_.GD.N0107.d009085 x / 2) = x ∘ p := by
  classical
  rw [_root_.GD.N0232.N0720.N1411.d019258, _root_.GD.N0232.N0720.N1411.d019259]
  by_cases h : 0 ≤ (x 0 - x 1) / 2
  · refine ⟨1, ?_⟩
    ext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1411.d019255, Real.sqrt_sq_eq_abs, abs_of_nonneg h] <;>
      ring
  · refine ⟨Equiv.swap 0 1, ?_⟩
    ext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1411.d019255, Real.sqrt_sq_eq_abs, abs_of_neg (lt_of_not_ge h)] <;> ring

theorem d019261 (omega : _root_.GD.N0232.N0720.N1080.d014170 2 2) :
    ∃ p : _root_.GD.N0232.N0720.N1506.d018997 2 2,
      _root_.GD.N0232.N0720.N1411.d019256
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0107.d009085 omega.1 / 2) (_root_.GD.N0107.d009085 omega.2 / 2) =
      _root_.GD.N0232.N0720.N1506.d018998 2 2 p omega := by
  obtain ⟨p, hp⟩ := _root_.GD.N0232.N0720.N1411.d019260 omega.1
  obtain ⟨q, hq⟩ := _root_.GD.N0232.N0720.N1411.d019260 omega.2
  exact ⟨(p, q), Prod.ext hp hq⟩



theorem d019262 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hp : ∀ p omega, d (_root_.GD.N0232.N0720.N1506.d018998 2 2 p omega) = d omega)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 2 2) :
    d omega = _root_.GD.N0232.N0720.N1459.d018930 2 2 (_root_.GD.N0232.N0720.N1411.d019257 d) omega := by
  obtain ⟨p, heq⟩ := _root_.GD.N0232.N0720.N1411.d019261 omega
  simp only [_root_.GD.N0232.N0720.N1459.d018930, _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
    _root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
    Nat.cast_ofNat, _root_.GD.N0232.N0720.N1411.d019257]
  rw [heq, hp]

theorem d019263 (b a u s : ℝ) (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1411.d019255 (b + a * u) (a ^ 2 * s) =
      _root_.GD.N0107.d009018 2 b a (_root_.GD.N0232.N0720.N1411.d019255 u s) := by
  have hs : Real.sqrt (a ^ 2 * s) = a * Real.sqrt s := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  ext i
  fin_cases i <;> simp [_root_.GD.N0232.N0720.N1411.d019255, _root_.GD.N0107.d009018, hs] <;> ring

theorem d019264 (b a u v s t : ℝ) (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1411.d019256 (b + a * u) (b + a * v) (a ^ 2 * s) (a ^ 2 * t) =
      _root_.GD.N0107.d009024 2 2 b a a (_root_.GD.N0232.N0720.N1411.d019256 u v s t) := by
  exact Prod.ext (_root_.GD.N0232.N0720.N1411.d019263 b a u s ha) (_root_.GD.N0232.N0720.N1411.d019263 b a v t ha)

theorem d019265 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1295.d019239 2 2 d) : _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1411.d019257 d) := by
  intro b a u v s t ha
  unfold _root_.GD.N0232.N0720.N1411.d019257
  rw [_root_.GD.N0232.N0720.N1411.d019264 b a u v s t ha, hd b a _ ha]

theorem d019266 (u v s t : ℝ) :
    _root_.GD.N0232.N0720.N1411.d019256 (-u) (-v) s t =
      _root_.GD.N0232.N0720.N1506.d018998 2 2 (Equiv.swap 0 1, Equiv.swap 0 1)
        (_root_.GD.N0232.N0720.N1446.d019019 2 2 (_root_.GD.N0232.N0720.N1411.d019256 u v s t)) := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1411.d019256, _root_.GD.N0232.N0720.N1411.d019255, _root_.GD.N0232.N0720.N1506.d018998,
        _root_.GD.N0232.N0720.N1446.d019019, Function.comp_def] <;> ring
  · ext i
    fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1411.d019256, _root_.GD.N0232.N0720.N1411.d019255, _root_.GD.N0232.N0720.N1506.d018998,
        _root_.GD.N0232.N0720.N1446.d019019, Function.comp_def] <;> ring

theorem d019267 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hp : ∀ p omega, d (_root_.GD.N0232.N0720.N1506.d018998 2 2 p omega) = d omega)
    (ho : ∀ omega, d (_root_.GD.N0232.N0720.N1446.d019019 2 2 omega) = -d omega) :
    _root_.GD.N0232.N0720.N1460.d003039 (_root_.GD.N0232.N0720.N1411.d019257 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1411.d019257
  rw [_root_.GD.N0232.N0720.N1411.d019266, hp, ho]


def d019268 (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) : ℝ → ℝ → ℝ :=
  _root_.GD.N0232.N0720.N1460.d003029 (_root_.GD.N0232.N0720.N1411.d019257 d)

theorem d019269 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) : Measurable (fun p : ℝ × ℝ ↦ _root_.GD.N0232.N0720.N1411.d019268 d p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1411.d019268 _root_.GD.N0232.N0720.N1460.d003029 _root_.GD.N0232.N0720.N1411.d019257
  apply hd.comp
  unfold _root_.GD.N0232.N0720.N1411.d019256 _root_.GD.N0232.N0720.N1411.d019255
  fun_prop

theorem d019270 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hp : ∀ p omega, d (_root_.GD.N0232.N0720.N1506.d018998 2 2 p omega) = d omega)
    (ho : ∀ omega, d (_root_.GD.N0232.N0720.N1446.d019019 2 2 omega) = -d omega) :
    _root_.GD.N0232.N0720.N1460.d003040 (_root_.GD.N0232.N0720.N1411.d019268 d) := by
  intro z q
  exact _root_.GD.N0232.N0720.N1460.d003041 (_root_.GD.N0232.N0720.N1411.d019257 d) (_root_.GD.N0232.N0720.N1411.d019267 hp ho) z q


def d019271 (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) : ℝ × ℝ → ℝ :=
  _root_.GD.N0232.N0720.N1458.d018936 (_root_.GD.N0232.N0720.N1411.d019268 (_root_.GD.N0232.N0720.N1295.d019242 2 2 d))

theorem d019272 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) : Measurable (_root_.GD.N0232.N0720.N1411.d019271 d) :=
  _root_.GD.N0232.N0720.N1458.d018937
    (_root_.GD.N0232.N0720.N1411.d019269 (_root_.GD.N0232.N0720.N1295.d019244 2 2 hd))



theorem d019273 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1295.d019239 2 2 d) (omega : _root_.GD.N0232.N0720.N1080.d014170 2 2)
    (hpos : 0 < _root_.GD.N0107.d009085 omega.1 / 2 + _root_.GD.N0107.d009085 omega.2 / 2) :
    _root_.GD.N0232.N0720.N1295.d019242 2 2 d omega =
      _root_.GD.N0232.N0720.N1437.d002998 (fun r s ↦ _root_.GD.N0232.N0720.N1411.d019271 d (r, s))
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0107.d009085 omega.1 / 2) (_root_.GD.N0107.d009085 omega.2 / 2) := by
  let e := _root_.GD.N0232.N0720.N1295.d019242 2 2 d
  have hp : ∀ p omega, e (_root_.GD.N0232.N0720.N1506.d018998 2 2 p omega) = e omega :=
    _root_.GD.N0232.N0720.N1295.d019247 2 2 d
  have ho : ∀ omega, e (_root_.GD.N0232.N0720.N1446.d019019 2 2 omega) = -e omega :=
    _root_.GD.N0232.N0720.N1295.d019248 2 2 d
  have ha : _root_.GD.N0232.N0720.N1437.d003000 (_root_.GD.N0232.N0720.N1411.d019257 e) :=
    _root_.GD.N0232.N0720.N1411.d019265 (_root_.GD.N0232.N0720.N1295.d019250 2 2 hd)
  calc
    e omega = _root_.GD.N0232.N0720.N1459.d018930 2 2 (_root_.GD.N0232.N0720.N1411.d019257 e) omega := _root_.GD.N0232.N0720.N1411.d019262 hp omega
    _ = _root_.GD.N0232.N0720.N1460.d003027 (_root_.GD.N0232.N0720.N1411.d019268 e)
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0107.d009085 omega.1 / 2) (_root_.GD.N0107.d009085 omega.2 / 2) := by
      simpa only [_root_.GD.N0232.N0720.N1459.d018930, _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
        _root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
        Nat.cast_ofNat, _root_.GD.N0232.N0720.N1411.d019268] using
        _root_.GD.N0232.N0720.N1460.d003038 (_root_.GD.N0232.N0720.N1411.d019257 e) ha hpos
    _ = _ := _root_.GD.N0232.N0720.N1458.d018941
      (_root_.GD.N0232.N0720.N1411.d019270 hp ho) hpos





theorem d019274 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta] fun omega ↦
      _root_.GD.N0232.N0720.N1437.d002998 (fun r s ↦ _root_.GD.N0232.N0720.N1411.d019271 d (r, s))
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0107.d009085 omega.1 / 2) (_root_.GD.N0107.d009085 omega.2 / 2) := by
  have hpos : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 2 2 theta,
      0 < _root_.GD.N0107.d009085 omega.1 / 2 + _root_.GD.N0107.d009085 omega.2 / 2 := by
    have href := _root_.GD.N0232.N0720.N1459.d018933 2 2 (by omega) (by omega)
    have href' : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
        0 < _root_.GD.N0107.d009085 omega.1 / 2 + _root_.GD.N0107.d009085 omega.2 / 2 := by
      filter_upwards [href] with omega homega
      simpa only [_root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548,
        Nat.cast_ofNat] using homega
    exact (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta).ae_le href'
  filter_upwards [_root_.GD.N0232.N0720.N1295.d019253 2 2 hd theta, hpos] with
    omega heq hscale
  rw [← heq]
  exact _root_.GD.N0232.N0720.N1411.d019273
    ((_root_.GD.N0232.N0720.N1295.d019240 2 2 d).2 hd.2.1) omega hscale

end
end GD.N0232.N0720.N1411

#print axioms _root_.GD.N0232.N0720.N1411.d019260
#print axioms _root_.GD.N0232.N0720.N1411.d019262
#print axioms _root_.GD.N0232.N0720.N1411.d019272
#print axioms _root_.GD.N0232.N0720.N1411.d019273
#print axioms _root_.GD.N0232.N0720.N1411.d019274
