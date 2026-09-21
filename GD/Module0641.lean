import GD.Module0274
import GD.Module0640
import GD.Module0409
import GD.Module0410

















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0228
namespace N0547
namespace N0778

noncomputable section



def d009365 (d : ℕ) : Measure ℝ :=
  gammaMeasure ((d : ℝ) / 2) (1 / 2)


def d009366 (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * p.2, (1 - p.1) * p.2)

theorem d009367 :
    _root_.GD.N0228.N0547.N0778.d009366 = _root_.GD.N0155.d006305 := by
  rfl

@[fun_prop]
theorem d009368 : Measurable _root_.GD.N0228.N0547.N0778.d009366 := by
  unfold _root_.GD.N0228.N0547.N0778.d009366
  fun_prop


theorem d009369
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (1 / beta a b) * (r ^ (a + b) / Real.Gamma (a + b)) =
      (r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b) := by
  rw [Real.rpow_add hr]
  unfold beta
  field_simp [
    (Real.Gamma_pos_of_pos ha).ne',
    (Real.Gamma_pos_of_pos hb).ne',
    (Real.Gamma_pos_of_pos (add_pos ha hb)).ne']



theorem d009370
    {a b T : ℝ} (hT : 0 < T) :
    T ^ (a - 1) * T ^ (b - 1) * T = T ^ (a + b - 1) := by
  calc
    T ^ (a - 1) * T ^ (b - 1) * T =
        T ^ ((a - 1) + (b - 1)) * T := by
          rw [Real.rpow_add hT]
    _ = T ^ ((a - 1) + (b - 1)) * T ^ (1 : ℝ) := by
          rw [Real.rpow_one]
    _ = T ^ (((a - 1) + (b - 1)) + 1) := by
          rw [← Real.rpow_add hT]
    _ = T ^ (a + b - 1) := by
          congr 1
          ring



theorem d009371
    (r u T : ℝ) :
    Real.exp (-(r * (u * T))) *
        Real.exp (-(r * ((1 - u) * T))) =
      Real.exp (-(r * T)) := by
  rw [← Real.exp_add]
  congr 1
  ring






theorem d009372
    {a b r u T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hu0 : 0 < u) (hu1 : u < 1) (hT : 0 < T) :
    betaPDFReal a b u * gammaPDFReal (a + b) r T =
      gammaPDFReal a r (u * T) *
        gammaPDFReal b r ((1 - u) * T) * T := by
  have huT : 0 < u * T := mul_pos hu0 hT
  have h1u : 0 < 1 - u := sub_pos.mpr hu1
  have h1uT : 0 < (1 - u) * T := mul_pos h1u hT
  rw [betaPDFReal, if_pos ⟨hu0, hu1⟩]
  rw [gammaPDFReal, if_pos hT.le]
  rw [gammaPDFReal, if_pos huT.le]
  rw [gammaPDFReal, if_pos h1uT.le]
  rw [Real.mul_rpow hu0.le hT.le]
  rw [Real.mul_rpow h1u.le hT.le]
  have hnormal := _root_.GD.N0228.N0547.N0778.d009369 ha hb hr
  have hradial := _root_.GD.N0228.N0547.N0778.d009370 (a := a) (b := b) hT
  have hexponential := _root_.GD.N0228.N0547.N0778.d009371 r u T
  calc
    1 / beta a b * u ^ (a - 1) * (1 - u) ^ (b - 1) *
          (r ^ (a + b) / Real.Gamma (a + b) *
            T ^ (a + b - 1) * Real.exp (-(r * T))) =
        ((1 / beta a b) * (r ^ (a + b) / Real.Gamma (a + b))) *
          (u ^ (a - 1) * (1 - u) ^ (b - 1)) *
          T ^ (a + b - 1) * Real.exp (-(r * T)) := by ring
    _ = ((r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b)) *
          (u ^ (a - 1) * (1 - u) ^ (b - 1)) *
          T ^ (a + b - 1) * Real.exp (-(r * T)) := by rw [hnormal]
    _ = ((r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b)) *
          (u ^ (a - 1) * (1 - u) ^ (b - 1)) *
          (T ^ (a - 1) * T ^ (b - 1) * T) *
          Real.exp (-(r * T)) := by rw [hradial]
    _ = (r ^ a / Real.Gamma a * (u ^ (a - 1) * T ^ (a - 1)) *
          Real.exp (-(r * (u * T)))) *
        (r ^ b / Real.Gamma b *
          ((1 - u) ^ (b - 1) * T ^ (b - 1)) *
          Real.exp (-(r * ((1 - u) * T)))) * T := by
            rw [← hexponential]
            ring



theorem d009373
    {d : ℕ} (hd : 1 < d) {u T : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hT : 0 < T) :
    betaPDFReal (1 / 2) (((d : ℝ) - 1) / 2) u *
        gammaPDFReal ((d : ℝ) / 2) (1 / 2) T =
      gammaPDFReal (1 / 2) (1 / 2) (u * T) *
        gammaPDFReal (((d : ℝ) - 1) / 2) (1 / 2)
          ((1 - u) * T) * T := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hb : 0 < ((d : ℝ) - 1) / 2 := by positivity
  have hshape : (1 / 2 : ℝ) + ((d : ℝ) - 1) / 2 = (d : ℝ) / 2 := by
    ring
  rw [← hshape]
  exact _root_.GD.N0228.N0547.N0778.d009372
    (by norm_num) hb (by norm_num) hu0 hu1 hT


theorem d009374 (q : ℝ) : q * (1 : ℝ) = q := by
  simp




theorem d009375
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Ω → ℝ) :
    μ.map (fun ω => Q ω * (1 : ℝ)) = μ.map Q := by
  exact congrArg (fun f : Ω → ℝ => μ.map f)
    (funext fun ω => _root_.GD.N0228.N0547.N0778.d009374 (Q ω))



theorem d009376
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Ω → ℝ)
    (hLaw : μ.map Q = _root_.GD.N0228.N0547.N0778.d009365 1) :
    μ.map (fun ω => Q ω * (1 : ℝ)) = _root_.GD.N0228.N0547.N0778.d009365 1 := by
  rw [_root_.GD.N0228.N0547.N0778.d009375 μ Q, hLaw]

end

end N0778
end N0547
end N0228
end GD

#print axioms _root_.GD.N0228.N0547.N0778.d009369
#print axioms _root_.GD.N0228.N0547.N0778.d009370
#print axioms _root_.GD.N0228.N0547.N0778.d009372
#print axioms _root_.GD.N0228.N0547.N0778.d009373
#print axioms _root_.GD.N0228.N0547.N0778.d009376
