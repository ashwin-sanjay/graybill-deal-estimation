import GD.Module0842
import GD.Module0845

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0781

noncomputable section

open _root_.GD.N0228.N0547.N0778
open _root_.GD.N0228.N0547.N0791
open _root_.GD.N0228.N0547.N0790

def d012916 (r s : ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 1).prod ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))


def d012917 (z : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (z.1 ^ 2, z.2)

@[fun_prop]
theorem d012918 : Measurable _root_.GD.N0228.N0547.N0781.d012917 := by
  unfold _root_.GD.N0228.N0547.N0781.d012917
  fun_prop



theorem d012919
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012917 =
      (_root_.GD.N0228.N0547.N0778.d009365 1).prod ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)) := by
  calc
    (_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012917 =
        ((gaussianReal 0 1).map (fun z : ℝ => z ^ 2)).prod
          (((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)).map id) := by
      letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) := by
        unfold _root_.GD.N0228.N0547.N0778.d009365
        exact isProbabilityMeasure_gammaMeasure
          (by positivity) (by norm_num)
      letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) := by
        unfold _root_.GD.N0228.N0547.N0778.d009365
        exact isProbabilityMeasure_gammaMeasure
          (by positivity) (by norm_num)
      exact (Measure.map_prod_map (gaussianReal 0 1)
        ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))
        (by exact (measurable_id.pow_const 2)) measurable_id).symm
    _ = (_root_.GD.N0228.N0547.N0778.d009365 1).prod ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)) := by
      rw [_root_.GD.N0121.d006355, Measure.map_id]
      rfl



def d012920 (z : ℝ × (ℝ × ℝ)) : Fin 3 → ℝ :=
  _root_.GD.N0228.N0547.N0791.d012866 (_root_.GD.N0228.N0547.N0781.d012917 z)

@[fun_prop]
theorem d012921 : Measurable _root_.GD.N0228.N0547.N0781.d012920 := by
  unfold _root_.GD.N0228.N0547.N0781.d012920
  fun_prop



theorem d012922
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012920 =
      _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
  have hrR : 0 < (r : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr hr) (by norm_num)
  have hsR : 0 < (s : ℝ) / 2 :=
    div_pos (Nat.cast_pos.mpr hs) (by norm_num)
  calc
    (_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012920 =
        ((_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012917).map
          _root_.GD.N0228.N0547.N0791.d012866 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0791.d012867
        _root_.GD.N0228.N0547.N0781.d012918]
      rfl
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))).map
            _root_.GD.N0228.N0547.N0791.d012866 := by
      rw [_root_.GD.N0228.N0547.N0781.d012919 hr hs]
    _ = _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
      have h := _root_.GD.N0228.N0547.N0791.d012873
        (a := (1 / 2 : ℝ)) (b := (r : ℝ) / 2)
        (c := (s : ℝ) / 2) (r := (1 / 2 : ℝ))
        (by norm_num) hrR hsR (by norm_num)
      simpa [_root_.GD.N0228.N0547.N0778.d009365] using h



def d012923
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) :
    (Fin 3 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (_root_.GD.N0228.N0547.N0781.d012920 z.1, z.2)

@[fun_prop]
theorem d012924 :
    Measurable _root_.GD.N0228.N0547.N0781.d012923 := by
  unfold _root_.GD.N0228.N0547.N0781.d012923
  fun_prop




theorem d012925
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ((_root_.GD.N0228.N0547.N0790.d012894 r s).prod (_root_.GD.N0228.N0547.N0790.d012893 r s)).map
        _root_.GD.N0228.N0547.N0781.d012923 =
      (_root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2)).prod
          (_root_.GD.N0228.N0547.N0790.d012893 r s) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hr
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hr
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012893 r s) := by
    unfold _root_.GD.N0228.N0547.N0790.d012893
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012894 r s) := by
    unfold _root_.GD.N0228.N0547.N0790.d012894
    infer_instance
  calc
    ((_root_.GD.N0228.N0547.N0790.d012894 r s).prod (_root_.GD.N0228.N0547.N0790.d012893 r s)).map
        _root_.GD.N0228.N0547.N0781.d012923 =
      ((_root_.GD.N0228.N0547.N0790.d012894 r s).map _root_.GD.N0228.N0547.N0781.d012920).prod
        ((_root_.GD.N0228.N0547.N0790.d012893 r s).map id) := by
        exact (Measure.map_prod_map (_root_.GD.N0228.N0547.N0790.d012894 r s)
          (_root_.GD.N0228.N0547.N0790.d012893 r s) _root_.GD.N0228.N0547.N0781.d012921
          measurable_id).symm
    _ = (_root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2)).prod
          (_root_.GD.N0228.N0547.N0790.d012893 r s) := by
      rw [Measure.map_id]
      have hbase : _root_.GD.N0228.N0547.N0790.d012894 r s = _root_.GD.N0228.N0547.N0781.d012916 r s := rfl
      rw [hbase, _root_.GD.N0228.N0547.N0781.d012922 hr hs]

end

end GD.N0228.N0547.N0781

#print axioms _root_.GD.N0228.N0547.N0781.d012922
#print axioms _root_.GD.N0228.N0547.N0781.d012925
