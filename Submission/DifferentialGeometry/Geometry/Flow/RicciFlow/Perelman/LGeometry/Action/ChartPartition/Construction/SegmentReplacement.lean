import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.EulerLagrange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Function _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.Interval

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

private theorem fin_segment_left {m : Nat} {i j : Fin m} (hji : j < i) :
    j.succ ≤ i.castSucc := by
  change j.val + 1 ≤ i.val
  exact hji

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.fin_segment_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.fin_segment_left target :: scope.openDecls } }

private theorem fin_segment_right {m : Nat} {i j : Fin m} (hij : i < j) :
    i.succ ≤ j.castSucc := by
  change i.val + 1 ≤ j.val
  exact hij

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.fin_segment_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.fin_segment_right target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem exists_continuous_curve_of_chartH1_segment_replacement
    {m : Nat} (t : Fin (m + 1) → Real) (htmono : Monotone t)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (j : Fin m) → timeH1 E (partitionIntervalLength t j))
    (hsrc : ∀ j, _root_.Set.MapsTo gamma (_root_.Set.Icc (t j.castSucc) (t j.succ))
      (chartAt H (p j)).source)
    (hrep : ∀ j, _root_.Set.EqOn (u j).toFun
      (fun r ↦ extChartAt I (p j) (gamma (t j.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t j)))
    (i : Fin m) (hpos : t i.castSucc < t i.succ)
    (v : timeH1 E (partitionIntervalLength t i)) (hends : v ∈ sameTimeEnds (u i))
    (htar : _root_.Set.MapsTo v.toFun (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (extChartAt I (p i)).target) :
    ∃ gammaV : Real → M,
      Continuous gammaV ∧
      gammaV (t 0) = gamma (t 0) ∧
      gammaV (t (Fin.last m)) = gamma (t (Fin.last m)) ∧
      (∀ j, _root_.Set.MapsTo gammaV (_root_.Set.Icc (t j.castSucc) (t j.succ))
        (chartAt H (p j)).source) ∧
      (∀ j, _root_.Set.EqOn ((Function.update u i v) j).toFun
        (fun r ↦ extChartAt I (p j) (gammaV (t j.castSucc + r)))
        (_root_.Set.Icc (0 : Real) (partitionIntervalLength t j))) := by
  classical
  let L : Real := partitionIntervalLength t i
  have hL : 0 ≤ L := by
    dsimp only [L, partitionIntervalLength]
    exact sub_nonneg.mpr hpos.le
  let pr : Real → Real := fun s ↦
    ((Set.projIcc (0 : Real) L hL s : _root_.Set.Icc (0 : Real) L) : Real)
  have hpr_mem (s : Real) : pr s ∈ _root_.Set.Icc (0 : Real) L :=
    (Set.projIcc (0 : Real) L hL s).2
  have hpr_cont : Continuous pr :=
    continuous_subtype_val.comp continuous_projIcc
  have hvpr : Continuous (fun s ↦ v.toFun (pr s)) :=
    v.continuousOn_toFun.comp_continuous hpr_cont hpr_mem
  have hvpr_tar : _root_.Set.MapsTo (fun s ↦ v.toFun (pr s)) _root_.Set.univ
      (extChartAt I (p i)).target := fun s _ ↦ htar (hpr_mem s)
  let liftV : Real → M := fun s ↦
    (extChartAt I (p i)).symm (v.toFun (pr (s - t i.castSucc)))
  have hlift : Continuous liftV := by
    rw [← continuousOn_univ]
    exact (continuousOn_extChartAt_symm (I := I) (p i)).comp
      (hvpr.comp (continuous_id.sub continuous_const)).continuousOn
      (hvpr_tar.comp fun _ _ ↦ _root_.Set.mem_univ _)
  have hshift_mem {s : Real} (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      s - t i.castSucc ∈ _root_.Set.Icc (0 : Real) L := by
    dsimp only [L, partitionIntervalLength]
    exact ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 _⟩
  have hpr_shift {s : Real} (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      pr (s - t i.castSucc) = s - t i.castSucc := by
    exact congrArg Subtype.val (Set.projIcc_of_mem hL (hshift_mem hs))
  have hend_add : t i.castSucc + L = t i.succ := by
    dsimp only [L, partitionIntervalLength]
    ring
  have hlift_left : liftV (t i.castSucc) = gamma (t i.castSucc) := by
    have hzero : (0 : Real) ∈ _root_.Set.Icc (0 : Real) L := ⟨le_rfl, hL⟩
    have hv0 : v.toFun 0 = (u i).toFun 0 := by
      rw [v.toFun_zero, (u i).toFun_zero]
      exact hends.1
    simp only [liftV, sub_self]
    rw [show pr 0 = 0 from
      congrArg Subtype.val (Set.projIcc_of_mem hL hzero), hv0,
      hrep i hzero]
    simp only [add_zero]
    exact (extChartAt I (p i)).left_inv (by
      simpa only [extChartAt_source] using hsrc i ⟨le_rfl, hpos.le⟩)
  have hlift_right : liftV (t i.succ) = gamma (t i.succ) := by
    have hLi : L ∈ _root_.Set.Icc (0 : Real) L := ⟨hL, le_rfl⟩
    have hsub : t i.succ - t i.castSucc = L := by
      simp only [L, partitionIntervalLength]
    have hvL : v.toFun L = (u i).toFun L := hends.2
    simp only [liftV]
    rw [hsub, show pr L = L from
      congrArg Subtype.val (Set.projIcc_of_mem hL hLi), hvL,
      hrep i hLi]
    change (extChartAt I (p i)).symm
      (extChartAt I (p i) (gamma (t i.castSucc + L))) = gamma (t i.succ)
    rw [hend_add]
    exact (extChartAt I (p i)).left_inv (by
      simpa only [extChartAt_source] using hsrc i ⟨hpos.le, le_rfl⟩)
  let gammaV : Real → M := Set.piecewise
    (_root_.Set.Icc (t i.castSucc) (t i.succ)) liftV gamma
  have hgammaV : Continuous gammaV := by
    apply hlift.piecewise (s := _root_.Set.Icc (t i.castSucc) (t i.succ))
    · intro s hs
      have hs' : s ∈ ({t i.castSucc, t i.succ} : Set Real) := by
        simpa only [frontier_Icc hpos.le] using hs
      rcases hs' with hs | hs
      · simpa only [hs] using hlift_left
      · have hs_eq : s = t i.succ := by
          simpa only [_root_.Set.mem_singleton_iff] using hs
        simpa only [hs_eq] using hlift_right
    · exact hgamma
  have hpiece_mem {s : Real} (hs : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      gammaV s = liftV s :=
    (_root_.Set.Icc (t i.castSucc) (t i.succ)).piecewise_eq_of_mem liftV gamma hs
  have hpiece_not {s : Real} (hs : s ∉ _root_.Set.Icc (t i.castSucc) (t i.succ)) :
      gammaV s = gamma s :=
    (_root_.Set.Icc (t i.castSucc) (t i.succ)).piecewise_eq_of_notMem liftV gamma hs
  have hpiece_left : gammaV (t i.castSucc) = gamma (t i.castSucc) := by
    rw [hpiece_mem ⟨le_rfl, hpos.le⟩, hlift_left]
  have hpiece_right : gammaV (t i.succ) = gamma (t i.succ) := by
    rw [hpiece_mem ⟨hpos.le, le_rfl⟩, hlift_right]
  have hother (j : Fin m) (hji : j ≠ i) {s : Real}
      (hs : s ∈ _root_.Set.Icc (t j.castSucc) (t j.succ)) : gammaV s = gamma s := by
    by_cases hsel : s ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)
    · rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hle : t j.succ ≤ t i.castSucc := htmono (fin_segment_left hlt)
        have heq : s = t i.castSucc := le_antisymm (hs.2.trans hle) hsel.1
        simpa only [heq] using hpiece_left
      · have hle : t i.succ ≤ t j.castSucc := htmono (fin_segment_right hgt)
        have heq : s = t i.succ := le_antisymm hsel.2 (hle.trans hs.1)
        simpa only [heq] using hpiece_right
    · exact hpiece_not hsel
  have hstart : gammaV (t 0) = gamma (t 0) := by
    by_cases hs : t 0 ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)
    · have hle : t 0 ≤ t i.castSucc := htmono (Fin.zero_le _)
      have heq : t 0 = t i.castSucc := le_antisymm hle hs.1
      simpa only [heq] using hpiece_left
    · exact hpiece_not hs
  have hlast : gammaV (t (Fin.last m)) = gamma (t (Fin.last m)) := by
    by_cases hs : t (Fin.last m) ∈ _root_.Set.Icc (t i.castSucc) (t i.succ)
    · have hle : t i.succ ≤ t (Fin.last m) := htmono (Fin.le_last _)
      have heq : t (Fin.last m) = t i.succ := le_antisymm hs.2 hle
      simpa only [heq] using hpiece_right
    · exact hpiece_not hs
  have hsrcV (j : Fin m) : _root_.Set.MapsTo gammaV
      (_root_.Set.Icc (t j.castSucc) (t j.succ)) (chartAt H (p j)).source := by
    intro s hs
    by_cases hji : j = i
    · subst j
      rw [hpiece_mem hs]
      simpa only [liftV, extChartAt_source] using
        (extChartAt I (p i)).map_target (htar (by
          rw [hpr_shift hs]
          exact hshift_mem hs))
    · rw [hother j hji hs]
      exact hsrc j hs
  have hrepV (j : Fin m) : _root_.Set.EqOn ((Function.update u i v) j).toFun
      (fun r ↦ extChartAt I (p j) (gammaV (t j.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t j)) := by
    intro r hr
    have hseg : t j.castSucc + r ∈ _root_.Set.Icc (t j.castSucc) (t j.succ) := by
      dsimp only [partitionIntervalLength] at hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      change v.toFun r = extChartAt I (p i) (gammaV (t i.castSucc + r))
      rw [hpiece_mem hseg]
      simp only [liftV]
      rw [
        hpr_shift hseg]
      have hsub : t i.castSucc + r - t i.castSucc = r := by ring
      rw [hsub]
      exact ((extChartAt I (p i)).right_inv (htar hr)).symm
    · rw [Function.update_of_ne hji]
      change (u j).toFun r = extChartAt I (p j) (gammaV (t j.castSucc + r))
      rw [hother j hji hseg]
      exact hrep j hr
  exact ⟨gammaV, hgammaV, hstart, hlast, hsrcV, hrepV⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_continuous_curve_of_chartH1_segment_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_continuous_curve_of_chartH1_segment_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_continuous_curve_of_chartH1_segment_replacement ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_continuous_curve_of_chartH1_segment_replacement

end DifferentialGeometry.PDE.RicciFlow.Perelman
