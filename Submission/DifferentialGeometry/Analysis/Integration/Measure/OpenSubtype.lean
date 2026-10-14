import Submission.DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Integral.Measure

open _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry (U : TopologicalSpace.Opens M) : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry (U : TopologicalSpace.Opens M) : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private def openSubtypePartialDiffeomorphOne (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M 1 where
  toPartialEquiv := (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv
  open_source := isOpen_univ
  open_target := by simpa using U.isOpen
  contMDiffOn_toFun := (contMDiff_subtype_val (I := I) (U := U) (n := 1)).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have hxU : x ∈ U := by simpa using hx
    have hs : ContMDiffAt I I ∞ (U.openPartialHomeomorphSubtypeCoe hU).symm x := by
      apply (ContMDiffAt.subtypeVal_comp_iff U _ x).mp
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [U.isOpen.mem_nhds hxU] with y hy
      exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv (by simpa using hy)
    exact hs.contMDiffWithinAt.of_le (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.openSubtypePartialDiffeomorphOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.openSubtypePartialDiffeomorphOne target :: scope.openDecls } }

theorem map_riemannianVolumeMeasure_restrictOpen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    Measure.map (Subtype.val : U → M)
      (riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U)) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict U := by
  classical
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  by_cases hU : Nonempty U
  · let Φ := openSubtypePartialDiffeomorphOne (I := I) U hU
    have hm : ∀ x ∈ Φ.source, ∀ v w, (g.restrictOpen U).inner x v w =
        g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
      intro x _ v w
      change g.inner (x : M) v w =
        g.inner (x : M) (mfderiv I I (Subtype.val : U → M) x v)
          (mfderiv I I (Subtype.val : U → M) x w)
      rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    have hv := riemannianVolumeMeasure_partialIsometry (g.restrictOpen U) g Φ hm
    have hs : Φ.source = Set.univ := rfl
    have ht : Φ.target = U := by simp [Φ, openSubtypePartialDiffeomorphOne]
    rw [hs, Measure.restrict_univ, ht] at hv
    have hi : AEMeasurable Φ.symm ((riemannianVolumeMeasure (I := I) (M := M) g).restrict U) := by
      have hi' : AEMeasurable Φ.symm
          ((riemannianVolumeMeasure (I := I) (M := M) g).restrict Φ.target) :=
        Φ.contMDiffOn_invFun.continuousOn.aemeasurable Φ.open_target.measurableSet
      rwa [ht] at hi'
    rw [hv, AEMeasurable.map_map_of_aemeasurable
      continuous_subtype_val.measurable.aemeasurable hi]
    calc
      _ = Measure.map id ((riemannianVolumeMeasure (I := I) (M := M) g).restrict U) := by
        apply Measure.map_congr
        filter_upwards [_root_.MeasureTheory.ae_restrict_mem U.isOpen.measurableSet] with y hy
        exact Φ.toPartialEquiv.right_inv (by simpa only [ht] using hy)
      _ = _ := Measure.map_id
  · let : IsEmpty U := not_nonempty_iff.mp hU
    have hUe : (U : Set M) = ∅ := by
      ext x
      exact ⟨fun hx => isEmptyElim (⟨x, hx⟩ : U), fun hx => hx.elim⟩
    have hz : riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) = 0 :=
      Subsingleton.elim _ _
    rw [hz, Measure.map_zero]
    exact (show (riemannianVolumeMeasure (I := I) (M := M) g).restrict U = 0 by
      rw [hUe, Measure.restrict_empty]).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.map_riemannianVolumeMeasure_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.map_riemannianVolumeMeasure_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.map_riemannianVolumeMeasure_restrictOpen ``Submission.DifferentialGeometry.Integral.Measure.map_riemannianVolumeMeasure_restrictOpen

end

end DifferentialGeometry.Integral.Measure
