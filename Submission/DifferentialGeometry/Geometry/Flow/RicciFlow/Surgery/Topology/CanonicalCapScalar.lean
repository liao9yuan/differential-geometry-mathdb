import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowScalarBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealThreeSpace : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealThreeSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealThreeSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeThreeSpaceMemOpensStandardCapWindow (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      (standardCapWindow D).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeThreeSpaceMemOpensStandardCapWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeThreeSpaceMemOpensStandardCapWindow target :: scope.openDecls } }

theorem exists_presented_cap_scalar_lower_bound_of_canonical_window
    (D : ℝ) (hD : StandardCap.transitionEnd < D) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {m : ℕ} {ε : ℝ}, ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            S.neck.scale / 2 ≤ metricScalarAt S.witness.metric (S.witness.cap z) := by
  obtain ⟨ε₀, C, hε₀, _, hbound⟩ :=
    StandardCap.exists_uniform_window_scalar_bounds_of_metric_close D StandardCap.transitionEnd
      (hD.trans (lt_add_one D))
  refine ⟨ε₀, hε₀, ?_⟩
  intro P Q a s E fixed m ε hε hm b S hcanonical z
  obtain ⟨x₀, δ, k, d, w, _, hinner, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hsmall := w.properties.window_close
  change metricDerivENormSupOn
    {y : standardCapWindow D | (riemannianEDistOf StandardCap.metric 0 y.val).toReal < D} m
    w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  have hrestrict := metricDerivENormSupOn_mono
    (show {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd} ⊆
      {y : standardCapWindow D | ‖y.val‖ < D} from fun y hy => hy.trans_lt hD)
    hm w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D))
  have hscalar := (hbound w.windowMetric
    (hrestrict.trans_lt (hsmall.trans_le (ENNReal.ofReal_le_ofReal hε))) x hx).1
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.window
      S.window_smooth.contMDiff
      (fun p => (S.window_smooth.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) rfl
  have heq := (curvature_of_injective_local_isometry w.windowMetric
    (scaleMetric S.neck.scale S.neck.scale_pos E.outputMetric) S.window hlocal
    S.window_smooth.isEmbedding.injective (fun y v z => by
      rw [scaleMetric_inner]
      exact hinner y v z) x).1
  rw [metricScalarAt_scaleMetric] at heq
  have hnormalized : S.neck.scale * metricScalarAt w.windowMetric x =
      metricScalarAt E.outputMetric (S.window x) := by
    rw [heq, ← mul_assoc, mul_inv_cancel₀ S.neck.scale_pos.ne', one_mul]
  have hlower := mul_le_mul_of_nonneg_left hscalar.le S.neck.scale_pos.le
  rw [hnormalized, hpoint, ← S.scalar_eq E] at hlower
  simpa only [div_eq_mul_inv, one_mul] using hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window

theorem exists_presented_cap_scalar_lower_bound_of_canonical_window_core
    (Dstar : ℝ) (hD : StandardCap.transitionEnd < Dstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}, Dstar ≤ D → ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            S.neck.scale / 2 ≤ metricScalarAt S.witness.metric (S.witness.cap z) := by
  obtain ⟨ε₀, C, hε₀, _, hbound⟩ :=
    StandardCap.exists_uniform_window_scalar_bounds_of_metric_close Dstar
      StandardCap.transitionEnd (hD.trans (lt_add_one Dstar))
  refine ⟨ε₀, hε₀, ?_⟩
  intro P Q a s E fixed D m ε hDD hε hm b S hcanonical z
  obtain ⟨x₀, δ, k, d, w, _, hinner, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hDpos : 0 < Dstar := StandardCap.transitionEnd_pos.trans hD
  let ws := w.restrictWindow hDpos hDD
  have hs : standardCapWindow Dstar ≤ standardCapWindow D := fun _ hy =>
    hy.trans_le (add_le_add hDD le_rfl)
  let inc := TopologicalSpace.Opens.inclusion hs
  let x' : standardCapWindow Dstar := ⟨x.val, show ‖x.val‖ < Dstar + 1 by
    linarith [hx.trans_lt hD]⟩
  have hsmall := ws.properties.window_close
  change metricDerivENormSupOn
    {y : standardCapWindow Dstar |
      (riemannianEDistOf StandardCap.metric 0 y.val).toReal < Dstar} m
    ws.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
      (StandardCap.metric.restrictOpen (standardCapWindow Dstar)) < ENNReal.ofReal ε at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  have hrestrict := metricDerivENormSupOn_mono
    (show {y : standardCapWindow Dstar | ‖y.val‖ ≤ StandardCap.transitionEnd} ⊆
      {y : standardCapWindow Dstar | ‖y.val‖ < Dstar} from fun y hy => hy.trans_lt hD)
    hm ws.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
      (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
  have hscalar := (hbound ws.windowMetric
    (hrestrict.trans_lt (hsmall.trans_le (ENNReal.ofReal_le_ofReal hε))) x' hx).1
  have hinc : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion hs
  have hJ : ContMDiff ThreeModel ThreeModel ∞ (S.window ∘ inc) :=
    S.window_smooth.contMDiff.comp hinc
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (S.window ∘ inc) :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      (S.window ∘ inc) hJ
      (fun p => by
        have hd := mfderiv_comp p (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
          (hinc.mdifferentiableAt (by simp))
        simp only [inc, mfderiv_opens_incl] at hd
        dsimp only [TangentSpace] at hd ⊢
        rw [hd]
        exact (S.window_smooth.isImmersion.isImmersionAt (inc p)).injective_mfderiv (by simp))
      rfl
  have hinj : Function.Injective (S.window ∘ inc) := fun p q h => by
    have h' := S.window_smooth.isEmbedding.injective h
    exact Subtype.ext (congrArg (fun y : standardCapWindow D => y.val) h')
  have heq := (curvature_of_injective_local_isometry ws.windowMetric
    (scaleMetric S.neck.scale S.neck.scale_pos E.outputMetric) (S.window ∘ inc) hlocal hinj
    (fun y v v' => by
      rw [scaleMetric_inner,
        StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
      change w.windowMetric.inner (inc y) v v' = _
      have hd := mfderiv_comp y (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
        (hinc.mdifferentiableAt (by simp))
      simp only [inc, mfderiv_opens_incl] at hd
      dsimp only [TangentSpace] at hd ⊢
      rw [hd]
      exact hinner (inc y) v v') x').1
  rw [metricScalarAt_scaleMetric] at heq
  have hx'eq : (S.window ∘ inc) x' = S.window x := rfl
  have hnormalized : S.neck.scale * metricScalarAt ws.windowMetric x' =
      metricScalarAt E.outputMetric (S.window x) := by
    rw [heq, hx'eq, ← mul_assoc, mul_inv_cancel₀ S.neck.scale_pos.ne', one_mul]
  have hlower := mul_le_mul_of_nonneg_left hscalar.le S.neck.scale_pos.le
  rw [hnormalized, hpoint, ← S.scalar_eq E] at hlower
  simpa only [div_eq_mul_inv, one_mul] using hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presented_cap_scalar_lower_bound_of_canonical_window_core

theorem exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ},
        StandardCap.transitionEnd < D → ε ≤ 1 / 2 → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ z : ThreeBall,
            |metricScalarAt S.witness.metric (S.witness.cap z)| ≤ C * S.neck.scale := by
  obtain ⟨C, hC, hbound⟩ := StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  refine ⟨C, hC, ?_⟩
  intro P Q a s E fixed D ε m hD hε hm b S hcanonical z
  obtain ⟨x₀, δ, k, d, w, _, hinner, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hscalar := hbound w hε hm E.outputMetric S.window S.window_smooth
    S.neck.scale S.neck.scale_pos hinner x (hx.trans_lt hD)
  rw [hpoint, ← S.scalar_eq E] at hscalar
  exact hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
