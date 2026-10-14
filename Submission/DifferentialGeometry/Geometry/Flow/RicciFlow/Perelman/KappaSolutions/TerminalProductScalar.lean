import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverCurvatureNorm
import Submission.DifferentialGeometry.Geometry.Metric.Product.ScalarCurvature
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [LocallyPathConnectedSpace N]
  [SemilocallySimplyConnectedSpace N] [Inhabited N]

private local instance terminalProductBaseC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductBaseC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductBaseC1 target :: scope.openDecls } }

private local instance terminalProductCoverC1 : IsManifold I 1 (UniversalCover N) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductCoverC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductCoverC1 target :: scope.openDecls } }


theorem metricScalarAt_lifted_native
    (g : SmoothRiemannianMetric I N) (x' : UniversalCover N) :
    metricScalarAt (I := I) (UniversalCover.liftedMetric (I := I) g) x' =
      metricScalarAt (I := I) g (UniversalCover.proj x') := by
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g (UniversalCover.proj x')
  let b' : Module.Basis
      (Fin (Module.finrank ℝ (TangentSpace I (UniversalCover.proj x')))) ℝ
      (TangentSpace I x') := by
    with_unfolding_all exact b
  have hb' : ∀ i j,
      (UniversalCover.liftedMetric (I := I) g).inner x' (b' i) (b' j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    change g.inner (UniversalCover.proj x') (b i) (b j) = _
    exact hb i j
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal
      (UniversalCover.liftedMetric (I := I) g) b' hb',
    metricScalarAt_eq_sum_sum_rm04_of_orthonormal g b hb]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) x'
      (vec4 (b j) (b i) (b i) (b j)) =
    metricRm04At (I := I) g (UniversalCover.proj x')
      (vec4 (b j) (b i) (b i) (b j))
  exact UniversalCover.metricRm04At_liftedMetric_apply g x' (vec4 (b j) (b i) (b i) (b j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_lifted_native then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_lifted_native"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_lifted_native ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricScalarAt_lifted_native

section SurfaceProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M]

private local instance terminalProductSurfaceC1 : IsManifold (𝓡 2) 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductSurfaceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalProductSurfaceC1 target :: scope.openDecls } }


theorem universalCover_product_scalar_eq
    (g : SmoothRiemannianMetric I N) (h : SmoothRiemannianMetric (𝓡 2) M)
    (Phi : (M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover N)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        h.inner y v w + a * c)
    (y : M) (s : ℝ) :
    metricScalarAt (I := I) g (UniversalCover.proj (Phi (y, s))) =
      metricScalarAt (I := 𝓡 2) h y := by
  let gP := Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Phi
  have hP (z : M) (r : ℝ) (v w : TangentSpace (𝓡 2) z) (a c : ℝ) :
      gP.inner (z, r) (v, a) (w, c) = h.inner z v w + a * c :=
    (Diffeomorph.pullbackMetricCross_inner
      (UniversalCover.liftedMetric (I := I) g) Phi (z, r) (v, a) (w, c)).trans
        (hproduct z r v w a c)
  have hp := metricScalarAt_product_real_of_inner_eq h gP hP y s
  have hc := metricScalar_cross (UniversalCover.liftedMetric (I := I) g) Phi (y, s)
  have hl := metricScalarAt_lifted_native g (Phi (y, s))
  exact (hc.trans hl).symm.trans hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_product_scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_product_scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_product_scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_product_scalar_eq


theorem bddAbove_scalar_iff_of_universalCover_product
    [ConnectedSpace N]
    (g : SmoothRiemannianMetric I N) (h : SmoothRiemannianMetric (𝓡 2) M)
    (Phi : (M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover N)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        h.inner y v w + a * c) :
    BddAbove (Set.range (metricScalarAt (I := I) g)) ↔
      BddAbove (Set.range (metricScalarAt (I := 𝓡 2) h)) := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro r ⟨y, rfl⟩
    rw [← universalCover_product_scalar_eq g h Phi hproduct y 0]
    exact hC (Set.mem_range_self _)
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro r ⟨x, rfl⟩
    let _ : PathConnectedSpace N := PathConnectedSpace.of_locallyPathConnectedSpace
    let x' : UniversalCover N :=
      ⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (_root_.Inhabited.default : N) x)⟩
    let q := Phi.symm x'
    have hproj : UniversalCover.proj (Phi (q.1, q.2)) = x := by
      change UniversalCover.proj (Phi (Phi.symm x')) = x
      rw [Phi.apply_symm_apply]
      rfl
    calc
      metricScalarAt (I := I) g x =
          metricScalarAt (I := I) g (UniversalCover.proj (Phi (q.1, q.2))) :=
        congrArg (metricScalarAt (I := I) g) hproj.symm
      _ = metricScalarAt (I := 𝓡 2) h q.1 :=
        universalCover_product_scalar_eq g h Phi hproduct q.1 q.2
      _ ≤ C := hC (Set.mem_range_self _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bddAbove_scalar_iff_of_universalCover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bddAbove_scalar_iff_of_universalCover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bddAbove_scalar_iff_of_universalCover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bddAbove_scalar_iff_of_universalCover_product

end SurfaceProduct

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
