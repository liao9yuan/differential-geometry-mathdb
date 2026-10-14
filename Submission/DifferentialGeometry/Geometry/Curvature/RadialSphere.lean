import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.NormedSphere
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Curvature

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.E3 target :: scope.openDecls } }
private abbrev Sphere2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.Sphere2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.Sphere2 target :: scope.openDecls } }
private abbrev I2 := 𝓡 2
private abbrev I3 := 𝓡 3
private abbrev IC := I2.prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.IC target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

private theorem isSmoothEmbedding_cylinder_slice
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    {level : ℝ} (hsource : ∀ q : Sphere2, (q, level) ∈ F.source) :
    IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere2 => F (q, level)) := by
  have hc : ContMDiff I2 I3 ∞ (fun q : Sphere2 => F (q, level)) :=
    contMDiffOn_univ.mp (F.contMDiffOn_toFun.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun q _ => hsource q))
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by decide) hc ?_,
    hc.continuous.isClosedEmbedding (fun q z h =>
      congrArg Prod.fst (F.toPartialEquiv.injOn (hsource q) (hsource z) h)) |>.isEmbedding⟩
  intro q
  have hmd : F.toOpenPartialHomeomorph.MDifferentiable IC I3 :=
    ⟨F.contMDiffOn_toFun.mdifferentiableOn (by decide),
      F.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  change Function.Injective (mfderiv I2 I3 (F ∘ fun z : Sphere2 => (z, level)) q)
  have hinc : ContMDiff I2 IC ∞ (fun z : Sphere2 => (z, level)) :=
    contMDiff_id.prodMk contMDiff_const
  rw [mfderiv_comp q (F.mdifferentiableAt (by decide) (hsource q))
    (hinc.mdifferentiableAt (by decide)), mfderiv_prod_left]
  exact (hmd.mfderiv_injective (hsource q)).comp (fun _ _ h => congrArg Prod.fst h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_cylinder_slice
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_cylinder_slice target :: scope.openDecls } }

theorem tangent_sectional_lower_bound_of_cylinder_chart
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    (U : TopologicalSpace.Opens (Sphere2 × ℝ)) (hU : (U : Set (Sphere2 × ℝ)) ⊆ F.source)
    (hslice : ∀ z : Sphere2, (z, 0) ∈ U)
    (G : SmoothRiemannianMetric IC (Sphere2 × ℝ)) (h : SmoothRiemannianMetric I3 E3)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace IC x,
      G.inner x.val v w = h.inner (F x.val) (mfderiv IC I3 F x.val v)
        (mfderiv IC I3 F x.val w))
    {c : ℝ} (hsec : ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (G.inner (z, 0) (u, 0) (u, 0) * G.inner (z, 0) (v, 0) (v, 0) -
        G.inner (z, 0) (u, 0) (v, 0) ^ 2) ≤
      metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0)) :
    ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u) *
        h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v) -
        h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v) ^ 2) ≤
      metricRm04StandardAt h (F (z, 0))
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u) := by
  intro z u v
  have hd (w : TangentSpace I2 z) :
      mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z w =
        mfderiv IC I3 F (z, 0) (w, 0) := by
    change mfderiv I2 I3 (F ∘ fun q : Sphere2 => (q, 0)) z w = _
    have hi : ContMDiff I2 IC ∞ (fun q : Sphere2 => (q, (0 : ℝ))) :=
      contMDiff_id.prodMk contMDiff_const
    rw [mfderiv_comp z (F.mdifferentiableAt (by decide) (hU (hslice z)))
      (hi.mdifferentiableAt (by decide)), mfderiv_prod_left]
    rfl
  simp only [hd]
  have ht := hsec z u v
  have hg (a b : TangentSpace IC (z, (0 : ℝ))) :
      G.inner (z, 0) a b = h.inner (F (z, 0))
        (mfderiv IC I3 F (z, 0) a) (mfderiv IC I3 F (z, 0) b) :=
    hmetric ⟨(z, 0), hslice z⟩ a b
  have hr : metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0) =
      metricRm04StandardAt h (F (z, 0)) (mfderiv IC I3 F (z, 0) (u, 0))
        (mfderiv IC I3 F (z, 0) (v, 0)) (mfderiv IC I3 F (z, 0) (v, 0))
        (mfderiv IC I3 F (z, 0) (u, 0)) :=
    metricRm04StandardAt_eq_of_partialDiffeomorph_restriction F U hU G h hmetric
      ⟨(z, 0), hslice z⟩ (u, 0) (v, 0) (v, 0) (u, 0)
  rwa [hg (u, 0) (u, 0), hg (v, 0) (v, 0), hg (u, 0) (v, 0), hr] at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tangent_sectional_lower_bound_of_cylinder_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tangent_sectional_lower_bound_of_cylinder_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tangent_sectional_lower_bound_of_cylinder_chart ``Submission.DifferentialGeometry.Geometry.Curvature.tangent_sectional_lower_bound_of_cylinder_chart

theorem isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    (U : TopologicalSpace.Opens (Sphere2 × ℝ)) (hU : (U : Set (Sphere2 × ℝ)) ⊆ F.source)
    (hslice : ∀ z : Sphere2, (z, 0) ∈ U)
    (G : SmoothRiemannianMetric IC (Sphere2 × ℝ)) (h : SmoothRiemannianMetric I3 E3)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace IC x,
      G.inner x.val v w = h.inner (F x.val) (mfderiv IC I3 F x.val v)
        (mfderiv IC I3 F x.val w))
    {c : ℝ} (hsec : ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (G.inner (z, 0) (u, 0) (u, 0) * G.inner (z, 0) (v, 0) (v, 0) -
        G.inner (z, 0) (u, 0) (v, 0) ^ 2) ≤
      metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0))
    {r : ℝ} (hr : 0 < r) (O : E3 ≃ₗᵢ[ℝ] E3)
    (hradial : ∀ z : Sphere2, F (z, 0) = r • O z.val) :
    let f : Sphere2 → E3 := fun z => F (z, 0)
    _root_.Manifold.IsSmoothEmbedding I2 I3 ∞ f ∧
      frontier (Metric.closedBall (0 : E3) r) = _root_.Set.range f ∧
      ∀ (z : Sphere2) (u v : TangentSpace I2 z),
        c * (h.inner (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z u) *
          h.inner (f z) (mfderiv I2 I3 f z v) (mfderiv I2 I3 f z v) -
          h.inner (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z v) ^ 2) ≤
        metricRm04StandardAt h (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z v)
          (mfderiv I2 I3 f z v) (mfderiv I2 I3 f z u) := by
  refine ⟨isSmoothEmbedding_cylinder_slice F (fun z => hU (hslice z)), ?_,
    tangent_sectional_lower_bound_of_cylinder_chart F U hU hslice G h hmetric hsec⟩
  rw [Metric.frontier_closedBall_eq_range_smul_linearIsometryEquiv O hr]
  congr 1
  exact funext (fun z => (hradial z).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart ``Submission.DifferentialGeometry.Geometry.Curvature.isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart

end DifferentialGeometry.Geometry.Curvature
