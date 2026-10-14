import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonReflexive
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u

private instance gQuotSphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuotSphere4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuotSphere4 target :: scope.openDecls } }

theorem gQuot_metricScalarAt_eq_six_mul
    (Dq : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3)
    {c : ℝ}
    (hsec : ∀ (x : Dq.Q) (X Y : TangentSpace (𝓡 3) x),
      metricRm04StandardAt (I := 𝓡 3) Dq.gQuot x X Y Y X =
        c * (Dq.gQuot.inner x X X * Dq.gQuot.inner x Y Y
          - Dq.gQuot.inner x X Y * Dq.gQuot.inner x X Y))
    (x : Dq.Q) : metricScalarAt (I := 𝓡 3) Dq.gQuot x = 6 * c := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have hb := exists_orthonormal_basis (I := 𝓡 3) Dq.gQuot x
  rw [hdim] at hb
  obtain ⟨bas, hbas⟩ := hb
  have hentry : ∀ i j : Fin 3,
      metricRm04StandardAt (I := 𝓡 3) Dq.gQuot x (bas j) (bas i) (bas i) (bas j) =
        c * ((if j = j then (1 : ℝ) else 0) * (if i = i then (1 : ℝ) else 0) -
          (if j = i then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0)) := by
    intro i j
    rw [hsec, hbas, hbas, hbas]
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal Dq.gQuot bas hbas]
  change (∑ i : Fin 3, ∑ j : Fin 3,
    metricRm04StandardAt (I := 𝓡 3) Dq.gQuot x (bas j) (bas i) (bas i) (bas j)) = 6 * c
  simp only [hentry, Fin.sum_univ_three]
  norm_num [(by decide : ¬((0 : Fin 3) = 1)), (by decide : ¬((0 : Fin 3) = 2)),
    (by decide : ¬((1 : Fin 3) = 0)), (by decide : ¬((1 : Fin 3) = 2)),
    (by decide : ¬((2 : Fin 3) = 0)), (by decide : ¬((2 : Fin 3) = 1))]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuot_metricScalarAt_eq_six_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuot_metricScalarAt_eq_six_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuot_metricScalarAt_eq_six_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuot_metricScalarAt_eq_six_mul

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

local instance roundClassC1 : IsManifold I3 1 F.M :=
  IsManifold.of_le (I := I3) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundClassC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundClassC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundClassC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundClassC1

private theorem connectedSpace_of_shrinkingSphericalSpaceFormFlow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) F) : ConnectedSpace F.M := by
  obtain ⟨_T, _hT, Dq, e, _hmetric⟩ := hround
  have hsurj : Function.Surjective Dq.proj := fun y =>
    ⟨_, (Dq.sectionAt y).proj_localSection ⟨y, (Dq.sectionAt y).mem_baseNeighborhood⟩⟩
  have hsphere : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
    refine isConnected_iff_connectedSpace.mp ?_
    refine isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 (r := 1) (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := hsphere
  let _ : ConnectedSpace Dq.Q := hsurj.connectedSpace Dq.proj_smooth.continuous
  exact e.symm.surjective.connectedSpace e.symm.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.connectedSpace_of_shrinkingSphericalSpaceFormFlow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.connectedSpace_of_shrinkingSphericalSpaceFormFlow target :: scope.openDecls } }

theorem roundComponent_of_shrinkingSphericalSpaceFormFlow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) {eps : ℝ} (heps : 0 < eps) :
    Nonempty (RoundComponent (M := F.M) F.S eps x t Set.univ) := by
  obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
  have ha : 0 < 4 * (T - t) := by
    have : 0 < T - t := by linarith
    linarith
  have hsurj : Function.Surjective Dq.proj := fun y =>
    ⟨_, (Dq.sectionAt y).proj_localSection ⟨y, (Dq.sectionAt y).mem_baseNeighborhood⟩⟩
  have hsphere : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
    refine isConnected_iff_connectedSpace.mp ?_
    refine isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 (r := 1) (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := hsphere
  let _ : CompactSpace Dq.Q := hsurj.compactSpace Dq.proj_smooth.continuous
  let _ : ConnectedSpace Dq.Q := hsurj.connectedSpace Dq.proj_smooth.continuous
  let _ : CompactSpace F.M := e.symm.surjective.compactSpace e.symm.continuous
  let _ : ConnectedSpace F.M := e.symm.surjective.connectedSpace e.symm.continuous
  let c : ℝ := Classical.choose Dq.gQuot_constPosSec
  have hcspec := Classical.choose_spec Dq.gQuot_constPosSec
  have hc : 0 < c := hcspec.1
  have hsec : ∀ (y : Dq.Q) (X Y : TangentSpace (𝓡 3) y),
      metricRm04StandardAt (I := 𝓡 3) Dq.gQuot y X Y Y X =
        c * (Dq.gQuot.inner y X X * Dq.gQuot.inner y Y Y
          - Dq.gQuot.inner y X Y * Dq.gQuot.inner y X Y) := hcspec.2
  have hscalar : ∀ y : Dq.Q, metricScalarAt (I := 𝓡 3) Dq.gQuot y = 6 * c :=
    fun y => gQuot_metricScalarAt_eq_six_mul Dq hsec y
  have hm : F.S.base.metric t =
      scaleMetric (I := I3) (4 * (T - t)) ha (Diffeomorph.pullbackMetricCross Dq.gQuot e) :=
    hmetric t ht
  have hscalar_t : ∀ y : F.M,
      metricScalarAt (I := I3) (F.S.base.metric t) y = (4 * (T - t))⁻¹ * (6 * c) := by
    intro y
    rw [hm,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric,
      metricScalar_cross (I := I3) (J := 𝓡 3) Dq.gQuot e y, hscalar (e y)]
  have hscalarBase : ∀ y : F.M, F.S.scalar t y = (4 * (T - t))⁻¹ * (6 * c) := hscalar_t
  have hQ : 0 < F.S.scalar t x := by
    rw [hscalarBase x]
    positivity
  have hQa : F.S.scalar t x * (4 * (T - t)) = 6 * c := by
    rw [hscalarBase x, mul_right_comm ((4 * (T - t))⁻¹) (6 * c) (4 * (T - t)),
      inv_mul_cancel₀ (by positivity : (4 * (T - t)) ≠ 0), one_mul]
  refine ⟨{
    Z := F.M
    topology := F.topology
    charted := F.charted
    smooth := F.smooth
    t2 := F.t2
    compact := inferInstance
    connected := inferInstance
    metric := scaleMetric (I := I3) (F.S.scalar t x) hQ (F.S.base.metric t)
    p := x
    scalar_one := ?scalar_one
    constant_curvature := ?constant_curvature
    map := PartialDiffeomorph.refl (I := I3) F.M
    source_eq := rfl
    target_eq := rfl
    center_eq := rfl
    Q_pos := hQ
    comparison := metricComparisonOnRefl
      (fun _ => scaleMetric (I := I3) (F.S.scalar t x) hQ (F.S.base.metric t))
      Set.univ {0} (⌈eps⁻¹⌉₊) heps
    metric_bounds := ?metric_bounds }⟩
  case scalar_one =>
    intro z
    rw [DifferentialGeometry.Geometry.Curvature.metricScalarAt_scaleMetric, hscalar_t z]
    have hne : (4 * (T - t)) ≠ 0 := by positivity
    have hval : (4 * (T - t))⁻¹ * (6 * c) = F.S.scalar t x := by
      rw [← hQa, mul_comm (F.S.scalar t x) (4 * (T - t)), ← mul_assoc,
        inv_mul_cancel₀ hne, one_mul]
    rw [hval, inv_mul_cancel₀ hQ.ne']
  case constant_curvature =>
    intro z v w
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    have hS : metricRm04StandardAt (I := I3) (M := F.M) (F.S.base.metric t) z v w w v =
        (4 * (T - t)) * (c *
          ((Diffeomorph.pullbackMetricCross Dq.gQuot e).inner z v v *
              (Diffeomorph.pullbackMetricCross Dq.gQuot e).inner z w w -
            (Diffeomorph.pullbackMetricCross Dq.gQuot e).inner z v w *
              (Diffeomorph.pullbackMetricCross Dq.gQuot e).inner z v w)) := by
      rw [hm, metricRmStandard_scale (I := I3) (4 * (T - t)) ha
          (Diffeomorph.pullbackMetricCross Dq.gQuot e) z v w w v,
        metricRm04Standard_pullbackCross (I := I3) (J := 𝓡 3) Dq.gQuot e z v w w v,
        hsec (e z) (mfderiv I3 (𝓡 3) (e : F.M → Dq.Q) z v)
          (mfderiv I3 (𝓡 3) (e : F.M → Dq.Q) z w),
        ← Diffeomorph.pullbackMetricCross_inner (I := I3) (J := 𝓡 3) Dq.gQuot e z v v,
        ← Diffeomorph.pullbackMetricCross_inner (I := I3) (J := 𝓡 3) Dq.gQuot e z w w,
        ← Diffeomorph.pullbackMetricCross_inner (I := I3) (J := 𝓡 3) Dq.gQuot e z v w]
    rw [hvec, ← metricRm04StandardAt_apply,
      metricRmStandard_scale (I := I3) (F.S.scalar t x) hQ (F.S.base.metric t) z v w w v, hS]
    simp only [scaleMetric_inner]
    rw [hm]
    simp only [scaleMetric_inner]
    have hcEq : c = F.S.scalar t x * (4 * (T - t)) / 6 := by
      rw [hQa]; ring
    rw [hcEq]
    field_simp
  case metric_bounds =>
    intro z v
    have hmap : ((↑(PartialDiffeomorph.refl (I := I3) F.M).toPartialEquiv) : F.M → F.M) = id := by
      funext y
      rfl
    have hQSm : (scaleMetric (I := I3) (F.S.scalar t x) hQ (F.S.base.metric t)).inner z v v =
        F.S.scalar t x * (F.S.base.metric t).inner z v v :=
      scaleMetric_inner (I := I3) (F.S.scalar t x) hQ (F.S.base.metric t) z v v
    have hnn : 0 ≤ (F.S.base.metric t).inner z v v :=
      inner_self_nonneg (F.S.base.metric t) z v
    have hnonneg : 0 ≤ F.S.scalar t x * (F.S.base.metric t).inner z v v := mul_nonneg hQ.le hnn
    rw [hmap]
    simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq]
    rw [hQSm]
    constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundComponent_of_shrinkingSphericalSpaceFormFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundComponent_of_shrinkingSphericalSpaceFormFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundComponent_of_shrinkingSphericalSpaceFormFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.roundComponent_of_shrinkingSphericalSpaceFormFlow

theorem canonicalAlternative_round_of_shrinkingSphericalSpaceFormFlow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) {eps C : ℝ} (heps : 0 < eps) :
    Nonempty (CanonicalAlternative (M := F.M) F.S eps C x t Set.univ) := by
  have hconn : ConnectedSpace F.M := connectedSpace_of_shrinkingSphericalSpaceFormFlow F hround
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨R⟩ := roundComponent_of_shrinkingSphericalSpaceFormFlow F hround ht x heps
  exact ⟨CanonicalAlternative.round (by simp) R⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.canonicalAlternative_round_of_shrinkingSphericalSpaceFormFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.canonicalAlternative_round_of_shrinkingSphericalSpaceFormFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.canonicalAlternative_round_of_shrinkingSphericalSpaceFormFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.canonicalAlternative_round_of_shrinkingSphericalSpaceFormFlow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
