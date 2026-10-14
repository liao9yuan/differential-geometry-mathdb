import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalProductSplitting
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRankTrichotomy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.IntrinsicLineNullPlane
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

universe uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem rm04_eq_zero_of_image_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt g x
      (metricAlgebraicCurvatureTensorAt g x)) = 0) : metricRm04At g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply DimensionThree.metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero g x hdim
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
  have hrange := Submodule.finrank_eq_zero.mp hzero
  rw [curvatureOperatorImageAt_eq_range] at hrange
  refine ContinuousLinearMap.ext fun v => ?_
  have hmem : curvatureOperatorEndomorphismAt g x (metricAlgebraicCurvatureTensorAt g x) v ∈
      (curvatureOperatorEndomorphismAt g x (metricAlgebraicCurvatureTensorAt g x)).range :=
    ⟨v, rfl⟩
  rw [hrange] at hmem
  exact hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04_eq_zero_of_image_finrank_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rm04_eq_zero_of_image_finrank_eq_zero target :: scope.openDecls } }

theorem curvatureOperatorImageAt_finrank_eq_one_of_line [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ} (hab : a < b)
    (hcar : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hnonflat : ∃ x : M, metricRm04At (S.base.metric b) x ≠ 0)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf (S.base.metric b) (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hb : b ∈ _root_.Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hsec (p : M) : metricRm04At (S.base.metric b) p ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) :=
    (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff _ p).mpr fun v w =>
      mem_algebraicSectionalNonnegativeCone.mp
        (algebraicCurvatureOperatorNonnegativeCone_le_sectionalNonnegativeCone (hR b hb p)) v w
  obtain ⟨v, w, hplane, hnull⟩ :=
    Perelman.KappaSolutions.exists_null_plane_of_nonnegative_sectional_intrinsic_line
      (S.base.metric b) hcomplete (by omega) hsec hline x
  rcases curvatureOperatorImageAt_finrank_trichotomy_at_right_endpoint S hS hdim hab hcar hreg hR
    with hzero | hone | hthree
  · obtain ⟨y, hy⟩ := hnonflat
    exact (hy (rm04_eq_zero_of_image_finrank_eq_zero _ y hdim (hzero y))).elim
  · exact hone x
  · have hp := DimensionThree.leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
      (S.base.metric b) x hdim (metricAlgebraicCurvatureTensorAt (S.base.metric b) x)
      (hR b hb x) (hthree x)
    have hpos := (Perelman.KappaSolutions.curvatureOperatorPositiveAt_iff_sectional
      (S.base.metric b) x hdim).mp
      (Perelman.KappaSolutions.curvatureOperatorPositiveAt_of_leastCurvatureOperatorEigenvalueAt_pos
        (S.base.metric b) x hdim hp) v w hplane
    rw [hnull] at hpos
    exact (lt_irrefl 0 hpos).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_line ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureOperatorImageAt_finrank_eq_one_of_line

theorem exists_surface_product_on_closed_interval_of_line [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ} (hab : a < b)
    (hcar : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hnonflat : ∃ x : M, metricRm04At (S.base.metric b) x ≠ 0)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf (S.base.metric b) (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N),
      let _ := hcs
      ∃ hmanifold : IsManifold (𝓡 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hSigma : SigmaCompactSpace N,
            let _ := hSigma
            ∃ (h : ℝ → SmoothRiemannianMetric (𝓡 2) N)
              (Phi : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), I⟯ M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ _root_.Set.Icc a b, Diffeomorph.pullbackMetricCross (S.base.metric t) Phi =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (h t)) ∧
              ∀ t ∈ _root_.Set.Ioc a b, ∀ y : N, 0 < metricScalarAt (h t) y := by
  exact exists_surface_product_on_closed_interval_of_terminal_rank_one S hS hdim hab hcar hreg hR
    hcomplete hbound (gamma 0)
    (curvatureOperatorImageAt_finrank_eq_one_of_line S hS hdim hab hcar hreg hR hcomplete
      hnonflat hline (gamma 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_surface_product_on_closed_interval_of_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_surface_product_on_closed_interval_of_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_surface_product_on_closed_interval_of_line ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_surface_product_on_closed_interval_of_line

section UniversalCover

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology

variable [ConnectedSpace M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  [Inhabited M]

theorem exists_universalCover_surface_product_on_closed_interval_of_line
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ} (hab : a < b)
    (hcar : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hnonflat : ∃ x : M, metricRm04At (S.base.metric b) x ≠ 0)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf (S.base.metric b) (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N),
      let _ := hcs
      ∃ hmanifold : IsManifold (𝓡 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hSigma : SigmaCompactSpace N,
            let _ := hSigma
            ∃ (h : ℝ → SmoothRiemannianMetric (𝓡 2) N)
              (Phi : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), I⟯ UniversalCover M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ _root_.Set.Icc a b,
                Diffeomorph.pullbackMetricCross (S.universalCover.base.metric t) Phi =
                  (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (h t)) ∧
              ∀ t ∈ _root_.Set.Ioc a b, ∀ y : N, 0 < metricScalarAt (h t) y := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let U := S.universalCover
  have hU : IsSolutionOn U := hS.universalCover S
  have hRU (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : UniversalCover M) :
      metricAlgebraicCurvatureTensorAt (U.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := UniversalCover M) :=
    (UniversalCover.metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
      (S.base.metric t) x).mpr (hR t ht (UniversalCover.proj x))
  have hboundU : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc a b, ∀ x : UniversalCover M,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ K := by
    obtain ⟨K, hK, hk⟩ := hbound
    refine ⟨K, hK, fun t ht x => ?_⟩
    change normSq0S (UniversalCover.liftedMetric (S.base.metric t)) x 4
      (metricRm04At (UniversalCover.liftedMetric (S.base.metric t)) x) ≤ K
    rw [UniversalCover.normSq0S_metricRm04At_liftedMetric]
    exact hk t ht (UniversalCover.proj x)
  let x₀ : UniversalCover M := ⟨default, ⟦Path.refl default⟧⟩
  have hrank := curvatureOperatorImageAt_finrank_eq_one_of_line S hS hdim hab hcar hreg hR
    hcomplete hnonflat hline (UniversalCover.proj x₀)
  have hrankU : Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric b) x₀
      (metricAlgebraicCurvatureTensorAt (U.family.metric b) x₀)) = 1 :=
    (UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric (S.base.metric b) x₀
      hdim).trans hrank
  exact exists_surface_product_on_closed_interval_of_terminal_rank_one U hU hdim hab hcar hreg
    hRU (S.universalCover_complete b hcomplete) hboundU x₀ hrankU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_universalCover_surface_product_on_closed_interval_of_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_universalCover_surface_product_on_closed_interval_of_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_universalCover_surface_product_on_closed_interval_of_line ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_universalCover_surface_product_on_closed_interval_of_line

end UniversalCover

end DifferentialGeometry.PDE.RicciFlow
