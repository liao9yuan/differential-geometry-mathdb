import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticScalarRatio
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

section Solution

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance ascrNormalizationSolutionC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSolutionC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSolutionC1 target :: scope.openDecls } }

theorem curvatureNormalizedSolution_ascr
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (s : ℝ) (p : M) :
    asymptoticScalarCurvatureRatio (I := I) (M := M)
        ((curvatureNormalizedSolution S t0 Q hQ ht0).family.metric s) p =
      asymptoticScalarCurvatureRatio (S.family.metric (parabolicTime t0 Q s)) p := by
  change asymptoticScalarCurvatureRatio
    (scaleMetric Q hQ (S.base.metric (parabolicTime t0 Q s))) p =
      asymptoticScalarCurvatureRatio (S.base.metric (parabolicTime t0 Q s)) p
  exact asymptoticScalarCurvatureRatio_scaleMetric
    (S.base.metric (parabolicTime t0 Q s)) Q hQ p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedSolution_ascr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedSolution_ascr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedSolution_ascr ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedSolution_ascr

end Solution

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ascrNormalizationTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationTopology
local instance ascrNormalizationCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationCharted
local instance ascrNormalizationSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationSmooth
local instance ascrNormalizationC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ascrNormalizationC1

theorem curvatureNormalizedFlow_ascr
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (s : ℝ) (p : F.M) :
    @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
        ((curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0).S.family.metric s) p =
      asymptoticScalarCurvatureRatio (F.S.family.metric (parabolicTime t0 Q s)) p :=
  curvatureNormalizedSolution_ascr F.S t0 Q hQ ht0 s p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr

theorem curvatureNormalizedFlow_ascr_zero
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (x0 p : F.M) :
    @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
        ((curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0).S.family.metric 0) p =
      asymptoticScalarCurvatureRatio (F.S.family.metric t0) p := by
  rw [curvatureNormalizedFlow_ascr, parabolicTime_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvatureNormalizedFlow_ascr_zero

end Pointed

section Ancient

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] ascrNormalizationTopology ascrNormalizationCharted
  ascrNormalizationSmooth ascrNormalizationC1

theorem ancientKappa_exists_curvatureNormalization_ascr {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F)
    (t0 : ℝ) (ht0 : t0 ≤ 0) (x0 : F.M) :
    ∃ hQ : 0 < F.S.scalar t0 x0,
      let G := curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
        t0 (F.S.scalar t0 x0) hQ
        (by simpa only [hF.carrier_eq, Set.mem_Iic] using ht0) x0
      IsAncientKappaSolution (I := I) kappa G ∧
        PointedFlowScalarAtBase (I := I) G 1 ∧
        ∀ p : F.M,
          @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
            (G.S.family.metric 0) p =
          asymptoticScalarCurvatureRatio (F.S.family.metric t0) p := by
  have hQ : 0 < F.S.scalar t0 x0 := ancientKappa_scalar_pos F hF ht0 x0
  refine ⟨hQ, ?_⟩
  dsimp only
  refine ⟨isAncientKappaSolution_curvatureNormalizedFlow
      F hF t0 (F.S.scalar t0 x0) hQ _ x0 rfl,
    curvatureNormalizedFlow_scalar_base F hF.carrier_eq hF.regular_eq
      t0 (F.S.scalar t0 x0) hQ _ x0 rfl, ?_⟩
  intro p
  exact curvatureNormalizedFlow_ascr_zero F hF.carrier_eq hF.regular_eq
    t0 (F.S.scalar t0 x0) hQ _ x0 p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_exists_curvatureNormalization_ascr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_exists_curvatureNormalization_ascr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_exists_curvatureNormalization_ascr ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_exists_curvatureNormalization_ascr

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
