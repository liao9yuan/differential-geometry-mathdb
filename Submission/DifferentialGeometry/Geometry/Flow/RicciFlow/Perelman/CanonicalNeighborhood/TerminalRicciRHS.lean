import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciHessian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RicciTerminalDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local instance terminalRHSC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRHSC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRHSC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRHSC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalRHSC1

theorem solution_ricciPairRHS_continuousWithinAt_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) (v w : TangentSpace I x) :
    ContinuousWithinAt (fun t => ricciPairRHS S t x v w) (Set.Iio b) b := by
  classical
  let frame := coordinateFrameAt (I := I) x
  have hb : b ∈ D.carrier := hslab ⟨hab.le, le_rfl⟩
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  have hInv (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => coordInv S x t x i j) (Set.Iio b) b := by
    have hmap : ContinuousOn (fun t : ℝ => (t, x)) D.carrier :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc := (coordInvContOn S hS x i j).comp hmap
      (fun t ht => ⟨ht, coordinateFrameAt_mem (I := I) x⟩)
    simpa only [Function.comp_def] using (hc b hb).mono_of_mem_nhdsWithin hnear
  have hRic (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => ricciCompInFrame S frame t x i j) (Set.Iio b) b := by
    have hc : ContinuousOn (fun t => S.ricci t x (vec2 (frame i x) (frame j x))) D.carrier := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hS.ricciCont.eval_continuous (P := {t : ℝ // t ∈ D.carrier})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun t => t.2) continuous_const
        (v := fun k _ => vec2 (frame i x) (frame j x) k) (fun _ => continuous_const)
    exact (hc b hb).mono_of_mem_nhdsWithin hnear
  have hRm (i k j l : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => rm04Comp (S.base.rm04 t) frame x i k j l) (Set.Iio b) b := by
    have hc : ContinuousOn (fun t => S.base.rm04 t x
        (vec4 (frame i x) (frame k x) (frame j x) (frame l x))) D.carrier := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hS.rm04Cont.eval_continuous (P := {t : ℝ // t ∈ D.carrier})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun t => t.2) continuous_const
        (v := fun q _ => vec4 (frame i x) (frame k x) (frame j x) (frame l x) q)
        (fun _ => continuous_const)
    exact (hc b hb).mono_of_mem_nhdsWithin hnear
  have hN (c d i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => coordNab2Ric S x t x c d i j) (Set.Iio b) b := by
    simp only [coordNab2Ric_eq_metricNabla2Ric]
    exact solution_metricNabla2Ric_eval_continuousWithinAt_terminal S hS hab hslab hreg x _
  have hL (i j : CoordinateIdx (𝕜 := ℝ) E) : ContinuousWithinAt
      (fun t => coordRoughRic S x (coordNab2Ric S x) t x i j) (Set.Iio b) b := by
    exact tendsto_finsetSum Finset.univ fun c _ =>
      tendsto_finsetSum Finset.univ fun d _ => (hInv c d).mul (hN c d i j)
  have hRaised (i j : CoordinateIdx (𝕜 := ℝ) E) : ContinuousWithinAt
      (fun t => raisedRicciCompInFrame S (coordInv S x) frame t x i j) (Set.Iio b) b := by
    exact tendsto_finsetSum Finset.univ fun c _ =>
      tendsto_finsetSum Finset.univ fun d _ => ((hInv i c).mul (hInv j d)).mul (hRic c d)
  have hOne (i k : CoordinateIdx (𝕜 := ℝ) E) : ContinuousWithinAt
      (fun t => ricciOneUpCompInFrame S (coordInv S x) frame t x i k) (Set.Iio b) b := by
    exact tendsto_finsetSum Finset.univ fun c _ => (hInv k c).mul (hRic i c)
  have hR (i j : CoordinateIdx (𝕜 := ℝ) E) : ContinuousWithinAt
      (fun t => rmRicciContractionCompInFrame S S.base.rm04 (coordInv S x) frame t x i j)
      (Set.Iio b) b := by
    exact tendsto_finsetSum Finset.univ fun k _ =>
      tendsto_finsetSum Finset.univ fun l _ => (hRm i k j l).mul (hRaised k l)
  have hQ (i j : CoordinateIdx (𝕜 := ℝ) E) : ContinuousWithinAt
      (fun t => ricciQuadraticCompInFrame S (coordInv S x) frame t x i j) (Set.Iio b) b := by
    exact tendsto_finsetSum Finset.univ fun k _ => (hOne i k).mul (hRic k j)
  exact tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
    continuousWithinAt_const.mul
      (((hL i j).sub (continuousWithinAt_const.mul (hR i j))).sub
        (continuousWithinAt_const.mul (hQ i j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPairRHS_continuousWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPairRHS_continuousWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPairRHS_continuousWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPairRHS_continuousWithinAt_terminal

theorem solution_ricciPair_hasDerivWithinAt_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => S.ricci t x (vec2 v w))
      (ricciPairRHS S b x v w) (Set.Iic b) b :=
  ricciPair_hasDerivWithinAt_terminal_of_rhsContinuous S hS hab hslab hreg x v w
    (solution_ricciPairRHS_continuousWithinAt_terminal S hS hab hslab hreg x v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPair_hasDerivWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPair_hasDerivWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPair_hasDerivWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_ricciPair_hasDerivWithinAt_terminal

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
