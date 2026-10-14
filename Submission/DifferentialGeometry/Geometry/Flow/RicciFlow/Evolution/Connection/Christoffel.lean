import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Pairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

def ChristoffelVariationEquationInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M), x ∈
    u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (rhs (t : Real) x i j k)
        D.carrier
        (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationEquationInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationEquationInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationEquationInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationEquationInFrameOn

def ChristoffelVariationMixedDerivativeInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOn (I := I) D.carrier u
      (fun s x =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn

def ChristoffelVariationMixedDerivativeInFrameOnRegular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall i j k : Idx,
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
      D.carrier D.regular u
      (fun s x =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (fun s x => rhs s x i j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOnRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOnRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOnRegular ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOnRegular

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ChristoffelVariationMixedDerivativeInFrameOn.toRegular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h :
      ChristoffelVariationMixedDerivativeInFrameOn
        (I := I) S frame hframe rhs) :
    ChristoffelVariationMixedDerivativeInFrameOnRegular
      (I := I) S frame hframe rhs := by
  intro i j k
  exact (h i j k).toRegular (I := I) (regularSet := D.regular)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn.toRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn.toRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn.toRegular ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelVariationMixedDerivativeInFrameOn.toRegular

def ChristoffelMetricVariationEquationInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ChristoffelVariationEquationInFrameOn (I := I) S frame hframe
    (christoffelVariationRHSFromMetricVariationInFrame (M := M) gInv metricCovDerivDt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelMetricVariationEquationInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelMetricVariationEquationInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelMetricVariationEquationInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelMetricVariationEquationInFrameOn

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelMetricVariation_hasDerivWithinAt
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h :
      ChristoffelMetricVariationEquationInFrameOn
        (I := I) S gInv frame hframe metricCovDerivDt)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M)
      (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (christoffelVariationRHSFromMetricVariationInFrame
        (M := M) gInv metricCovDerivDt (t : Real) x i j k)
      D.carrier
      (t : Real) :=
  h t x hx i j k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelMetricVariation_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelMetricVariation_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelMetricVariation_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelMetricVariation_hasDerivWithinAt

def ChristoffelEvolutionEquationInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M), x ∈
    u ->
    forall i j k : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection s) frame hframe x i j k)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
          (t : Real) x i j k)
        D.carrier
        (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem frameCoeff_eq_sum_inv_metricPairing
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x hx i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using (hinv t x hx i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          DifferentialGeometry.Geometry.Curvature.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.frameCoeff_eq_sum_inv_metricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.frameCoeff_eq_sum_inv_metricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.frameCoeff_eq_sum_inv_metricPairing ``Submission.DifferentialGeometry.PDE.RicciFlow.frameCoeff_eq_sum_inv_metricPairing

omit [SigmaCompactSpace M] [T2Space M] in
theorem frameCoeffLocal
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
    intro i j
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx i j).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx i j).2
  calc
    hframe.coeff k x V = (hframe.toBasisAt hx).repr V k := by
        simp [IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv t x k l * (S.family.metric t).inner x (frame l x) V := by
        simpa [IsLocalFrameOn.toBasisAt_coe] using
          DifferentialGeometry.Geometry.Curvature.basis_coord_eq_sum_inv_inner
            (I := I) (M := M) (S.family.metric t) (hframe.toBasisAt hx)
            (fun i j : Idx => gInv t x i j) hinvAt k V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.frameCoeffLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.frameCoeffLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.frameCoeffLocal ``Submission.DifferentialGeometry.PDE.RicciFlow.frameCoeffLocal

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelVariationEquationInFrameOn_of_pairing_local
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (loweredRHS : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hpair :
      forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
        x ∈ u ->
        forall i j l : Idx,
          HasDerivWithinAt
            (fun s : Real =>
              (S.family.metric (t : Real)).inner x (frame l x)
                ((S.family.connection s (frame j) x) (frame i x)))
            (loweredRHS (t : Real) x i j l)
            D.carrier
            (t : Real)) :
    ChristoffelVariationEquationInFrameOn
      (I := I) S frame hframe
      (christoffelVariationRHSFromLoweredInFrame (M := M) gInv loweredRHS) := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx, gInv (t : Real) x k l *
          loweredRHS (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l * loweredRHS (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x hx i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelVariationEquationInFrameOn_of_pairing_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelVariationEquationInFrameOn_of_pairing_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelVariationEquationInFrameOn_of_pairing_local ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelVariationEquationInFrameOn_of_pairing_local

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelSymbol_sub_eq_sum_inv_connectionDiff
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (base var : Real) {x : M} (hx : x ∈ u)
    (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k =
      ∑ l : Idx, gInv var x k l *
        connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
  let Vvar : TangentSpace I x :=
    (S.family.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (S.family.connection base (frame j) x) (frame i x)
  have hvar :=
    frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv var hx k Vvar
  have hbase :=
    frameCoeff_eq_sum_inv_metricPairing
      (I := I) S gInv frame hframe hinv var hx k Vbase
  calc
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k
        = (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vvar) -
          (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vbase) := by
            change hframe.coeff k x Vvar - hframe.coeff k x Vbase =
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vvar) -
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vbase)
            rw [hvar, hbase]
    _ = ∑ l : Idx, gInv var x k l *
          ((S.family.metric var).inner x (frame l x) Vvar -
            (S.family.metric var).inner x (frame l x) Vbase) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun l _hl => ?_
            ring
    _ = ∑ l : Idx, gInv var x k l *
          (S.family.metric var).inner x (frame l x) (Vvar - Vbase) := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            rw [map_sub]
    _ = ∑ l : Idx, gInv var x k l *
          connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            unfold connectionDiffLoweredInFrame connectionDiffVectorInFrame Vvar Vbase
            rw [(S.family.metric var).symm x (frame l x)
              ((S.family.connection var (frame j) x) (frame i x) -
                (S.family.connection base (frame j) x) (frame i x))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelSymbol_sub_eq_sum_inv_connectionDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelSymbol_sub_eq_sum_inv_connectionDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelSymbol_sub_eq_sum_inv_connectionDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelSymbol_sub_eq_sum_inv_connectionDiff

omit [SigmaCompactSpace M] [T2Space M] in
theorem gammaSubLocal
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (base var : Real) {x : M} (hx : x ∈ u)
    (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k =
      ∑ l : Idx, gInv var x k l *
        connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
  let Vvar : TangentSpace I x :=
    (S.family.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (S.family.connection base (frame j) x) (frame i x)
  have hvar :=
    frameCoeffLocal
      (I := I) S gInv frame hframe hinv var hx k Vvar
  have hbase :=
    frameCoeffLocal
      (I := I) S gInv frame hframe hinv var hx k Vbase
  calc
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection var) frame hframe x i j k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection base) frame hframe x i j k
        = (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vvar) -
          (∑ l : Idx, gInv var x k l *
            (S.family.metric var).inner x (frame l x) Vbase) := by
            change hframe.coeff k x Vvar - hframe.coeff k x Vbase =
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vvar) -
              (∑ l : Idx, gInv var x k l *
                (S.family.metric var).inner x (frame l x) Vbase)
            rw [hvar, hbase]
    _ = ∑ l : Idx, gInv var x k l *
          ((S.family.metric var).inner x (frame l x) Vvar -
            (S.family.metric var).inner x (frame l x) Vbase) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun l _hl => ?_
            ring
    _ = ∑ l : Idx, gInv var x k l *
          (S.family.metric var).inner x (frame l x) (Vvar - Vbase) := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            rw [map_sub]
    _ = ∑ l : Idx, gInv var x k l *
          connectionDiffLoweredInFrame (I := I) S frame var base var x i j l := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            unfold connectionDiffLoweredInFrame connectionDiffVectorInFrame Vvar Vbase
            rw [(S.family.metric var).symm x (frame l x)
              ((S.family.connection var (frame j) x) (frame i x) -
                (S.family.connection base (frame j) x) (frame i x))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.gammaSubLocal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.gammaSubLocal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.gammaSubLocal ``Submission.DifferentialGeometry.PDE.RicciFlow.gammaSubLocal

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelEvolutionEquationInFrameOn_of_pairing
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hpair : ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx,
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelEvolutionEquationInFrameOn_of_pairing_local
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hpair : ConnectionVariationPairingEquationInFrameOnLocal
      (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic := by
  intro t x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (S.family.metric (t : Real)).inner x (frame l x)
        ((S.family.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ l : Idx, gInv (t : Real) x k l * pair l s)
        (∑ l : Idx,
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa [pair, Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv (t : Real) x k l * pair l s)
        (A' := fun l =>
          gInv (t : Real) x k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        (s := D.carrier) (x := (t : Real))
        (fun l _hl =>
          by
            exact HasDerivWithinAt.const_mul
              (gInv (t : Real) x k l) (hpair t x hx i j l)))
  refine hsum.congr ?_ ?_
  · intro s _hs
    symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection s (frame j) x) (frame i x))).symm
  · symm
    exact (frameCoeffLocal
      (I := I) S gInv frame hframe hinv (t : Real) hx k
      ((S.family.connection (t : Real) (frame j) x) (frame i x))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing_local ``Submission.DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionEquationInFrameOn_of_pairing_local

end Components

end DifferentialGeometry.PDE.RicciFlow
