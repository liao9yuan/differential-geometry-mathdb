import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureRicciContraction
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Contractions
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Sections
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Identities
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.Higher
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem levi_civita_contracted_bianchi_field
    (g : SmoothRiemannianMetric I M) :
    let cov := metricCov (I := I) (M := M) g
    let hcov := metricCov_smooth (I := I) (M := M) g
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let scalar : M -> Real := fun x => metricTracePair0SAt (I := I) g (Ric x)
    let hscalar := trace02_smooth (I := I) g Ric
    metricTraceFirstTwoField (I := I) (M := M) g nablaRic =
      (1 / 2 : Real) • duSec (I := I) scalar hscalar := by
  classical
  dsimp only
  apply DFunLike.ext _ _
  intro x
  obtain ⟨basis, horth⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  let delta := identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))
  have hinv : MetricInverseInBasis (I := I) g x basis delta :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let scalar : M -> Real := fun y => metricTracePair0SAt (I := I) g (Ric y)
  let nablaRicAt := totalNabla0SFun (I := I) 2 cov Ric x
  let dScalar := differential1FormFun (I := I) scalar x
  obtain ⟨nablaRm04, hsecond, hRmSymm, hRicTrace, hScalar⟩ :=
    exists_levi_civita_bianchi_trace_identities (I := I) (M := M) g basis delta hinv
  have hInv : forall i j, delta i j = delta j i := by
    intro i j
    simp [delta, identityInvMetric, diagonalInvMetric, eq_comm]
  have hcontract :
      ContractedBianchiOfSecondAt (I := I) basis delta nablaRm04 nablaRicAt dScalar :=
    contractOfSecond (I := I) basis delta nablaRm04 nablaRicAt dScalar
      hRmSymm hRicTrace hScalar hInv
  have hbianchi : ContractedBianchiAt (I := I) basis delta nablaRicAt dScalar :=
    contracted_bianchi_of_second (I := I) basis delta nablaRm04 nablaRicAt dScalar
      hcontract hsecond
  rw [metricTraceFirstTwoField_apply, totalNabla0S_apply]
  apply ext0S_basis (I := I) basis
  intro idx
  simp only [component0S_apply]
  rw [metricTraceFirstTwo0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis delta hinv]
  unfold metricTrace0S2InBasis
  have hslot : (fun _ : Fin 1 => basis (idx 0)) = (fun a : Fin 1 => basis (idx a)) := by
    funext q
    fin_cases q
    rfl
  have hinput (i j) :
      metricTraceInput (I := I) (basis i) (basis j) (fun a : Fin 1 => basis (idx a)) =
        vec3 (I := I) (basis i) (basis j) (basis (idx 0)) := by
    funext q
    fin_cases q <;> rfl
  simp_rw [hinput]
  have hb := hbianchi (basis (idx 0))
  simpa [cov, Ric, scalar, nablaRicAt, dScalar, Tensor0SSpace.smul_apply,
    metricTraceInput_apply, hslot] using hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.levi_civita_contracted_bianchi_field
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.levi_civita_contracted_bianchi_field target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem levi_civita_nabla_contracted_bianchi
    (g : SmoothRiemannianMetric I M) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (X Y : TangentSpace I x) :
    let cov := metricCov (I := I) (M := M) g
    let hcov := metricCov_smooth (I := I) (M := M) g
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
    let nabla2Ric := totalNabla0SFun (I := I) 3 cov nablaRic x
    let scalar : M -> Real := fun y => metricTracePair0SAt (I := I) g (Ric y)
    let hscalar := trace02_smooth (I := I) g Ric
    let HessScalar := hessianSec (I := I) cov hcov scalar hscalar
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nabla2Ric (vec4 (I := I) X (basis i) (basis j) Y)) =
      (1 / 2 : Real) * HessScalar x (vec2 (I := I) X Y) := by
  classical
  dsimp only
  let cov := metricCov (I := I) (M := M) g
  let hcov := metricCov_smooth (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
  let scalar : M -> Real := fun y => metricTracePair0SAt (I := I) g (Ric y)
  let hscalar := trace02_smooth (I := I) g Ric
  let tail : Fin 1 -> TangentSpace I x := fun _ => Y
  have hmc : IsMetricCompatible (I := I) cov g := by
    simpa [cov, metricCov] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have htrace := nabla_metricTraceFirstTwo0S (I := I) (M := M) cov g hmc nablaRic
    basis gInv hinv X tail
  have hfield := levi_civita_contracted_bianchi_field (I := I) (M := M) g
  have hinput (i j) :
      Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail) =
        vec4 (I := I) X (basis i) (basis j) Y := by
    funext q
    fin_cases q <;> rfl
  have htail : Fin.cons X tail = vec2 (I := I) X Y := by
    funext q
    fin_cases q <;> rfl
  simp_rw [hinput] at htrace
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * totalNabla0SFun (I := I) 3 cov nablaRic x
          (vec4 (I := I) X (basis i) (basis j) Y)) =
      totalNabla0SFun (I := I) 1 cov
        (metricTraceFirstTwoField (I := I) (M := M) g nablaRic) x
        (Fin.cons X tail) := htrace.symm
    _ = totalNabla0SFun (I := I) 1 cov
        ((1 / 2 : Real) • duSec (I := I) scalar hscalar) x
        (Fin.cons X tail) := by rw [hfield]
    _ = (1 / 2 : Real) *
        hessianSec (I := I) cov hcov scalar hscalar x (vec2 (I := I) X Y) := by
      rw [totalNabla0SFun_smul]
      rw [htail]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.levi_civita_nabla_contracted_bianchi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.levi_civita_nabla_contracted_bianchi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.levi_civita_nabla_contracted_bianchi ``Submission.DifferentialGeometry.Geometry.Connection.levi_civita_nabla_contracted_bianchi

end DifferentialGeometry.Geometry.Connection
