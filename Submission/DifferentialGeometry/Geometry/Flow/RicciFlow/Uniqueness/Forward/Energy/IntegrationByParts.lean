import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.Difference
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.Divergence
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section Lift

variable {s : ℕ}

def ccLift0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    SmoothCcTensor g 0 s where
  toSection := unitScalarRSLiftCₛ (I := I) (M := M) T
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccLift0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccLift0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccLift0S ``Submission.DifferentialGeometry.PDE.RicciFlow.ccLift0S

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ccLift0S_toSection (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    (ccLift0S (I := I) g T).toSection x =
      unitScalarRSLiftSection (I := I) (M := M) (fun y : M => T y) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccLift0S_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccLift0S_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccLift0S_toSection ``Submission.DifferentialGeometry.PDE.RicciFlow.ccLift0S_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem ccLift0S_unit (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (ccLift0S (I := I) g T).toSection x)
        (unitZeroSec (I := I) (M := M) x) = T x :=
  unitScalarRSLiftSection_apply_unit (I := I) (M := M) (fun y : M => T y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccLift0S_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccLift0S_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccLift0S_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.ccLift0S_unit

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ccLift0S_unitModel (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    unitModel (I := I) (M := M) g s (ccLift0S (I := I) g T) x =
      Tensor0SSpace.toModel (T x) := by
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (ccLift0S (I := I) g T).toSection x)
        (unitZeroSec (I := I) (M := M) x)) = Tensor0SSpace.toModel (T x)
  rw [ccLift0S_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ccLift0S_unitModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ccLift0S_unitModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ccLift0S_unitModel ``Submission.DifferentialGeometry.PDE.RicciFlow.ccLift0S_unitModel

end Lift

section Identification

variable {s : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivLift_unit (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => (ccLift0S (I := I) g T).toSection y) x v)
        (unitZeroSec (I := I) (M := M) x) slots =
      metricNabla0S (I := I) g T x (Fin.cons v slots) := by
  classical
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  subst hX
  have hsec : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[Real] Tensor0SSpace s I y from
        (ccLift0S (I := I) g T).toSection y) (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => T y) := by
    funext y
    exact ccLift0S_unit (I := I) g T y
  have key :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => (ccLift0S (I := I) g T).toSection y) x (X x))
        (unitZeroSec (I := I) (M := M) x) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
        (LeviCivita (I := I) g) X T x := by
    rw [covDeriv_unit_eval_eq (I := I) (M := M) g s
      (ccLift0S (I := I) g T).toSection x (X x)]
    rw [hsec]
    exact (nabla0SFun_eq_tensor0SCovariantDerivative (I := I) g s X T x).symm
  have hslot :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (LeviCivita (I := I) g) X T x slots =
        metricNabla0S (I := I) g T x (Fin.cons (X x) slots) :=
    (totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
      (LeviCivita (I := I) g) X T x slots).symm
  exact (congrArg (fun A : Tensor0SSpace s I x => A slots) key).trans hslot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDerivLift_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDerivLift_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDerivLift_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.covDerivLift_unit

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem tensor0SSum_apply {x : M} {s : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (m : Fin s → TangentSpace I x) :
    (∑ i ∈ t, F i) m = ∑ i ∈ t, F i m := by
  classical
  refine Finset.cons_induction_on t ?_ ?_
  · rfl
  · intro a u ha ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.tensor0SSum_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.tensor0SSum_apply target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem orthoBasisAt (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ frame : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      (∀ i, frame i = smoothOrthoFrame (I := I) g x i x) ∧
      (∀ i j, g.inner x (frame i) (frame j) = if i = j then (1 : Real) else 0) := by
  classical
  have hON : ∀ i j, g.inner x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent Real
      (fun i : Fin (Module.finrank Real E) => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hzero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at hzero
    have hpull : ∀ j ∈ fs,
        g.inner x (smoothOrthoFrame (I := I) g x k x)
          (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : Real) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul
        (c j) (smoothOrthoFrame (I := I) g x j x), smul_eq_mul, hON k j]
    rw [Finset.sum_congr rfl hpull] at hzero
    rw [Finset.sum_eq_single_of_mem k hk] at hzero
    · rw [if_pos rfl, mul_one] at hzero
      exact hzero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    change Fintype.card (Fin (Module.finrank Real E)) = Module.finrank Real E
    exact Fintype.card_fin _
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · intro i
    change (basisOfLinearIndependentOfCardEqFinrank hli hcard :
      Fin (Module.finrank Real E) → TangentSpace I x) i =
        smoothOrthoFrame (I := I) g x i x
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show (basisOfLinearIndependentOfCardEqFinrank hli hcard :
          Fin (Module.finrank Real E) → TangentSpace I x) i =
            smoothOrthoFrame (I := I) g x i x from by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank],
      show (basisOfLinearIndependentOfCardEqFinrank hli hcard :
          Fin (Module.finrank Real E) → TangentSpace I x) j =
            smoothOrthoFrame (I := I) g x j x from by
          rw [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact hON i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.orthoBasisAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.orthoBasisAt target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem traceFirstTwo_eq_frame_sum (g : SmoothRiemannianMetric I M) {x : M}
    (frame : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (frame i) (frame j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (slots : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g A slots =
      ∑ i : Fin (Module.finrank Real E), A (Fin.cons (frame i) (Fin.cons (frame i) slots)) := by
  classical
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g frame
    (fun a k => if a = k then (1 : Real) else 0)
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g frame hON) A slots]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · change (if i = i then (1 : Real) else 0) *
        A (metricTraceInput (I := I) (frame i) (frame i) slots) = _
    rw [if_pos rfl, one_mul]
    rfl
  · intro j _ hji
    change (if i = j then (1 : Real) else 0) *
        A (metricTraceInput (I := I) (frame i) (frame j) slots) = 0
    rw [if_neg (fun h => hji h.symm), _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_eq_frame_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_eq_frame_sum target :: scope.openDecls } }

theorem covDivLift_unit (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) (x : M) :
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      covDiv0SField (I := I) g V x := by
  classical
  obtain ⟨frame, hfr, hON⟩ := orthoBasisAt (I := I) g x
  have hraw : (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x =
      ∑ i : Fin (Module.finrank Real E),
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)) := rfl
  rw [hraw, sum_apply]
  refine DFunLike.ext _ _ fun slots => ?_
  have hterm : ∀ i : Fin (Module.finrank Real E),
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) slots =
      metricNabla0S (I := I) g V x
        (Fin.cons (frame i) (Fin.cons (frame i) slots)) := by
    intro i
    have hsmooth : MDifferentiableAt I (I.prod 𝓘(Real, E))
        (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
          (smoothOrthoFrame (I := I) g x i z)) x :=
      (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
    rw [codiffPsi_apply (I := I) (M := M) g s (ccLift0S (I := I) g V) x hsmooth hsmooth]
    have hcontract :
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          contractCovariant 0 s x (smoothOrthoFrame (I := I) g x i x)
            (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)
              (fun z : M => (ccLift0S (I := I) g V).toSection z) x
              (smoothOrthoFrame (I := I) g x i x)))
          (unitZeroSec (I := I) (M := M) x) slots =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace (s + 1) I x from
          TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)
            (fun z : M => (ccLift0S (I := I) g V).toSection z) x
            (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x)
          (Fin.cons (smoothOrthoFrame (I := I) g x i x) slots) := rfl
    rw [hcontract, hfr i]
    exact covDerivLift_unit (I := I) g V x (smoothOrthoFrame (I := I) g x i x)
      (Fin.cons (smoothOrthoFrame (I := I) g x i x) slots)
  rw [tensor0SSum_apply (I := I) (M := M) Finset.univ
    (fun i : Fin (Module.finrank Real E) =>
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        covDivergenceBilinear (I := I) (M := M) g s (ccLift0S (I := I) g V) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x)) slots]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [covDiv0SField, metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply]
  exact (traceFirstTwo_eq_frame_sum (I := I) g frame hON
    (metricNabla0S (I := I) g V x) slots).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDivLift_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDivLift_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDivLift_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.covDivLift_unit

theorem covDivLift_eq (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V) =
      ccLift0S (I := I) g (covDiv0SField (I := I) g V) := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [ccLift0S_unitModel]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (covDivergence (I := I) (M := M) g s (ccLift0S (I := I) g V)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
    Tensor0SSpace.toModel (covDiv0SField (I := I) g V x)
  rw [covDivLift_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDivLift_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDivLift_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDivLift_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.covDivLift_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem covGradLift_eq (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    covGrad (I := I) (M := M) g 0 s (ccLift0S (I := I) g T) =
      ccLift0S (I := I) g (metricNabla0S (I := I) g T) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [ccLift0S_unitModel]
  refine ContinuousMultilinearMap.ext fun v => ?_
  let vt : Fin (s + 1) → TangentSpace I x :=
    fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
  have hcons : vt = Fin.cons (vt 0) (Matrix.vecTail vt) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro k
      simp [Matrix.vecTail]
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s (ccLift0S (I := I) g T)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) vt =
    Tensor0SSpace.eval (metricNabla0S (I := I) g T x) vt
  rw [covGrad_apply_unit_eval (I := I) (M := M) g s
    (ccLift0S (I := I) g T) x vt]
  rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s (ccLift0S (I := I) g T) x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x (vt 0)),
    ContinuousLinearEquiv.symm_apply_apply]
  have hval := covDerivLift_unit (I := I) g T x (vt 0) (Matrix.vecTail vt)
  refine hval.trans ?_
  conv_rhs => rw [hcons]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covGradLift_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covGradLift_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covGradLift_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.covGradLift_eq

end Identification

section Payoff

variable {s : ℕ}

theorem l2Inner_nabla_eq_neg_div (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun
        (ccLift0S (I := I) g V).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (ccLift0S (I := I) g T).toFun
          (ccLift0S (I := I) g (covDiv0SField (I := I) g V)).toFun := by
  rw [← covGradLift_eq (I := I) g T, ← covDivLift_eq (I := I) g V]
  exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence (I := I) (M := M) g s
    (ccLift0S (I := I) g T) (ccLift0S (I := I) g V)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_eq_neg_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_eq_neg_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_eq_neg_div ``Submission.DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_eq_neg_div

theorem l2Inner_nabla_self_eq_neg_lap (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun
        (ccLift0S (I := I) g (metricNabla0S (I := I) g T)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (ccLift0S (I := I) g T).toFun
          (ccLift0S (I := I) g (roughLap0SField (I := I) g T)).toFun :=
  l2Inner_nabla_eq_neg_div (I := I) g T (metricNabla0S (I := I) g T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_self_eq_neg_lap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_self_eq_neg_lap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_self_eq_neg_lap ``Submission.DifferentialGeometry.PDE.RicciFlow.l2Inner_nabla_self_eq_neg_lap

end Payoff

end DifferentialGeometry.PDE.RicciFlow
