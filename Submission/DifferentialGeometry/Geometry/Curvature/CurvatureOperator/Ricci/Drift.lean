import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Hessian
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.CotangentSharpSmoothness
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetricField
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Norm.Product
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I 1 M]
variable [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }


noncomputable def ricGradForm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  partialEval0SField (I := I) (metricRicci (I := I) (M := M) g)
    (gradG (I := I) g ⟨_, hf⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricGradForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricGradForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricGradForm ``Submission.DifferentialGeometry.Geometry.Curvature.ricGradForm

@[simp] theorem ricGradForm_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricGradForm (I := I) g hf x =
      tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
        (metricRicciAt (I := I) (M := M) g x) (gradG (I := I) g ⟨_, hf⟩ x) := by
  simp [ricGradForm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricGradForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricGradForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricGradForm_apply ``Submission.DifferentialGeometry.Geometry.Curvature.ricGradForm_apply


noncomputable def ricGradVec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (fun x : M => cotangentSharp (I := I) g x
      (ricGradForm (I := I) g hf x))
    (cotangentSharp_gen_contMDiff_total (I := I) g
      (fun a j => by
        exact cotangentSection_chartComponent_contMDiffOn
          (I := I) (ricGradForm (I := I) g hf) a j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricGradVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricGradVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricGradVec ``Submission.DifferentialGeometry.Geometry.Curvature.ricGradVec

@[simp] theorem ricGradVec_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricGradVec (I := I) g hf x =
      cotangentSharp (I := I) g x (ricGradForm (I := I) g hf x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricGradVec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricGradVec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricGradVec_apply ``Submission.DifferentialGeometry.Geometry.Curvature.ricGradVec_apply


noncomputable def ricDriftVec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (fun x : M => ricGradVec (I := I) g hf x -
      ((1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x) •
        gradG (I := I) g ⟨_, hf⟩ x)
    ((ricGradVec (I := I) g hf).contMDiff.sub_section
      ((contMDiff_const.mul (metricScalar_smooth (I := I) (M := M) g)).smul_section
        (gradG (I := I) g ⟨_, hf⟩).contMDiff))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricDriftVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricDriftVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricDriftVec ``Submission.DifferentialGeometry.Geometry.Curvature.ricDriftVec

@[simp] theorem ricDriftVec_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    ricDriftVec (I := I) g hf x = ricGradVec (I := I) g hf x -
      ((1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x) •
        gradG (I := I) g ⟨_, hf⟩ x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricDriftVec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricDriftVec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricDriftVec_apply ``Submission.DifferentialGeometry.Geometry.Curvature.ricDriftVec_apply

theorem divergence_ricGradVec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    divergence (I := I) (metricCov (I := I) (M := M) g)
        (fun y : M => ricGradVec (I := I) g hf y) x =
      (1 / 2 : Real) *
          mvfderiv (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x
            (gradG (I := I) g ⟨_, hf⟩ x) +
        inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) f hf x) := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov := metricCov_smooth (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let G := gradG (I := I) g ⟨_, hf⟩
  let beta := ricGradForm (I := I) g hf
  let hRicRegularity := totalNabla0S_regularity (I := I) 2 cov hcov Ric
  let nRic := totalNabla0S (I := I) 2 cov Ric hRicRegularity
  let hBetaRegularity := totalNabla0S_regularity (I := I) 1 cov hcov beta
  let nBeta := totalNabla0S (I := I) 1 cov beta hBetaRegularity
  have hRicReal : TotalNabla0SRealizes (I := I) 2 cov Ric nRic := by
    exact totalNabla0S_realizes (I := I) 2 cov Ric hRicRegularity
  have hBetaReal : TotalNabla0SRealizes (I := I) 1 cov beta nBeta := by
    exact totalNabla0S_realizes (I := I) 1 cov beta hBetaRegularity
  have hmc : IsMetricCompatible (I := I) cov g := by
    rw [show cov =
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g by rfl]
    exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  let delta : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real :=
    fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x basis delta :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let X : Fin (Module.finrank Real (TangentSpace I x)) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun i => (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (basis i)).choose
  have hX (i : Fin (Module.finrank Real (TangentSpace I x))) :
      X i x = basis i :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (basis i)).choose_spec
  have hsharp (i : Fin (Module.finrank Real (TangentSpace I x))) :
      cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i) =
        cotangentSharp (I := I) g x
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
            (nBeta x) (basis i)) := by
    have h0 := cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
      (I := I) cov g hmc beta nBeta hBetaReal (X i) x
      ((ricGradVec (I := I) g hf).contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
    simpa only [ricGradVec_apply, hX] using h0
  have hcomp (i : Fin (Module.finrank Real (TangentSpace I x))) :
      g.inner x
          (cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i))
          (basis i) =
        nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
    rw [hsharp i, cotangentSharp_inner_eval,
      tensor0S_curry_apply_cons]
    calc
      nBeta x (Fin.cons (basis i) (fun _ : Fin 1 => basis i)) =
          nabla0SFun (I := I) 1 cov (X i) beta x
            (fun _ : Fin 1 => basis i) := by
        simpa only [hX] using
          (TotalNabla0SRealizes.apply hBetaReal (X i) x
            (fun _ : Fin 1 => basis i))
      _ =
          (freezeFirstTwoArgs0S (I := I) (nRic x) (basis i) (G x) +
            tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (Ric x)
              (cov (fun y : M => G y) x (basis i)))
            (fun _ : Fin 1 => basis i) := by
        rw [show beta = partialEval0SField (I := I) Ric G by rfl]
        rw [nabla_partialEval0S (I := I) cov Ric nRic hRicReal (X i) G x]
        rw [hX]
      _ =
          nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
        rw [Tensor0SSpace.add_apply, freezeFirstTwoArgs0S_apply,
          tensor0S_curry_one_apply]
        rw [metricTraceInput_one_eq_vec3]
        simp only [Ric, metricRicci_apply]
        rfl
  let nRic0 := totalNabla0SFun (I := I) 2 cov Ric x
  let dR := differential1FormFun (I := I)
    (fun y : M => metricScalarAt (I := I) (M := M) g y) x
  have hdR : dR = differential1FormFun (I := I)
      (fun y : M => metricTracePair0SAt (I := I) g
        (metricRicci (I := I) (M := M) g y)) x := by
    apply congrArg (fun F : M → Real => differential1FormFun (I := I) F x)
    funext y
    dsimp only [dR, metricScalarAt]
    rw [metricRicci_apply]
  have hNablaSymm : NablaRicSymmAt (I := I) nRic0 := by
    simpa only [nRic0, cov, Ric, metricCov, metricRicci,
      LeviCivita_eq_leviCivitaConnectionOfMetric] using
      (metricNablaSymm (I := I) (M := M) g x)
  have hpack :
      ∃ nablaRm04 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 5 x,
        SecondBianchiAt (I := I) nablaRm04 ∧
          NablaRmSymmAt (I := I) nablaRm04 ∧
            NablaRicTraceAt (I := I) basis delta nablaRm04 nRic0 ∧
              DScalarTraceAt (I := I) basis delta nRic0 dR := by
    rw [hdR]
    simpa only [cov, Ric, nRic0, metricCov, metricRicci,
      LeviCivita_eq_leviCivitaConnectionOfMetric] using
      (exists_levi_civita_bianchi_trace_identities (I := I) (M := M) g basis delta hinv)
  obtain ⟨nablaRm04, hsecond, hRmSymm, hRicTrace, hScalar⟩ := hpack
  have hInv : ∀ i j, delta i j = delta j i := by
    intro i j
    simp [delta, eq_comm]
  have hcontract :
      ContractedBianchiOfSecondAt (I := I) basis delta nablaRm04 nRic0 dR :=
    contractOfSecond (I := I) basis delta nablaRm04 nRic0 dR
      hRmSymm hRicTrace hScalar hInv
  have hBianchi : ContractedBianchiAt (I := I) basis delta nRic0 dR :=
    contracted_bianchi_of_second (I := I) basis delta nablaRm04 nRic0 dR
      hcontract hsecond
  have hRicPart :
      (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) =
        (1 / 2 : Real) *
          mvfderiv (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
    calc
      (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) =
          ∑ i, nRic0 (vec3 (I := I) (basis i) (basis i) (G x)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show nRic x = nRic0 by rfl]
        exact hNablaSymm (basis i) (G x) (basis i)
      _ = (1 / 2 : Real) * dR (fun _ : Fin 1 => G x) := by
        simpa [delta] using hBianchi (G x)
      _ = (1 / 2 : Real) *
          mvfderiv (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
        rw [differential1FormFun_apply_eq_mvfderiv]
  have hHessPart :
      (∑ i, metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i))) =
        inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) cov hcov f hf x) := by
    have htrace :
        LinearMap.trace Real (TangentSpace I x)
            ((cotangentSharpLinear (I := I) g x).comp
              ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
                  (metricRicciAt (I := I) (M := M) g x)).toLinearMap.comp
                (cov (fun y : M => G y) x).toLinearMap)) =
          ∑ i, metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
      rw [trace_eq_ortho_sum (I := I) g x _ basis hON]
      apply Finset.sum_congr rfl
      intro i _
      simp only [LinearMap.comp_apply]
      change g.inner x
          (cotangentSharp (I := I) g x
            (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
              (metricRicciAt (I := I) (M := M) g x)
              (cov (fun y : M => G y) x (basis i))))
          (basis i) = _
      rw [cotangentSharp_inner_eval, tensor0S_curry_one_apply]
      rfl
    rw [← htrace]
    have hGfun : (fun y : M => G y) = fun y : M => gradFun (I := I) g f y := by
      funext y
      exact gradient_eq_gradFun (I := I) g f y
    rw [hGfun]
    simpa only [cov, hcov, gradient_eq_gradFun] using
      (ricHess_eq_inner (I := I) cov hcov g hmc f hf x)
  rw [divergence_eq]
  rw [trace_eq_ortho_sum (I := I) g x _ basis hON]
  calc
    (∑ i, g.inner x
        (cov (fun y : M => ricGradVec (I := I) g hf y) x (basis i))
        (basis i)) =
        ∑ i, (nRic x (vec3 (I := I) (basis i) (G x) (basis i)) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcomp i
    _ =
        (∑ i, nRic x (vec3 (I := I) (basis i) (G x) (basis i))) +
          ∑ i, metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cov (fun y : M => G y) x (basis i)) (basis i)) := by
      rw [Finset.sum_add_distrib]
    _ =
        (1 / 2 : Real) *
            mvfderiv (I := I)
              (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) +
          inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
            (hessianSec (I := I) cov hcov f hf x) := by
      rw [hRicPart, hHessPart]
    _ = _ := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.divergence_ricGradVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.divergence_ricGradVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.divergence_ricGradVec ``Submission.DifferentialGeometry.Geometry.Curvature.divergence_ricGradVec

theorem ricDriftDiv [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    divergenceG (I := I) g (ricDriftVec (I := I) g hf) x =
      inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
          (hessianSec (I := I) (metricCov (I := I) (M := M) g)
            (metricCov_smooth (I := I) (M := M) g) f hf x) -
        (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
          ΔG (I := I) g ⟨_, hf⟩ x := by
  let cov := metricCov (I := I) (M := M) g
  let G := gradG (I := I) g ⟨_, hf⟩
  let RG := ricGradVec (I := I) g hf
  let a : M -> Real := fun y =>
    (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g y
  have ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a := by
    exact contMDiff_const.mul (metricScalar_smooth (I := I) (M := M) g)
  have haMD : MDifferentiableAt I 𝓘(Real, Real) a x :=
    ha.contMDiffAt.mdifferentiableAt (by simp)
  have hbridge :
      divergence (I := I) cov (fun y : M => ricDriftVec (I := I) g hf y) x =
        divergenceG (I := I) g (ricDriftVec (I := I) g hf) x := by
    rw [show cov = LeviCivita (I := I) g by rfl]
    change divergence (I := I) (LeviCivita (I := I) g)
      (ricDriftVec (I := I) g hf).toFun x = _
    exact divergence_levi_eq (I := I) g (ricDriftVec (I := I) g hf) x
  have hdivRG :
      divergence (I := I) cov (fun y : M => RG y) x =
        (1 / 2 : Real) *
            mvfderiv (I := I)
              (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) +
          inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
            (hessianSec (I := I) cov
              (metricCov_smooth (I := I) (M := M) g) f hf x) := by
    simpa only [cov, LeviCivita, metricCov, RG, G] using
      divergence_ricGradVec (I := I) g hf x
  have hdivaG :
      divergence (I := I) cov (fun y : M => a y • G y) x =
        a x * divergence (I := I) cov (fun y : M => G y) x +
          mvfderiv (I := I) a x (G x) := by
    rw [show (fun y : M => a y • G y) = a • fun y : M => G y by rfl]
    exact divergence_smul (I := I) (X := fun y : M => G y) (x := x) cov inferInstance haMD
      (G.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hLap :
      divergence (I := I) cov (fun y : M => G y) x = ΔG (I := I) g ⟨_, hf⟩ x := by
    rw [show cov = LeviCivita (I := I) g by rfl]
    rw [show (fun y : M => G y) = gradientFun (I := I) g f by
      funext y
      exact (gradient_eq_gradFun (I := I) g f y).symm]
    exact laplacian_levi_eq (I := I) g hf x
  have hda :
      mvfderiv (I := I) a x (G x) =
        (1 / 2 : Real) *
          mvfderiv (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y) x (G x) := by
    exact mvfderiv_const_mul_apply (I := I) (1 / 2 : Real) (G x)
      ((metricScalar_smooth (I := I) (M := M) g).contMDiffAt.mdifferentiableAt
        (by simp))
  rw [← hbridge]
  change divergence (I := I) cov
      (fun y : M => RG y - a y • G y) x = _
  calc
    divergence (I := I) cov (fun y : M => RG y - a y • G y) x =
        divergence (I := I) cov (fun y : M => RG y) x -
          divergence (I := I) cov (fun y : M => a y • G y) x := by
      rw [show (fun y : M => RG y - a y • G y) =
        (fun y : M => RG y) - fun y : M => a y • G y by rfl]
      exact divergence_sub (I := I)
        (X := fun y : M => RG y) (Y := fun y : M => a y • G y) (x := x) cov
        (RG.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((ha.smul_section G.contMDiff).contMDiffAt.mdifferentiableAt (by simp))
    _ = _ := by
      rw [hdivRG, hdivaG, hLap, hda]
      dsimp only [a]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricDriftDiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricDriftDiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricDriftDiv ``Submission.DifferentialGeometry.Geometry.Curvature.ricDriftDiv

theorem ricDriftAct [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) (x : M) :
    tangentSectionAction (I := I) (ricDriftVec (I := I) g hf) f x =
      metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (gradG (I := I) g ⟨_, hf⟩ x)
            (gradG (I := I) g ⟨_, hf⟩ x)) -
        (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
          g.inner x (gradG (I := I) g ⟨_, hf⟩ x) (gradG (I := I) g ⟨_, hf⟩ x) := by
  let fb : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  change tangentSectionAction (I := I) (ricDriftVec (I := I) g hf) (⇑fb) x =
    metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (gradG (I := I) g fb x)
          (gradG (I := I) g fb x)) -
      (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
        g.inner x (gradG (I := I) g fb x) (gradG (I := I) g fb x)
  rw [tangentSectionAction_eq_inner_grad_g (I := I) g fb
    (ricDriftVec (I := I) g hf) x]
  simp only [ricDriftVec_apply, map_sub, map_smul,
    sub_apply, smul_apply,
    ricGradVec_apply, cotangentSharp_inner_eval, ricGradForm_apply,
    tensor0S_curry_one_apply, smul_eq_mul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricDriftAct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricDriftAct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricDriftAct ``Submission.DifferentialGeometry.Geometry.Curvature.ricDriftAct

end DifferentialGeometry.Geometry.Curvature

end
