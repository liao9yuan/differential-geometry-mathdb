import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.LpIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Lp.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianRhs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma smoothRicciPairing_contMDiff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  classical
  have hRic :=
    ricciTensor_contMDiff (I := I) g
  have hGradφ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g φ b)) :=
    gradFun_contMDiff_total_section (I := I) g φ.contMDiff
  have hGradv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g v.toFun b)) :=
    gradFun_contMDiff_total_section (I := I) g v.smooth
  have happ :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ricciTensor (I := I) g m
              (gradFun (I := I) g φ m)
              (gradFun (I := I) g v.toFun m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic hGradφ hGradv
  intro m
  have hpm := happ m
  rw [Bundle.contMDiffAt_totalSpace] at hpm
  exact hpm.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairing_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairing_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairing_contMDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairing_contMDiff

noncomputable def smoothRicciPairingBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun b => ricciTensor
    (I := I) g b
    (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)
  smooth := smoothRicciPairing_contMDiff (I := I) (M := M) g φ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma smoothRicciPairingBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (b : M) :
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).toFun b =
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingBundle_apply

noncomputable def smoothRicciPairingLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothToLp (I := I) (M := M) g (smoothRicciPairingBundle g φ v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothRicciPairingLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothRicciPairingLp (I := I) (M := M) g φ v =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle g φ v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_def ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_def

noncomputable def gradInnerLaplacianRhsOfPairings
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)
    - (2 : ℝ) • h_ricci_part
    - (2 : ℝ) • h_hess_part

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem gradInnerLaplacianRhsOfPairings_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_def ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_def

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianRhsOfPairings_ricci_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part1 h_ricci_part2 h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
        (h_ricci_part1 + h_ricci_part2) h_hess_part =
      gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
          h_ricci_part1 h_hess_part -
        (2 : ℝ) • h_ricci_part2 := by
  unfold gradInnerLaplacianRhsOfPairings
  rw [smul_add]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_ricci_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_ricci_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_ricci_add ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_ricci_add

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianRhsOfPairings_hess_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part1 h_hess_part2 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
        h_ricci_part (h_hess_part1 + h_hess_part2) =
      gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
          h_ricci_part h_hess_part1 -
        (2 : ℝ) • h_hess_part2 := by
  unfold gradInnerLaplacianRhsOfPairings
  rw [smul_add]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_hess_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_hess_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_hess_add ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_hess_add

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianRhsOfPairings_norm_lt_top
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    _root_.MeasureTheory.eLpNorm
        ((gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
            h_ricci_part h_hess_part : _root_.MeasureTheory.Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
  (Lp.memLp _).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_lt_top ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_lt_top

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianRhsOfPairings_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖gradInnerLaplacianRhsOfPairings (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ +
      2 * ‖h_ricci_part‖ +
      2 * ‖h_hess_part‖ := by
  unfold gradInnerLaplacianRhsOfPairings
  have hstep1 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ +
      ‖(2 : ℝ) • h_hess_part‖ := by
    exact norm_sub_le _ _
  have hstep2 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ +
      ‖(2 : ℝ) • h_ricci_part‖ := by
    exact norm_sub_le _ _
  have hstep3 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ := by
    exact norm_sub_le _ _
  have hstep4 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ := by
    exact norm_sub_le _ _
  have h_smul_ricci : ‖(2 : ℝ) • h_ricci_part‖ = 2 * ‖h_ricci_part‖ := by
    rw [norm_smul]
    simp
  have h_smul_hess : ‖(2 : ℝ) • h_hess_part‖ = 2 * ‖h_hess_part‖ := by
    rw [norm_smul]
    simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess,
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ
      (preimageLift (I := I) (M := M) g hu_h)),
    norm_nonneg ((2 : ℝ) • h_ricci_part),
    norm_nonneg ((2 : ℝ) • h_hess_part)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_le ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.gradInnerLaplacianRhsOfPairings_norm_le

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRicciPairingLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (smoothRicciPairingLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun b : M =>
        ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  unfold smoothRicciPairingLp
  exact MemLp.coeFn_toLp
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).memLp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianRhs.smoothRicciPairingLp_coeFn

end GradInnerLaplacianRhs
end Laplacian
end Analysis
end DifferentialGeometry

end
