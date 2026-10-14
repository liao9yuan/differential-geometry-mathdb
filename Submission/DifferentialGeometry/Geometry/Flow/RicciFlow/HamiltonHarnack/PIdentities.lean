import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] in
noncomputable def hamiltonP {x : M}
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  nablaRic - nablaRic.domDomCongr (Equiv.swap (0 : Fin 3) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP

omit [FiniteDimensional Real E] in
@[simp] theorem hamiltonP_apply {x : M}
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (A B C : TangentSpace I x) :
    hamiltonP (I := I) nablaRic (vec3 A B C) =
      nablaRic (vec3 A B C) - nablaRic (vec3 B A C) := by
  rw [hamiltonP, Tensor0SSpace.sub_apply,
    Tensor0SSpace.domDomCongr_apply]
  have hslots :
      (fun q => vec3 A B C ((Equiv.swap (0 : Fin 3) 1) q)) =
        vec3 B A C := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_apply

omit [FiniteDimensional Real E] in
theorem hamiltonP_skew {x : M}
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (A B C : TangentSpace I x) :
    hamiltonP (I := I) nablaRic (vec3 A B C) =
      -hamiltonP (I := I) nablaRic (vec3 B A C) := by
  rw [hamiltonP_apply, hamiltonP_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_skew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_skew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_skew ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_skew

omit [FiniteDimensional Real E] in
theorem hamiltonP_cyclic {x : M}
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hSymm : NablaRicSymmAt (I := I) nablaRic)
    (A B C : TangentSpace I x) :
    hamiltonP (I := I) nablaRic (vec3 A B C) +
        hamiltonP (I := I) nablaRic (vec3 B C A) +
      hamiltonP (I := I) nablaRic (vec3 C A B) = 0 := by
  rw [hamiltonP_apply, hamiltonP_apply, hamiltonP_apply,
    hSymm A B C, hSymm B A C, hSymm C B A]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_cyclic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_cyclic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_cyclic ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_cyclic

omit [FiniteDimensional Real E] in
theorem hamiltonP_first_trace
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (hScalar : DScalarTraceAt (I := I) basis gInv nablaRic dScalar)
    (hSymm : NablaRicSymmAt (I := I) nablaRic)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * hamiltonP (I := I) nablaRic (vec3 (basis i) X (basis j))) =
      -(1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := by
  classical
  have hleft :
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) X (basis j))) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) X (basis j))) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) (basis j) X) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hSymm (basis i) X (basis j)]
      _ = (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := hBianchi X
  simp only [hamiltonP_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hleft, ← hScalar X]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_first_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_first_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_first_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_first_trace

omit [FiniteDimensional Real E] in
theorem hamiltonP_second_trace
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (hScalar : DScalarTraceAt (I := I) basis gInv nablaRic dScalar)
    (hSymm : NablaRicSymmAt (I := I) nablaRic)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * hamiltonP (I := I) nablaRic (vec3 X (basis i) (basis j))) =
      (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := by
  classical
  have hright :
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) X (basis j))) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) X (basis j))) =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 (basis i) (basis j) X) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hSymm (basis i) X (basis j)]
      _ = (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) := hBianchi X
  simp only [hamiltonP_apply, mul_sub, Finset.sum_sub_distrib]
  rw [← hScalar X, hright]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonP_second_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonP_second_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonP_second_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonP_second_trace

omit [FiniteDimensional Real E] in
theorem curvature_divergence_eq_hamiltonP
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hSecond : SecondBianchiAt (I := I) nablaRm04)
    (hRmSymm : NablaRmSymmAt (I := I) nablaRm04)
    (hRicTrace : NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic)
    (A B D : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaRm04 (vec5 (basis i) (basis j) D A B)) =
      hamiltonP (I := I) nablaRic (vec3 B A D) := by
  classical
  have hpoint (i j : Idx) :
      nablaRm04 (vec5 (basis i) (basis j) D A B) +
          nablaRm04 (vec5 A (basis i) B D (basis j)) -
        nablaRm04 (vec5 B (basis i) A D (basis j)) = 0 := by
    have h := hSecond (basis i) A B (basis j) D
    rw [hRmSymm.2.2 (basis i) A B (basis j) D] at h
    have hsecond :
        nablaRm04 (vec5 A B (basis i) (basis j) D) =
          nablaRm04 (vec5 A (basis i) B D (basis j)) := by
      rw [hRmSymm.2.1 A (basis i) B (basis j) D,
        hRmSymm.1 A (basis i) B (basis j) D]
      ring
    have hthird :
        nablaRm04 (vec5 B (basis i) A (basis j) D) =
          -nablaRm04 (vec5 B (basis i) A D (basis j)) :=
      hRmSymm.1 B (basis i) A (basis j) D
    rw [hsecond, hthird] at h
    linarith
  have hsum :
      (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRm04 (vec5 (basis i) (basis j) D A B)) +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRm04 (vec5 A (basis i) B D (basis j))) -
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRm04 (vec5 B (basis i) A D (basis j))) = 0 := by
    calc
      _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (nablaRm04 (vec5 (basis i) (basis j) D A B) +
              nablaRm04 (vec5 A (basis i) B D (basis j)) -
              nablaRm04 (vec5 B (basis i) A D (basis j))) := by
                simp only [mul_add, mul_sub, Finset.sum_add_distrib,
                  Finset.sum_sub_distrib]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [hpoint i j, _root_.MulZeroClass.mul_zero]
  rw [hamiltonP_apply, hRicTrace B A D, hRicTrace A B D]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvature_divergence_eq_hamiltonP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvature_divergence_eq_hamiltonP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvature_divergence_eq_hamiltonP ``Submission.DifferentialGeometry.PDE.RicciFlow.curvature_divergence_eq_hamiltonP

variable [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

noncomputable def hamiltonPAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  hamiltonP (I := I) (metricNablaRic (I := I) (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt

noncomputable def hamiltonPField
    (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  metricNablaRic (I := I) (M := M) g -
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞)
      (Equiv.swap (0 : Fin 3) 1) (metricNablaRic (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPField ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPField

omit [SigmaCompactSpace M] in
@[simp] theorem hamiltonPField_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    hamiltonPField (I := I) g x = hamiltonPAt (I := I) g x := by
  ext slots
  simp only [hamiltonPField, hamiltonPAt, hamiltonP,
    ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
    Tensor0SField.domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPField_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPField_apply

omit [SigmaCompactSpace M] in
@[simp] theorem hamiltonPAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : TangentSpace I x) :
    hamiltonPAt (I := I) g x (vec3 A B C) =
      metricNablaRic (I := I) (M := M) g x (vec3 A B C) -
        metricNablaRic (I := I) (M := M) g x (vec3 B A C) := by
  rw [hamiltonPAt, hamiltonP_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_apply

omit [SigmaCompactSpace M] in
theorem hamiltonPAt_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : TangentSpace I x) :
    hamiltonPAt (I := I) g x (vec3 A B C) =
      -hamiltonPAt (I := I) g x (vec3 B A C) := by
  exact hamiltonP_skew (metricNablaRic (I := I) (M := M) g x) A B C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_skew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_skew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_skew ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_skew

omit [SigmaCompactSpace M] in
theorem hamiltonPAt_cyclic
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B C : TangentSpace I x) :
    hamiltonPAt (I := I) g x (vec3 A B C) +
        hamiltonPAt (I := I) g x (vec3 B C A) +
      hamiltonPAt (I := I) g x (vec3 C A B) = 0 := by
  exact hamiltonP_cyclic
    (metricNablaRic (I := I) (M := M) g x)
    (metricNablaRic_last_two_symm (I := I) (M := M) g x) A B C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_cyclic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_cyclic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_cyclic ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_cyclic

omit [SigmaCompactSpace M] in
theorem hamiltonPAt_first_trace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * hamiltonPAt (I := I) g x (vec3 (basis i) X (basis j))) =
      -(1 / 2 : Real) *
        differential1FormFun (I := I)
          (fun y : M => metricScalarAt (I := I) (M := M) g y) x
          (fun _ : Fin 1 => X) := by
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g) x
  let nablaRic :=
    metricNablaRic (I := I) (M := M) g x
  let dScalar := differential1FormFun (I := I)
    (fun y : M => metricTracePair0SAt (I := I) g
      (metricRicci (I := I) (M := M) g y)) x
  have hcore :
      SecondBianchiAt (I := I) nablaRm04 ∧
        NablaRmSymmAt (I := I) nablaRm04 ∧
          NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic ∧
            DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
    simpa [nablaRm04, nablaRic, dScalar, metricNablaRic, metricCov, metricRm04,
      metricRicci, metricScalarAt, metricCov_smooth] using
      (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_scalar_trace_identities
        (I := I) (M := M) g basis gInv hinv)
  have hInv : ∀ i j : Idx, gInv i j = gInv j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) g x basis gInv hinv
  have hcontract :
      ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
        nablaRic dScalar :=
    contractOfSecond (I := I) basis gInv nablaRm04 nablaRic dScalar
      hcore.2.1 hcore.2.2.1 hcore.2.2.2 hInv
  have hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar :=
    contracted_bianchi_of_second (I := I) basis gInv nablaRm04 nablaRic dScalar
      hcontract hcore.1
  simpa [hamiltonPAt, nablaRic, dScalar, metricScalarAt,
    metricRicci_apply] using
    hamiltonP_first_trace (I := I) basis gInv nablaRic dScalar hBianchi
      hcore.2.2.2 (metricNablaRic_last_two_symm (I := I) (M := M) g x) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_first_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_first_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_first_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_first_trace

omit [SigmaCompactSpace M] in
theorem hamiltonPAt_second_trace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * hamiltonPAt (I := I) g x (vec3 X (basis i) (basis j))) =
      (1 / 2 : Real) *
        differential1FormFun (I := I)
          (fun y : M => metricScalarAt (I := I) (M := M) g y) x
          (fun _ : Fin 1 => X) := by
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g) x
  let nablaRic :=
    metricNablaRic (I := I) (M := M) g x
  let dScalar := differential1FormFun (I := I)
    (fun y : M => metricTracePair0SAt (I := I) g
      (metricRicci (I := I) (M := M) g y)) x
  have hcore :
      SecondBianchiAt (I := I) nablaRm04 ∧
        NablaRmSymmAt (I := I) nablaRm04 ∧
          NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic ∧
            DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
    simpa [nablaRm04, nablaRic, dScalar, metricNablaRic, metricCov, metricRm04,
      metricRicci, metricScalarAt, metricCov_smooth] using
      (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_scalar_trace_identities
        (I := I) (M := M) g basis gInv hinv)
  have hInv : ∀ i j : Idx, gInv i j = gInv j i :=
    MetricInverseInBasis.symmetric (I := I) (M := M) g x basis gInv hinv
  have hcontract :
      ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
        nablaRic dScalar :=
    contractOfSecond (I := I) basis gInv nablaRm04 nablaRic dScalar
      hcore.2.1 hcore.2.2.1 hcore.2.2.2 hInv
  have hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar :=
    contracted_bianchi_of_second (I := I) basis gInv nablaRm04 nablaRic dScalar
      hcontract hcore.1
  simpa [hamiltonPAt, nablaRic, dScalar, metricScalarAt,
    metricRicci_apply] using
    hamiltonP_second_trace (I := I) basis gInv nablaRic dScalar hBianchi
      hcore.2.2.2 (metricNablaRic_last_two_symm (I := I) (M := M) g x) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_second_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_second_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_second_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.hamiltonPAt_second_trace

omit [SigmaCompactSpace M] in
theorem metric_curvature_divergence_eq_hamiltonPAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) g x basis gInv)
    (A B D : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            4 (metricCov (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g) x
            (vec5 (basis i) (basis j) D A B)) =
      hamiltonPAt (I := I) g x (vec3 B A D) := by
  let nablaRm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (metricCov (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g) x
  let nablaRic :=
    metricNablaRic (I := I) (M := M) g x
  let dScalar := differential1FormFun (I := I)
    (fun y : M => metricTracePair0SAt (I := I) g
      (metricRicci (I := I) (M := M) g y)) x
  have hcore :
      SecondBianchiAt (I := I) nablaRm04 ∧
        NablaRmSymmAt (I := I) nablaRm04 ∧
          NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic ∧
            DScalarTraceAt (I := I) basis gInv nablaRic dScalar := by
    simpa [nablaRm04, nablaRic, dScalar, metricNablaRic, metricCov, metricRm04,
      metricRicci, metricScalarAt, metricCov_smooth] using
      (DifferentialGeometry.Geometry.Connection.levi_civita_bianchi_scalar_trace_identities
        (I := I) (M := M) g basis gInv hinv)
  simpa [hamiltonPAt, nablaRm04, nablaRic] using
    curvature_divergence_eq_hamiltonP (I := I) basis gInv nablaRm04 nablaRic
      hcore.1 hcore.2.1 hcore.2.2.1 A B D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_curvature_divergence_eq_hamiltonPAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_curvature_divergence_eq_hamiltonPAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_curvature_divergence_eq_hamiltonPAt ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_curvature_divergence_eq_hamiltonPAt

end DifferentialGeometry.PDE.RicciFlow
