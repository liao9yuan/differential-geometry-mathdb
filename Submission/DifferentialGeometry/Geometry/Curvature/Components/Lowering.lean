import Submission.DifferentialGeometry.Geometry.Curvature.Components.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

def Rm04LowersRm13At
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall X Y Z W : TangentSpace I x,
    Rm04 (vec4 X Y Z W) =
      Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At ``Submission.DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At

theorem rm04RealizesLower
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (hLower : forall x : M,
      Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x)) :
    rm04RealizesConnection (I := I) g cov Rm04 := by
  intro X Y Z W x
  rw [hLower x (X x) (Y x) (Z x) (W x)]
  have h := hRm13 X Y Z x
    (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) (W x)))
  simpa [tangentFlatLinear_apply, cotangentToDual_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04RealizesLower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04RealizesLower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04RealizesLower ``Submission.DifferentialGeometry.Geometry.Curvature.rm04RealizesLower

theorem rm04LowersRm13At_of_realizes
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) :
    Rm04LowersRm13At (I := I) g x (Rm13 x) (Rm04 x) := by
  intro X Y Z W
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x W
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ysec, hYsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Y
  obtain ⟨Zsec, hZsec⟩ :=
    ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := (TangentSpace I : M -> Type _))
      (n := (⊤ : ℕ∞)) x Z
  let alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W)
  have h04 := hRm04 Xsec Ysec Zsec Wsec x
  have h13 := hRm13 Xsec Ysec Zsec x alpha
  have h04' :
      Rm04 x (vec4 X Y Z W) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p)) x) := by
    simpa [hWsec, hXsec, hYsec, hZsec] using h04
  have h13' :
      Rm13 x
          (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
          (vec3 X Y Z) =
        g.inner x W
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p) (fun p : M => Zsec p)) x) := by
    simpa [alpha, hXsec, hYsec, hZsec, tangentFlatLinear_apply, cotangentToDual_apply] using
      h13
  exact h04'.trans h13'.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes ``Submission.DifferentialGeometry.Geometry.Curvature.rm04LowersRm13At_of_realizes

def Rm13MetricSkewAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (Rm13 : Tensor13At (I := I) (M := M) x) : Prop :=
  forall W X Y Z : TangentSpace I x,
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z) =
      -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Rm13MetricSkewAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Rm13MetricSkewAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Rm13MetricSkewAt ``Submission.DifferentialGeometry.Geometry.Curvature.Rm13MetricSkewAt

def Rm04OutputSkewAt
    (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  forall X Y Z W : TangentSpace I x,
    Rm04 (vec4 X Y Z W) = -Rm04 (vec4 X Y W Z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt ``Submission.DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt

theorem rm13MetricSkewAt_of_rm04_outputSkew
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (hSkew : Rm04OutputSkewAt (I := I) Rm04) :
    Rm13MetricSkewAt (I := I) g x Rm13 := by
  intro W X Y Z
  calc
    Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) W))
        (vec3 X Y Z)
        = Rm04 (vec4 X Y Z W) := (hLower X Y Z W).symm
    _ = -Rm04 (vec4 X Y W Z) := hSkew X Y Z W
    _ = -Rm13 (dualToCotangent (I := I) ((tangentFlatLinear (I := I) g x) Z))
        (vec3 X Y W) := by rw [hLower X Y W Z]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_rm04_outputSkew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_rm04_outputSkew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_rm04_outputSkew ``Submission.DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_rm04_outputSkew

theorem rm13MetricSkewAt_of_realizes_outputSkew
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (hRm04 : rm04RealizesConnection (I := I) g cov Rm04)
    {x : M}
    (hSkew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    Rm13MetricSkewAt (I := I) g x (Rm13 x) :=
  rm13MetricSkewAt_of_rm04_outputSkew (I := I) g (Rm13 x) (Rm04 x)
    (rm04LowersRm13At_of_realizes (I := I) g cov Rm13 Rm04 hRm13 hRm04 x)
    hSkew

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_realizes_outputSkew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_realizes_outputSkew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_realizes_outputSkew ``Submission.DifferentialGeometry.Geometry.Curvature.rm13MetricSkewAt_of_realizes_outputSkew
end DifferentialGeometry.Geometry.Curvature
