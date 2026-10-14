import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F G H K L M N P : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K) (C : ModelWithCorners ℝ G L)
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace K N]
variable [TopologicalSpace P] [ChartedSpace L P]

theorem bijective_mfderiv_comp (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, _root_.Function.Bijective (mfderiv J C g y)) (x : M) :
    Bijective (mfderiv I C (g ∘ f) x) := by
  rw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact (hbg (f x)).comp (hbf x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.bijective_mfderiv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_comp ``Submission.DifferentialGeometry.Topology.Manifold.bijective_mfderiv_comp

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem differentialEquivOfBijective_comp (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, _root_.Function.Bijective (mfderiv J C g y))
    (hcomp : ∀ x : M, _root_.Function.Bijective (mfderiv I C (g ∘ f) x)) (x : M) :
    differentialEquivOfBijective I C (g ∘ f) hcomp x =
      (differentialEquivOfBijective I J f hbf x).trans
        (differentialEquivOfBijective J C g hbg (f x)) := by
  apply ContinuousLinearEquiv.ext
  funext v
  have h := mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  exact congrArg (fun A : E →L[ℝ] G => A v) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_comp ``Submission.DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_comp

variable [FiniteDimensional ℝ G]
variable [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold C ∞ P]

theorem pullbackSmoothOrientation_comp_apply (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, _root_.Function.Bijective (mfderiv J C g y))
    (hcomp : ∀ x : M, _root_.Function.Bijective (mfderiv I C (g ∘ f) x))
    (o : SmoothOrientation C P) (x : M) :
    (pullbackSmoothOrientation I C (g ∘ f) (hg.comp hf) hcomp o).val x =
      (pullbackSmoothOrientation I J f hf hbf
        (pullbackSmoothOrientation J C g hg hbg o)).val x := by
  change tangentOrientationEquiv
      (differentialEquivOfBijective I C (g ∘ f) hcomp x).symm.toLinearEquiv (o.val (g (f x))) =
    tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv
      (tangentOrientationEquiv (differentialEquivOfBijective J C g hbg (f x)).symm.toLinearEquiv
        (o.val (g (f x))))
  rw [differentialEquivOfBijective_comp I J C f g hf hg hbf hbg hcomp x]
  exact tangentOrientationEquiv_trans
    (differentialEquivOfBijective J C g hbg (f x)).symm.toLinearEquiv
    (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv (o.val (g (f x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_comp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_comp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_comp_apply ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_comp_apply

theorem pullbackSmoothOrientation_pushforward (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) (x : M) :
    tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv
      ((pullbackSmoothOrientation I J f hf hbf o).val x) = o.val (f x) := by
  exact tangentOrientationEquiv_symm (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv
    (o.val (f x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_pushforward

theorem pullbackSmoothOrientation_eq_iff (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbf : ∀ x : M, _root_.Function.Bijective (mfderiv I J f x))
    (oN : SmoothOrientation J N) (oM : SmoothOrientation I M) (x : M) :
    (pullbackSmoothOrientation I J f hf hbf oN).val x = oM.val x ↔
      tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv
        (oM.val x) = oN.val (f x) := by
  constructor
  · intro h
    rw [← h]
    exact pullbackSmoothOrientation_pushforward I J f hf hbf oN x
  · intro h
    apply (tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv).injective
    exact (pullbackSmoothOrientation_pushforward I J f hf hbf oN x).trans h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem bijective_mfderiv_open_val (U : TopologicalSpace.Opens M) (x : U) :
    Bijective (mfderiv I I (Subtype.val : U → M) x) := by
  rw [DifferentialGeometry.mfderiv_subtype_val]
  exact Function.bijective_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_open_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.bijective_mfderiv_open_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_open_val ``Submission.DifferentialGeometry.Topology.Manifold.bijective_mfderiv_open_val

omit [IsManifold I ∞ M] in
theorem differentialEquivOfBijective_open_val (U : TopologicalSpace.Opens M)
    (hbij : ∀ x : U, _root_.Function.Bijective (mfderiv I I (Subtype.val : U → M) x)) (x : U) :
    differentialEquivOfBijective I I (Subtype.val : U → M) hbij x =
      ContinuousLinearEquiv.refl ℝ E := by
  apply ContinuousLinearEquiv.ext
  funext v
  change mfderiv I I (Subtype.val : U → M) x v = v
  rw [DifferentialGeometry.mfderiv_subtype_val]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_open_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_open_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_open_val ``Submission.DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_open_val

theorem pullbackSmoothOrientation_open_val_apply (U : TopologicalSpace.Opens M)
    (hbij : ∀ x : U, _root_.Function.Bijective (mfderiv I I (Subtype.val : U → M) x))
    (o : SmoothOrientation I M) (x : U) :
    (pullbackSmoothOrientation I I (Subtype.val : U → M)
      (contMDiff_subtype_val (I := I) (U := U)) hbij o).val x = o.val x.val := by
  change tangentOrientationEquiv
    (differentialEquivOfBijective I I (Subtype.val : U → M) hbij x).symm.toLinearEquiv (o.val x.val) = _
  rw [differentialEquivOfBijective_open_val]
  exact tangentOrientationEquiv_refl (o.val x.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_open_val_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_open_val_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_open_val_apply ``Submission.DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_open_val_apply
end DifferentialGeometry.Topology.Manifold
