import Submission.DifferentialGeometry.Topology.Manifold.ClopenDecomposition
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable (U : Opens M) (hU : IsClosed (U : Set M))

theorem clopenSumDiffeomorph_mfderiv
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) :
    mfderiv I I (clopenSumDiffeomorph I U hU) p = ContinuousLinearMap.id ℝ E := by
  let V : _root_.TopologicalSpace.Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  let D := clopenSumDiffeomorph I U hU
  cases p with
  | inl q =>
    have hι : ContMDiff I I ∞ (Sum.inl : U → U ⊕ V) := ContMDiff.inl
    have hc := mfderiv_comp (f := (Sum.inl : U → U ⊕ V)) (g := D) q
      (D.contMDiff.mdifferentiableAt (by simp)) (hι.mdifferentiableAt (by simp))
    rw [mfderiv_sumInl (p := Sum.inl q)] at hc
    have hc' : (mfderiv I I (D ∘ (Sum.inl : U → U ⊕ V)) q : E →L[ℝ] E) =
        mfderiv I I D (Sum.inl q) := hc
    have hv : (mfderiv I I (D ∘ (Sum.inl : U → U ⊕ V)) q : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := DifferentialGeometry.mfderiv_subtype_val (I := I) U q
    exact hc'.symm.trans hv
  | inr q =>
    have hι : ContMDiff I I ∞ (Sum.inr : V → U ⊕ V) := ContMDiff.inr
    have hc := mfderiv_comp (f := (Sum.inr : V → U ⊕ V)) (g := D) q
      (D.contMDiff.mdifferentiableAt (by simp)) (hι.mdifferentiableAt (by simp))
    rw [mfderiv_sumInr] at hc
    have hc' : (mfderiv I I (D ∘ (Sum.inr : V → U ⊕ V)) q : E →L[ℝ] E) =
        mfderiv I I D (Sum.inr q) := hc
    have hv : (mfderiv I I (D ∘ (Sum.inr : V → U ⊕ V)) q : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := DifferentialGeometry.mfderiv_subtype_val (I := I) V q
    exact hc'.symm.trans hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_mfderiv ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_mfderiv

theorem clopenSumDiffeomorph_symm_mfderiv (p : M) :
    mfderiv I I (clopenSumDiffeomorph I U hU).symm p = ContinuousLinearMap.id ℝ E := by
  let D := clopenSumDiffeomorph I U hU
  have hc := mfderiv_comp (f := D.symm) (g := D) p
    (D.contMDiff.mdifferentiableAt (by simp)) (D.symm.contMDiff.mdifferentiableAt (by simp))
  rw [clopenSumDiffeomorph_mfderiv] at hc
  have hc' : (mfderiv I I (D ∘ D.symm) p : E →L[ℝ] E) = mfderiv I I D.symm p := hc
  have hm : D ∘ D.symm = id := funext D.apply_symm_apply
  let d : (M → M) → (E →L[ℝ] E) := fun g => mfderiv I I g p
  have hd : (mfderiv I I (D ∘ D.symm) p : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
    (congrArg d hm).trans (mfderiv_id (I := I) (x := p))
  exact hc'.symm.trans hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_symm_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_symm_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_symm_mfderiv ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_symm_mfderiv

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

def clopenSumSmoothOrientation (o : SmoothOrientation I M) :
    SmoothOrientation I (U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) :=
  pullbackSmoothOrientation I I (clopenSumDiffeomorph I U hU)
    (clopenSumDiffeomorph I U hU).contMDiff
    (fun p => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) p).bijective) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation

theorem clopenSumSmoothOrientation_apply (o : SmoothOrientation I M)
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) :
    (clopenSumSmoothOrientation I U hU o).val p = o.val (clopenSumDiffeomorph I U hU p) := by
  let D := clopenSumDiffeomorph I U hU
  let e := differentialEquivOfBijective I I D
    (fun x => (D.mfderivToContinuousLinearEquiv (by simp) x).bijective) p
  have he : e = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : E →L[ℝ] E => A v) (clopenSumDiffeomorph_mfderiv I U hU p)
  change tangentOrientationEquiv e.symm.toLinearEquiv (o.val (D p)) = o.val (D p)
  rw [he]
  exact tangentOrientationEquiv_refl (o.val (D p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_apply

theorem clopenSumSmoothOrientation_pushforward (o : SmoothOrientation I M)
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) :
    tangentOrientationEquiv (differentialEquivOfBijective I I (clopenSumDiffeomorph I U hU)
      (fun x => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
        ((clopenSumSmoothOrientation I U hU o).val p) = o.val (clopenSumDiffeomorph I U hU p) :=
  pullbackSmoothOrientation_pushforward I I (clopenSumDiffeomorph I U hU)
    (clopenSumDiffeomorph I U hU).contMDiff
    (fun x => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) x).bijective) o p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_pushforward

theorem clopenSumSmoothOrientation_symm_preserves (o : SmoothOrientation I M) (p : M) :
    tangentOrientationEquiv (differentialEquivOfBijective I I (clopenSumDiffeomorph I U hU).symm
      (fun x => ((clopenSumDiffeomorph I U hU).symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
        (o.val p) = (clopenSumSmoothOrientation I U hU o).val ((clopenSumDiffeomorph I U hU).symm p) := by
  let D := clopenSumDiffeomorph I U hU
  let e := differentialEquivOfBijective I I D.symm
    (fun x => (D.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p
  have he : e = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : E →L[ℝ] E => A v) (clopenSumDiffeomorph_symm_mfderiv I U hU p)
  change tangentOrientationEquiv e.toLinearEquiv (o.val p) = _
  rw [he]
  have hr : tangentOrientationEquiv (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv (o.val p) = o.val p :=
    tangentOrientationEquiv_refl (o.val p)
  exact hr.trans ((congrArg o.val (D.apply_symm_apply p).symm).trans
    (clopenSumSmoothOrientation_apply I U hU o (D.symm p)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_symm_preserves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_symm_preserves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_symm_preserves ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumSmoothOrientation_symm_preserves
end DifferentialGeometry.Topology.Manifold
