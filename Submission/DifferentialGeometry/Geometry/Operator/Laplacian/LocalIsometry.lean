import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LocalPullback
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LocalRestriction
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem laplacian_comp_of_local_isometry_on
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    {Phi : M → N} {U : Set M} (hU : IsOpen U)
    (hPhi : IsLocalDiffeomorphOn I I ∞ Phi U)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I Phi x v) (mfderiv I I Phi x w))
    {f : N → ℝ} {V : Set N} (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) {x : M} (hx : x ∈ U) (hfx : Phi x ∈ V) :
    laplacian (Connection.LeviCivita g) g (f ∘ Phi) x =
      laplacian (Connection.LeviCivita h) h f (Phi x) := by
  let O : _root_.TopologicalSpace.Opens M := ⟨U, hU⟩
  let _ : SigmaCompactSpace O :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I hU)
  let PhiO : O → N := fun z => Phi (z : M)
  have hPhiO : IsLocalDiffeomorph I I ∞ PhiO :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open O hPhi
  have hD (z : O) (v : TangentSpace I z) :
      mfderiv I I PhiO z v = mfderiv I I Phi (z : M) v := by
    have hc := mfderiv_comp_apply z ((hPhi z).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := I) (U := O) (n := ∞)).mdifferentiable (by simp) z) v
    have hi : mfderiv I I (fun w : O => (w : M)) z v = v :=
      mfderiv_subtype_val_apply (I := I) O z v
    exact hc.trans (congrArg (mfderiv I I Phi (z : M)) hi)
  have hmetricO : g.restrictOpen O = localPullMetric h PhiO hPhiO := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, localPullMetric_inner, hD, hD]
    exact hmetric z z.2 v w
  have hPhiSm : ContMDiffOn I I ∞ Phi U := by
    intro z hz
    exact (hPhi ⟨z, hz⟩).contMDiffAt.contMDiffWithinAt
  have hUV : IsOpen (U ∩ Phi ⁻¹' V) :=
    hPhiSm.continuousOn.isOpen_inter_preimage hU hV
  have hfComp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f ∘ Phi) (U ∩ Phi ⁻¹' V) :=
    hf.comp (hPhiSm.mono _root_.Set.inter_subset_left) (fun _ hz => hz.2)
  let xO : O := ⟨x, hx⟩
  calc
    laplacian (Connection.LeviCivita g) g (f ∘ Phi) x =
        laplacian (Connection.LeviCivita (g.restrictOpen O)) (g.restrictOpen O)
          (fun z : O => (f ∘ Phi) (z : M)) xO :=
      (laplacian_restrictOpen_of_contMDiffOn g O hUV hfComp xO ⟨hx, hfx⟩).symm
    _ = laplacian (Connection.LeviCivita (localPullMetric h PhiO hPhiO))
        (localPullMetric h PhiO hPhiO) (f ∘ PhiO) xO := by
      rw [hmetricO]
      rfl
    _ = laplacian (Connection.LeviCivita h) h f (Phi x) :=
      laplacian_localPull_of_contMDiffOn h PhiO hPhiO hV hf xO hfx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_comp_of_local_isometry_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_comp_of_local_isometry_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_comp_of_local_isometry_on ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_comp_of_local_isometry_on

end DifferentialGeometry.Geometry.Operator
