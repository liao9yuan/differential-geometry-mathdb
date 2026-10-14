import Submission.DifferentialGeometry.Geometry.Metric.ExteriorPowerRiemannian
import Submission.DifferentialGeometry.Geometry.Metric.BundleMusical
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Bundle.Hom.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.Topology

namespace exteriorPower
open _root_.exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.exteriorPower in
private def dualToAlternating (k : ℕ) :
    ((⋀[ℝ]^k E) →L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := by
  let : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  exact (musicalEquiv k).toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toContinuousLinearEquiv.toContinuousLinearMap

run_cmd do
  let target := ``Submission.exteriorPower.dualToAlternating
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.dualToAlternating target :: scope.openDecls } }

open _root_.exteriorPower in
private theorem dualToAlternating_apply (k : ℕ)
    (a : (⋀[ℝ]^k E) →L[ℝ] ℝ) (v : Fin k → E) :
    dualToAlternating k a v = a (_root_.exteriorPower.ιMulti ℝ k v) := by
  let : CompleteSpace (⋀[ℝ]^k E) := FiniteDimensional.complete ℝ _
  change musicalEquiv k ((InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm a) v = _
  rw [musicalEquiv_apply, InnerProductSpace.toDual_symm_apply]

run_cmd do
  let target := ``Submission.exteriorPower.dualToAlternating_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.dualToAlternating_apply target :: scope.openDecls } }

end exteriorPower

namespace Bundle.ExteriorPower
open _root_.Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

private theorem musicalEquiv_inCoordinates (k : ℕ) (x y : B)
    (hy : y ∈ (_root_.FiberBundle.trivializationAt F V x).baseSet) (u : ⋀[ℝ]^k (V y)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    (_root_.FiberBundle.trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) x
        ⟨y, exteriorPower.musicalEquiv k u⟩).2 =
      exteriorPower.dualToAlternating k
        ((_root_.FiberBundle.trivializationAt ((⋀[ℝ]^k F) →L[ℝ] ℝ)
          (fun x => (⋀[ℝ]^k (V x)) →L[ℝ] ℝ) x ⟨y, innerSL ℝ u⟩).2) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply, hom_trivializationAt_apply]
  apply ContinuousAlternatingMap.ext
  intro v
  rw [exteriorPower.dualToAlternating_apply]
  simp only [ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  change (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial B ℝ) x).continuousLinearMapAt ℝ y
      (exteriorPower.musicalEquiv k u
        (fun i => (_root_.FiberBundle.trivializationAt F V x).symmL ℝ y (v i))) = _
  apply congrArg ((_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial B ℝ) x).continuousLinearMapAt ℝ y)
  rw [exteriorPower.musicalEquiv_apply]
  change ⟪u, _⟫ = ⟪u, _⟫
  congr 1
  rw [Trivialization.symmL_apply _ (show y ∈
      (_root_.FiberBundle.trivializationAt (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) x).baseSet from hy),
    trivializationAt_eq F V k x,
    trivialization_symm_apply F V k (_root_.FiberBundle.trivializationAt F V x) hy,
    exteriorPower.map_apply_ιMulti]
  rfl

run_cmd do
  let target := ``Submission.Bundle.ExteriorPower.musicalEquiv_inCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.ExteriorPower.musicalEquiv_inCoordinates target :: scope.openDecls } }

variable
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  [IsContMDiffRiemannianBundle IB n F V]

theorem contMDiff_musicalEquiv_map (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun p : _root_.Bundle.TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) =>
        (⟨p.1, exteriorPower.musicalEquiv k p.2⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let := isContMDiffRiemannianBundle (IB := IB) (n := n) F V k
  have hdual := (contMDiff_id :
    ContMDiff (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun p : _root_.Bundle.TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) => p)).innerSL_bundle
  intro p
  have hd := hdual p
  rw [_root_.Bundle.contMDiffAt_totalSpace] at hd ⊢
  refine ⟨hd.1, ?_⟩
  have hL : ContMDiff 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ℝ) 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ) n
      (exteriorPower.dualToAlternating (E := F) k) :=
    (exteriorPower.dualToAlternating (E := F) k).contMDiff
  have h := hL.contMDiffAt.comp p hd.2
  apply h.congr_of_eventuallyEq
  let e := _root_.FiberBundle.trivializationAt F V p.1
  have hx : p.1 ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V p.1
  have hbase := hd.1.continuousAt (e.open_baseSet.mem_nhds hx)
  filter_upwards [hbase] with q hq
  exact musicalEquiv_inCoordinates F V k p.1 q.1 hq q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiff_musicalEquiv_map then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiff_musicalEquiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiff_musicalEquiv_map ``Submission.Bundle.ExteriorPower.contMDiff_musicalEquiv_map

theorem contMDiff_musicalEquiv (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] F [⋀^Fin k]→L[ℝ] ℝ)) n
      (fun x => (⟨x, (exteriorPower.musicalEquiv (E := V x) k).toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace ((⋀[ℝ]^k F) →L[ℝ] F [⋀^Fin k]→L[ℝ] ℝ)
          (fun x => (⋀[ℝ]^k (V x)) →L[ℝ] V x [⋀^Fin k]→L[ℝ] ℝ))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact ContMDiff.clm_bundle_of_map (contMDiff_musicalEquiv_map F V k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiff_musicalEquiv then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiff_musicalEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiff_musicalEquiv ``Submission.Bundle.ExteriorPower.contMDiff_musicalEquiv

theorem contMDiff_musicalEquiv_symm (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff IB (IB.prod 𝓘(ℝ, (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)) n
      (fun x => (⟨x, (exteriorPower.musicalEquiv (E := V x) k).symm.toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k F)
          (fun x => (V x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  let : CompleteSpace (⋀[ℝ]^k F) := FiniteDimensional.complete ℝ _
  have h := (contMDiff_musicalEquiv (IB := IB) (n := n) F V k).clm_bundle_inverse
    (fun _ => ContinuousLinearMap.isInvertible_equiv)
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiff_musicalEquiv_symm then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiff_musicalEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiff_musicalEquiv_symm ``Submission.Bundle.ExteriorPower.contMDiff_musicalEquiv_symm

theorem contMDiff_musicalEquiv_symm_map (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiff (IB.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, ⋀[ℝ]^k F)) n
      (fun p : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial B ℝ)) =>
        (⟨p.1, (exteriorPower.musicalEquiv k).symm p.2⟩ :
          TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  let := vector_bundle F V k
  exact (contMDiff_musicalEquiv_symm F V k).clm_bundle_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.ExteriorPower.contMDiff_musicalEquiv_symm_map then
    throwError "Refusing to shadow existing declaration Bundle.ExteriorPower.contMDiff_musicalEquiv_symm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.ExteriorPower.contMDiff_musicalEquiv_symm_map ``Submission.Bundle.ExteriorPower.contMDiff_musicalEquiv_symm_map

end Bundle.ExteriorPower
