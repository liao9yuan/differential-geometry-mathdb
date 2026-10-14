import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Contraction
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.DomainPermutation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.instCompleteSpaceE_keystone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.instCompleteSpaceE_keystone target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem interiorProductField_jointContMDiffOn_vecJoint (s : ℕ) {S : Set ℝ}
    (X : ∀ p : M × ℝ, TangentSpace I p.1)
    (hX : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (X p))
      ((Set.univ : Set M) ×ˢ S))
    (α : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 1) I p.1)
    (hα : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1 (α p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s p.1 (X p) (α p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hα' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z)).mp (hα p₀ hp₀)
  have hX' := (Bundle.contMDiffWithinAt_totalSpace (F := E) (E := TangentSpace I)).mp (hX p₀ hp₀)
  have h_combine :
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E) ∞
        (fun p : M × ℝ => Tensor0SBundle.modelInteriorBilinear ℝ E s
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2)
          ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
            (fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) x₀ ⟨p.1, α p⟩).2))
        ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := Tensor0SBundle.modelInteriorBilinear ℝ E s)).clm_apply
      hX'.2).clm_apply hα'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 with hsymmL
    set gtilde : E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀ ⟨p.1, X p⟩).2 with hgtilde
    change (α p) (@Fin.cons s (fun _ => E) ((X p : TangentSpace I p.1) : E) (fun i => symmL (v i)))
      =
      (α p) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p : TangentSpace I p.1) : E) = symmL gtilde
      have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx (X p)
      have hcl : (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p.1 (X p) =
          gtilde := by
        change (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p.1 (X p) = _
        rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl
  · have hx : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀
    apply ContinuousMultilinearMap.ext
    intro v
    set symmL := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 with hsymmL
    set gtilde : E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀ ⟨p₀.1, X p₀⟩).2 with hgtilde
    change (α p₀) (@Fin.cons s (fun _ => E) ((X p₀ : TangentSpace I p₀.1) : E)
        (fun i => symmL (v i))) =
      (α p₀) (fun i => symmL (@Fin.cons s (fun _ => E) gtilde v i))
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change ((X p₀ : TangentSpace I p₀.1) : E) = symmL gtilde
      have hx0 : p₀.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
      have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := ℝ) hx0 (X p₀)
      have hcl : (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p₀.1 (X p₀) =
          gtilde := by
        change (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ p₀.1 (X p₀) = _
        rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hx0]
      rw [hcl] at h
      exact h.symm
    · intro j
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.interiorProductField_jointContMDiffOn_vecJoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.interiorProductField_jointContMDiffOn_vecJoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.interiorProductField_jointContMDiffOn_vecJoint ``Submission.DifferentialGeometry.interiorProductField_jointContMDiffOn_vecJoint

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem contractTraceField_joint_pointwise (r s : ℕ) (x₀ : M) (z : M)
    (Tz : Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)
    (hx : z ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    (_root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contractTrace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2
          =
      Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (1 + r) (s + 1)
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (1 + r)
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  set L : E →L[ℝ] E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef
  set Linv : E →L[ℝ] E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ z with
    hLinvdef
  set Tx : Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E :=
    Tensor0SBundle.tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) z Tz with hTxdef
  have hL : L.comp Linv = ContinuousLinearMap.id ℝ E := by
    ext y
    exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ) hx y
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SSpace k I z) (v : Fin k → E),
      (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).linearMapAt ℝ z) =
        fun y => (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀ ⟨z, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SBundle.Tensor0SModel k ℝ E) (u : Fin k → E),
      ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ y : E, L (Linv y) = y := by
      intro y
      have h := congrArg (fun f : E →L[ℝ] E => f y) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i; exact (h_inv (u i)).symm
    calc
      ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U) u
          = ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt ℝ z
            ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).symmL ℝ z U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace k I y) x₀).continuousLinearMapAt_symmL
              (R := ℝ) hx]
  have h_input :
      ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I y) x₀ ⟨z, Tz⟩).2) =
      (Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (s + 1) L).comp
        (Tx.comp (Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace (s + 1) I y) x₀).continuousLinearMapAt ℝ z
        ((Tz) ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (s + 1) L)
        (Tx ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    have hβ :
        (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β =
          Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := z)
            ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β) := by
      apply Tensor0SBundle.Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro u
      change Tensor0SBundle.Tensor0SSpace.toModel
          ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (1 + r) ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace (1 + r) I y) x₀).symmL ℝ z β) u =
        ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) (1 + r) Linv) β) u
      have hs := h_symmL (1 + r) β u
      exact hs
    rw [hβ]; rfl
  have h_output :
      (_root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x₀
        ⟨z, Tensor0SBundle.contractTrace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz⟩).2
          =
      (Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) s L).comp
        ((Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s Tx).comp
          (Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) x₀).continuousLinearMapAt ℝ z
        ((Tensor0SBundle.contractTrace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s z Tz)
          ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β)) v =
      ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) s L)
        ((Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s Tx)
          ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) r Linv) β))) v
    rw [h_cLMAt, Tensor0SBundle.model_covariantChange_apply]
    change ((Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s
          ((Tensor0SBundle.tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) z) Tz))
        ((Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) r z)
          ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β))) (fun i => L (v i))
              =
      (((Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s) Tx)
        ((Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) r Linv) β)) (fun i => L (v i))
    have hβ2 : (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) r z)
          ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) x₀).symmL ℝ z β) =
          (Tensor0SBundle.modelCovariantChange (𝕜 := ℝ) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      rw [Tensor0SBundle.model_covariantChange_apply]
      exact h_symmL r β u
    rw [hβ2]
  rw [h_input, h_output]
  exact (Tensor0SBundle.model_contract_trace_naturality (𝕜 := ℝ) (E := E)
    r s L Linv hL Tx).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.contractTraceField_joint_pointwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.contractTraceField_joint_pointwise target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem contractTraceField_jointContMDiffOn (r s : ℕ) {S : Set ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I p.1)
    (hT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) p.1 (T p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1
        (Tensor0SBundle.contractTrace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s p.1 (T p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (1 + r) (s + 1)
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (1 + r)
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hT' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z)).mp (hT p₀ hp₀)
  have hTrace : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r s
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel (1 + r) (s + 1) ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace (1 + r) (s + 1) I z) x₀ ⟨p.1, T p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (Tensor0SBundle.modelContractTrace (𝕜 := ℝ) (E := E) r
      s).contMDiff.contMDiffAt.comp_contMDiffWithinAt
      p₀ hT'.2
  refine hTrace.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p.1 (T p) hx
  · have hx : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact contractTraceField_joint_pointwise (I := I) r s x₀ p₀.1 (T p₀) hx0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contractTraceField_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contractTraceField_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contractTraceField_jointContMDiffOn ``Submission.DifferentialGeometry.contractTraceField_jointContMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem domDomCongrField_joint_pointwise {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x₀ : M) (z : M)
    (Zz : Tensor0SBundle.Tensor0SSpace d I z)
    (hx : z ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀
        ⟨z, Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel Zz))⟩).2 =
      ContinuousMultilinearMap.domDomCongr ρ
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, Zz⟩).2) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  set L : E →L[ℝ] E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ z with hLdef
  have h_cLMAt : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).continuousLinearMapAt ℝ z U v =
      U (fun i => L (v i)) := by
    intro U v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
    rfl
  have h_coord : ∀ (U : Tensor0SBundle.Tensor0SSpace d I z) (v : Fin d → E),
      (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, U⟩).2 v =
      U (fun i => L (v i)) := by
    intro U v
    rw [← h_cLMAt U v, Trivialization.continuousLinearMapAt_apply,
      show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).linearMapAt ℝ z) =
        fun y => (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀ ⟨z, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hx]
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [h_coord, h_coord]
  have hof : ∀ (m : Fin d → E),
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
        (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m =
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
    intro m
    have h := Tensor0SBundle.Tensor0SSpace.toModel_ofModel (𝕜 := ℝ) (I := I) (x := z)
      (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))
    calc (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
            (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m
        = Tensor0SBundle.Tensor0SSpace.toModel
            (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := z)
              (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz))) m
                := rfl
      _ = (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SBundle.Tensor0SSpace.toModel Zz)) m := by
            rw [h]
  rw [hof, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.domDomCongrField_joint_pointwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.domDomCongrField_joint_pointwise target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem domDomCongrField_jointContMDiffOn {d : ℕ} (ρ : Equiv.Perm (Fin d)) {S : Set ℝ}
    (Z : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (Z p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z p)))))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hZ' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hZ p₀ hp₀)
  have hcongr : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => ContinuousMultilinearMap.domDomCongr ρ
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ ⟨p.1, Z p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel d ℝ E => ContinuousMultilinearMap.domDomCongr ρ U) :=
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
        ρ).toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hZ'.2
  refine hcongr.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p.1 (Z p) hx).symm
  · have hx : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
      _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀
    have hx0 : p₀.1 ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by rw [← hx₀]; exact hx
    exact (domDomCongrField_joint_pointwise (I := I) ρ x₀ p₀.1 (Z p₀) hx0).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.domDomCongrField_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.domDomCongrField_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.domDomCongrField_jointContMDiffOn ``Submission.DifferentialGeometry.domDomCongrField_jointContMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpace_add {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_add (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpace_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpace_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpace_add ``Submission.DifferentialGeometry.jointTotalSpace_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpace_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpace_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpace_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpace_sub ``Submission.DifferentialGeometry.jointTotalSpace_sub

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpace_smul {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine
    ((contMDiffWithinAt_const (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpace_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpace_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpace_smul ``Submission.DifferentialGeometry.jointTotalSpace_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    rw [Pi.add_apply]
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · rw [Pi.add_apply]
    exact (e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpaceRS_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpaceRS_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpaceRS_add ``Submission.DifferentialGeometry.jointTotalSpaceRS_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_const_smul {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul (I := 𝓘(ℝ, ℝ))
    hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpaceRS_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpaceRS_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpaceRS_const_smul ``Submission.DifferentialGeometry.jointTotalSpaceRS_const_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.jointTotalSpaceRS_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.jointTotalSpaceRS_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.jointTotalSpaceRS_sub ``Submission.DifferentialGeometry.jointTotalSpaceRS_sub

end DifferentialGeometry
