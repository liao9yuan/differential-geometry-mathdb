import Submission.DifferentialGeometry.Tensor.RSTensor.Smoothness.Parametric
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.ParametricSmoothness
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Spectral (slotExtendFib_apply)

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

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem curriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z)).mp (hA p₀ hp₀)
  have hcurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) x₀ ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SBundle.Tensor0SModel (d + 1) ℝ E =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hA'.2
  refine hcurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p.2⟩) x₀ p.1 hx
    rw [TensorMultilinear.curriedSection] at hc
    exact hc
  · have hx0 : p₀.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀
    have hc := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun z : M => A ⟨z, p₀.2⟩) x₀ p₀.1 hx0
    rw [TensorMultilinear.curriedSection] at hc
    exact hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.curriedField_jointContMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.curriedField_jointContMDiffOn target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem uncurriedField_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace d I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hG' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z)).mp (hG p₀ hp₀)
  have huncurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
      (fun p : M × ℝ => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
        ((_root_.FiberBundle.trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) x₀
          ⟨p.1, G p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E) ∞
        (fun U : E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hG'.2
  have hpt : ∀ p : M × ℝ,
      p.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace d I y) x₀).baseSet →
      (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (d + 1) I y) x₀
          ⟨p.1, (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm (G p)⟩).2 =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm
          ((_root_.FiberBundle.trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
            (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace d I y) x₀
            ⟨p.1, G p⟩).2) := by
    rintro ⟨x, t⟩ hz
    have hUcurry : TensorMultilinear.curriedSection (I := I) (M := M)
        (fun y : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, t⟩)) x =
          G ⟨x, t⟩ := by
      rw [TensorMultilinear.curriedSection]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hfwd := TensorMultilinear.trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun y : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d y).symm (G ⟨y, t⟩)) x₀ x hz
    rw [hUcurry] at hfwd
    have hback := congrArg
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => E) ℝ).symm hfwd
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hback.symm
  refine huncurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpt p hx
  · have hx0 : p₀.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
        (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀
    exact hpt p₀ hx0

run_cmd do
  let target := ``Submission.DifferentialGeometry.uncurriedField_jointContMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.uncurriedField_jointContMDiffOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem slotInsertEndo0Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S) A hA
  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace d I z) p.1
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
        (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace d I x)
      (φ := fun p : M × ℝ => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p))
      (S := S)
    intro Z
    have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hΛZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Λ p (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) :=
      ContMDiffOn.clm_bundle_apply (b := Prod.fst) hΛ hZjoint
    have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hΛZ
    refine happ.congr (fun p _ => ?_)
    rfl
  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
    (fun p : M × ℝ => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)).comp (Λ p)) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  exact slotInsertEndoFib_zero (I := I) (M := M) d p.1 (Λ p) (A p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.slotInsertEndo0Field_apply_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.slotInsertEndo0Field_apply_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.slotInsertEndo0Field_apply_jointContMDiffOn ``Submission.DifferentialGeometry.slotInsertEndo0Field_apply_jointContMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem slotInsertEndo1Field_apply_jointContMDiffOn {d : ℕ} {S : Set ℝ}
    (Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hΛ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (Λ p))
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (d + 2) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 2) I z) p.1
        (slotInsertEndoFib (I := I) (M := M) (d + 2) 1 p.1 (Λ p) (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hcurry := curriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S) A hA
  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
        ((slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (d + 1) I x)
      (φ := fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p)))
      (S := S)
    intro Z
    have hcurryZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (d + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (d + 1) I z) p.1
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)))
        ((Set.univ : Set M) ×ˢ S) := by
      have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
          ((Set.univ : Set M) ×ˢ S) :=
        Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
      exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hcurry hZjoint
    have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := d) (S := S)
      (Λ := Λ) hΛ
      (A := fun p : M × ℝ =>
        tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p) (Z p.1)) hcurryZ
    refine happ.congr (fun p _ => ?_)
    rfl
  have huncurry := uncurriedField_jointContMDiffOn (I := I) (M := M) (d := d + 1) (S := S)
    (fun p : M × ℝ => (slotInsertEndoFib (I := I) (M := M) (d + 1) 0 p.1 (Λ p)).comp
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (d + 1) p.1 (A p))) hcomp
  refine huncurry.congr (fun p _ => ?_)
  congr 1
  rw [show (1 : Fin (d + 2)) = (0 : Fin (d + 1)).succ from rfl,
    slotInsertEndoFib_succ (I := I) (M := M) (d + 1) 0 p.1 (Λ p),
    slotExtendFib_apply (I := I) (M := M) (d + 1) (d + 1) p.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.slotInsertEndo1Field_apply_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.slotInsertEndo1Field_apply_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.slotInsertEndo1Field_apply_jointContMDiffOn ``Submission.DifferentialGeometry.slotInsertEndo1Field_apply_jointContMDiffOn

end DifferentialGeometry
