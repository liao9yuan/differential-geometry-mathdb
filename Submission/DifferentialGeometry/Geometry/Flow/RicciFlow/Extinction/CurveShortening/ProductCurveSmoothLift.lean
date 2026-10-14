import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem isInvertible_of_injective_realLine (f : ℝ →L[ℝ] ℝ)
    (hf : Function.Injective f) : f.IsInvertible := by
  have hf1 : f 1 ≠ 0 := by
    intro h
    refine one_ne_zero (hf ?_)
    rw [h, map_zero]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · refine ContinuousLinearMap.ext fun x => ?_
    have hx : ∀ y : ℝ, f y = y * f 1 := fun y => by
      simpa [smul_eq_mul] using f.map_smul y (1 : ℝ)
    have hgy : ∀ y : ℝ, ((f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) y = (f 1)⁻¹ * y :=
      fun y => rfl
    rw [ContinuousLinearMap.comp_apply, hgy, hx ((f 1)⁻¹ * x),
      ContinuousLinearMap.id_apply]
    field_simp
  · refine ContinuousLinearMap.ext fun x => ?_
    have hx : ∀ y : ℝ, f y = y * f 1 := fun y => by
      simpa [smul_eq_mul] using f.map_smul y (1 : ℝ)
    have hgy : ∀ y : ℝ, ((f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) y = (f 1)⁻¹ * y :=
      fun y => rfl
    rw [ContinuousLinearMap.comp_apply, hx x, hgy, ContinuousLinearMap.id_apply]
    field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isInvertible_of_injective_realLine
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isInvertible_of_injective_realLine target :: scope.openDecls } }

private theorem isLocalDiffeomorphAt_addCircle_coe (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t := by
  have hinv : ∀ y ∈ (_root_.Set.univ : Set ℝ),
      (fderiv ℝ
        (writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) y
          (fun s : ℝ => (s : AddCircle (1 : ℝ))))
        (extChartAt 𝓘(ℝ, ℝ) y y)).IsInvertible := by
    intro y _
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ => (s : AddCircle (1 : ℝ))) y :=
      AddCircle.contMDiff_coe.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
    have hderiv : fderiv ℝ
          (writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) y
            (fun s : ℝ => (s : AddCircle (1 : ℝ))))
          (extChartAt 𝓘(ℝ, ℝ) y y) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) y := by
      rw [hmd.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
    rw [hderiv]
    exact isInvertible_of_injective_realLine _
      (AddCircle.bijective_mfderiv_coe y).1
  obtain ⟨Φ, htΦ, -, hEq⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := AddCircle (1 : ℝ))
      (x := t) isOpen_univ (_root_.Set.mem_univ t) AddCircle.contMDiff_coe.contMDiffOn hinv
  exact ⟨Φ, htΦ, hEq⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorphAt_addCircle_coe
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.isLocalDiffeomorphAt_addCircle_coe target :: scope.openDecls } }

theorem contDiffOn_of_contMDiffOn_addCircle_lift {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → AddCircle (1 : ℝ)} {y : ℝ × ℝ → ℝ}
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f U)
    (hy : ∀ p, (y p : AddCircle (1 : ℝ)) = f p)
    (hyc : ContinuousOn y U) : ContDiffOn ℝ ∞ y U := by
  intro q hq
  obtain ⟨Φ, hqΦ, hEqΦ⟩ := isLocalDiffeomorphAt_addCircle_coe (y q)
  have hΦ : Φ (y q) = f q := (hEqΦ hqΦ).symm.trans (hy q)
  have hfq : f q ∈ Φ.target := by
    rw [← hΦ]
    exact Φ.toPartialEquiv.map_source hqΦ
  have hsymm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (Φ.symm : AddCircle (1 : ℝ) → ℝ)
      (f q) :=
    Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hfq)
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      ((Φ.symm : AddCircle (1 : ℝ) → ℝ) ∘ f) U q :=
    ContMDiffWithinAt.comp q hsymm.contMDiffWithinAt (hf q hq) (fun _ _ => _root_.Set.mem_univ _)
  have hpt : y q = Φ.symm (f q) := by
    rw [← Φ.toPartialEquiv.left_inv hqΦ, hΦ]
    rfl
  have heq : y =ᶠ[𝓝[U] q] (Φ.symm : AddCircle (1 : ℝ) → ℝ) ∘ f := by
    filter_upwards [(hyc q hq).preimage_mem_nhdsWithin (Φ.open_source.mem_nhds hqΦ),
      (hf q hq).continuousWithinAt.preimage_mem_nhdsWithin (Φ.open_target.mem_nhds hfq)]
      with p hyp hfp
    have hp : Φ (y p) = f p := (hEqΦ hyp).symm.trans (hy p)
    rw [← Φ.toPartialEquiv.left_inv hyp, hp]
    rfl
  exact (contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp).congr_of_eventuallyEq heq hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contDiffOn_of_contMDiffOn_addCircle_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contDiffOn_of_contMDiffOn_addCircle_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contDiffOn_of_contMDiffOn_addCircle_lift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contDiffOn_of_contMDiffOn_addCircle_lift

omit [CompleteSpace E] in
private theorem contMDiff_fst_quotientProductAtlas (A : QuotientProductAtlas I M) [I.Boundaryless] :
    letI := A.charts
    letI := A.smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (Prod.fst : M × Surgery.Topology.Circle → M) := by
  let := A.charts
  let := A.smoothManifold
  intro z
  obtain ⟨w, hw⟩ := surjective_productCoverProjection (M := M) z
  obtain ⟨Φ, hwΦ, hEqΦ⟩ := isLocalDiffeomorph_productCoverProjection (I := I) (M := M) A w
  have hzΦ : z ∈ Φ.target := by
    rw [← hw, hEqΦ hwΦ]
    exact Φ.toPartialEquiv.map_source hwΦ
  have hsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
      (Prod.fst : M × Surgery.Topology.Circle → M) Φ.target := by
    refine ((contMDiff_fst (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).comp_contMDiffOn
      Φ.symm.contMDiffOn_toFun).congr (fun z' hz' => ?_)
    have h1 : Φ (Φ.symm z') = z' := Φ.toPartialEquiv.right_inv hz'
    have h2 : productCoverProjection (Φ.symm z') = Φ (Φ.symm z') :=
      hEqΦ (Φ.toPartialEquiv.map_target hz')
    change Prod.fst z' = Prod.fst ((Φ.symm : M × Surgery.Topology.Circle → M × ℝ) z')
    calc Prod.fst z' = Prod.fst (Φ (Φ.symm z')) := by rw [h1]
      _ = Prod.fst (productCoverProjection (Φ.symm z')) := by rw [h2]
      _ = Prod.fst (Φ.symm z') := rfl
  exact hsmooth.contMDiffAt (Φ.open_target.mem_nhds hzΦ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiff_fst_quotientProductAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiff_fst_quotientProductAtlas target :: scope.openDecls } }

omit [CompleteSpace E] in
private theorem contMDiff_snd_quotientProductAtlas (A : QuotientProductAtlas I M) [I.Boundaryless] :
    letI := A.charts
    letI := A.smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) := by
  let := A.charts
  let := A.smoothManifold
  intro z
  obtain ⟨w, hw⟩ := surjective_productCoverProjection (M := M) z
  obtain ⟨Φ, hwΦ, hEqΦ⟩ := isLocalDiffeomorph_productCoverProjection (I := I) (M := M) A w
  have hzΦ : z ∈ Φ.target := by
    rw [← hw, hEqΦ hwΦ]
    exact Φ.toPartialEquiv.map_source hwΦ
  have hsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) Φ.target := by
    refine (AddCircle.contMDiff_coe.comp_contMDiffOn
      ((contMDiff_snd (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).comp_contMDiffOn
        Φ.symm.contMDiffOn_toFun)).congr (fun z' hz' => ?_)
    have h1 : Φ (Φ.symm z') = z' := Φ.toPartialEquiv.right_inv hz'
    have h3 : productCoverProjection (Φ.symm z') = Φ (Φ.symm z') :=
      hEqΦ (Φ.toPartialEquiv.map_target hz')
    calc (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) z'
        = Prod.snd (Φ (Φ.symm z')) := by rw [h1]
      _ = Prod.snd (productCoverProjection (Φ.symm z')) := by rw [h3]
      _ = (((Φ.symm : M × Surgery.Topology.Circle → M × ℝ) z').2 :
          Surgery.Topology.Circle) := rfl
  exact hsmooth.contMDiffAt (Φ.open_target.mem_nhds hzΦ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiff_snd_quotientProductAtlas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.contMDiff_snd_quotientProductAtlas target :: scope.openDecls } }

namespace ProductCurve

omit [CompleteSpace E] in
theorem projection_smoothOn_of_map_smoothOn (A : QuotientProductAtlas I M) [I.Boundaryless]
    (c : ProductCurve M) (J : Set ℝ)
    (hm : letI := A.charts
      letI := A.smoothManifold
      c.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) J) :
    c.projection.SmoothOn (I := I) J := by
  let := A.charts
  let := A.smoothManifold
  refine ((contMDiff_fst_quotientProductAtlas (I := I) (M := M) A).comp_contMDiffOn hm).congr
    (fun p _ => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_smoothOn_of_map_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_smoothOn_of_map_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_smoothOn_of_map_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.projection_smoothOn_of_map_smoothOn

omit [CompleteSpace E] in
theorem contDiffOn_height_of_map_smoothOn_of_continuousOn (A : QuotientProductAtlas I M)
    [I.Boundaryless] (c : ProductCurve M) (J : Set ℝ)
    (hyc : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J))
    (hm : letI := A.charts
      letI := A.smoothManifold
      c.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J) := by
  let := A.charts
  let := A.smoothManifold
  refine contDiffOn_of_contMDiffOn_addCircle_lift ?_ (fun p => c.lift_eq p.1 p.2) hyc
  refine ((contMDiff_snd_quotientProductAtlas (I := I) (M := M) A).comp_contMDiffOn hm).congr
    (fun p _ => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.contDiffOn_height_of_map_smoothOn_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.contDiffOn_height_of_map_smoothOn_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.contDiffOn_height_of_map_smoothOn_of_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.contDiffOn_height_of_map_smoothOn_of_continuousOn

omit [CompleteSpace E] in
theorem coverSmoothLift_of_continuousOn_height (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (c : ProductCurve M) (J : Set ℝ)
    (hyc : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J)) :
    CoverSmoothLift A c J := by
  intro hm
  exact ⟨c.projection_smoothOn_of_map_smoothOn A J hm,
    c.contDiffOn_height_of_map_smoothOn_of_continuousOn A J hyc hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverSmoothLift_of_continuousOn_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverSmoothLift_of_continuousOn_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverSmoothLift_of_continuousOn_height ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.coverSmoothLift_of_continuousOn_height

end ProductCurve

def circleHeightJumpCurve : ProductCurve ℝ where
  map := fun _ t => (0, (t : Surgery.Topology.Circle))
  y := fun _ t => t + (if 0 ≤ t then 1 else 0)
  degree := 0
  lift_eq := by
    intro x t
    have hk : (((if 0 ≤ t then (1 : ℝ) else 0) : ℝ) : Surgery.Topology.Circle) = 0 := by
      by_cases h : 0 ≤ t
      · rw [if_pos h, AddCircle.coe_period]
      · rw [if_neg h, AddCircle.coe_zero]
    rw [AddCircle.coe_add, hk, add_zero]
  increment := by
    intro x t
    simp [Int.cast_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJumpCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJumpCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJumpCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJumpCurve

private def circleHeightJump (p : ℝ × ℝ) : ℝ :=
  circleHeightJumpCurve.y p.1 p.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJump
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJump target :: scope.openDecls } }

private theorem circleHeightJump_not_continuousAt_zero :
    ¬ ContinuousAt circleHeightJump ((0 : ℝ), (0 : ℝ)) := by
  intro hca
  have h1 : circleHeightJump ((0 : ℝ), (0 : ℝ)) = 1 := by
    simp [circleHeightJump, circleHeightJumpCurve]
  have htend : Filter.Tendsto circleHeightJump (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (1 : ℝ)) := by
    have := hca.tendsto
    rwa [h1] at this
  have hct : Filter.Tendsto (fun t : ℝ => circleHeightJump (0, t)) (𝓝 (0 : ℝ))
      (𝓝 (1 : ℝ)) :=
    htend.comp ((continuous_const.prodMk continuous_id).tendsto (0 : ℝ))
  have hA : {t : ℝ | 1 / 2 < circleHeightJump (0, t)} ∈ 𝓝 (0 : ℝ) :=
    hct.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hA
  have hhalf : 0 < ε / 2 := by linarith
  have ht : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, show (-(ε / 2) - 0 : ℝ) = -(ε / 2) from by ring]
    rw [abs_neg, abs_of_pos hhalf]
    linarith
  have hgt : (1 : ℝ) / 2 < circleHeightJump (0, -(ε / 2)) := hε ht
  have hval : circleHeightJump (0, -(ε / 2)) = -(ε / 2) := by
    simp only [circleHeightJump, circleHeightJumpCurve]
    rw [if_neg (by linarith : ¬ ((0 : ℝ) ≤ -(ε / 2))), add_zero]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJump_not_continuousAt_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.circleHeightJump_not_continuousAt_zero target :: scope.openDecls } }

theorem not_contDiffOn_height_circleHeightJumpCurve :
    ¬ ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => circleHeightJumpCurve.y p.1 p.2)
      ((_root_.Set.univ : Set ℝ) ×ˢ (_root_.Set.univ : Set ℝ)) := by
  intro h
  exact circleHeightJump_not_continuousAt_zero (h.continuousOn.continuousAt (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_contDiffOn_height_circleHeightJumpCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_contDiffOn_height_circleHeightJumpCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_contDiffOn_height_circleHeightJumpCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_contDiffOn_height_circleHeightJumpCurve

theorem not_coverSmoothLift_circleHeightJumpCurve (A : QuotientProductAtlas 𝓘(ℝ, ℝ) ℝ) :
    ¬ ProductCurve.CoverSmoothLift A circleHeightJumpCurve Set.univ := by
  let := A.charts
  let := A.smoothManifold
  intro h
  have hg : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => ((0 : ℝ), p.2)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact ContMDiff.prodMap contMDiff_const contMDiff_id
  have hm : circleHeightJumpCurve.map.SmoothOn (I := (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      Set.univ := by
    refine ((A.cover_smooth.comp hg).contMDiffOn).congr (fun p _ => ?_)
    rfl
  exact not_contDiffOn_height_circleHeightJumpCurve (h hm).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_coverSmoothLift_circleHeightJumpCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_coverSmoothLift_circleHeightJumpCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_coverSmoothLift_circleHeightJumpCurve ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.not_coverSmoothLift_circleHeightJumpCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
