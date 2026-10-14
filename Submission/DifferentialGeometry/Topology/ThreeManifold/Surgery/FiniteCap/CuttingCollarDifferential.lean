import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarDifferential
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem mfderiv_cuttingCollarCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ))
    (v : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 1)) :
    let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    mfderiv IR IC (cuttingCollarCylinderMap hδ b) q (v, t) =
      (v, cuttingSign b * mvfderiv (I := (𝓡∂ 1))
        (Subtype.val : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) → ℝ) q.2 t) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
  dsimp only
  erw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := IR) (J := IC)
    (cuttingCollarCylinderMap hδ b) q]
  change mfderiv IR IC
    (fun p : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) =>
      (p.1, cuttingSign b + cuttingSign b * p.2.val)) q (v, t) = _
  let g : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) → ℝ :=
    fun s => cuttingSign b + cuttingSign b * s.val
  have hs := (isSmoothEmbedding_halfClosedInterval_inclusion (cuttingCollarWidth_pos hδ)).contMDiff
  have hg : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) g q.2 :=
    (contMDiff_const.add (contMDiff_const.mul hs)).mdifferentiableAt (by simp)
  change mfderiv IR IC (Prod.map (id : S2 → S2) g) q (v, t) = _
  rw [mfderiv_prodMap mdifferentiableAt_id hg, mfderiv_id]
  change (v, mfderiv (𝓡∂ 1) 𝓘(ℝ) g q.2 t) = _
  congr 1
  have hm := congrArg (fun D => D t)
    (mvfderiv_mul (x := q.2) (mdifferentiableAt_const (c := cuttingSign b)) (hs.mdifferentiableAt (by simp)))
  change mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun s : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) => cuttingSign b * s.val) q.2 t =
    cuttingSign b * mvfderiv (I := (𝓡∂ 1)) (Subtype.val : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) → ℝ) q.2 t +
      q.2.val * mvfderiv (I := (𝓡∂ 1)) (fun _ : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) => cuttingSign b) q.2 t at hm
  erw [mvfderiv_const, zero_apply, _root_.MulZeroClass.mul_zero, add_zero] at hm
  change mfderiv (𝓡∂ 1) 𝓘(ℝ)
    (fun s : _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) => cuttingSign b + cuttingSign b * s.val) q.2 t = _
  erw [mfderiv_add mdifferentiableAt_const ((contMDiff_const.mul hs).mdifferentiableAt (by simp)),
    mfderiv_const, zero_add]
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_cuttingCollarCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_cuttingCollarCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_cuttingCollarCylinderMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_cuttingCollarCylinderMap


open private originalTubularDomainMap from
  Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding

private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry target :: scope.openDecls } }

theorem mfderiv_originalTubularMap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M)
    (hs : ContMDiff IC I ∞ f) (q : S2 × _root_.Set.Icc (-2 : ℝ) 2)
    (q₀ : bufferedCylinder δ) (hq₀ : q₀.val = (q.1, q.2.val))
    (v : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 1)) :
    mfderiv IR I (originalTubularMap hδ hδ1 f) q (v, t) =
      mfderiv IC I f q₀
        (v, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : _root_.Set.Icc (-2 : ℝ) 2 → ℝ) q.2 t) := by
  let j := originalTubularDomainMap hδ hδ1
  have hj : _root_.Manifold.IsSmoothEmbedding IR IC ∞ j :=
    isSmoothEmbedding_intoOpen IR IC (bufferedCylinder δ) j
      ((IsSmoothEmbedding.id : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞ (id : S2 → S2)).prodMap
        (isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)))
  have heq : j q = q₀ := Subtype.ext hq₀.symm
  change mfderiv IR I (f ∘ j) q (v, t) = _
  erw [mfderiv_comp_apply q (hs.mdifferentiableAt (by simp))
    (hj.contMDiff.mdifferentiableAt (by simp))]
  have hD : mfderiv IR IC j q (v, t) =
      (v, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : _root_.Set.Icc (-2 : ℝ) 2 → ℝ) q.2 t) := by
    erw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := IR) (J := IC) j q]
    change mfderiv IR IC (Prod.map (id : S2 → S2)
      (Subtype.val : _root_.Set.Icc (-2 : ℝ) 2 → ℝ)) q (v, t) = _
    erw [mfderiv_prodMap mdifferentiableAt_id
      ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)), mfderiv_id]
    rfl
  rw [hD, heq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_originalTubularMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_originalTubularMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_originalTubularMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.mfderiv_originalTubularMap

end DifferentialGeometry.Topology.ThreeManifold.Surgery
