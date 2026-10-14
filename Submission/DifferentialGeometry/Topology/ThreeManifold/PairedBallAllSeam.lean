import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2)
      (flagMap N endpoint chart q '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2))
  (a : E → BoundaryAttachment)

def allCore [Finite E] : TopologicalSpace.Opens (Σ v, PuncturedFactor N endpoint chart v) :=
  ⟨(⋃ (e : E) (b : Bool), _root_.Set.range (fun z =>
      (⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :
        Σ v, PuncturedFactor N endpoint chart v)))ᶜ,
    (isClosed_iUnion_of_finite fun e => isClosed_iUnion_of_finite fun b =>
      (isCompact_range (continuous_sigmaMk.comp
        (continuous_boundaryPoint N endpoint chart hdisj e b))).isClosed).isOpen_compl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allCore ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allCore

def allCoreInclusion [Finite E] : allCore N endpoint chart hdisj →
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y) :=
  fun x => Quot.mk _ x.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allCoreInclusion ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allCoreInclusion

def allSeamChart (e : E) : SelfAttachment.directSeamDomain →
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y) :=
  Quot.map id (fun {_ _} h => ⟨e, h⟩) ∘ seamChart N endpoint chart hdisj e (a e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allSeamChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allSeamChart

theorem allSeamChart_nonneg (e : E) (p : SelfAttachment.directSeamDomain)
    (ht : 0 ≤ p.val.2) :
    allSeamChart N endpoint chart hdisj a e p =
      Quot.mk _ ⟨endpoint e _root_.Bool.false,
        radialPoint N endpoint chart hdisj e _root_.Bool.false p.val.1 (1 + p.val.2)
          ⟨by linarith, by linarith [p.property.2.2]⟩⟩ := by
  simp only [allSeamChart, _root_.Function.comp_apply, seamChart, dif_pos ht]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_nonneg ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_nonneg

theorem allSeamChart_neg (e : E) (p : SelfAttachment.directSeamDomain)
    (ht : p.val.2 < 0) :
    allSeamChart N endpoint chart hdisj a e p =
      Quot.mk _ ⟨endpoint e _root_.Bool.true,
        radialPoint N endpoint chart hdisj e _root_.Bool.true ((a e).val p.val.1) (1 - p.val.2)
          ⟨by linarith, by linarith [p.property.2.1]⟩⟩ := by
  simp only [allSeamChart, _root_.Function.comp_apply, seamChart, dif_neg (not_le.mpr ht)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_neg ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_neg

theorem allSeamChart_zero (e : E) (z : SelfAttachment.Sphere (n := 3)) :
    allSeamChart N endpoint chart hdisj a e
      ⟨(z, 0), _root_.Set.mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ =
      Quot.mk _ ⟨endpoint e _root_.Bool.false, boundaryPoint N endpoint chart hdisj e _root_.Bool.false z⟩ := by
  change Quot.map id (fun {_ _} h => ⟨e, h⟩)
    (seamChart N endpoint chart hdisj e (a e) _) = _
  rw [seamChart_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_zero ``Submission.DifferentialGeometry.Topology.PairedBallGluing.allSeamChart_zero

theorem all_local_maps_cover [Finite E]
    (q : Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y)) :
    (∃ x, allCoreInclusion N endpoint chart hdisj a x = q) ∨
      ∃ e z, allSeamChart N endpoint chart hdisj a e
        ⟨(z, 0), _root_.Set.mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ = q := by
  classical
  induction q using Quot.inductionOn with
  | h x =>
    by_cases hx : x ∈ allCore N endpoint chart hdisj
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · right
      have hx' : x ∈ ⋃ (e : E) (b : Bool), _root_.Set.range (fun z =>
          (⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :
            Σ v, PuncturedFactor N endpoint chart v)) := not_not.mp hx
      obtain ⟨e, hx'⟩ := mem_iUnion.mp hx'
      obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hx'
      cases b with
      | false => exact ⟨e, z, allSeamChart_zero N endpoint chart hdisj a e z⟩
      | true =>
        refine ⟨e, (a e).val.symm z, ?_⟩
        rw [allSeamChart_zero]
        apply Quot.sound
        refine ⟨e, (a e).val.symm z, Or.inl ⟨rfl, ?_⟩⟩
        rw [(a e).val.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.all_local_maps_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.all_local_maps_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.all_local_maps_cover ``Submission.DifferentialGeometry.Topology.PairedBallGluing.all_local_maps_cover

theorem range_allCoreInclusion_union_iUnion_range_allSeamChart [Finite E] :
    _root_.Set.range (allCoreInclusion N endpoint chart hdisj a) ∪
      (⋃ e, _root_.Set.range (allSeamChart N endpoint chart hdisj a e)) = univ := by
  apply _root_.Set.eq_univ_of_forall
  intro q
  rcases all_local_maps_cover N endpoint chart hdisj a q with h | ⟨e, z, hz⟩
  · exact Or.inl h
  · exact Or.inr (mem_iUnion.mpr ⟨e, _, hz⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.range_allCoreInclusion_union_iUnion_range_allSeamChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.range_allCoreInclusion_union_iUnion_range_allSeamChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.range_allCoreInclusion_union_iUnion_range_allSeamChart ``Submission.DifferentialGeometry.Topology.PairedBallGluing.range_allCoreInclusion_union_iUnion_range_allSeamChart

end DifferentialGeometry.Topology.PairedBallGluing
