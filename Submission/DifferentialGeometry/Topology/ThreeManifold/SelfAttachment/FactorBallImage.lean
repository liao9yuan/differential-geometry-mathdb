import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSum
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CollarAbsorption

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.SelfAttachment

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.E3 target :: scope.openDecls } }
variable (M : ConnectedClosedOrientedManifold.{u} 3)
  (p q : OrientedBallChart M.toClosedOrientedManifold)
  (hpq : Disjoint (p.chart '' closedBall 0 2) (q.chart '' closedBall 0 2))

theorem exists_orientedBallChart_family_complement_homeomorph {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (hep : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 → (e i).chart x ∉ p.chart '' _root_.Metric.closedBall 0 2)
    (heq : ∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 → (e i).chart x ∉ q.chart '' _root_.Metric.closedBall 0 2)
    (he : Pairwise fun i j => Disjoint ((e i).chart '' _root_.Metric.closedBall (0 : E3) 2)
      ((e j).chart '' _root_.Metric.closedBall (0 : E3) 2)) :
    ∃ s : SmoothSelfAttachment p q hpq boundaryAttachment,
    ∃ F : ClosedOrientedManifold.OrientedDiffeomorph
        s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
    ∃ b : ι → OrientedBallChart (connectedSum M sphereTwoTimesCircleLift).toClosedOrientedManifold,
      (∀ i x, x ∈ _root_.Metric.closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (p.chart '' _root_.Metric.ball 0 1 ∪ q.chart '' _root_.Metric.ball 0 1)ᶜ,
          (b i).chart x = F.val (coreInclusion p.toBallChart q.toBallChart hpq
            boundaryAttachment.val.toHomeomorph ⟨(e i).chart x, hx⟩)) ∧
      (Pairwise fun i j => Disjoint ((b i).chart '' _root_.Metric.closedBall (0 : E3) 2)
        ((b j).chart '' _root_.Metric.closedBall (0 : E3) 2)) ∧
      ∃ H : Quot (fun x y : {x : p.toBallChart.DoublePunctured q.toBallChart //
          x.val ∉ ⋃ i, (e i).chart '' _root_.Metric.ball (0 : E3) 1} =>
          directRel p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph x.val
              y.val) ≃ₜ
        {x : (connectedSum M sphereTwoTimesCircleLift).Carrier //
          x ∉ ⋃ i, (b i).chart '' _root_.Metric.ball (0 : E3) 1},
        (∀ x, (H (Quot.mk _ x)).val = F.val (coreToBand p.toBallChart q.toBallChart hpq
          boundaryAttachment.val.toHomeomorph x.val)) ∧
        (∀ i z (_ : z ∈ _root_.Metric.closedBall (0 : E3) 2)
          (hx : (e i).chart z ∈ (p.chart '' _root_.Metric.ball 0 1 ∪ q.chart '' _root_.Metric.ball 0 1)ᶜ)
          (hu : (e i).chart z ∉ ⋃ j, (e j).chart '' _root_.Metric.ball (0 : E3) 1),
          (H (Quot.mk _ ⟨⟨(e i).chart z, hx⟩, hu⟩)).val = (b i).chart z) := by
  obtain ⟨s, F, hF⟩ := exists_smoothSelfAttachment_orientedDiffeomorph_retaining_charts M p q hpq
  have havoid (i : ι) (x : E3) (hx : x ∈ _root_.Metric.closedBall (0 : E3) 2) :
      (e i).chart x ∉ p.chart '' _root_.Metric.closedBall 0 1 ∪ q.chart '' _root_.Metric.closedBall 0 1 := by
    rintro (hp | hq)
    · exact hep i x hx ((_root_.Set.image_mono (_root_.Metric.closedBall_subset_closedBall (by norm_num))) hp)
    · exact heq i x hx ((_root_.Set.image_mono (_root_.Metric.closedBall_subset_closedBall (by norm_num))) hq)
  obtain ⟨b, hb⟩ := hF e havoid
  let U : Set (p.toBallChart.DoublePunctured q.toBallChart) :=
    {x | x.val ∈ ⋃ i, (e i).chart '' _root_.Metric.ball (0 : E3) 1}
  have hU : IsOpen U := (isOpen_iUnion fun i => (e i).toBallChart.isOpen_chart_image_ball).preimage
    continuous_subtype_val
  have hball : _root_.Metric.ball (0 : E3) 1 ⊆ _root_.Metric.closedBall (0 : E3) 2 :=
    ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_closedBall (by norm_num))
  have hUp (x : p.toBallChart.DoublePunctured q.toBallChart) (hx : x ∈ U) :
      x.val ∉ p.chart '' _root_.Metric.closedBall (0 : E3) 2 := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact hzx ▸ hep i z (hball hz)
  have hUq (x : p.toBallChart.DoublePunctured q.toBallChart) (hx : x ∈ U) :
      x.val ∉ q.chart '' _root_.Metric.closedBall (0 : E3) 2 := by
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact hzx ▸ heq i z (hball hz)
  let H₀ := directBandComplementHomeomorph p.toBallChart q.toBallChart hpq
    boundaryAttachment.val.toHomeomorph U hU hUp hUq
  have hmem (y : Quotient p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph) :
      y ∈ coreInclusion p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph '' U ↔
      F.val y ∈ ⋃ i, (b i).chart '' _root_.Metric.ball (0 : E3) 1 := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      refine mem_iUnion.mpr ⟨i, z, hz, ?_⟩
      exact hbz.trans (congrArg F.val (congrArg
        (coreInclusion p.toBallChart q.toBallChart hpq boundaryAttachment.val.toHomeomorph)
          (Subtype.ext hzx)))
    · intro hy
      obtain ⟨i, z, hz, hzy⟩ := mem_iUnion.mp hy
      obtain ⟨hz', hbz⟩ := hb i z (hball hz)
      refine ⟨⟨(e i).chart z, hz'⟩, mem_iUnion.mpr ⟨i, z, hz, rfl⟩, ?_⟩
      exact F.val.injective (hbz.symm.trans hzy)
  let H₁ := F.val.toHomeomorph.subtype
    (p := fun y => y ∉ coreInclusion p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph '' U)
    (q := fun y => y ∉ ⋃ i, (b i).chart '' _root_.Metric.ball (0 : E3) 1)
    (fun y => not_congr (hmem y))
  let H := H₀.trans H₁
  refine ⟨s, F, b, hb, ?_, H, fun _ => rfl, ?_⟩
  · intro i j hij
    rw [_root_.Set.disjoint_left]
    rintro x ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    obtain ⟨hz', hbz⟩ := hb i z hz
    obtain ⟨hw', hbw⟩ := hb j w hw
    have hco := F.val.injective (hbz.symm.trans ((hzx.trans hwx.symm).trans hbw))
    have hev := congrArg Subtype.val
      (coreInclusion_injective p.toBallChart q.toBallChart hpq
          boundaryAttachment.val.toHomeomorph hco)
    exact disjoint_left.mp (he hij) ⟨z, hz, hev⟩ ⟨w, hw, rfl⟩
  · intro i z hz hx hu
    change F.val (coreToBand p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph ⟨(e i).chart z, hx⟩) = _
    obtain ⟨hx', hbz⟩ := hb i z hz
    exact (congrArg F.val (coreToBand_of_not_mem_chart_image p.toBallChart q.toBallChart hpq
      boundaryAttachment.val.toHomeomorph ⟨(e i).chart z, hx⟩ (hep i z hz) (heq i z
          hz))).trans hbz.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.exists_orientedBallChart_family_complement_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.exists_orientedBallChart_family_complement_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.exists_orientedBallChart_family_complement_homeomorph ``Submission.DifferentialGeometry.Topology.SelfAttachment.exists_orientedBallChart_family_complement_homeomorph

end DifferentialGeometry.Topology.SelfAttachment
