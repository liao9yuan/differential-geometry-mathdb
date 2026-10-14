import Submission.DifferentialGeometry.Topology.Collar.AttachmentRescaling
import Submission.DifferentialGeometry.Topology.Order.IntervalPush

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.Collar

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B]
  [TopologicalSpace X] [T2Space X]

theorem exists_attachment_homeomorph
    (f : C(B, X)) {ε δ a : ℝ} (ha : 0 < a) (haδ : 2 * a < δ) (hδε : δ ≤ ε)
    (c : C(B × _root_.Set.Icc (0 : ℝ) ε, X)) (hc : _root_.Topology.IsEmbedding c)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, (by linarith : 0 ≤ ε)⟩⟩) = f p)
    (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ})) :
    ∃ h : MappingCylinder f ≃ₜ X,
      (∀ x, h (mappingCylinderOriginal f x) =
        rescale c hc (intervalPush a (haδ.le.trans hδε)) x) ∧
      ∀ q : B × _root_.Set.Icc (0 : ℝ) 1, h (mappingCylinderProduct f q) =
        c (q.1, ⟨a * (1 - q.2.val),
          ⟨mul_nonneg ha.le (sub_nonneg.mpr q.2.property.2), by
            have ht := q.2.property.1
            nlinarith⟩⟩) := by
  let cut : _root_.Set.Icc (0 : ℝ) ε := ⟨a, ha.le, by linarith⟩
  apply exists_attachment_homeomorph_of_rescaling (a := cut) f ha haδ c hc hzero hopen
    (intervalPush a (haδ.le.trans hδε)) (strictMono_intervalPush a _).injective
  · apply Subtype.ext
    simp [cut, intervalPush, max_eq_right ha.le]
  · exact range_intervalPush _
  · exact intervalPush_fixed a _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Collar.exists_attachment_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Collar.exists_attachment_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Collar.exists_attachment_homeomorph ``Submission.DifferentialGeometry.Topology.Collar.exists_attachment_homeomorph

end DifferentialGeometry.Topology.Collar
