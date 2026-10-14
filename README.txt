MathDB-specific fork of Ziyang Qin's DifferentialGeometry

This repository is a fork of Ziyang Qin's DifferentialGeometry repository,
created specifically to prepare and submit its Poincare-conjecture formalization
to MathDB. Upstream: https://github.com/qinz1yang/differential-geometry
MathDB problem: https://mathdb.com/p/316224/poincare-conjecture

Entry point: Submission.solution : Problem.Target in Submission.lean.
The target is imported unchanged from FtpEvalBench.YPoincare_poincare_conjecture.
All submission helper source modules are below Submission/.

This package is based on DifferentialGeometry v0.1.3, commit
7a48598d35109aa99d1cc678e2724c213cdf4ff3. It uses Lean 4.33.1 and
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, matching the frozen
MathDB environment. No precompiled proof caches are shipped.

The original formalization is by Ziyang Qin, Yuan Liao, Ayush Khaitan,
and Bennett Chow. Qin and Liao contributed equally. See PAPER_REFERENCE.md
and https://arxiv.org/html/2609.33842v1 for the paper and pinned release.
All source licenses and vendored attribution are preserved.

The adapter derives compactness and simple connectivity from MathDB's
homotopy-equivalence hypothesis and applies the original Poincare theorem.
The compactness bridge and needed compatibility definitions are backported
from DifferentialGeometry v0.1.4 and its Mathlib version; exact provenance
is recorded under verification/ and in the original source headers.

Helpers were relocated into namespace Submission. Resolver aliases preserve
upstream reference spelling while resolving to relocated declarations;
they introduce no new proof axioms and do not replace trusted constants.
The original elaboration options are included in the source files because
MathDB does not execute repository Lake configuration or build scripts.

verification/final-validation.json records the completed local checks;
verification/source-manifest.json records the exact submitted source hashes.
Local validation and acceptance by MathDB are distinct. Consult the MathDB
solution's live status for the website verification result.

Completed local validation

All 14,234 helper modules and the root Submission.lean compiled. Independent
kernel replay checked 237,010 new logical declarations against 798,651 unchanged
frozen declarations. The actual logical type/body dependencies use only propext,
Classical.choice, and Quot.sound. Compact audit reports are under verification/.

The compiled artifacts contain automatic Lean auxiliaries. The namespace audit
separately validated 338 serialized helpers by trusted-only regeneration, including
uniform alignment of fresh private names and one exact Omega arithmetic proof.
It identified 108 compiler runtime companions of safe recursive definitions with
matching types and universes. No logical declaration refers to those companions;
they are explicitly recorded and excluded from logical kernel replay. No actual
unsafe declaration, new axiom, or other partial declaration is admitted.

One relocated upstream proof uses a command-local heartbeat budget of 400,000
to accommodate elaboration after relocation. Its mathematical proof is preserved.
