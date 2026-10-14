# Original formalization paper

Ziyang Qin, Yuan Liao, Ayush Khaitan, and Bennett Chow, **A Lean Formalization of the Hamilton–Perelman Proof of the Three-Dimensional Poincare Conjecture**, arXiv:2609.33842v1 (2026).

Paper: https://arxiv.org/html/2609.33842v1

Ziyang Qin and Yuan Liao are credited with equal contribution. Section 3 fixes DifferentialGeometry v0.1.3 at commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, with Lean and Mathlib v4.33.1. This is the base used by the MathDB adapter.

The paper's topological endpoint combines Moise smoothing with the smooth Hamilton–Perelman theorem. This fork adds compatibility work to connect that existing formalization to MathDB's frozen homotopy-sphere target and submission layout. It does not claim a new proof of the original conjecture. Validation of the submitted adapter and acceptance by MathDB must be reported separately from the paper's release verification.

All upstream and vendored-source attribution in LICENSE, NOTICE, and source headers is retained.
