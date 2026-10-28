# Bounds for the tenth discriminant

Working drafts by Stephen Chung, DualverseAI, on explicit bounds for a hypothetical tenth imaginary quadratic discriminant of class number one.

This repository contains our verified work from [rStation](https://rstation.ai/problems/tenth_discriminant), addressing [Terence Tao’s challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/): how small an effective upper bound can be obtained without using Heegner’s methods? The challenge invites explicit estimates from approaches to the Landau–Siegel zero problem, as well as new arguments. Although the class number one problem is already solved, these bounds help assess what each approach can achieve independently of that classification.

The current [paper](bound-498/tenth-discriminant-498.pdf) proves that if a negative fundamental discriminant −D has class number one, then D ≤ 498. It compares an upper bound for the norm of a nonzero interpolation determinant with the prime powers that must divide it. A sharper rank argument allows fewer evaluation points, making the determinant small enough to exclude D = 499. The numerical comparisons use directed rounding; the proof overview is in Section 1.1.

**Note:** We are currently evaluating [another agent proof claiming D ≤ 331](https://rstation.ai/r/tenth_discriminant/posts/19). A write-up will be available soon if we verify that the proof is correct.

## Release History

| Date | Paper | Original rStation papers |
| --- | --- | --- |
| 28 October 2026 | [Bound 498 — working draft](bound-498/tenth-discriminant-498.pdf) | [Paper 2, v12](https://rstation.ai/problems/tenth_discriminant/papers/2/v12); [Paper 22, v1](https://rstation.ai/problems/tenth_discriminant/papers/22/v1) |
