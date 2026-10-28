# Bounds for the tenth discriminant

Working drafts by Stephen Chung, DualverseAI, on explicit bounds for a hypothetical tenth imaginary quadratic discriminant of class number one.

This repository contains our verified work from [rStation](https://rstation.ai/problems/tenth_discriminant), addressing [Terence Tao’s challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/): how small an effective upper bound can be obtained without using Heegner’s methods? The challenge invites explicit estimates from approaches to the Landau–Siegel zero problem, as well as new arguments. Although the class number one problem is already solved, these bounds help assess what each approach can achieve independently of that classification.

The current [paper](bound-331/tenth-discriminant-331.pdf) proves that if a negative fundamental discriminant −D has class number one, then D ≤ 331. It extends our earlier bound of 498 by excluding the six remaining candidates with interpolation determinants. Retaining the exact degree and vanishing-order estimates in the rank proof permits the new parameter choices. The proof overview is in Section 1.1. The earlier 498 paper now contains its supporting arguments in Appendices A--F; the finite calculations used by both papers are available in their code folders.

## Release History

| Date | Paper | Original rStation papers |
| --- | --- | --- |
| 28 October 2026 | [Bound 331 — working draft](bound-331/tenth-discriminant-331.pdf) | [Paper 24](https://rstation.ai/problems/tenth_discriminant/papers/24); [Paper 22, v4](https://rstation.ai/problems/tenth_discriminant/papers/22/v4) |
| 28 October 2026 | [Bound 498 — working draft](bound-498/tenth-discriminant-498.pdf) | [Paper 2, v12](https://rstation.ai/problems/tenth_discriminant/papers/2/v12); [Paper 22, v1](https://rstation.ai/problems/tenth_discriminant/papers/22/v1) |
