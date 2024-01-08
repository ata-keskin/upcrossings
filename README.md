## Abstract

In the scope of this entry, we formalize Doob's Upcrossing Inequality and subsequently prove Doob's first martingale convergence theorem. 

Doob's upcrossing inequality is a fundamental result in the study of martingales. It provides a bound on the expected number of times a submartingale crosses a certain threshold within a given interval.

The theorem states that, if $(M_n) _{n \in \mathbb{N}}$ is a submartingale with $\sup _n \mathbb{E}[M^{+} _n] < \infty$, then, the limit process $M _\infty := \lim_n M_n$ exists almost surely and is integrable. Furthemore the limit process is measurable with respect to $F _\infty = (\bigcup _{n \in \mathbb{N}}. F_n)$. Equivalent statements for martingales and supermartingales are also provided as corollaries.

The proofs provided are based mostly on the formalization done in the Lean mathematical library.

## Related Publications

- Ying, K., Degenne, R. (2022). A Formalization of Doob's Martingale Convergence Theorems in mathlib. arXiv. https://doi.org/10.48550/arXiv.2212.05578
