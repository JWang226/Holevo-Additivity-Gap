# Third-party code notices

## KaTeX

The reader website bundles the unmodified KaTeX 0.19.0 JavaScript, stylesheet,
and fonts from its [official release](https://github.com/KaTeX/KaTeX/releases/tag/v0.19.0).
The original MIT license and copyright notice are retained in
[the vendored LICENSE](tools/docs-site/vendor/katex/LICENSE).
[UPSTREAM.md](tools/docs-site/vendor/katex/UPSTREAM.md) records the archive hash
and source. These display assets have no role in Lean or Comparator checking.

## SLT: Statistical Learning Theory in Lean

Two eigenbasis coordinate proof patterns in
`Nonadditivity/GaussianQuadratic.lean` were adapted from
[`SLT/HansonWright.lean`](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/SLT/HansonWright.lean)
at commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876` of
`YuanheZ/lean-stat-learning-theory`:

| Original declaration | Local declaration |
| --- | --- |
| `symmetric_inner_apply_eq_sum_eigenvalues_repr` | `Nonadditivity.GaussianQuadratic.quadratic_eq_eigen_sum` |
| `orthonormalBasis_repr_sum_smul` | `Nonadditivity.GaussianQuadratic.basis_repr_sum` |

Original source notice:

> Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

The adaptations change simplification arguments and proof steps for this
project's pinned mathlib API. The local source file retains the copyright,
license, and author attribution and identifies the adaptations.

The complete repository license, including its contributor copyright notice,
is reproduced unchanged in [`LICENSES/SLT-Apache-2.0.txt`](LICENSES/SLT-Apache-2.0.txt).
It was retrieved from the pinned commit's
[`LICENSE`](https://github.com/YuanheZ/lean-stat-learning-theory/blob/d0f506f0a695018265dccb33bcb05e2f5ca1c876/LICENSE).
The downloaded file matches Git blob
`ed749eb456f1a773072f76aaf4ceefeee3f9bce8`.
The complete file tree at that commit contains no separate `NOTICE` file.

The general SLT Hanson–Wright theorem and the SLT dependency tree are not
imported. The Gaussian density calculation, centered quadratic moment
generating function, concentration bounds, finite-net argument, and channel
construction in this project are proved locally against the pinned mathlib.

The Apache 2.0 terms apply to the adapted portions. This notice does not
assign a license to unrelated project material or change the licenses of
Lean and mathlib dependencies.

## QMDL portable verification

The portable verification wrapper, Comparator replay helper, Nanoda helper,
negative controls, and Nanoda toolchain metadata are adapted at the author’s
request from [JWang226/QMDL](https://github.com/JWang226/QMDL) at commit
`fd36df94068299e3d5e0bb193d19649319a40422`. Original copyright attribution to
the 2026 Free Entropy formalization contributors is retained in the adapted files.
See the original [NOTICE](https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/NOTICE)
and [LICENSE](https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/LICENSE).
That project’s license selection is pending; this adaptation does not assign it
an open-source license. The checker implementations themselves are downloaded
from their pinned upstream repositories and retain their own licenses.
