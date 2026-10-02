<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# The sharp one-pair Haar range

## Mathematical content

For moment order $p\ge2$ and actual local dimension $D\ge2^{32}p^{80}$, the strengthened one-pair estimate bounds the real normalized Haar trace moment by the corresponding real free trace moment plus

$$
D^{-1/2}\,\|f_{\mathrm{regular}}\|_{\mathrm{op}}^p.
$$

The coefficient representations are the finite matrix/free-factor models specified by the formal theorem.

## Proof idea

Keep the chronological exploration positions in the path counts. The weighted count, combined with the repaired coefficient estimate, bounds the normalized path sum. Summing the mixed-length contributions yields the trace comparison.

The accompanying iterated-expectation theorem applies an admissible one-pair comparison across distinct tensor legs to control a norm expectation.

## Relation to the main channel route

The sharper threshold is a separate proved endpoint. The prescribed-channel assembler actually references the $2^{80}p^{80}$ one-pair version, which is sufficient for its chosen size. These two routes are shown separately in the [proof map](site:dependencies.html).

See [Haar moments and path counting](concept:finite-moments) for the defect and dimension conventions.
