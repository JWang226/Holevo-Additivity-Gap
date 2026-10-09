# Additive expected-statement configuration

[source-certificate.json](source-certificate.json) selects the unchanged
production proof evidence while adding the isolated
`ComparatorChallenges.F_TwoUseSeparation` configuration. It is a configuration
extension of the [October 6 rebuild/type certificate](../elaboration-20261006/source-certificate.json),
not a new proof execution record. The predecessor certificate, its public-type
comparison, and its archived compiler outputs remain unchanged.

All 369 production proof sources, the other measured build drivers, and the
five original challenge sources/configurations must retain their recorded
SHA-256 hashes. The declaration export and comparison script must also remain
byte-identical. The additional target,
`Nonadditivity.DeterministicConsequences.actual_small_large`, was already a
public theorem in the unchanged export covered by the exact comparison of all
5,323 public declaration types.

[base-lakefile.toml](base-lakefile.toml) is an exact copy of `lakefile.toml` from
the predecessor's measured source commit
`e943a85f0234a573477a10871f60a2d9583fa47b`. Its SHA-256 is
`6199431f211399fe13fbec0233844e625156954d0e46c207acad72cfc8148c25`, matching
both the measured build and declaration-export bindings. The extension
validator checks the predecessor against those historical bytes and requires
the current parsed Lake configuration to differ only by appending the F root.
The current Lake file and both new challenge files have separate current
hash bindings in the extension certificate. No exception permits a changed
production proof, dependency manifest, compiler driver, or existing challenge.

The extension itself records `not_run` for a new source rebuild, the additional
expected-statement check, Comparator, and Nanoda. It does not review the new
manuscript or certify English-to-Lean correspondence. The fresh six-configuration,
seven-root verification and manuscript review have their own successor records;
the earlier portable and statement-review records retain their original scope.

Select the extension explicitly when rebuilding and checking the current tree:

```sh
bash scripts/verify.sh all \
  --source-certificate verification/additive-20261008/source-certificate.json
```

The original schema-1 certificate still rejects the changed current Lake file
when selected directly. Synthetic rejection controls for both certificate
schemas are run with `python3 -B scripts/test_source_certificate.py`; they
exercise integrity gates in temporary Git repositories and execute no proof
compiler or kernel.
