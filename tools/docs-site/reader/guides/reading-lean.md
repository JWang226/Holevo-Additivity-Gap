<!-- Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution. -->
# Reading the Lean statements

## Start with a mathematical claim

For example, the [prescribed-channel result](result:prescribed-dimensions) says that numerical conditions on $K,n$ suffice to produce one actual finite channel with exact dimensions and three information bounds. Its result page states the mathematics before presenting the formal declarations.

Follow the declaration link to the readable elaborated type. This expands context that a literal source header can leave implicit, including namespace variables, finite-type instances, and hypotheses.

## Inspect what the symbols mean

The word “channel” should lead to an actual physical object. [FiniteQuantumChannel](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel) contains a [KrausChannel](lean:Nonadditivity.Channels.KrausChannel), whose matrices satisfy the completeness equation. [chi](lean:Nonadditivity.ActualConsequences.FiniteQuantumChannel.chi) leads to the bit-valued Holevo quantity of its output states.

For capacity, follow [operationalCapacity](lean:Nonadditivity.Operational.operationalCapacity). It optimizes rates of code sequences. The [coding equality](result:operational-coding) is a theorem about that definition.

These links let a reader check that the formal problem is the intended one, rather than judging by a theorem's name alone.

## Read the hypotheses before the conclusion

A theorem accepting a Haar expectation comparison is conditional on that comparison. The [certificate theorem](lean:Nonadditivity.StructuredHaarConsequences.exists_explicit_certificate) is such a step; [explicitHaarExpectation](lean:Nonadditivity.HaarPrescribedDimension.explicitHaarExpectation) supplies its analytic input in the final construction.

By contrast, [exists_prescribed_channel_with_lower_bound](lean:Nonadditivity.HaarPrescribedDimension.exists_prescribed_channel_with_lower_bound) has only its displayed numerical hypotheses, apart from ordinary finite-type context. Do not infer the assumptions of the final theorem from every older interface in a source module.

A definition of a convergence predicate also does not prove that it holds. The [generic convergence entry](result:generic-haar-convergence) records that distinction explicitly.

## Read the proof and its dependencies

Every declaration page links the exact source module. A known line anchor is used when trustworthy; otherwise the whole module is provided. Direct statement references and stored proof/definition references are listed separately, with reverse references.

The [proof map](site:dependencies.html) groups selected results. An arrow has a witnessed path through actual proof or definition references, with helpers omitted from the picture. The [informal proof route](stage:1) explains why the mathematical steps are useful; these are complementary views.

## Understand the evidence

The [verification page](site:verify.html) gives copyable Lean and Comparator reproducer commands and retained results. The Lean build and transitive axiom audit passed under the standard three permitted axioms. The portable run also passed pinned Comparator API comparison and Lean replay, plus independent Nanoda checking for all six challenge roots. These local checks were unsandboxed; source-bound reports and acceptance/rejection controls are retained.

Proof checking concerns the exact formal statements and definitions. English explanations and manuscript correspondences remain reading aids. The [machine-readable map](site:reader-map.json) identifies which explanation refers to which actual Lean declaration, including definitions and conditional predicates.
