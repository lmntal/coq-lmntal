# LMNtal in Rocq

This repository contains the Rocq (formerly Coq) development for the paper
"Formalizing a Syntax-directed Graph Rewriting Language in Rocq".

The file `LMNtalSyntax.v` is the complete, self-contained development used
in the paper. It formalizes the syntax and semantics of flat LMNtal (a
text-based graph rewriting language) and proves:

- the admissibility of two structural congruence rules, (E4) (alpha-conversion
  of local link names) and (E8) (symmetry of connectors), relative to a
  smaller set of base rules;
- the correspondence between reverse execution and rule inversion;
- the paper's main result: a full correspondence between LMNtal's structural
  congruence and graph isomorphism on the corresponding port graphs
  (`congm_giso_iff`/`cong_giso_iff`), for arbitrary well-formed (not only
  closed) terms, in both directions, together with closed-term corollaries
  and two further robustness results (the interface hypothesis is necessary;
  on connector-free terms, this notion of graph isomorphism coincides with
  the textbook one via link renaming).

Every proof in the file depends on nothing beyond two standard classical-logic
axioms from Rocq's standard library (`Classical_Prop.classic` and
`Description.constructive_definite_description`); this can be checked with
`Print Assumptions` on any top-level theorem. There are no `Admitted` lemmas
anywhere in the file.

## Building

```
rocq c -Q . LMNTAL LMNtalSyntax.v
```

Tested with Rocq 9.2.

## Other files in this repository

The remaining `.v` files (`LMNtalGraph*.v`, `LMNtalShapeType.v`,
`Properties*.v`, `Util.v`, `LMNtalSyntax2.v`) are from earlier, separate work
and are not part of this paper's development.
