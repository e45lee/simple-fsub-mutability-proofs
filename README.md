# Artifact for the OOPSLA 2023 paper 'Simple Reference Immutability for System F-sub'

This GitHub repository constitutes the artifact for our paper

> Simple Reference Immutability for System F-Sub.  Edward Lee and Ondřej Lhoták.
> Conditionally accepted at OOPSLA 2023.

## Overview

The artifact consists of the Coq proofs for our paper.  There are two calculi
formalized in this artifact.

1.  System Lm, our untyped reference immutability calculus with the dynamic
    immutability safety results discussed in Section 3 of the paper.
2.  System Fm, our typed calculi building on Lm and System F-sub with both the static
    soundness results discussed in Section 4 of our paper as well as the
    dynamic immutability safety results discussed in Section 4 of the paper.

While the repository contains the sources of the Coq files and the documentation
associated with the Coq proofs as well, a pre-built archive of the compiled Coq proof
can be downloaded and inspected by pulling the following automatically generated Docker image.

```
    docker pull ghcr.io/e45lee/simple-fsub-mutability-proofs:main
```

The Coq proofs and generated documentation can be found under `/proofs` in the generated Docker image.
To extract the pre-built proofs and documentation (into a folder called `proofs`), run:

```
    docker run -w / ghcr.io/e45lee/simple-fsub-mutability-proofs:main tar c proofs | tar x
```

In addition, the Coq documentation can be found online at (hopefully soon!):

<https://e45lee.github.io/simple-fsub-mutability-proofs/toc.html>
 
## Getting Started -- Building Locally

We have prepared a Dockerfile to test and build our artifact locally.  To build the Docker
image containing our proof artifact and documentation, run the following command from the top-level
directory of the repository.

```
    docker build -t simple-fsub-mutability-proofs:local .
```

If you have Coq 8.15 installed, you can also build our proofs by running `make && make coqdoc` as well.

```
    make && make coqdoc
```

## Kick-the-Tires -- Coq proofs

In Section 6, we claim:

> Our mechanization of System F<:M is based on the mechanization of System F<: by Aydemir et al .
> [2008]. Our mechanization is a faithful model of System F<:M as described in this paper except for one
> case. To facilitate mechanization, reduction in our mechanization is done via explicit congruence
> rules in each reduction rule instead of an implicit rule for reducing inside an evaluation context,
> similar to how Aydemir et al. [2008] originally mechanize System F<: as well.
> Proofs for all lemmas except for Theorem 5.10 and Lemmas 3.9, 5.2, and 5.4 have been mechanized
> using Coq 8.15 in the attached artifact. Theorem 5.10 and Lemmas 5.2, 5.4, and 5.13 have not been
> mechanized as they require computation on typing derivations which is hard to encode in Coq
> as computation on Prop cannot be reflected into Set. Lemma 3.9 has been omitted from our
> mechanization as it is hard to formally state, let alone prove, in a setting where reduction is done
> by congruence, though it almost follows intuitively from how the reduction rules are set up.

### Definitions
Definitions for System Fm can be found in `Fm_Definitions.v`.  Definitions for the untyped
calculus System Lm can be found in `Lm_Definitions.v`.

### System Lm (Section 3)
Our dynamic immutability safety results for System Lm can be found in the files
`Lm_Immutability.v` and `Lm_MultistepImmutability.v`.  Lemmas 3.4, 3.5, 3.6,
and 3.7 can be found in `Lm_Immutability.v`.  Lemma 3.8 can be found in `Lm_MultistepImmutability.v`

### System Fm (Sections 4 and 5)

#### Normal Forms (Section 4)
Our lemmas regarding normal forms of types in System Fm can be found in `Fm_NormalForms.v`.
and in `Fm_Soundness.v`. In particular, Lemma 4.2 is located in `Fm_NormalForms.v`,
and Lemma 4.3 can be found in `Fm_Soundness.v`.

#### Inversion, Canonical Forms, Soundness (Section 4)
Our lemmas regarding canonical forms, inversion, and soundness can be found in `Fm_Soundness.v`.  In particular, Lemmas 4.4, 4.5, 4.6, 4.7, and 4.8 can be found in `Fm_Soundness.v`.
In addition, both progress and preservation (Theorems 4.9 and 4.11) can be found in `Fm_Soundness.v`.

#### Immutability Safety Lemmas for System Fm (Section 5)
Our dynamic immutability safety results for System Fm can be found in the
files `Fm_Immutability.v` and `Fm_MultistepImmutability.v`.  As System Fm's dynamic
reduction semantics are a small extension of System Lm's (the only new forms are
type abstraction and type application), the proofs in these files are very similar
to the proofs of the analogous results for System Lm in `Lm_Immutability.v` and `Lm_MultistepImmutability.v`.

Lemmas 5.1, 5.5, 5.6, 5.7, 5.8, and 5.11 can be found in `Fm_Immutability.v`.
Lemmas 5.8, 5.9, 5.12, and 5.13 can be found in `Fm_MultistepImmutability.v`.

