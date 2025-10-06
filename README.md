# Modeling with TLA+


## Outline

This is a tutorial on modeling with TLA+ intended for engineers. Topics covered
include:

- model checking

- refinement

- composition

- conformance of implementation


### First part: Modeling, checking, refining, proving

Modeling is first presented using the very simple example of a wall clock. Model
checking is explained while introducing the concept of invariant.

Refinement is then addressed using a new model that adds an alarm feature to the
wall clock. The refinement is validated through the checker. The checker
limitations are discussed at this point.

The prover is then introduced to overcome these limitations. Invariants and
refinement are proven step-by-step.

Finally, different types of invariants are discussed.


### Second part: Composing

Decomposition of a model into smaller models is justified. A graphical formalism
for components is introduced, and the main composition modes are described, as
well as how to express them in TLA.

As an example, a system is introduced where a device can download versioned
themes from a server. The download is performed atomically in this first
iteration. The system is conceptually divided into two subcomponents and a
parent component, then formalized in TLA. Invariants are proven in the parent,
leveraging proofs from the subcomponents.

The system is then refined by replacing the atomic download by a simple
request-reply protocol where the device lists then gets the themes. Each
subcomponent and the parent are refined, and invariants and refinement are
proven.

This part concludes on some recommendations on refinement and decomposition.


### Third part: Conforming

The refined theme system is implemented in C++ 20 and the [messaging library
ZeroMQ](https://zeromq.org/), with an executable for the device and another one
for the server.

The mapping of implementation behaviors on model behaviors is explained. Each
executable produces logs that must be post-processed to be merged and produce a
trace, corresponding hopefully to a valid model behavior.

The checker is used to validate the trace. An invalid step is discovered
revealing an implementation bug. Once the bug is fixed, a new trace is produced
that is validated by the checker. The advantages and limitations of this
technique are discussed.


## Approach

The tutorial is oriented towards proofs, following a correct-by-construction
approach that can be summarized by the following diagram:

```
make a model
      │
      ▾
express invariants
      │
      ▾
prove invariants
      │
      ▾
make a model    ◂───────────┐
      │                     │
      ▾                     │
express invariants          │
      │                     │
      ▾                     │
prove invariants            │
      │                     │
      ▾                     │
express refinement mapping  │
      │                     │
      ▾                     │
prove refinement ───────────┘
      │
      ▾
derive implementation
```

In plain English, start with a high-level model, then refine it as many times as
necessary, to finally obtain a model low-level enough to allow for the
derivation of an implementation.

At each step, the invariants are expressed and proven and the current model is
proven to refine the previous one. In other words, each new model is proven to
be an implementation of the previous one.

Finally, if the implementation is hand-written, as is the case in the tutorial,
its conformance to the last, most refined, model is verified on an execution by
execution basis.


## How to build


### Requirements

To build the PDF on Unix, you will need:

- [Pandoc](https://pandoc.org): to convert from Markdown to PDF

- [XeLaTeX](https://en.wikipedia.org/wiki/Xelatex): to produce the PDF *per se*

- [Make](https://en.wikipedia.org/wiki/Make_(software)): to handle build dependencies

- Some fonts:

    + [FiraCode-Regular.ttf](https://github.com/tonsky/FiraCode/releases)

    + [FiraMono-Regular.ttf](https://fonts.google.com/specimen/Fira+Mono)

    + [FiraTlas-Regular.ttf](https://github.com/jskri/FiraTlas/releases/)

### Build

```bash
cd build/
make modeling-with-tla.pdf
```

### Docker image

Alternatively, you can use a docker image. At the root of the repository, type:

```bash
docker run --rm --volume "$(pwd):/data" --user "$(id -u):$(id -g)" dvnh87/pandoc-with-make-and-tla-fonts:1.0 modeling-with-tla.pdf
```

The PDF is generated in `build/modeling-with-tla.pdf`.

You can clean with:

```bash
docker run --rm --volume "$(pwd):/data" --user "$(id -u):$(id -g)" dvnh87/pandoc-with-make-and-tla-fonts:1.0 clean
```
