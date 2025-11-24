# Di- is for Directed: First-Order Directed Type Theory via Dinaturality

This Agda formalization supports the claims made in the paper about the semantics using categories, (di)functors, dipresheaves, and dinatural transformations.

- We do not formalize the syntax/metatheory of the type theory.
- Whenever the semantics of a rule is described in the paper, we link a formalization of its semantics here.
- All of the rules of the type theory have a corresponding semantic claim in Agda **except for the rules related to naturality in the equational theory**. We only provide an example for these in [Dinaturality.NaturalExample](Dinaturality/NaturalityExample.agda) for the case of exponentials and the rule _(exp)_. This is both because formalizing naturality for all rules is somewhat a high formalization effort/low reward situation, and because, even without taking naturality into account, many of the rules in the formalization suffer from running out of memory very quickly. Finding a workaround to fully formalize naturality for every rule is a non-trivial endeavour, which is however easily justified in pen-and-paper proofs by appeal to a "parametricity"-like metatheorem, which our proofs satisfy.
- All files typecheck without postulates or unsolved metas.

## List of claims

1. The semantics for all the rules in Figure 11 is formalized in Agda. A list of rules contained in each file is given in `All.agda`.
2. Theorem 4.5 is formalized in [Dinaturality.GroupoidCompose](Dinaturality/GroupoidCompose.agda).
3. Theorem 4.6 is formalized in [Dinaturality.NaturalDinatural](Dinaturality/NaturalDinatural.agda).
4. Each component of Theorem 5.1, describing the semantics of each rule, is formalized in Agda with each rule in its appropriate module, **except for the rules related to naturality in the equational theory** which are **not** formalized.
5. The remark in Section 6 links to the formalization for the naturality of the (exp) rule as example of what is meant by naturality of each rule. These are captured formally in Appendix B and Appendix E, which are **not** formalized in Agda.

## Comments

The advantage of not formalizing the syntax/metatheory of the type theory is that we can take some liberties in how we formalize certain aspects of the rule: for example, we take context concatenation to directly correspond to the product of contexts, rather than relying on the more precise inductive definition of contexts as lists of which one would take the product over.

At the same time, compared to a traditional pen-and-paper proof, the formalization has some explicit isomorphisms needed to make everything typecheck. This is most apparent in files like [Dinaturality.CutCoherence](Dinaturality/CutCoherence.agda), where we rely on explicit helpers to simplify compositions of functors that would be transparent/implicit in the syntax in a pen-and-paper proof. Concretely, these operations involve 1. appropriately copying hypotheses inside entailments, 2. applying weakening operations whenever necessary, 3. applying some trivial isomorphisms which are transparent in the syntax but are here explicit because of the way they are implemented in `agda-categories`.

To save on typechecking time and effort, we do not use combinators which are defined in `agda-categories`, and instead manually define some explicit helpers that apply such conversions/weakenings, both to make proofs more readable on what kind of conversions are needed and because they are very easy to prove since they all reduce. For simplicity we do not prove that some of these are (natural) isomorphisms since, e.g., in the case of [Dinaturality.CutCoherence](Dinaturality/CutCoherence.agda), the point of the formalization is just to show that the signature of rules _(cut-din)_ and _(cut-nat)_ can be appropriately massaged in such a way that the statement typechecks modulo some trivial aspects that one would gloss over in the pen-and-paper proof.

## How to run this

### Option 1 (Recommended)

1. Install [Nix](https://nixos.org/download/), and enable [flakes](https://nixos.wiki/wiki/Flakes). Tested with Nix 2.29.0.
2. Run `nix develop`. This puts you in a `bash` shell with a working Agda installation with all libraries installed.
3. Run `nix build`. This `--safe`ly typechecks the entire formalization and builds browsable HTML files.
4. The build is successful if the above command successfuly terminates. The formalization files can be browsed interactively in the `html/` folder, starting from the `All.agda` file.

Using Nix ensures that all dependencies are pinned by `flake.lock` to their correct versions.

### Option 2

1. Install [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) `v2.6.4.1` manually.
2. Install the [`agda-categories`](https://github.com/agda/agda-categories) library `v0.2.0`.
3. Install the [`agda-stdlib`](https://github.com/agda/agda-stdlib) library `v2.0`.
4. Run `agda --html --html-dir=html/ --highlight-occurrences --safe All.agda +RTS -M16G`.
5. The build is successful if the above command successfuly terminates. The formalization files can be browsed interactively in the `html/` folder, starting from the `All.agda` file.

## Description

The file `All.agda` groups all formalization files for batch typechecking/inspection. Typecheck the code by running Agda in Safe Mode:
```bash
$ agda --safe ./All.agda +RTS -M16G  # Recommended flags for Agda.
```

The flake output `agda-html` can be used to typecheck and build the HTML for the `All.agda` file (the above flags are already active):

```bash
$ nix build '.#agda-html' # This typechecks and creates a browsable HTML output.
$ xdg-open html/All.html  # Open html/All.html in your browser.
```

> [!WARNING]
> Most of the files contained here are particularly slow to typecheck and require considerable memory, and might run out of memory even with >8 GB allocated.
> The recommended flags for Agda under which this formalization has been tested are at least `+RTS -M16G`, which should ensure that eventually every file compiles.

## Files structure

Each of the theorems in the paper links to a single formalization file, which typically only has a single main definition. Every file which typechecks is contained in the [All](All.agda) file, which gives a short description of each file.

## Typechecking time

Running `agda --safe ./All.agda +RTS -M16G` on an AMD Ryzen 7 5800X (16) @ 3.792GHz running Debian 12 on WSL2 (Windows 10.0.19045 x86_64) takes approximately ~30 mins to complete (assuming all libraries have been compiled).

## Requirements

- `nix` 2.29.0 (Optional)
- `agda` 2.6.4.1
- `agda-categories` 0.2.0
- `agda-stdlib` 2.0

## License

MIT
