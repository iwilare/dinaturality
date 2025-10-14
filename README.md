## Di- is for Directed: First-Order Directed Type Theory via Dinaturality

The formalization supports the claims made in the paper about the semantics using categories, (di)functors, dipresheaves, and dinatural transformations. We do not formalize the syntax/metatheory of the type theory.

## How to run this

### Option 1

1. Install [Nix](https://nixos.org/download/), and enable [flakes](https://nixos.wiki/wiki/Flakes).
2. Run `nix develop` to have a working Agda installation.
3. Run `nix build` to `--safe`ly typecheck the entire formalization and build browsable HTML files.

### Option 2

1. Install [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) `v2.6.4.1` manually.
2. Install the [`agda-categories`](https://github.com/agda/agda-categories) library `v0.2.0`.
3. Install the [`agda-stdlib`](https://github.com/agda/agda-stdlib) library `v2.0`.
4. Run `agda --html --html-dir=html/ --highlight-occurrences --safe All.agda +RTS -M16G`.
5. Browse the formalization, starting from the `All.agda` file.

# Description

The file `All.agda` groups all formalization files for batch typechecking/inspection. Typecheck the code by running Agda in Safe Mode:
```bash
$ agda --safe ./All.agda +RTS -M16G  # Recommended flags for Agda.
```

> [!WARNING]
> Most of the files contained here are particularly slow to typecheck and require considerable memory, and might run out of memory even with >8 GB allocated.
> The recommended flags for Agda under which this formalization has been tested are `+RTS -M16G`, which should ensure that eventually every file compiles.

The flake output `agda-html` can be used to typecheck and build the HTML for the `All.agda` file (the above flags are already active):

```bash
$ nix build '.#agda-html' # This typechecks and creates a browsable HTML output.
$ xdg-open html/All.html  # Open html/All.html in your browser.
```

## Files structure

Each of the theorems in the paper links to a single formalization file, which typically only has a single main definition.

## Comments

Naturality of the rules is only shown for the case of exponentials in [Dinaturality.NaturalExample](Dinaturality/NaturalityExample.agda), due to the technical limitation of running out of memory for most of the remaining rules.
Finding a workaround to fully formalize naturality for every rule is left for future work.

Every file which typechecks is contained in the [All](All.agda) file.

## Typechecking time

Running `agda --safe ./All.agda +RTS -M16G` on an AMD Ryzen 7 5800X (16) @ 3.792GHz running Debian 12 on WSL2 (Windows 10.0.19045 x86_64) takes approximately ~30 mins to complete (assuming all libraries have been compiled).

## Requirements

- `agda` 2.6.4.1
- `agda-categories` 0.2.0
- `agda-stdlib` 2.0
