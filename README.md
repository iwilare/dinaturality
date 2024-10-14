# Directed equality for (co)end calculus

## How to run this

Install [Nix](https://nixos.org/download/) [with flakes](https://nixos.wiki/wiki/Flakes) enabled, then run `nix develop` to have a working Agda installation. Alternatively, install the correct [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) version manually.

The file `All.agda` groups all formalization files for batch typechecking/inspection. Typecheck the code by running Agda in Safe Mode:
```bash
$ agda --safe ./All.agda
```

> [!WARNING]
> Most of the files contained here are particularly slow to typecheck and require considerable memory, and might run out of memory even with 16 GB allocated.
> The recommended flags for Agda under which this formalization has been tested are `+RTS -M32G`, which should ensure that eventually every file compiles.

The flake output `agda-html` can be used to typecheck and build the HTML for the `All.agda` file (the above flags are already active):

```bash
$ nix build '.#agda-html' # This typechecks and creates a browsable HTML output.
$ xdg-open html/All.html  # Open html/All.html in your browser.
```

## Files structure

Each of the theorems in the paper links to a single formalization file, which typically only has a single main definition with secondary definitions given later.

## Comments

Naturality of the rules is only shown for the case of exponentials in [Dinaturality.NaturalExample](Dinaturality/NaturalityExample.agda), due to the technical limitation of running out of memory for most of the remaining rules.
Finding a workaround to fully formalize naturality for every rule is left for future work.

Every file which typechecks is contained in the [All](All.agda) file.

The formalization for the left relative adjunction in [Dinaturality/Sketch/HomRelativeAdjunction](Dinaturality/Sketch/HomRelativeAdjunction.agda) contains only a minimal formalization sketch. See the description at the top of the file.

Files in the folder [Failure/](Dinaturality/Failure/) do not typecheck (on purpose), and they are not included in the [All](All.agda) file. They are just sanity checks to verify that something is not provable.

## Requirements

- `agda` 2.6.4.1 (flags: `+RTS -M32G`)
- `agda-categories` 0.2.0
