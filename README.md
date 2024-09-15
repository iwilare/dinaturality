# Directed equality with dinaturality

Agda formalization for the main theorems given in the paper "Directed equality with dinaturality" by Laretto, Loregian, Veltri.

## How to run this

Install [Nix](https://nixos.org/download/) [with flakes](https://nixos.wiki/wiki/Flakes) enabled, then run `nix develop` to have a working Agda installation.

## Files structure

Each of the theorems in the paper links to a single formalization file, which typically only has a single main definition with secondary stuff defined later.

## Comments

Every file which typechecks is contained in the [All](All.agda) file.

The only file worthy of comment is the file for the [left relative adjunction](Dinaturality/Sketch/HomRelativeAdjunction.agda), given in the [Sketch/](Dinaturality/Sketch/HomRelativeAdjunction.agda) folder, for which only a minimal formalization sketch is provided. See the description at the top of the file.

Files in the folder [Failure/](Dinaturality/Failure/) do not typecheck (on purpose) and they are not included in the [All](All.agda) file. They are just brief sanity-checks to verify that something is not easily provable.

## Requirements

- `agda` 2.6.4.1
- `agda-categories` 0.2.0
