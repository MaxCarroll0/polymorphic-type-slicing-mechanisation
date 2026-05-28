# polymorphic-type-slicing-formalism

Agda mechanisation accompanying my Part III (Cambridge) dissertation
[polymorphic-type-slicing-tex](https://github.com/MaxCarroll0/polymorphic-type-slicing-tex)
on **polymorphic type slicing** for bidirectional, gradually-typed languages.

## Verify type-checking with Nix

Install Nix with flakes if you don't have it:

```
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

Then:

```
nix build github:MaxCarroll0/polymorphic-type-slicing-formalism
```

Alternatively, clone the repo and run `nix build` within.

The build runs `agda -W error --double-check all.agda` against the pinned
standard library and writes:

- `result/build.log` — full Agda output
- `result/status` — `PASS …` or `FAIL …` with the agda exit code

The Nix build itself always succeeds (so the log is recoverable even on a
failing check); read `result/status` to confirm type-checking actually passed.

## Dev shell
Use direnv with the .envrc or nix develop:

```
nix develop
```

Then, `agda all.agda` type-checks the whole project.
