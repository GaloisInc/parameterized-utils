# Developer documentation

## Downstream projects

When evaluating breaking changes to the API, it can be helpful to consider the needs of major downstream projects (and even provide patches to migrate them).
Here are a few, with brief descriptions of how they use this project:

- [Crucible](https://github.com/GaloisInc/crucible):

  - Crucible's `TypeRepr` is a "singleton" parameterized type, implementing classes such as `EqF`, `KnownRepr`, `HashableF`, and `OrdF`.
  - Crucible uses `Assignment`s to enforce variable-scoping constraints (i.e., the SSA invariant) on its control-flow graphs.
  - Crucible uses the classes from `TraversableFC` to manage its "syntax extensions", as well as its native expression and statement types.
  - Crucible-LLVM embeds the width of pointers as a type-level `Nat`, and uses `NatRepr` to reason about it.

- [Cryptol](https://github.com/GaloisInc/cryptol) depends on `parameterized-utils`.
- [Macaw](https://github.com/GaloisInc/macaw) uses `Assignment`s to represent structs of registers.
- [param-tlc](https://github.com/robdockins/param-tlc) provides an example of how to use `parameterized-utils` to define a strongly-typed lambda-calculus interpreter.
- [SAW](https://github.com/GaloisInc/saw-script) contains parameterized types such as `TypeShape`.
- [What4](https://github.com/GaloisInc/what4) makes extensive use of parameterized types, especially the central `App`, `BaseTypeRepr`, and `Expr` types.
  It uses `Nonce`s to perform cached traversals of terms with sharing (i.e., hash-consing).

## GHC versions

We support at least three versions of GHC at a time.
We are not aggressive about dropping older versions, but will generally do so for versions outside of the support window if maintaining that support would require efforts such as significant numbers of C pre-processor `ifdef` sections or Cabal `if` sections.
We try to support new versions as soon as they are supported by the libraries that we depend on.

### Adding a new version

The following checklist enumerates the steps needed to support a new version of GHC.
When performing such an upgrade, it can be helpful to copy/paste this list into the MR description and check off what has been done, so as to not forget anything.

- [ ] Allow the new version of `base` in the Cabal `build-depends`
- [ ] Run `cabal {build,test,haddock}`, bumping dependency bounds as needed
- [ ] Fix any new warnings from `-Wdefault`
- [ ] Add the new GHC version to the matrix in the GitHub Actions configuration
- [ ] Change the `doc` job to use the new GHC version
- [ ] Add the new version to the code that sets `GHC_NIXPKGS` in the CI config
- [ ] Add the new GHC version to the Cabal `tested-with` field
- [ ] Optionally follow the below steps to remove any old GHC versions

### Removing an old version

- [ ] Remove the old version from the matrix in the GitHub Actions configuration
- [ ] Remove the old version from the Cabal `tested-with` field
- [ ] Remove outdated CPP `ifdef`s that refer to the dropped version
- [ ] Remove outdated `if` stanzas in the Cabal file

## Warnings

`parameterized-utils` is a research-grade codebase.
As developers, we should therefore adopt development practices that enable relatively rapid and frictionless prototyping of interesting functionality.
However, correctness remains a major concern, and we should be willing to invest some effort in practices that reduce bugs.
When forming judgements about appropriate practices, it is worth remembering that `parameterized-utils` is also upstream of a substantial number of projects, such as What4, Crucible, and Macaw.

The developers currently judge that the warnings included in GHC's `-Wdefault` are conservative enough to be worth fixing in most cases.
The documentation for `-Wdefault` [states](https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html#ghc-flag-Wdefault) that they are:

> a standard set of warnings which are generally likely to indicate bugs in your program[^wdefault]

Given that correctness is a high priority, the current default development practice is to fix instances of `-Wdefault` in new code.
However, we also trust one anothers' judgement to override this practice in any particular case.
When doing so, developers are encouraged to disable individual warnings on a per-module basis, ideally accompanied by a comment including some justification for why the warnings were not (and/or should not be) fixed.
To prevent warnings from slipping in unnoticed and thus unexamined, we enable `-Werror=default` in CI.

We also enable `-Werror=compat` in order to gradually prepare for breaking changes in GHC.

To reproduce the behavior of the CI build locally, developers can run
```sh
cabal configure --enable-tests --ghc-options='-Werror=compat -Werror=default'
```

[^wdefault]: Unfortunately, this is not strictly true. `-Wdefault` includes (for example) `-Wtabs`, which is about code style, and `-Winaccessible-code`, which is about dead code. However, the majority of the warnings in `-Wdefault` do indeed affect correctness, and hence should generally be fixed.
