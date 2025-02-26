# Developer documentation

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

[^wdefault]: Unfortunately, this is not strictly true. `-Wdefault` includes (for example) `-Wtabs`, which is about code style, and `-Winaccessible-code`, which is about dead code. However, the majority of the warnings in `-Wdefault` do indeed affect correctness, and hence should generally be fixed.
