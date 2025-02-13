# Developer documentation

## Warnings

`parameterized-utils` is a research-grade codebase, so correctness in all cases is not *always* the highest priority.
In particular, as developers, we must weigh the cost of development practices that prioritize correctness, uniformity, or other concerns against our desire to encourage relatively rapid prototyping of interesting functionality.
When forming judgements about appropriate practices, it is worth remembering that `parameterized-utils` is also upstream of a substantial number of projects, such as What4, Crucible, and Macaw.

The developers currently judge that the warnings included in GHC's `-Wdefault` are conservative enough to be worth fixing in most cases.
Accordingly, the current default development practice is to fix instances of `-Wdefault` in new code.
However, we also trust one anothers' judgement to override this practice in any particular case.
When doing so, developers are encouraged to disable individual warnings on a per-module basis, ideally accompanied by a comment including some justification for why the warnings were not (and/or should not be) fixed.
To prevent warnings from slipping in unnoticed and thus unexamined, we enable `-Werror=default` in CI.

We also enable `-Werror=compat` in order to gradually prepare for breaking changes in GHC.