Introduction
------------
The goal of this patch is to experiment with the introduction of temperature,
in an attempt to get better cache locality. It also features slightly cheaper
exception handlers.


Attributes
----------
Functions can be annotated with either `[@hot]` or `[@cold]`, while
`if`/`then`/`else` constructs and `try`/`with` constructs can be annotated
with either `[@likely]` or `[@unlikely]`:

```
let[@hot] a_hot_function ... = ...
let[@cold] a_cold_function ... = ...

let ... =
  ...
  if[@likely] then ... else ...
  ...
  if[@unlikely] then ... else ...
  ...
  try[@likely] ... with ...
  ...
  try[@unlikely] ... with ...
  ...
```

A function annotated with `[@hot]` (resp. `[@cold]`) will simply be placed
in the hot (resp. cold) section of the program.

The `[@likely]` (resp. `[@unlikely]`) annotation on an `if`/`then`/`else`
construct means that the condition is expected to evaluate to `true` (resp.
`false`).

The `[@likely]` (resp. `[@unlikely]`) annotation on a `try`/`with` construct
means that the protected expression is expected to fully evaluate (resp. not
fully evaluate). In other words, in `try[@likely] e with ...`, `e` is expected
not to raise any exception, while in `try[@unlikely] e with ...`, `e` is
expected to raise an exception.


Computed attributes
-------------------
Besides attributes explicitly specified by the developer, some are
automatically computed by the compiler. The current version only performs
such computations on `if`/`then`/`else` constructs whose condition is using
either `&&` or `||` as the top-most operator.

If the expression is `if[@ifattr] (arg1 && arg2) ...`, then attributes are
computed as follows:

| ifattr   | arg1 attribute | arg2 attribute |
|----------|----------------|----------------|
| *none*   | *none*         | *none*         |
| likely   | likely         | likely         |
| unlikely | *none*         | unlikely       |

If the expression is `if[@ifattr] (arg1 || arg2) ...`, then attributes are
computed as follows:

| ifattr   | arg1 attribute | arg2 attribute |
|----------|----------------|----------------|
| *none*   | *none*         | *none*         |
| likely   | *none*         | likely         |
| unlikely | unlikely       | unlikely       |


Inlining
--------
When computing the inlining cost of an `if`/`then`/`else` construct, if the
construct is annotated with `[@likely]` (resp. `[@unlikely]`) then only the
code from the `then` (resp. `else`) branch is taken into account.

Similarly, if a `try`/`with` construct is annotated with `[@likely]` then
only the body of the expression (as opposed to the exception handler) is
taken into account.


Temperature of a given instruction
----------------------------------
The temperature of a given instruction (*i.e.* the code section it belongs to)
is determined by applying the following rules:

- the temperature at the start of a function is the function temperature
  (i.e. hot if annotated with `[@hot]` and cold if annotated `[@cold]`, tepid
  otherwise);
- the temperature at the start of a module entry function is tepid;
- `if`/`then`/`else`

  | attribute   | current temperature | then temperature | else temperature |
  |-------------|---------------------|------------------|------------------|
  | [@likely]   | cold                | cold             | cold             |
  | [@likely]   | tepid               | tepid            | cold             |
  | [@likely]   | hot                 | hot              | cold             |
  | [@unlikely] | cold                | cold             | cold             |
  | [@unlikely] | tepid               | cold             | tepid            |
  | [@unlikely] | hot                 | cold             | hot              |
- `try`/`with`

  | attribute   | current temperature | try temperature | with temperature |
  |-------------|---------------------|-----------------|------------------|
  | [@likely]   | cold                | cold            | cold             |
  | [@likely]   | tepid               | tepid           | cold             |
  | [@likely]   | hot                 | hot             | cold             |
  | [@unlikely] | cold                | cold            | cold             |
  | [@unlikely] | tepid               | tepid           | tepid            |
  | [@unlikely] | hot                 | hot             | hot              |
- other constructs do not modify the temperature.

For instance, given the following code:
```
let[@hot] f ... =
  expr_before;
  if[@likely] ... then
    expr_then
  else
    expr_else;
  expr_after
```
the compiler will emit `expr_before`, `expr_then`, and `expr_after` in the
hot section while `expr_else` will be emitted in the cold section. The whole
`expr_before`/`expr_then`/`expr_after` sequence is hence contiguous.
Additionally, the conditional jump related to the condition will be followed
only in the unlikely case (*i.e.* if the condition evaluates to `false`).


Exception handlers
------------------
The compilation of the exception handler is modified in order to avoid a jump
before evaluating the `try` expression. Moreover, if the `try` and `with` have
different temperatures there is no jump after evaluating the `try` expression.
In practice, it means that the execution of `try[@likely] e with ...` is
jump-free (with respect to the compilation of `try`/`with`) if `e` does not
raise.


Differences with the previous patch
-----------------------------------
- the previous version did not support attributes on `try`/`with` constructs;
- the previous version did not include the `setuptrap` optimization
  (cheaper exception handlers);
- the previous version marked `[@cold]` a function with no `[@hot]`/`[@cold]`
  attribute but marked `[@inline never]`;
- the previous version marked `[@cold]` functions that always raise;
- the previous version implicitly added attributes to generated code
  (for instance, accesses to float arrays were marked `[@cold]`);
- the output of various `-dxyz` command-line switches has been modified;


Implementation details
----------------------
- the code maintains an "explicit" boolean (currently unused) in order
  to distinguish user-provided annotations from compiler-introduced ones;
- the description above is about the native compiler; the bytecode compiler
  only uses the attribute on `if`/`else` constructs in order to avoid a
  conditional jump in the likely case;
- the computation of the temperature of a given instruction is performed
  during linearization;
- all expressions introduced by pattern matching compilation are tepid;
- all expressions introduced by spacetime instrumentation are tepid;
- all expressions introduced to handle divisions by zero are cold;
- all expressions introduced to handle assertions are cold;
- all expressions checking the tags of generic arrays are tepid;
- all cache checks (objects) are tepid;
- all send/apply/curry/tuplify functions are hot.


TODO
----
- check whether [Linearize.fix_label_temperatures] is still needed;
- check whether [Linearize.add_jump_for_temperature_changes] is still needed;
- check whether the patch is OK under macOS;
  (note: LLVM uses ".section .text.cold" under Linux but
   ".section __TEXT,__text.cold,regular,pure_instructions" under Darwin);
- check whether the patch is OK under Windows;
- extend the patch to other backends.
