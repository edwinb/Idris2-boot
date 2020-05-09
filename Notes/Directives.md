# Compiler Directives

There are a number of directives (instructions to the compiler, beginning with
a `%` symbol) which are not part of the Idris 2 language, but nevertheless
provide useful information to the compiler. Mostly these will be useful for
library (especially Prelude) authors. They are ordered here approximately
by "likelihood of being useful to most programmers".

## Language directives

### %name

Syntax: `%name <name> <name_list>`

For interactive editing purposes, use `<name_list>` as the preferred names
for variables with type `<name>`.

### %hide

Syntax: `%hide <name>`

Throughout the rest of the file, consider the `<name>` to be private to its
own namespace.

### %auto_lazy

Syntax: `%auto_lazy <on | off>`

Turn the automatic insertion of laziness annotations on or off. Default is
`on` as long as `%lazy` names have been defined (see below).

### %runElab

Syntax: `%runElab <expr>`

NOT YET IMPLEMENTED

Run the elaborator reflection expression `<expr>`, which must be of type
`Elab a`. Note that this is only minimally implemented at the moment.

### %pair

Syntax: `%pair <pair_type> <fst_name> <snd_name>`

Use the given names in `auto` implicit search for projecting from pair types.

### %rewrite

Syntax: `%rewrite <rewrite_name>`

Use the given name as the default rewriting function in the `rewrite` syntax.

### %integerLit

Syntax: `%integerLit <fromInteger_name>`

Apply the given function to all integer literals when elaborating.
The default Prelude sets this to `fromInteger`.

### %stringLit

Syntax: `%stringLit <fromString_name>`

Apply the given function to all string literals when elaborating.
The default Prelude does not set this.

### %charLit

Syntax: `%charLit <fromChar_name>`

Apply the given function to all character literals when elaborating.
The default Prelude does not set this.

### %allow_overloads

Syntax: `%allow_overloads <name>`

This is primarily for compatibility with the Idris 1 notion of name overloading
which allows in particular `(>>=)` and `fromInteger` to be overloaded in an
ad-hoc fashion as well as via the `Monad` and `Num` interfaces respectively.

It effect is: If `<name>` is one of the possibilities in an ambiguous
application, and one of the other possibilities is immediately resolvable by
return type, remove `<name>` from the list of possibilities.

If this sounds quite hacky, it's because it is. It's probably better not to
use it other than for the specific cases where we need it for compatibility.
It might be removed, if we can find a better way to resolve ambiguities with
`(>>=)` and `fromInteger` in particular!

## Implementation/debugging directives

### %logging

Syntax: `%logging <level>`

Set the logging level. In general `1` tells you which top level declaration
the elaborator is working on, up to `5` gives you more specific details of
each stage of the elaboration, and up to `10` gives you full details of
type checking including progress on unification problems

## Code Generator Directives

### %cg

#### Backend code injection

Syntax:
* `%cg <backend> <single-line instruction>`
* `%cg <backend> { <multi-line instructions> }`

The given instructions are passed directly to the code generator, to be
interpreted in a backend-specific way.

Currently known backends are: `chez`, `chicken`, `racket` and `gambit`.

## Backend Specific Directives

### Chez

#### Dynamic library loading

Syntax: `%cg chez lib<library_name>`

Instructs chez to load given external library at
runtime, eg. using dynamic library loader. The compiler looks for a
file called  `library_name` in the following directories and generates
corresponding file-loading code:

* current directory `.`
* directories listed in the `IDRIS2_LIBS` environment variable, if
  set
* directories `lib/` in each package the code depends on (`base` and
  `prelude` are automatically added). Loads library as absolute path name of _first matchine file_
  found.
* directory `lib/` in the Idris2 installation path (usually
  `~/.idris2/idris2`).

Note the file is loaded referencing an absolute path of the first
matching file found, except when it's the current directory in which
case the file is simply referenced as `./library_name`

### Chicken

The directive should be scheme code which is inserted directly into the generated
code. This can be used, for example, to import external libraries, e.g.
`%cg chicken (use posix)`.
