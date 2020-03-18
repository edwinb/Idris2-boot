module recordname

namespace Foo
  export
  record Name where
    constructor MkName
    foo : Int

  x : Name -> Int
  x = foo

test : recordname.Foo.Name
