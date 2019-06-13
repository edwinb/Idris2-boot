module PrimIO

import Builtin

public export
data IORes : Type -> Type where
     MkIORes : (result : a) -> (1 x : %World) -> IORes a

export
data IO : Type -> Type where
     MkIO : (1 fn : (1 x : %World) -> IORes a) -> IO a

export
io_pure : a -> IO a
io_pure x = MkIO (\w => MkIORes x w)

export
io_bind : (1 act : IO a) -> (1 k : a -> IO b) -> IO b
io_bind (MkIO fn)
    = \k => MkIO (\w => let MkIORes x' w' = fn w 
                            MkIO res = k x' in
                            res w')

%extern prim__putStr : String -> (1 x : %World) -> IORes ()
%extern prim__getStr : (1 x : %World) -> IORes String

public export
data Ptr : Type where

public export
data ThreadID : Type where

public export
data FArgList : Type where
     Nil : FArgList
     (::) : {a : Type} -> (1 arg : a) -> (1 args : FArgList) -> FArgList

%extern prim__cCall : (ret : Type) -> String -> (1 args : FArgList) -> 
                      (1 x : %World) -> IORes ret
%extern prim__schemeCall : (ret : Type) -> String -> (1 args : FArgList) -> 
                           (1 x : %World) -> IORes ret

export %inline
primIO : (1 fn : (1 x : %World) -> IORes a) -> IO a
primIO op = MkIO op

export %inline
schemeCall : (ret : Type) -> String -> (1 args : FArgList) -> IO ret
schemeCall ret fn args = primIO (prim__schemeCall ret fn args)
 
export %inline
cCall : (ret : Type) -> String -> FArgList -> IO ret
cCall ret fn args = primIO (prim__cCall ret fn args)
 
export
putStr : String -> IO ()
putStr str = primIO (prim__putStr str)

export
putStrLn : String -> IO ()
putStrLn str = putStr (prim__strAppend str "\n")

export
getLine : IO String
getLine = primIO prim__getStr

export
fork : (1 prog : IO ()) -> IO ThreadID
fork (MkIO act) = schemeCall ThreadID "blodwen-thread" [act]

unsafeCreateWorld : (1 f : (1 x : %World) -> a) -> a
unsafeCreateWorld f = f %MkWorld

unsafeDestroyWorld : (1 x : %World) -> a -> a
unsafeDestroyWorld %MkWorld x = x

export
unsafePerformIO : IO a -> a
unsafePerformIO (MkIO f)
    = unsafeCreateWorld (\w => case f w of
                               MkIORes res w' => unsafeDestroyWorld w' res)
