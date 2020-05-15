module System

import Data.So

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign support "idris2_sleep"
prim_sleep : Int -> PrimIO ()
%foreign support "idris2_usleep"
prim_usleep : Int -> PrimIO ()

export
sleep : Int -> IO ()
sleep sec = primIO (prim_sleep sec)

export
usleep : (x : Int) -> So (x >= 0) => IO ()
usleep sec = primIO (prim_usleep sec)

-- This one is going to vary for different back ends. Probably needs a
-- better convention. Will revisit...
%foreign "scheme:blodwen-args"
prim__getArgs : PrimIO (List String)

export
getArgs : IO (List String)
getArgs = primIO prim__getArgs

%foreign "C:getenv,libc 6"
prim_getEnv : String -> PrimIO (Ptr String)

export
getEnv : String -> IO (Maybe String)
getEnv var
   = do env <- primIO $ prim_getEnv var
        if prim__nullPtr env /= 0
           then pure Nothing
           else pure (Just (prim__getString env))

%foreign "C:system,libc 6"
         "scheme:blodwen-system"
prim_system : String -> PrimIO Int

export
system : String -> IO Int
system cmd = primIO (prim_system cmd)

%foreign support "idris2_time"
         "scheme:blodwen-time"
prim_time : PrimIO Int

export
time : IO Integer
time = pure $ cast !(primIO prim_time)
