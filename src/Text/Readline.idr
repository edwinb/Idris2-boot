module Text.Readline

%include C "readline/readline.h"
%include C "readline/history.h"

prim_readline : String -> IO String
prim_readline = foreign FFI_C "readline" (String -> IO String)

export
readline : String -> IO (Maybe String)
readline prompt = do
  s <- prim_readline prompt
  isNull <- nullStr s
  if isNull
     then pure Nothing
     else pure $ Just s

export
addHistory : String -> IO ()
addHistory = foreign FFI_C "add_history" (String -> IO ())
