module Main where

-- Runs the program in "TestProgram.hs" (the Haskell extraction of the Coq AST
-- generated from an Erlang file, see "execute_interp.erl") with the sequential
-- interpreter, and prints the result in the format that
-- `execute_coq:parse_coq_result/2` expects (the result as an Erlang term).

import RocqExtraction (Redex(..), Exp(..), Val(..), Lit(..), ExcClass(..))
import SequentialInterpreter
import TestProgram (test)

steps :: Integer
steps = 1000000

main :: IO ()
main = putStrLn (render (run steps [] (RExp (EExp test))))

render :: Outcome -> String
render (Value [v])       = "__coqresult:" ++ erl v
render (Value vs)        = "__coqresult:" ++ erl (VTuple vs)
render (Exc ((c, r), d)) = "__exceptioncoqresult:{" ++ cls c ++ "," ++ erl r ++ "," ++ erl d ++ "}"
render o                 = "__nocoqresult:" ++ show o

cls :: ExcClass -> String
cls Error = "error"
cls Throw = "throw"
cls Exit  = "exit"

-- Values as Erlang terms
erl :: Val -> String
erl VNil               = "[]"
erl (VLit (Atom a))    = "'" ++ a ++ "'"
erl (VLit (Integer i)) = show i
erl (VCons h t)        = "[" ++ erl h ++ "|" ++ erl t ++ "]"
erl (VTuple vs)        = "{" ++ commas (map erl vs) ++ "}"
erl (VMap kvs)         = "#{" ++ commas [erl k ++ "=>" ++ erl v | (k, v) <- kvs] ++ "}"
erl _                  = "'__unsupported__'"

commas :: [String] -> String
commas []       = ""
commas [x]      = x
commas (x : xs) = x ++ "," ++ commas xs
