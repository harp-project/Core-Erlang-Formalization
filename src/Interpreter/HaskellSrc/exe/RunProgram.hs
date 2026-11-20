module Main where

-- Runs the program in "TestProgram.hs" (the Haskell extraction of the Coq AST
-- generated from an Erlang file, see "execute_interp.erl") with the sequential
-- interpreter, and prints the result in the format that
-- `execute_coq:parse_coq_result/2` expects (the result as an Erlang term).

import RocqExtraction (Redex(..), Exp(..), Val(..), Lit(..), ExcClass(..), Bvn(..), N(..), bvn_unsigned)
import SequentialInterpreter
import Data.Bits (shiftR, (.&.))
import Numeric (showHex)
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
-- quotes, backslashes, control and non-ASCII characters are escaped, so the
-- atom is read back exactly by erl_scan, and the output is plain ASCII
erl (VLit (Atom a))    = "'" ++ concatMap escape a ++ "'"
  where
    escape '\'' = "\\'"
    escape '\\' = "\\\\"
    escape c
      | c >= ' ' && c <= '~' = [c]
      | otherwise            = "\\x{" ++ showHex (fromEnum c) "" ++ "}"
erl (VLit (Integer i)) = show i
erl (VCons h t)        = "[" ++ erl h ++ "|" ++ erl t ++ "]"
erl (VTuple vs)        = "{" ++ commas (map erl vs) ++ "}"
erl (VMap kvs)         = "#{" ++ commas [erl k ++ "=>" ++ erl v | (k, v) <- kvs] ++ "}"
-- The value of a bitstring is stored MSB first: the whole bytes are taken from
-- the top, and the remaining bits (if any) are printed as Value:Size,
-- e.g. a 12-bit 0xABC is <<171,12:4>>
erl (VBitstring b@(Bv_to_bvn size _)) = "<<" ++ commas (bytes ++ rest) ++ ">>"
  where
    n = case size of { N0 -> 0; Npos p -> p }
    v = bvn_unsigned b
    (q, r) = n `divMod` 8
    bytes = [show ((v `shiftR` fromInteger (n - 8 * (i + 1))) .&. 255) | i <- [0 .. q - 1]]
    rest  = [show (v .&. (2 ^ r - 1)) ++ ":" ++ show r | r > 0]
erl _                  = "'__unsupported__'"

commas :: [String] -> String
commas []       = ""
commas [x]      = x
commas (x : xs) = x ++ "," ++ commas xs
