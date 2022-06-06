{-# OPTIONS --guardedness #-}
module Main where

open import InsertSort

open import IO
open import Data.Nat.Show
open import Data.Unit.Polymorphic
open import Level

putList : {l : Level} -> List -> IO (⊤ {l})
putList [] = putStr "[]"
putList (x +> l) = putStr "[" >> putStr (show x) >> putRest l
  where
    putRest : List -> IO ⊤
    putRest [] = putStr "]"
    putRest (x +> l) = putStr ", " >> putStr (show x) >> putRest l

main : Main
main = run (putList (324 +> 49 +> 292 +> 9 +> []) >> putStrLn "")
