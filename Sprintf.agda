{-# OPTIONS --safe #-}
module Sprintf where

open import Data.Char
open import Data.List
open import Data.Integer
open import Data.Float
open import Data.String

sprintf-type : List Char -> Set
sprintf-type [] = String
sprintf-type (x ∷ []) = String
sprintf-type ('$' ∷ 'd' ∷ s) = ℤ -> sprintf-type s
sprintf-type ('$' ∷ 'f' ∷ s) = Float -> sprintf-type s
sprintf-type ('$' ∷ 'c' ∷ s) = Char -> sprintf-type s
sprintf-type ('$' ∷ '$' ∷ s) = sprintf-type s
sprintf-type (a ∷ b ∷ s) = sprintf-type (b ∷ s)

sprintf-lc : (s : List Char) -> sprintf-type s
sprintf-lc [] = ""
sprintf-lc (x ∷ []) = fromList (x ∷ [])
sprintf-lc ('$' ∷ 'd' ∷ s) z = {!Data.Integer.show z!}
sprintf-lc ('$' ∷ 'f' ∷ s) = {!!}
sprintf-lc ('$' ∷ 'c' ∷ s) = {!!}
sprintf-lc ('$' ∷ '$' ∷ s) = {!!}
sprintf-lc (a ∷ b ∷ s) = {!!}

sprintf : (s : String) -> sprintf-type (toList s)
sprintf s = sprintf-lc (toList s)
