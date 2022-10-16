module Formula where

import GHC.Natural (Natural)

data Formula = Falsum | Atom Natural | And Formula Formula | Or Formula Formula | Impl Formula Formula
  deriving (Eq)

instance Show Formula where
  showsPrec _ Falsum = ("\\bot" ++)
  showsPrec _ (Atom n) = if n < 10 then ("A_" ++) . (show n ++) else ("A_{" ++) . (show n ++) . ("}" ++)
  showsPrec p (And f1 f2) = showParen (p >= 3) $ showsPrec 3 f1 . (" \\land " ++) . showsPrec 3 f2
  showsPrec p (Or f1 f2) = showParen (p >= 2) $ showsPrec 2 f1 . (" \\lor " ++) . showsPrec 2 f2
  showsPrec _ (Impl f1 Falsum) = ("\\lnot " ++) . showsPrec 5 f1
  showsPrec p (Impl f1 f2) = showParen (p >= 4) $ showsPrec 4 f1 . (" \\rightarrow " ++) . showsPrec 4 f2

infixr 4 -->

(-->) :: Formula -> Formula -> Formula
(-->) = Impl

infixr 3 /\

(/\) :: Formula -> Formula -> Formula
(/\) = And

infixr 2 \/

(\/) :: Formula -> Formula -> Formula
(\/) = Or

type AssumptionCounter = Natural

data Assumption = Assumption Formula AssumptionCounter
  deriving (Show)

type Theory = [Formula]

data DeductionTree = Tree Formula (Maybe AssumptionCounter) [DeductionTree] | Assumption' Assumption
  deriving (Show)

conclusion :: DeductionTree -> Formula
conclusion (Tree f _ _) = f
conclusion (Assumption' (Assumption f _)) = f

collectKnown :: [DeductionTree] -> [DeductionTree]
collectKnown = go []
  where
    go acc [] = acc
    go acc (deduction : rest) = case conclusion deduction of
      And lhs rhs ->
        let lhsDeduction = Tree lhs Nothing [deduction]
            rhsDeduction = Tree rhs Nothing [deduction]
         in go acc (lhsDeduction : rhsDeduction : rest)
      _ -> deduction : go acc rest
