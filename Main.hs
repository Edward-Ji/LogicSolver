{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Applicative (empty, (<|>))
import Data.List (intersperse)
import Formula
  ( Assumption (Assumption),
    DeductionTree (Assumption', Tree),
    Formula (And, Atom, Falsum, Impl, Or),
    Theory,
    conclusion,
  )
import Solver
  ( Solver,
    SolverEnviron (Environ),
    System (Classical, Intuitionistic),
    constructFromKnownDeduction,
    findKnown,
    getSystem,
    runSolver,
    withAssumption,
    withoutKnown,
  )

printDeductionTree :: DeductionTree -> IO ()
printDeductionTree = go 0
  where
    spaces :: Int -> String
    spaces = flip replicate ' ' . (* 4)

    go :: Int -> DeductionTree -> IO ()
    go indentLevel (Assumption' (Assumption f counter)) = do
      putStr $ spaces indentLevel
      putChar '['
      putStr $ show f
      putStr "]^"
      print counter
    go indentLevel (Tree f _ []) = do
      putStr $ spaces indentLevel
      print f
    go indentLevel (Tree f maybeCounter inferences) = do
      putStr $ spaces indentLevel
      putStr "\\infer"
      case maybeCounter of
        Nothing -> putChar '\n'
        Just counter -> do putStr "[^"; putStr $ show counter; putStr "]\n"
      putStr $ spaces (indentLevel + 1)
      putChar '{'
      putStr $ show f
      putStr "}\n"
      putStr $ spaces (indentLevel + 1)
      putStr "{\n"
      sequence_ $ intersperse (putStr (spaces (indentLevel + 2)) >> putStrLn "&") $ map (go (indentLevel + 2)) inferences
      putStr $ spaces (indentLevel + 1)
      putStr "}\n"

proofNI :: Formula -> Theory -> Maybe DeductionTree
proofNI f theory = fst <$> runSolver (proof' f) (Environ theory Intuitionistic)

proofNK :: Formula -> Theory -> Maybe DeductionTree
proofNK f theory = fst <$> runSolver (proof' f) (Environ theory Classical)

proof' :: Formula -> Solver DeductionTree
proof' f =
  proofFromKnown f
    <|> proofByIntroduction f
    <|> proofByElimination f
    <|> ( getSystem
            >>= ( \case
                    Intuitionistic -> empty
                    Classical -> proofByContradiction f
                )
        )

proofFromKnown :: Formula -> Solver DeductionTree
proofFromKnown f = constructFromKnownDeduction (\deduction -> if conclusion deduction == f then return deduction else empty)

proofByIntroduction :: Formula -> Solver DeductionTree
proofByIntroduction f = case f of
  Falsum -> empty
  Atom _ -> empty
  And lhs rhs -> Tree f Nothing <$> sequence [proof' lhs, proof' rhs]
  Or lhs rhs -> Tree f Nothing . return <$> (proof' lhs <|> proof' rhs)
  Impl lhs rhs -> do
    (rhsProof, assumptionNumber) <- proof' rhs `withAssumption` Left lhs
    return $ Tree f (Just assumptionNumber) [rhsProof]

proofByElimination :: Formula -> Solver DeductionTree
proofByElimination f = eliminateAnd <|> eliminateImplication <|> eliminateOr <|> eliminateFalsum
  where
    eliminateAnd :: Solver DeductionTree
    eliminateAnd = Tree f Nothing . return <$> findKnown (\case And lhs rhs -> f == lhs || f == rhs; _ -> False)

    eliminateImplication :: Solver DeductionTree
    eliminateImplication = do
      constructFromKnownDeduction
        ( \deduction -> case conclusion deduction of
            Impl lhs rhs ->
              if rhs /= f
                then empty
                else (\lhsDeduction -> Tree f Nothing [lhsDeduction, deduction]) <$> proof' lhs
            _ -> empty
        )

    eliminateOr :: Solver DeductionTree
    eliminateOr =
      constructFromKnownDeduction
        ( \deduction -> case conclusion deduction of
            Or lhs rhs ->
              ( do
                  (leftDeduction, assumptionNumber) <- proof' f `withAssumption` Left lhs
                  (rightDeduction, _) <- proof' f `withAssumption` Right (Assumption rhs assumptionNumber)
                  return $ Tree f (Just assumptionNumber) [deduction, leftDeduction, rightDeduction]
              )
                `withoutKnown` deduction
            _ -> empty
        )

    eliminateFalsum :: Solver DeductionTree
    eliminateFalsum =
      constructFromKnownDeduction
        ( \deduction -> case conclusion deduction of
            Falsum -> return $ Tree f Nothing [deduction]
            _ -> empty
        )

proofByContradiction :: Formula -> Solver DeductionTree
proofByContradiction f = case f of
  Impl _ Falsum -> empty -- This case should already be handled by the (->) introduction
  Falsum -> empty -- Proving falsum by contradiction doesn't make sense
  _ -> do
    (falsumProof, assumptionNumber) <- proof' Falsum `withAssumption` Left (Impl f Falsum)
    return $ Tree f (Just assumptionNumber) [falsumProof]

main :: IO ()
main = undefined
