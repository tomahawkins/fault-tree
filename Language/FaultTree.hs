module Language.FaultTree
  ( Event (..)
  , imply
  , dot
  , cutsets
  ) where

import Data.List
import Data.Maybe
import Math.SMT.Yices.Pipe
import Math.SMT.Yices.Syntax
import Text.Printf

type Name = String

-- | An event.
data Event
  = Leaf   Name         -- ^ Leaf node.
  | Branch Name Event   -- ^ Named branch node.
  | Not         Event   -- ^ Logical NOT.
  | And        [Event]  -- ^ Logical AND.
  | Or         [Event]  -- ^ Logical OR.
  deriving (Show, Eq)

-- | Logical implication.
imply :: Event -> Event -> Event
imply a b = Or [Not a, b]

-- | Render a Graphviz dot file from a set of 'Event' (fault) trees.
dot :: [Event] -> String
dot a = unlines
  [ "digraph {"
  , "\trankdir=BT"
  , unlines $ map node events'
  , unlines $ map edge events'
  , "}"
  ]
  where
  events'' :: [(Event, String)]
  events'' = [ (a, "event_" ++ show i) | (i, a) <- zip [0 ..] $ nub $ concatMap events a ]
  events' = fst $ unzip events''
  eventId :: Event -> String
  eventId a = fromJust $ lookup a events''
  node :: Event -> String
  node a = case a of
    Leaf   name   -> printf "\t%s [label=\"%s\"]"  (eventId a) name
    Branch name _ -> printf "\t%s [label=\"%s\"]"  (eventId a) name
    Not _         -> printf "\t%s [label=\"NOT\"]" (eventId a)
    And _         -> printf "\t%s [label=\"AND\"]" (eventId a)
    Or  _         -> printf "\t%s [label=\"OR\"]"  (eventId a)

  edge :: Event -> String
  edge a = case a of
    Leaf _     -> ""
    Branch _ b -> printf "\t%s -> %s" (eventId b) (eventId a)
    Not b      -> printf "\t%s -> %s" (eventId b) (eventId a)
    And b      -> unlines [ printf "\t%s -> %s" (eventId b) (eventId a) | b <- b ]
    Or  b      -> unlines [ printf "\t%s -> %s" (eventId b) (eventId a) | b <- b ]

-- Unique list of events.
events :: Event -> [Event]
events a = case a of
  Leaf _     -> [a]
  Branch _ b -> a : events b
  Not b      -> a : events b
  And b      -> a : nub (concatMap events b)
  Or  b      -> a : nub (concatMap events b)

-- | Minimal cut set analysis.
-- > cutsets pathToYices maxNumberOfLeafEvents failureEvent assumptions
cutsets :: FilePath -> Int -> Event -> [Event] -> IO ()
cutsets yices n event assumes = do
  --mapM_ print model
  check 1 []
  where
  eventId :: Event -> String
  eventId a = fromJust $ lookup a eventNames
  events' = nub $ concatMap events $ event : assumes
  eventNames = [ (a, "event_" ++ show i) | (i, a) <- zip [0 ..] events' ]
  model :: [CmdY]
  model = map var events' ++ mapMaybe expr events' ++ [ASSERT $ VarE $ eventId event] ++ [ ASSERT $ VarE $ eventId assume | assume <- assumes ]
  var :: Event -> CmdY
  var a = DEFINE (eventId a, VarT "bool") Nothing
  expr :: Event -> Maybe CmdY
  expr a = case a of
    Leaf _     -> Nothing
    Branch _ b -> Just $ ASSERT $ VarE (eventId a) := VarE (eventId b)
    Not b      -> Just $ ASSERT $ VarE (eventId a) := NOT (VarE $ eventId b)
    And b      -> Just $ ASSERT $ VarE (eventId a) := AND [ VarE $ eventId b | b <- b ]
    Or  b      -> Just $ ASSERT $ VarE (eventId a) := OR  [ VarE $ eventId b | b <- b ]

  nEvents :: Int -> CmdY
  nEvents n = ASSERT $ LitI (fromIntegral n) := foldl1 (:+:) [ IF (VarE $ eventId a) (LitI 1) (LitI 0) | a@(Leaf _) <- events' ]

  check :: Int -> [[String]] -> IO ()
  check i _ | i > n = return ()
  check i assumes = do
    result <- quickCheckY yices [] $ model ++ [nEvents i] ++ [ ASSERT $ NOT $ AND [ VarE a | a <- assume ] | assume <- assumes ]
    case result of
      Sat a -> do
        putStrLn $ concat [ name ++ "\n" | Leaf name <- cutSet a ] 
        check i $ [ eventId a | a <- cutSet a ] : assumes
      UnSat _ -> check (i + 1) assumes
      a -> error $ "unexpected smt result: " ++ show a

  cutSet :: [ExpY] -> [Event]
  cutSet result = [ a | (a@(Leaf _), label) <- eventNames, elem' label ]
    where
    match label (VarE label' := LitB True) = label == label'
    match _ _ = False
    elem' a = case find (match a) result of
      Nothing -> False
      Just _  -> True

