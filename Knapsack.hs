{-#LANGUAGE FlexibleInstances #-}
import Prelude hiding(head,tail,lookup)
import Control.Applicative
import Data.Array
import Data.Functor
import GHC.Base (Functor(..))

import Data.Time
import System.Environment (getArgs)
import Data.Maybe (listToMaybe)
import Control.Monad (when)
import Control.DeepSeq (deepseq)

--data Nat = Zero | Succ Nat deriving (Show,Eq,Ord)
type Val = Int


wvs = [(12, 4), (1, 2), (2, 2), (1, 1), (4, 10)]

knapsack1 :: Int -> Val
knapsack1 0 = 0
knapsack1 c = max' [ knapsack1 (c-w) + v   | (w,v)<-wvs,  w <= c]

max' [] = 0
max' xs = maximum xs

knapsack2 c = table ! c where
          table :: Array Int Val
          table = array (0,c) [(i,ks i) | i <- [0..c] ]
          ks :: Int -> Val
          ks i = max' [v + table ! (i-w) | (w,v) <- wvs, w <= i]

class Comonad n where
      extract :: n a -> a
      duplicate :: n a -> n (n a)

data Cofree f a = Cons {head :: a , tail :: f (Cofree f a)}

instance Functor f => Functor (Cofree f) where
         fmap f (Cons a ts) = Cons (f a) (fmap (fmap f) ts)

--corecursion
coiterate :: (Functor f) => (a -> b) -> (a -> f a) -> (a -> Cofree f b)
coiterate hd tl a = Cons (hd a) (fmap (coiterate hd tl) (tl a))

instance Functor f => Comonad (Cofree f) where
         extract = head
         duplicate = coiterate id tail

data NatF a = Zero | Succ a

instance Functor NatF where
         fmap f Zero = Zero
         fmap f (Succ n) = Succ $ f n

lookup :: Cofree NatF v -> Int -> Maybe v
lookup (Cons a _) 0 = Just a
lookup (Cons a Zero) n | n >0 = Nothing
lookup (Cons a (Succ t)) n | n >0 = lookup t (n-1)

dist :: Functor f => f (Cofree f a) -> Cofree f (f a)
dist = coiterate (fmap head) (fmap tail)

inNat :: NatF Int -> Int
inNat Zero = 0
inNat (Succ n) = n + 1

inRev :: Int -> NatF Int
inRev 0 = Zero
inRev c | c>0 = Succ (c-1)

inFold :: (NatF b -> b) -> (Int -> b)
inFold alg 0 = alg Zero
inFold alg n | n > 0 = alg $ Succ (inFold alg (n-1))

fanAlg :: NatF (Cofree NatF Int) -> Cofree NatF Int
fanAlg = (fmap inNat) . dist

fan :: Int -> Cofree NatF Int
fan = inFold fanAlg

instance Show a => Show (Cofree NatF a) where
         show (Cons a Zero) = "Cons " ++ show a ++ " Zero"
         show (Cons a (Succ t)) = "Cons " ++ show a ++ " Succ(" ++ show t ++ ")"

knap :: NatF (Cofree NatF Val) -> Val
knap Zero = 0
knap (Succ table) = max' [ v1 + v2 | (w',v1)<-wvs, Just v2 <- [lookup table (w'-1)] ]

knapsack3 :: Int -> Val
knapsack3 = knap . (fmap (fmap knapsack3 . fan)) . inRev

sharpAlg :: Functor f => (f (Cofree f a) -> a) -> (f (Cofree f a) -> Cofree f a)
sharpAlg b = fmap b . dist . fmap duplicate

sharpAlg' :: Functor f => (f (Cofree f a) -> a) -> (f (Cofree f a) -> Cofree f a)
sharpAlg' b = coiterate b (fmap tail)

knapsack4 = extract . (inFold (sharpAlg knap))
knapsack4' = extract . (inFold (sharpAlg' knap))

optAlg :: Functor f => (f (Cofree f a) -> a) -> (f (Cofree f a) -> Cofree f a)
optAlg b ts = Cons (b ts) ts

knapsack5 :: Int -> Val
knapsack5 = extract . (inFold (optAlg knap))


newtype Id a = Id {runId :: a}
instance Functor Id where
         fmap f = Id . f . runId

toStream :: (Int -> Val) -> Cofree Id Val
toStream f = Cons (f 0) (Id $ toStream (f . (+1))) 


knapsack6 :: Int -> Val
knapsack6 0 = 0
knapsack6 c = max' [ find' sack (c-w) + v   | (w,v)<-wvs,  w <= c]

find' :: Cofree Id v -> Int -> v
find' (Cons a _) 0 = a
find' (Cons _ idTail) n | n>0 = find' (runId idTail) (n-1)

sack :: Cofree Id Val
sack = toStream knapsack6

sacktable :: Int -> Cofree NatF Val
sacktable 0 = Cons 0 Zero
sacktable n | n>0 = let share = sacktable (n-1)
  in Cons (knapsack6t $ Succ share) (Succ $ share)

knapsack6t Zero = 0
knapsack6t (Succ table) = max' [ v' + v   | (w,v)<-wvs, w>0, Just v' <- [lookup table (w-1)]]

knapsack6' 0 = 0
knapsack6' n = knapsack6t $ Succ (sacktable (n-1))

sacktable7 :: Int -> Cofree NatF Val
sacktable7 0 = Cons 0 Zero
sacktable7 n | n>0 = let share = sacktable7 (n-1)
          in Cons (knapsack7t share n) (Succ share)

knapsack7t table 0 = 0
knapsack7t table c = max' [ v' + v   | (w,v)<-wvs, w>0, w <= c, Just v' <- [lookup table (w-1)]]

knapsack7 0 = 0
knapsack7 n = knapsack7t (sacktable7 (n-1)) n


sacktable8 0 = [0]
sacktable8 n | n>0 = let share = sacktable8 (n-1) in (knap8 share n) : share

knap8 table 0 = 0
knap8 table c = max' [ v' + v   | (w,v)<-wvs, w>0, w <= c, Just v' <- [lookup' table (w-1)]]

lookup' :: [a] -> Int -> Maybe a
lookup' [] 0 = Nothing
lookup' (x:_) 0 = Just x
lookup' (_:xs) n | n>0 = lookup' xs (n-1)

knapsack8 0 = 0
knapsack8 n = knap8 (sacktable8 (n-1)) n

{-
sack' :: Cofree NatF Val -> Int -> Cofree NatF Val
sack' table 0 = Cons 0 Zero
sack' table n | n > 0 = 
      case tail table of
           Zero -> Cons (knapsack6t table n) Zero
           Succ t -> Cons (knapsack6t table n) (Succ $  sack' t (n-1))

-}

maybeRead :: Read a => String -> Maybe a
maybeRead = fmap fst . listToMaybe . reads

knapsacks = [knapsack1,knapsack2,knapsack3,knapsack4,knapsack5,knapsack6,knapsack7,knapsack8]

main :: IO ()
main = do
     args <- getArgs
     while True args (getLine >>= return . words) processArgs

processArgs :: [String] -> IO Bool
processArgs args = do
     let instanceNumStr = args !! 0
     let instanceNum = maybe (-1) id (maybeRead instanceNumStr)
     let numStr = args !! 1
     let num = maybe (-1) id (maybeRead numStr)
     let ans = (knapsacks !! (instanceNum-1)) num
     if (length args >= 2 && instanceNum > 0 && num >= 0) then do
           before <- getCurrentTime
           deepseq ans (return ())
           after <- getCurrentTime
           print $ diffUTCTime after before 
           return True
     else return False


while :: Monad m => Bool -> a -> m a -> (a -> m Bool) -> m ()
while b a nextArg act = if b then do
	 x <- act a
         y <- nextArg
	 while x y nextArg act
         else return ()