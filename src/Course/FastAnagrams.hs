{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Course.FastAnagrams where

import Course.Core
import Course.List
import Course.Functor
import qualified Data.Set as S

-- Return all anagrams of the given string
-- that appear in the given dictionary file.
fastAnagrams ::
  Chars
  -> Filename
  -> IO (List Chars)
fastAnagrams chars dictionaryFilename =
  let dictionary = lines <$> readFile dictionaryFilename
      charsPerms = S.fromList . hlist . permutations $ chars
   in filter (flip S.member charsPerms) <$> dictionary

fastAnagrams' ::
  Chars
  -> Filename
  -> IO (List Chars)
fastAnagrams' chars dictionaryFilename =
  let dictionary = lines <$> readFile dictionaryFilename
      sortedChars = NoCaseString $ sort chars
   in filter ((sortedChars ==) . NoCaseString . sort)  <$> dictionary

sort :: Ord a => List a -> List a
sort Nil = Nil
sort (x :. xs) = sort before ++ x :. sort after
  where before = filter (< x) xs
        after = filter (>= x) xs

newtype NoCaseString =
  NoCaseString {
    ncString :: Chars
  }

instance Eq NoCaseString where
  (==) = (==) `on` map toLower . ncString

instance Show NoCaseString where
  show = show . ncString
