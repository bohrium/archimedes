{-  author: samtenka
 -  change: 2020-09-30
 -  create: 2020-09-30
 -  descrp: combinator-based parsing for calculus expressions 
 -  thanks: I found Eli Bendersky's post on the Applicative typeclass very
 -          useful: "Deciphering Haskell's applicative and monadic parsers".
 -  to use: `make parse` 
 -}

import System.IO
import Data.Char
import Data.Maybe
import Data.List

-- ============================================================================
-- ===  0. PARSER MONAD  ======================================================
-- ============================================================================

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  0.0. Parser Type  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newtype Parser a = PP (String -> Maybe (a, String))

parse :: Parser a -> String -> Maybe (a, String)
parse (PP p) inp = p inp

failure :: Parser a
failure = PP (\inp -> Nothing)

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  0.1. Instantiate Composition Operators  ~~~~~~~~~~~~~~~~~~~~~~~

instance Functor Parser where
    -- fmap :: (a -> b) -> Parser a -> Parser b
    fmap f p = PP (\inp -> case parse p inp of
                                Nothing -> Nothing
                                Just (v, out) -> Just (f v, out)) 

instance Applicative Parser where
    -- pure  :: a -> Parser a
    -- (<*>) :: Parser (a -> b) -> Parser a -> Parser b
    pure a = PP (\inp -> Just (a, inp))
    fp <*> ap = PP (\inp -> case parse fp inp of
                                 Nothing -> Nothing
                                 Just (f, out) -> parse (fmap f ap) out)    

instance Monad Parser where
    -- return :: a -> Parser a
    -- (>>=)  :: Parser a -> (a -> Parser b) -> Parser b
    return v = pure v
    PP p >>= f = PP (\inp -> case parse (PP p) inp of
                                  Nothing -> Nothing
                                  Just (v,out) -> parse (f v) out)

-- ============================================================================
-- ===  1. BASIC PARSERS  =====================================================
-- ============================================================================

item  :: Parser Char
(+++) :: Parser a -> Parser a -> Parser a
sat   :: (Char -> Bool) -> Parser Char
sats  :: (Char -> Bool) -> Parser String
space :: Parser ()
strg  :: String -> Parser String
spop  :: String -> Parser String
wrap  :: Parser x -> Parser a -> Parser y -> Parser a

item = PP (\inp -> case inp of
                        [] -> Nothing
                        (x:xs) -> Just (x, xs))

p +++ q = PP (\inp -> case parse p inp of
                           Nothing -> parse q inp
                           Just (v, out) -> Just (v, out))

sat p = do x <- item
           if p x then (return x) else failure

sats p = do c <- sat p
            (do cc <- sats p
                return (c:cc)) +++ return [c]

wrap open p close = do open ; x <- p ; close
                       return x

space = (do sat isSpace
            space) +++ (return ()) 

strg s = case s of
              [] -> return "" 
              (c:cs) -> do cc <- sat ((==) c)
                           ss <- strg cs
                           return (cc:ss) 

spop a = wrap space (strg a) space

chain :: [Parser a] -> Parser [a]
chain ps = case ps of
                []     -> return [] 
                (p:pp) -> do x <- p
                             xx <- chain pp
                             return (x:xx) 

-- ============================================================================
-- ===  2. EXPRESSION GRAMMAR  ================================================
-- ============================================================================

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  2.0. ParseTree Type  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data ETree =   Sum [ETree]
             | Product [ETree] 
             | Num Double 
             | Var String
             | Theta Int ETree    
             | Smooth [String] String 

theta_derivative_name :: Int -> String 
theta_derivative_name n = if n==0 then "theta"
                          else         "delta"++(concat $ replicate (n-1) "'")

lotsa_ds :: [String] -> String 
lotsa_ds nms = intercalate " " $ map (\nm->"D_"++nm) nms

wrap_if_has_sum :: [ETree] -> String -> String
wrap_if_has_sum es s = if or (map (\e -> case e of Sum _ -> True
                                                   _ -> False) es) then "("++s++")" 
                       else s

showtree :: ETree -> String
showtree et = 
    case et of Sum es        -> intercalate " + " $ map showtree es
               Product es    -> wrap_if_has_sum es $ intercalate "*" (map showtree es)
               Num q         -> show q
               Var nm        -> nm
               Theta n e     -> (theta_derivative_name n) ++ "("++(showtree e)++")" 
               Smooth nms nm -> if null nms then nm  
                                else            (lotsa_ds nms) ++ "["++nm++"]"

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  2.1. Expression Recursions  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

expr   :: Parser ETree
term   :: Parser ETree
fact   :: Parser ETree
num    :: Parser ETree
var    :: Parser ETree
theta  :: Parser ETree
smooth :: Parser ETree

expr = do a <- term  
          (do op <- spop "+"
              b <- expr 
              return (case b of Sum es -> Sum (a:es)  
                                _      -> Sum [a, b])
              ) +++ return a


term = do a <- fact 
          (do op <- spop "*"
              b <- term
              return (case b of Product es -> Product (a:es)  
                                _          -> Product [a, b])
              ) +++ return a

fact = do num +++ var +++ theta +++ smooth  

num    = do s <- sats (\c -> (isDigit c) || (elem c "-."))
            return (Num (read s))

var    = do c <- sats (\c -> elem c "xyt")
            return (Var c) 

theta  = do sat (\c -> elem c "T")
            sat (\c -> elem c "(")
            e <- expr 
            sat (\c -> elem c ")")
            return (Theta 0 e)
            
smooth = do c <- sats (\c -> elem c "g")
            return (Smooth [] c) 

-- ============================================================================
-- ===  3. TRANSLATE  =========================================================
-- ============================================================================
       
diff :: String -> ETree -> ETree   
diff wrt et = case et of Sum es        -> Sum (map (diff wrt) es)
                         Product es    -> let rr = [0 .. (length es - 1)] in
                                              Sum (map (\i -> Product (map (\j -> if i==j then (diff wrt (es !! j)) else (es !! j)) rr)) rr)
                         Num q         -> Num 0
                         Var nm        -> if nm == wrt then Num 1 else Num 0 
                         Theta n e     -> Product [Theta (n+1) e, diff wrt e]
                         Smooth nms nm -> Smooth (wrt:nms) nm

match_num :: Double -> Bool -> ETree -> Bool
match_num x b e = case e of Num y -> if y==x then b else not b
                            _     -> not b 

simp :: ETree -> ETree
simp et = case et of Sum es        -> let terms = map simp es
                                          nonzero = filter (match_num 0.0 False) terms in
                                          if null nonzero then Num 0.0 else Sum nonzero
                     Product es    -> let facts = map simp es
                                          haszero = or $ map (match_num 0.0 True) facts 
                                          nonone = filter (match_num 1.0 False) facts in
                                          if haszero then Num 0.0
                                          else if null nonone then Num 1.0
                                          else Product nonone
                     Theta n e     -> Theta n (simp e) 
                     _             -> et

-- ============================================================================
-- ===  4. MAIN LOOP  =========================================================
-- ============================================================================

try_parse s = case parse expr s of
                   Nothing -> "Failed to Parse" 
                   Just (a, out) -> showtree $ simp (diff "t" (simp (diff "x" a)))

main = do putStr "hello!\n\n"
          contents <- readFile "moo.txt" 
          putStr $ try_parse contents
          putStr "\n\nbye!\n"
