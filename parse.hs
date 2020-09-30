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
             | Prod [ETree] 
             | Num Double 
             | Var String
             | Theta Int ETree    
             | Smooth [String] String 
             deriving Show

theta_derivative_name :: Int -> String 
theta_derivative_name n = if n==0 then "\\theta"
                          else         "\\delta"++(concat $ replicate (n-1) "'")

lotsa_ds :: [String] -> String 
lotsa_ds nms = intercalate " " $ map (\nm->"D_"++nm) nms

wrap_if_is_sum :: ETree -> String
wrap_if_is_sum e = case e of Sum _ -> "("++(showtree e)++")"
                             _     -> showtree e

showtree :: ETree -> String
showtree et = 
    case et of Sum es        -> intercalate " + " $ map showtree es
               Prod es    -> intercalate "*" (map wrap_if_is_sum es)
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
              return (case b of Prod es -> Prod (a:es)  
                                _          -> Prod [a, b])
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

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  3.0. Simplification  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- simplify using distributivity of * over +  
dstr :: ETree -> ETree
dstr et = case et of Prod (h:t) -> case dstr h of
                                           Sum terms -> Sum (map (\e -> dstr (Prod (e:t))) terms) 
                                           hh        -> case dstr $ Prod t of
                                                             Sum terms -> Sum (map (\e -> dstr $ Prod [hh,e]) terms) 
                                                             tt -> Prod [hh,tt] 
                     Sum es       -> Sum (map dstr es)
                     _            -> et

-- simplify using associativiy of + and *  

asso :: ETree -> ETree
asso et = case et of
  Sum (h:t) -> let ash = asso h   
                   ast = asso (Sum t)
                   hs = (case ash of Sum hh -> hh
                                     _      -> [ash]) 
                   ts = (case ast of Sum tt -> tt
                                     _      -> [ast])  in Sum (hs++ts) 
  Prod (h:t) -> let ash = asso h   
                    ast = asso (Prod t)
                    hs = (case ash of Prod hh -> hh
                                      _       -> [ash]) 
                    ts = (case ast of Prod tt -> tt
                                      _       -> [ast])  in Prod (hs++ts) 
  _         -> et 

-- simplify using identity and vanishing laws of 0 and 1
canc :: ETree -> ETree
canc et = case et of Sum es        -> let terms = map canc es
                                          nonzero = filter (match_num 0.0 False) terms in
                                          case nonzero of
                                              [] -> Num 0.0
                                              [e] -> e
                                              _ -> Sum nonzero
                     Prod es    -> let facts = map canc es
                                       haszero = or $ map (match_num 0.0 True) facts 
                                       nonone = filter (match_num 1.0 False) facts in
                                       if haszero then Num 0.0
                                       else case nonone of
                                                 [] -> Num 1.0
                                                 [e] -> e
                                                 _ -> Prod nonone
                     Theta n e     -> Theta n (canc e) 
                     _             -> et

match_num :: Double -> Bool -> ETree -> Bool
match_num x b e = case e of Num y -> if y==x then b else not b
                            _     -> not b 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  3.1. Differentiation  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

diff_inner :: String -> ETree -> ETree   
diff_inner wrt et =
  case et of Sum es        -> Sum (map (diff_inner wrt) es)
             Prod es       -> let rr = [0 .. (length es - 1)] in
                                  Sum (map (\i -> Prod (map (\j -> if i==j then (diff_inner wrt (es !! j)) else (es !! j)) rr)) rr)
             Num q         -> Num 0
             Var nm        -> if nm == wrt then Num 1 else Num 0 
             Theta n e     -> Prod [Theta (n+1) e, diff_inner wrt e]
             Smooth nms nm -> Smooth (wrt:nms) nm

diff :: String -> ETree -> ETree
diff wrt et = canc $ asso $ canc $ dstr $ canc $ diff_inner wrt et
 
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- ~~~~~~~~~~~  3.2. Integration  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

integrate :: ETree -> String

data Affine = XY1 ETree ETree ETree 

mag2_grad :: Affine -> String
mag2_grad (XY1 cx cy c1) = intercalate " + " $ map (\c -> "(" ++ (showtree c) ++ ")^2") [cx, cy]

rotate :: Affine -> Affine
rotate (XY1 cx cy c1) = XY1 (Prod [Num (0-1), cy])
                            (Prod [Num (0+1), cx])
                            (Num 0.0)

eval_at_zero :: ETree -> ETree 
eval_at_zero et =
  case et of Sum es        -> Sum  (map eval_at_zero es)
             Prod es       -> Prod (map eval_at_zero es)
             Var "x"       -> Num 0.0
             Var "y"       -> Num 0.0
             _             -> et
 
aff_from :: ETree -> Affine
aff_from et = XY1 (canc $ eval_at_zero $ (diff "x") et) 
                  (canc $ eval_at_zero $ (diff "y") et)
                  (canc $ eval_at_zero $            et)

tree_from :: Affine -> ETree
tree_from (XY1 cx cy c1) = Sum [Prod [cx, Var "x"], Prod [cy, Var "y"], c1]

invert :: Affine -> (ETree, ETree) 
invert a = 
  case a of
    XY1 cx cy c1 ->
      let norm = Var ("(1/("++(mag2_grad a)++"))") in 
        (
          Prod [Sum [Prod [Num (0-1),cy, Var "j"], Prod [Num  1.0, cx, Var "k"], Prod[Num (0-1),cx, c1]], norm],
          Prod [Sum [Prod [Num  1.0, cx, Var "j"], Prod [Num  1.0, cy, Var "k"], Prod[Num (0-1),cy, c1]], norm]
        )

normalize :: Affine -> ETree -> ETree 
normalize a et =
  let (xx,yy) = invert a in 
    case a of
      XY1 cx cy c1 ->
        case et of Sum es     -> Sum (map (normalize a) es)
                   Prod es -> Prod (map (normalize a) es) 
                   Var "x"    -> xx
                   Var "y"    -> yy
                   Theta n e  -> Theta n $ normalize a e
                   _          -> et

get_thetas :: Int -> [ETree] -> [ETree]
get_thetas n ets = filter (\et -> case et of Theta m _ -> m==n
                                             _         -> False) ets   

integrate_term :: [ETree] -> String
integrate_term ets =
    let et = Prod ets
        thetas = get_thetas 0 ets 
        deltas = get_thetas 1 ets in
        case deltas of []  -> "\\int_{x,y}\\," ++ (showtree et)
                       [Theta 1 d] -> let a = aff_from d in 
                                        "\\frac{1}"++"{"++(mag2_grad a)++"}" ++
                                        "\\int_{j,k}\\," ++ (showtree $ canc $ asso $ canc $ normalize a et)

integrate et = case et of
    Sum es  -> intercalate " + " $ map integrate es  
    Prod es -> integrate_term es
    _       -> "\\int... " ++ (showtree et)
 
-- ============================================================================
-- ===  4. MAIN LOOP  =========================================================
-- ============================================================================

try_parse s = case parse expr s of
                   Nothing -> "Failed to Parse" 
                   Just (a, out) -> let dd = diff "t" a in 
                                      (show dd) ++ "\n\n" ++ (showtree dd) ++ "\n\n" ++ (integrate dd)

main = do putStr "hello!\n\n"
          contents <- readFile "moo.txt" 
          putStr $ try_parse contents
          putStr "\n\nbye!\n"
