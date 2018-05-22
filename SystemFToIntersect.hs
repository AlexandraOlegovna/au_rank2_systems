module SystemFToIntersect where

import Data.List

type Symb = String

infixr 3 :->
infixr 3 ::->
infixl 2 :@:
infixl 3 :/\
infix 1 ||-


data Decl = VDecl Symb TypeF
          | TDecl Symb
    deriving (Read,Show,Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _    == TDecl _    = True
  _          == _          = False


data VTypes = VTypes Symb [TypeF]
  deriving (Read,Show,Ord)

instance Eq VTypes where
    VTypes _ t1 == VTypes _ t2 = t1 == t2


type Env = [Decl]


data TypeF = TIdx Int
          | TypeF :-> TypeF
          | ForAll Symb TypeF
    deriving (Read,Show,Ord)


instance Eq TypeF where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  _           == _           = False


data TypeI =
            TIdx' Int
          | TypeI ::-> TypeI
          | TypeI :/\ TypeI
    deriving (Read,Show,Ord)


instance Eq TypeI where
  TIdx' n1     == TIdx' n2     = n1 == n2
  (t1 ::-> t3) == (t2 ::-> t4) = t1 == t2 && t3 == t4
  (t1 :/\ t3) == (t2 :/\ t4) = t1 == t2 && t3 == t4
  _           == _           = False


data Term = Idx Int
        | Term :@: Term
        | Term :@> TypeF
        | Lmb Decl Term
  deriving (Read,Show,Eq,Ord)



shiftT :: Int -> TypeF -> TypeF
shiftT val t = shiftT' 0 t val
shiftT' :: Int -> TypeF -> Int -> TypeF
shiftT' cutoff (TIdx k) val
               | k < cutoff = TIdx k
               | otherwise  = TIdx $ k + val
shiftT' cutoff (s :-> t) val = shiftT' cutoff s val :-> shiftT' cutoff t val
shiftT' cutoff (ForAll s t) val = ForAll s (shiftT' (succ cutoff) t val )


substTT :: Int -> TypeF -> TypeF -> TypeF
substTT j s (TIdx k)
          | k == j = s
          | otherwise = TIdx k
substTT j s (t1 :-> t2) = substTT j s t1 :-> substTT j s t2
substTT j s (ForAll sy t) = ForAll sy (substTT (succ j) (shiftT 1 s) t)



itemOf :: Int -> [a] -> Maybe a
x `itemOf` xs = let xslen = length xs in
                if ((abs x) >= xslen)
                    then Nothing
                    else Just (xs !! x)



(||-) :: Env -> TypeF -> Bool
e ||- (TIdx t)
    | (Just (TDecl _)) <- itemOf t e = True
e ||- (t1 :-> t2) = (e ||- t1) && (e ||- t2)
e ||- (ForAll t1 t2) = [TDecl t1] ++ e ||- t2
_ ||- _ = False


validEnv :: Env -> Bool
validEnv [] = True
validEnv ((TDecl _  ):envs) = validEnv envs
validEnv ((VDecl _ t):envs) = and [envs ||- t, validEnv envs]



-- envoroment -> input term -> lambda depth -> table of types substitution ->
--    Maybe(type in System F, type in Intersection System, new table of types substitution)
infer :: Env -> Term -> Int -> [VTypes] -> Maybe (TypeF, TypeI, [VTypes])
infer e (Idx i) d table |
    validEnv e = if i < 0 || i >= length e
                    then Nothing
                    else case e !! i of
                        (VDecl _ t) -> Just $ (shiftT (i + 1) t, (f2i (shiftT (i + 1) t) 0), table)
                        (TDecl _) -> Nothing


infer e (s1@(Idx a) :@: s2@(Idx b)) d table |
    Just ((t1 :-> t2), (t1' ::-> t2'), table1) <- infer e s1 d table,
    Just (t3, t3', table2) <- infer e s2 d table,
    t1 == t3,
    t1'== t3' =
        let table1' = addTo a (t1 :-> t2) table1 in
        let table2' = addTo b (t3) table2 in
        Just (t2, t2', concatTable table1' table2')


infer e (s1@(Idx a) :@: s2) d table |
    Just ((t1 :-> t2), (t1' ::-> t2'), table1) <- infer e s1 d table,
    Just (t3, t3', table2) <- infer e s2 d table,
    t1 == t3,
    t1'== t3' =
        let table1' = addTo a (t1 :-> t2) table1 in
        Just (t2, t2', concatTable table1' table2)


infer e (s1 :@: s2@(Idx a)) d table |
    Just ((t1 :-> t2), (t1' ::-> t2'), table1) <- infer e s1 d table,
    Just (t3, t3', table2) <- infer e s2 d table,
    t1 == t3,
    t1'== t3' =
        let table2' = addTo a (t3) table2 in
        Just (t2, t2', concatTable table1 table2')


infer e (s1 :@: s2) d table |
    Just ((t1 :-> t2), (t1' ::-> t2'), table1) <- infer e s1 d table,
    Just (t3, t3', table2) <- infer e s2 d table,
    t1 == t3,
    t1'== t3' =
        Just (t2, t2', concatTable table1 table2)


infer e (Lmb (VDecl sy t1) s) d table |
    Just (t, t', table') <- infer ((VDecl sy t1) : e) s (d + 1) ((VTypes sy [t1]) : table),
    e ||- t1 =
        let (VTypes _ ty) = table' !! (length table' - (d + 1) - 1) in
        Just (t1 :-> shiftT (-1) t, ((concatType ty 0) ::-> t'), table')


infer e (Lmb (TDecl a) s) d table |
    Just (t, t', table') <- infer ((TDecl a) : e) s d table =
        Just (ForAll a t, t', table')


infer e (s :@> t) d table |
    Just (ForAll a t1, t1', table') <- infer e s d table ,
    e ||- t =
        let x = shiftT (-1) $ substTT 0 (shiftT 1 t) t1 in
        Just (x, f2i x 0, addTo d x table')

infer _ _ _ _  = Nothing



infer' e t = infer e t (-1) []
infer0 t = infer [] t (-1) []
infer0' t = snd' $ infer [] t (-1) []



fst' x | Just (a, _, _) <- x = a
snd' x | Just (_, b, _) <- x = b
thd' x | Just (_, _, c) <- x = c



addTo :: Int -> TypeF -> [VTypes] -> [VTypes]
addTo 0 newVal [] = error $ show newVal
addTo 0 newVal ((VTypes s x):xs) = ((VTypes s (x ++ [newVal])):xs)
addTo n newVal (x:xs) = x:addTo (n-1) newVal xs


concatType :: [TypeF] -> Int -> TypeI
concatType (x:xs) d = concatType' xs
    where
        concatType' [] = f2i x d
        concatType' [t] = f2i t d
        concatType' (t:ts) = (f2i t d) :/\ (concatType' ts)


f2i :: TypeF -> Int -> TypeI
f2i (TIdx i) d = TIdx' (i + d)
f2i (t1 :-> t2) d = (f2i t1 d) ::-> (f2i t2 d)
f2i (ForAll _ t) d = f2i t d


concatTable :: [VTypes] -> [VTypes] -> [VTypes]
concatTable (x:xs) (y:ys) = (concatTable' x y) : (concatTable xs ys)
concatTable (x:xs) [] = x : concatTable xs []
concatTable [] (y:ys) = y : concatTable [] ys
concatTable [] [] = []


concatTable' :: VTypes -> VTypes -> VTypes
concatTable' (VTypes s1 (a:as)) (VTypes s2 (b:bs)) |
    a == b, s1 == s2 =
        VTypes s1 (a : union as bs)
