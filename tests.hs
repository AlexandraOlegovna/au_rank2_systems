module Main where
import SystemFToIntersect


ex0 = lV "f" botT $ lT "beta" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)

ex0' = lV "f" botT $ lT "beta" $ lT "gamma" $ Idx 2 :@> (TIdx 0 :-> TIdx 1) :@: (Idx 2 :@> TIdx 0)

ex1 = lV "f" topT $ lT "beta" $ Idx 1 :@> ((TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> (TIdx 0 :-> TIdx 0)) :@: (Idx 1 :@> TIdx 0)

ex2 = lV "f" boolT $ lT "a" $ Idx 1 :@> (TIdx 0 :-> TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0) :@: (Idx 1 :@> TIdx 0)

ex3 = lV "f" botT $ Idx 0 :@> (botT :-> topT :-> botT) :@: (Idx 0 :@> botT) :@: (Idx 0 :@> topT)

ex4 = lV "f" topT $ lT "a" $ Idx 1 :@> ((TIdx 0 :-> TIdx 0) :-> (TIdx 0 :-> TIdx 0)) :@: (Idx 1 :@> (TIdx 0 :-> TIdx 0)) :@: (Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0))

ex5 = lV "f" topT $ (Idx 0 :@> (topT)) :@: Idx 0

ex6 = lV "s" (ForAll "a" $ TIdx 0 :-> TIdx 1 :-> TIdx 0) $ lT "a" $ lV "z" (TIdx 0) $ Idx 2 :@> (TIdx 3 :-> TIdx 1 ) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)

ex7 = lV "s" (ForAll "a" $ TIdx 0 :-> TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lT "a" $ lV "z" (TIdx 0) $ Idx 2 :@> (TIdx 4 :-> TIdx 3 :-> TIdx 1) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)


test0 = (infer0' ex0) == (((TIdx' 0 ::-> TIdx' 0) :/\ TIdx' 0) ::-> TIdx' 0)

test0' = (infer0' ex0') == (((TIdx' 0 ::-> TIdx' 1) :/\ TIdx' 0) ::-> TIdx' 1)

test1 = (infer0' ex1) == (((((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0)) ::-> ((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0))) :/\ (((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0)) :/\ (TIdx' 0 ::-> TIdx' 0))) ::-> (TIdx' 0 ::-> TIdx' 0))

test2 = (infer0' ex2 ) == ((((TIdx' 0 ::-> (TIdx' 0 ::-> TIdx' 0)) ::-> ((TIdx' 0 ::-> (TIdx' 0 ::-> TIdx' 0)) ::-> (TIdx' 0 ::-> (TIdx' 0 ::-> TIdx' 0)))) :/\ (TIdx' 0 ::-> (TIdx' 0 ::-> TIdx' 0))) ::-> (TIdx' 0 ::-> (TIdx' 0 ::-> TIdx' 0)))

test3 = (infer0' ex3) == (((TIdx' 0 ::-> ((TIdx' 0 ::-> TIdx' 0) ::-> TIdx' 0)) :/\ (TIdx' 0 :/\ (TIdx' 0 ::-> TIdx' 0))) ::-> TIdx' 0)

test4 = (infer0' ex4) == (((((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0)) ::-> ((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0))) :/\ (((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0)) :/\ (TIdx' 0 ::-> TIdx' 0))) ::-> (TIdx' 0 ::-> TIdx' 0))

test5 = (infer0' ex5) == ((((TIdx' 0 ::-> TIdx' 0) ::-> (TIdx' 0 ::-> TIdx' 0)) :/\ (TIdx' 0 ::-> TIdx' 0)) ::-> (TIdx' 0 ::-> TIdx' 0))

test6 = (snd' $ infer' [TDecl "beta"] ex6) == ((((TIdx' 3 ::-> TIdx' 1) ::-> (TIdx' 3 ::-> (TIdx' 3 ::-> TIdx' 1))) :/\ (TIdx' 1 ::-> (TIdx' 3 ::-> TIdx' 1))) ::-> (TIdx' 1 ::-> (TIdx' 3 ::-> (TIdx' 3 ::-> TIdx' 1))))

test7 = (snd' $ infer' [TDecl "gamma",TDecl "beta"] ex7) == ((((TIdx' 4 ::-> (TIdx' 3 ::-> TIdx' 1)) ::-> (TIdx' 4 ::-> (TIdx' 3 ::-> (TIdx' 4 ::-> (TIdx' 3 ::-> TIdx' 1))))) :/\ (TIdx' 1 ::-> (TIdx' 4 ::-> (TIdx' 3 ::-> TIdx' 1)))) ::-> (TIdx' 1 ::-> (TIdx' 4 ::-> (TIdx' 3 ::-> (TIdx' 4 ::-> (TIdx' 3 ::-> TIdx' 1))))))



main :: IO ()
main = print $ and [test0, test0', test1, test2, test3, test4, test5, test6, test7]



lV :: Symb -> TypeF -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl


topT = ForAll "a" (TIdx 0 :-> TIdx 0)
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0
botT = ForAll "a" (TIdx 0)
