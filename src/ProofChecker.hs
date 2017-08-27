module ProofChecker where

import Syntax
import Pretty
import Matching
import KindChecker

import Text.PrettyPrint
import Control.Monad.Reader

type KSubst = [(Name, Exp)]
type PCMonad a = (ReaderT [(Name, Exp)] (ReaderT KSubst (Either Doc))) a

isFree :: Name -> [(Name, Exp)] -> Bool
isFree x m =
  let a = map (\ (y, t) ->  x `elem` (freeVars t)) m 
  in or a

kindable :: Exp -> KSubst -> PCMonad ()
kindable t ks =
  case runKinding t ks of
    Left err -> lift $ lift $ Left $ text "ill-kinded type: " <+> disp t
    Right Star -> return ()
    Right e -> 
      lift $ lift $ Left ((text "ill-kinded type " <+> disp t) $$
                          nest 2 (text "expected: *" <+>
                                   text "actual kind:" <+> disp e)) 

proofCheck :: Exp -> PCMonad Exp
proofCheck (Var x) =
  do env <- ask
     case lookup x env of
       Nothing -> lift $ lift $ Left 
                  $ text "proof checking error: undefined variable" 
                  <+> text x
       Just f -> 
         do ks <- lift ask 
            kindable f ks
            return f

proofCheck (Const x) =
  do env <- ask
     case lookup x env of
       Nothing -> lift $ lift $ Left 
                  $ text "proof checking error: unknown constructor" 
                  <+> text x
       Just f -> return f

proofCheck (TApp e1 e2)  =
  do f1 <- proofCheck e1
     ks <- lift ask
     k <- lift $ lift $ runKinding e2 ks
     case k of
       Star -> 
         case f1 of
           Forall x a2 -> 
             do let res = normalize $ apply (Subst [(x, e2)]) a2
                kindable res ks   
                return res    
           b -> lift $ lift $ Left $
                (text "proof checking error on"
                  <+> disp e1) $$ (nest 2 $ text "unexpected type:" <+> disp b)
       _ ->  lift $ lift $ Left $
             (text "kinding checking error on"
               <+> disp e2) $$ (nest 2 $ text "unexpected kind:" <+> disp k)         
            
proofCheck (App e1 e2) =
  do f1 <- proofCheck e1 
     f2 <- proofCheck e2
     case f1 of
       Imply a1 a2 -> 
         if a1 `alphaEq` f2
         then return a2
         else lift $ lift $ Left 
              ((text "proof checking error at application"
                 <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
               $$ (nest 2 $ disp f2))
       b ->  lift $ lift $ Left 
             ((text "proof checking error at application"
                <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
               $$ (nest 2 $ disp f2))

proofCheck (Abs x t) = 
  do f <- proofCheck t
     e <- ask
     if isFree x e
       then lift $ lift $ Left $
            sep [text "proof checking error",
                  text "generalized variable" <+> disp x,
                  text "appears in the assumptions",
                  text "when checking the proof",
                  nest 2 $ disp (Abs x t),
                  text "current assumption", nest 2 $ disp e ]
       else 
       do ks <- lift ask
          kindable (Forall x f) ks   
          return $ (Forall x f)

proofCheck (Lambda (Ann p t1) t) =
  do newEnv <- checkPattern p t1
     t' <- local (\ y -> newEnv ++ y) (proofCheck t)
     return $ Imply t1 t'


checkPattern :: Exp -> Exp -> PCMonad [(Name, Exp)]
checkPattern (Var x) t = return [(x, t)]
checkPattern p t =
  let (p1:ps) = flatten p
      (c:ts) = flattenT p1   
  in case c of
       Const con ->
         do env <- ask
            case lookup con env of
              Nothing -> lift $ lift $ Left 
                         $ text "proof checking error: unknown constructor" 
                         <+> disp con
              Just f ->
                let (vars, h, bs) = separate f
                in
                  if (length vars == length ts) &&
                     (length bs == length ps)
                  then let subs = Subst $ zip vars ts
                           h' = apply subs h
                           bs' = map (apply subs) bs
                           pss = zip ps bs'
                       in if h' == t then
                            do res <- mapM (\ (x, y) -> checkPattern x y) pss
                               return $ concat res
                          else lift $ lift $ Left $
                               text "proof checking error: type mismatch when applying " 
                               <+> disp con <+> text "::" <+> disp f $$
                               nest 2 (text "expected result type:" <+> disp t) $$
                               nest 2 (text "actual result type:" <+> disp h')
                  else lift $ lift $ Left $
                       text "proof checking error: arity mismatch when applying " 
                       <+> disp con <+> text "::" <+> disp f $$
                       nest 2 (text "it is applied to types:" <+> vcat (map disp ts)) $$
                       nest 2 (text "then is applied to patterns:" <+> vcat (map disp ps))

       _ -> error "internal error from checkPattern" 