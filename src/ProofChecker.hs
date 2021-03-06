module ProofChecker where

import Syntax
import Pretty
import Matching
import KindChecker

import Text.PrettyPrint
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Debug.Trace
-- type KSubst = [(Name, Exp)]
type PCMonad a = StateT Int (ReaderT [(Name, Exp)] (StateT KindDef (Either Doc))) a

isFree :: Name -> [(Name, Exp)] -> Bool
isFree x m =
  let a = map (\ (y, t) ->  x `elem` (freeVars t)) m 
  in or a

kindable :: Exp -> PCMonad ()
kindable t = do
  ks <- lift $ lift get
  case runKinding' t ks of
    Left err -> lift $ lift $ lift $ Left $ text "error from proof checking, ill-kinded type: " <+> disp t $$
                nest 2 (text "current kind environment:" $$ nest 2 (disp ks)) $$
                (nest 2 err)
    Right (e, sub) | grounding e == Star ->
--      do
      lift $ lift $ modify (\e ->  map (\(y, v) -> (y, apply (Subst sub) v)) e)
         -- env <- lift $ lift $ get
         -- let env' = map (\(y, e) -> (y, apply x e)) env
         -- lift $ lift $ put env'
         -- return ()
    Right (e, _) -> 
      lift $ lift $ lift $ Left ((text "error from proof checking, ill-kinded type " <+> disp t) $$
                          nest 2 (text "expected: *" <+>
                                   text "actual kind:" <+> disp e)) 

proofChecks ks tyenv l = mapM (\ ((Var n _), f, t) -> runProofCheck n t f ks tyenv) l
runProofCheck :: Name -> Exp -> Exp -> KindDef -> [(Name, Exp)] -> Either Doc ()
runProofCheck n t f ks ev = 
  case evalStateT (runReaderT (evalStateT (proofCheck t) 0) ev) ks of
    Left err -> Left err
    Right f' ->
      if f' `alphaEq` f then return ()
      else Left $
           sep [text "proof checking error", text "expected type:" <+> disp f,
                 text "actual type:", disp f']
           
proofCheck :: Exp -> PCMonad Exp
--proofCheck state | trace ("proofCheck " ++show (state) ++"\n") False = undefined
proofCheck (Var x _) =
  do env <- ask
     case lookup x env of
       Nothing -> lift $ lift $ lift $ Left 
                  $ text "proof checking error: undefined variable" 
                  <+> text x $$ nest 2 (text "current type environment:" $$ nest 2 (disp env))
                  ---- $$ nest 2 (text "current kind environment:" $$ nest 2 (disp ks))
       Just f -> -- return f
         do kindable f 
            return f

proofCheck (Const x _) =
  do env <- ask
     case lookup x env of
       Nothing -> lift $ lift $ lift $ Left 
                  $ text "proof checking error: unknown constructor" 
                  <+> text x
       Just f -> return f

proofCheck (TApp e1 e2)  =
  do f1 <- proofCheck e1
--     k <- lift $ lift $ runKinding e2 ks
     -- case k of
     --   Star -> 
     case f1 of
           Forall x a2 -> 
             do let res = normalize $ apply (Subst [(x, e2)]) a2
                kindable res
                return res    
           b -> lift $ lift $ lift $ Left $
                (text "proof checking error on"
                  <+> disp e1) $$ (nest 2 $ text "unexpected type:" <+> disp b)
       -- _ ->  lift $ lift $ lift $ Left $
       --       (text "kinding checking error on"
       --         <+> disp e2) $$ (nest 2 $ text "unexpected kind:" <+> disp k)         
            
proofCheck (App e1 e2) =
  do f1 <- proofCheck e1 
     f2 <- proofCheck e2
     ks <- lift $ lift get
     kindable f1
     kindable f2
     case f1 of
       Imply a1 a2 -> 
         if a1 `alphaEq` f2
         then return a2
         else lift $ lift $ lift $ Left 
              ((text "proof checking error at application"
                 <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
               $$ (nest 2 $ disp f2))
       b ->  lift $ lift $ lift $ Left 
             ((text "proof checking error at application"
                <+> disp (App e1 e2)) $$ (nest 2 $ text "relevant types:" <+> disp f1)
               $$ (nest 2 $ disp f2))

proofCheck (Abs x t) = 
  do n<- get
     modify (+1)
     lift $ lift (modify (\e -> (x, Var ("kvar"++show n ++ "#") dummyPos): e))
     f <- (proofCheck t)
     e <- ask
     if isFree x e
       then lift $ lift $ lift $ Left $
            sep [text "proof checking error",
                  text "generalized variable" <+> disp x,
                  text "appears in the assumptions",
                  text "when checking the proof",
                  nest 2 $ disp (Abs x t),
                  text "current assumption", nest 2 $ disp e ]
       else 
       do kindable (Forall x f) 
          return $ (Forall x f)

proofCheck (Lambda (Ann p t1) t) =
  do newEnv <- checkPattern p t1
     t' <- local (\ y -> newEnv ++ y) (proofCheck t)
--     ks <- lift ask
     kindable (Imply t1 t')
     return $ Imply t1 t'

proofCheck (Case (Ann e t) alts) =
  do kindable t
     t' <- proofCheck e
     if t' == t then
       checkBranches alts t
       else lift $ lift $ lift $ Left $
            (text "proof checking error for"
              <+> disp e) $$ (nest 2 $ text "expected type:" <+> disp t) $$
            (nest 2 $ text "actual type:" <+> disp t')

       where checkBranch (p1, e1) t =
               do newEnv <- checkPattern p1 t
                  local (\ y -> newEnv ++ y) (proofCheck e1)
             checkBranches (b:[]) t = checkBranch b t
             checkBranches (b1:bs) t =
               do t' <- checkBranches bs t
                  t1 <- checkBranch b1 t
                  if t' `alphaEq` t1 then return t'
                    else lift $ lift $ lift $ Left $
                         (text "proof checking error at the branch"
                          <+> disp (fst b1) <+> text "->") $$
                         (nest 2 $ text "expected type:" <+> disp t') $$
                         (nest 2 $ text "actual type:" <+> disp t1)

proofCheck (Let defs e) =
  do newEnv <- checkAllPats $ map fst defs
     checkDefs newEnv defs
     local (\ y -> newEnv ++ y) (proofCheck e)
  where -- checkAllPats state | trace ("checkallpats " ++show (state) ++"\n") False = undefined
        checkAllPats ((Ann p@(App _ _) t):ds) =
          do penv <- checkPattern p t
             env <- checkAllPats ds
             return $ penv ++ env
             
        checkAllPats ((Ann x t):ds) | (isVar $ erase x) = 
          do t' <- local (\ y -> (getName $ erase x, t):y) (proofCheck x)
             if t' `alphaEq` t then
               do env <- checkAllPats ds
                  return $ (getName $ erase x, t):env
               else  lift $ lift $ lift $ Left $
                    (text "proof checking error at the let-branch"
                     <+> disp x) $$
                    (nest 2 $ text "expected type:" <+> disp t) $$
                    (nest 2 $ text "actual type:" <+> disp t')
        checkAllPats [] = return []

        checkDefs env ((Ann _ t, e):ds) =
             do kindable t
                t' <- local (\ y -> env ++ y) $ proofCheck e
                if t' `alphaEq` t then
                   checkDefs env ds
                  else lift $ lift $ lift $ Left $
                       (text "proof checking error at the let-branch"
                         <+> disp e) $$
                       (nest 2 $ text "expected type:" <+> disp t) $$
                       (nest 2 $ text "actual type:" <+> disp t')
        checkDefs env [] = return ()
                         
proofCheck e = error $ "from proofCheck " ++ show e
       
checkPattern :: Exp -> Exp -> PCMonad [(Name, Exp)]
checkPattern (Var x _) t = return [(x, t)]
checkPattern p t =
  let (p1:ps) = flatten p
      (c:ts) = flattenT p1   
  in case c of
       Const con _ ->
         do env <- ask
            case lookup con env of
              Nothing -> lift $ lift $ lift $ Left 
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
                       in if h' `alphaEq` t then
                            do res <- mapM (\ (x, y) -> checkPattern x y) pss
                               return $ concat res
                          else lift $ lift $ lift $ Left $
                               text "proof checking error: type mismatch when applying " 
                               <+> disp con <+> text "::" <+> disp f $$
                               nest 2 (text "expected result type:" <+> disp t) $$
                               nest 2 (text "actual result type:" <+> disp h')
                  else lift $ lift $ lift $ Left $
                       text "proof checking error: arity mismatch when applying " 
                       <+> disp con <+> text "::" <+> disp f $$
                       nest 2 (text "it is applied to types:" <+> vcat (map disp ts)) $$
                       nest 2 (text "then is applied to patterns:" <+> vcat (map disp ps))

       c' -> error $ "internal error from checkPattern during proof checking" ++ show c'
