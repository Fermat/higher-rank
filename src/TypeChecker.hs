module TypeChecker where

import Syntax
import Pretty
import Matching
import KindChecker

import Text.PrettyPrint
import Data.List
import Data.Char
import Debug.Trace

type Pos = [Int] 

-- type environment
type TyEnv = [(Name, Exp)]
type TyDef = [(Name, Exp)]

makeTyEnv :: [Decl] -> TyEnv
makeTyEnv a =
  let (tyenv, def) = makeTyEnv' a in
    map (\ (x, t) -> (x, normalizeTy t def)) tyenv
makeTyEnv' :: [Decl] -> (TyEnv, TyDef)
makeTyEnv' [] = ([], [])
makeTyEnv' ((DataDecl _ _ cons):xs) =
  let (tyenv, tydef) = makeTyEnv' xs in
    ([(d, e) | (Const d _, e) <- cons] ++ tyenv, tydef )
makeTyEnv' ((FunDecl (Var f _) t _):xs) =
  let (tyenv, tydef) = makeTyEnv' xs in 
    ((f, t):tyenv, tydef)
makeTyEnv' ((Prim (Var f _) t):xs) =
  let (tyenv, tydef) = makeTyEnv' xs in
    ((f, t):tyenv, tydef)
makeTyEnv' ((Syn (Const t _) k e):xs) =
  let (tyenv, tydef) = makeTyEnv' xs in
    (tyenv, (t, e):tydef)
makeTyEnv' (_:xs) = makeTyEnv' xs
makeLam pats e = foldr (\ p e' -> Lambda p e') e pats


process fv (Var x p) =
  if x `elem` fv then
    (Const "Void#" p)
  else (Var x p)
process fv (Const x p) =
  if isUpper $ head x then Const x p
  else (Var x p)
process fv (App e1 e2) = App (process fv e1) (process fv e2)
process fv (TApp e1 e2) = TApp (process fv e1) (process fv e2)
process fv (Imply e1 e2) = Imply (process fv e1) (process fv e2)
process fv (Lambda (Ann p t) e2) =
  Lambda (Ann (process fv p) (process fv t)) (process fv e2)
process fv (Lambda (Var x p) e2) =
  Lambda (Var x p) (process fv e2)
process fv (Abs x e2) = Abs x (process fv e2)
process fv (Forall x e2) = Forall x (process fv e2)
process fv (Ann e t) = Ann (process fv e) (process fv t)
process fv (Case e alts) = Case (process fv e) alts'
  where alts' = map (\(p, exp) -> (process fv p, process fv exp)) alts
process fv (Let alts e) = Let alts' (process fv e)
  where alts' = map (\(p, exp) -> (process fv p, process fv exp)) alts
process fv e = error $ "from process " ++ show e 


checkDecls :: [Decl] -> Either Doc [(Exp, Exp, Exp)]
-- checkDecls state | trace ("checkdecl " ++show ("hi") ++"\n") False = undefined
checkDecls a =
  let (tyEnv, tydef) = makeTyEnv' a
      tyEnv' = map (\ (x, t) -> (x, normalizeTy t tydef)) tyEnv
      funcDefs = concat [map (\(pats, d) -> (t, makeLam pats d, f, p)) defs |
                          (FunDecl (Var f p) t defs) <- a]
  in mapM (\ (t, e, f, p) ->
              let t' = normalizeTy t tydef in 
                do{(e', vars) <- typeCheck f tyEnv' (t', e);
                   return (Var f p, t', process vars e')
                })
     funcDefs

typeCheck :: Name -> TyEnv -> (Exp, Exp) -> Either Doc (Exp, [Name])
typeCheck f env (goal, e) =
  let phi = Phi [] (Just goal) (Just e) env []
      init = Res f goal [phi] Nothing 0
  in ersm [init] 
    

-- subgoals state    
data Phi = Phi{
              position :: Pos,
              currentGoal :: Maybe Exp,
              currentProg :: Maybe Exp,
              env :: TyEnv,
              scope :: [(Exp, Int)] }
           deriving (Show)

-- Resolution state
data ResState = Res{
  funName :: Name,
  mixedTerm :: Exp,
  phi :: [Phi],
  errMessage :: Maybe Doc,
  counter :: Int
  } deriving (Show)


                
reImp :: [Exp] -> Exp -> Exp
reImp [] h = h
reImp (x:xs) h = Imply x (reImp xs h)

reLam :: [Exp] -> Exp -> Exp
reLam [] h = h
reLam (x:xs) h = Lambda x (reLam xs h)

patternVars :: Exp -> Int -> (TyEnv, Int)
patternVars p i = 
  let fvs = freeVars p
      j = (i+(length fvs))-1
      ns = [i..j]
      vars = map (\ n -> Var ("y"++show n++"#") dummyPos) ns
  in (zip fvs vars, j+1)
    

makePatEnv :: [Exp] -> Int -> ([TyEnv], Int)
makePatEnv [] i = ([], i)
makePatEnv (x:xs) i =
  let (env, j) = patternVars x i
      (res, n) = makePatEnv xs j
  in (env:res, n)


makeLvars ((env, Var y p1, Var x _, e):xs) n = (Var y p1, n):makeLvars xs n
makeLvars ((env, Var y p1, p, e):xs) n =
  let r = map (\(u, v) -> (v, n)) env
  in r ++ (Var y p1,n):makeLvars xs n
makeLvars ((env, t, Var x _, e):xs) n = makeLvars xs n
makeLvars [] n = []


makePats ((t, Var x p1, e):xs) i =
  let (ps, j) = makePats xs i
  in (([(x, t)], t, Var x p1, e):ps, j)
    
makePats ((t, p, e):xs) i =
  let (env, j) = patternVars p i
      (ps, j') = makePats xs j
  in ((env, t, p, e):ps, j')
makePats [] i = ([], i)

annotate l = map ann l 
ann (Ann (Var x p) t, e) = (Just t, (Var x p), e)
ann (p, e) = (Nothing, p, e)


withVars ((Just t, (Var x p1), e):xs) i =
  let (ps, j) = withVars xs i
  in ((t, (Var x p1), e):ps, j)
withVars ((Nothing, p, e):xs) i =
  let (ps, j) = withVars xs (i+1)
  in ((Var ("y"++show i++"#") dummyPos, p, e):ps, j)
withVars [] i = ([], i)



-- Postion encoding scheme:
-- App 0 1
-- TApp 0 1
-- Abs 0 1
-- Lambda 0 1
-- Case 0 1 [(0, 0, 1), (1, 0, 1),... (n, 0, 1)]
-- Let 0 [(0, 0, 1), (1, 0, 1)..(n, 0, 1)] 1

replace :: Exp -> Pos -> Exp -> Exp
replace e [] r = r
replace (App t1 t2) (x:xs) r
  | x ==1 = App t1 (replace t2 xs r)
  | x ==0 = App (replace t1 xs r) t2

replace (TApp t1 t2) (x:xs) r
  | x ==1 = TApp t1 (replace t2 xs r)
  | x ==0 = TApp (replace t1 xs r) t2

replace (Lambda t t2) (x:xs) r
  | x == 1 = Lambda t (replace t2 xs r)
  | x == 0 =
      case t of
        Ann e ty -> Lambda (Ann (replace e xs r) ty) t2
        _ -> Lambda (replace t xs r) t2

replace (Abs y t2) (x:xs) r
  | x == 1 = Abs y (replace t2 xs r)
  | x == 0 = error "internal error from replace"

replace (Case e alts) (x:xs) r
  | x == 0 =
    case e of
      Ann e' ty -> Case (Ann (replace e' xs r) ty) alts
      _ -> Case (replace e xs r) alts
  | x == 1 =
      case xs of
        [] -> error "internal: wrong position for case"
        y:y':ys -> Case e $ replaceL y y' ys alts r

replace (Let defs e) (x : xs) r
  | x == 1 = Let defs (replace e xs r)
  | x == 0 =
    case xs of
      [] -> error "internal: wrong position for let"
      y:y':ys -> Let (replaceL y y' ys defs r) e

-- replace (Ann e t) pos r = Ann (replace e pos r) t

replace a b r = error $ "from replace " ++ show a
replaceL y y' ys [] r = error "internal: wrong position for case/let branch"
replaceL 0 0 ys ((Ann p t,e):alts) r = (Ann (replace p ys r) t, e):alts
replaceL 0 0 ys ((p,e):alts) r = ((replace p ys r), e):alts
replaceL 0 1 ys ((p,e):alts) r = (p, (replace e ys r)):alts
replaceL y y' ys (a:alts) r | y > 0 = a : replaceL (y-1) y' ys alts r

isSingle (Var _ _) = True
isSingle (Const _ _) = True
isSingle _ = False

stream1 = 1 : stream1
stream0 = 0 : stream0

make n s | n > 0 = take (n-1) s

takeOnes 1 = [[]]
takeOnes n | n > 1 = (take (n-1) stream1):takeOnes (n-1)

makeZeros 0 = []
makeZeros n | n > 0 = make n stream0 : makeZeros (n-1)


applyS :: [(Name, Exp)] -> [(Exp, Int)] -> [(Exp, Int)]
-- applyS state g | trace ("applyS " ++show ("hi") ++"\n") False = undefined
applyS sub l = applyS' sub l []
  where applyS' :: [(Name, Exp)] -> [(Exp, Int)] -> [(Exp, Int)] -> [(Exp, Int)]
        applyS' sub [] store = store           
        applyS' sub (((Const x p1), n):xs) store = ((Const x p1), n): applyS' sub xs store
        applyS' sub a@(((Var x p1), n):xs) store =
          case lookup x sub of
            Nothing -> applyS' sub xs (((Var x p1), n):store)
            Just e ->
              let fvs = freeVars e
                  vars = [ x | ((Var x _), _) <- (a ++ store)]
                  extra = [ y | y <- fvs, not $ y `elem` vars]
                  (store', n') = updateS fvs store n
                  (xs', n'') = updateS fvs xs n'
                  store'' = (map (\ x -> (Var x dummyPos, n'')) extra) ++ store'
              in applyS' sub xs' store''
        updateS fvs ((Const x p1, v):l) n =
          let (res, n') = updateS fvs l n
          in ((Const x p1, v):res, n')
        updateS fvs ((Var x p1, v):l) n =
          if x `elem` fvs
          then let n' = min n v
                   (res, n'') = updateS fvs l n'
               in ((Var x p1, n''):res, n'')
          else let (res, n'') = updateS fvs l n
               in ((Var x p1, v) : res, n'')
        updateS fvs [] n = ([], n)


mylookup x ((Var y _, n):xs) | x == y = Just n
                             | otherwise = mylookup x xs
mylookup x ((Const y _, n):xs) | x == y = Just n
                               | otherwise = mylookup x xs
mylookup x [] = Nothing

scopeCheck :: [(Exp, Int)] -> [(Name, Exp)] -> Bool
-- scopeCheck state g | trace ("scopeCheck " ++show ("hi") ++"\n") False = undefined
scopeCheck lvars [] = True 
scopeCheck lvars ((x, e):xs) =
  case mylookup x lvars of
    Nothing -> scopeCheck lvars xs
    Just n ->
      let evars = eigenVar e
      in checkEigen evars lvars n && scopeCheck lvars xs
  where checkEigen (y:ys) lvars n =
          case mylookup y lvars of
            Nothing -> False
            Just n' -> n' < n && checkEigen ys lvars n
        checkEigen [] lvars n = True
  
                         
applyPhi :: [(Name, Exp)] -> [Phi] -> Either Doc [Phi]
applyPhi sub ls =
  let f = [(scopeCheck lvars sub, l) | l@(Phi p g e env lvars) <- ls]
      ls' = map (\(Phi p g e env lvars) ->
                    (Phi p (normalize' $ apply' (Subst sub) g)
                      e 
                      (map (\ (x, t) -> (x, normalize $ apply (Subst sub) t))
                        env)
                      (applyS sub lvars)))
            ls
  in if and $ map fst f then Right ls'
     else let (Phi p g e env lvars):as = [ l | (b, l) <- f, not b]
              m = (nest 2 (text "environmental scope error when applying substitution") $$
                    nest 2 ( text "[" <+> disp sub <+> text "]")) $$
                  (nest 2 $ text "local variables list:" $$
                    nest 2 (hsep $ map (\ (x, i) -> parens $ disp x <+> text ","
                                                    <+> int i) lvars)) $$
                  (nest 2 $ text "the local goal:" $$ nest 2 (disp g)) $$
                  (nest 2 $ text "the local expression:" $$ nest 2 (disp e))
          in Left m


getValue :: [(Exp, Int)] -> Int
getValue [] = 1
getValue xs = (maximum $ map snd xs) + 1

-- arranging the order of subgoals is a heuristic, we want to first solve
-- the subgoal that give us the most information. In this case, we want to
-- to solve the most sophisticated subgoal first, because sophisticated subgoal
-- contains more information. The notion of sophistication of
-- a subgoal is defined by the number of implication it has, and whether
-- the subgoal is a variable or a constant.
-- TLDR: arranging subgoals is basically a black magic
-- measure state | trace ("measure " ++show (state) ++"\n") False = undefined
measure :: Exp -> Int
measure (Var _ _) = 0
measure (Const _ _) = 1
measure (Imply a b) = (measure a) + (measure b) + 1
measure (Forall a b) = measure b
measure (App a b) = 1

-- sortGT state1 state2 | trace ("sortGT " ++show (state1) ++"\n") False = undefined
sortGT ((p1, g1),e1) ((p2, g2),e2)
  | measure g1 < measure g2 = GT
  | measure g1 > measure g2 = LT
  | measure g1 == measure g2 = EQ
  
arrange :: [((Pos, Exp), Exp)] -> [((Pos, Exp), Exp)]
-- ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
-- arrange state1 | trace ("arrange " ++show (state1) ++"\n") False = undefined
arrange l = sortBy sortGT l 
-- arrange ls =  partition helper ls
--   where helper ((p,(Var _)), (Lambda _ _)) = False
--         helper _ = True



scopeError fun imp goal f y sub lvars pf exp pos =
  text "when checking function" <+> text fun $$
  text "at position" <+> disp pos $$
  text "scope error when matching" <+> disp imp $$
  text "against"<+> disp (goal)$$
  (nest 2 (text "when applying" <+> text y <+> text ":"
            <+> disp f)) $$
  (nest 2 (text "when applying substitution" <+> text "["
            <+> disp sub <+> text "]")) $$
  (nest 2 $ text "current variables list:" $$
    nest 2 (hsep $ map (\(x,i) ->
                          parens $ disp x <+> comma <+> int i)
             lvars)) $$
  (nest 2 $ text "the current expression:" <+> disp exp) $$
  (nest 2 $ text "the current mixed proof term:" $$
   nest 2 (disp pf))

matchError fun imp goal y f pf exp pos =
  text "when type checking the function" <+> text fun $$
  text "at position" <+> disp pos $$
  text "can't match" <+> disp imp $$
  text "against" <+> disp goal $$
  (nest 2 (text "when applying" <+>text y <+> text ":"
           <+> disp f)) $$
  (nest 2 (text "current expression:" <+> disp exp)) $$
  (nest 2 $ text "current mixed proof term" $$
   nest 2 (disp pf))

transit :: ResState -> [ResState]
-- transit state | trace ("transit " ++show (state) ++"\n") False = undefined
transit (Res fun pf
          ((Phi pos
             (Just goal@(Forall x y))
             (Just exp@(Lambda _ _)) gamma lvars):phi)
          Nothing i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "#") vars [i..]
      absNames' = map (\ x -> Const x dummyPos) absNames
      absVars = zip absNames' [getValue lvars ..]
      sub = zip vars absNames'
      imp' = apply (Subst sub) imp
      newAbs = foldr (\ a b -> Abs a b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream1
  in [(Res fun pf'
       ((Phi pos'
          (Just imp')
          (Just exp)
          gamma
          (lvars++ absVars)):phi)
       Nothing (i+lv))]


transit (Res fun pf
          ((Phi pos
             (Just goal@(Imply _ _))
             (Just exp@(Lambda _ _ )) gamma lvars):phi)
          Nothing i) =
  let (bs, h) = getHB goal
      (vars, b) = (viewLArgs exp, viewLBody exp)
      len = length vars
      lenB = length bs
      l = min len lenB
      (vars', b', h') =
        if len > lenB
        then (take lenB vars, reLam (drop lenB vars) b, h)
        else (vars, b, reImp (drop len bs) h)
      (thetas, j) = makePatEnv vars' i
      newlvars = map snd $ concat thetas
      n = getValue lvars
      indlvars = map (\ x -> (x, n)) newlvars
      lvars' = lvars++ indlvars
      positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes l)      
      pairs = zip (zip (zip positionsVars bs) vars') thetas
      newEnv = map (\ (((pos', g), pat), thetaP) ->
                       (Phi pos'
                         (Just g)
                         (Just pat)
                         (thetaP++gamma) lvars'))
               pairs
      boPos = pos++(take (l-1) stream1)++[1]
      newEnv' = newEnv ++
                [(Phi boPos (Just h') (Just b') (concat thetas ++ gamma) lvars')]
      newLam = foldr (\ a b -> Lambda (Ann a a) b) h' bs
      pf' = replace pf pos newLam
  in [(Res fun pf' (newEnv' ++ phi) Nothing j)]

transit (Res fun pf
          ((Phi pos
             (Just goal)
             (Just exp@(Case e alts))
             gamma lvars):phi)
          Nothing i) =
  let pats = map fst alts
      brExps = map snd alts
      y = "y"++show i++"#"
      len = length alts
      n = getValue lvars
      (thetas, j) = makePatEnv pats (i+1)
      newlvars = (Var y dummyPos, n) : map (\x -> (x, n)) (map snd $ concat thetas)
      lvars' = lvars++newlvars
      posLeft =  map (\ p -> pos++[1, p, 0]) [0..(len-1)]
      posRight = map (\ p -> pos++[1, p, 1]) [0..(len-1)]
      leftEnv = map (\(po, (p, th)) ->
                        (Phi po (Just (Var y dummyPos))
                          (Just p) (th++gamma) lvars')) 
                (zip posLeft (zip pats thetas))
      rightEnv = map (\(po, (e', th)) ->
                         (Phi po (Just goal)
                           (Just e') (th++gamma) lvars')) 
                 (zip posRight (zip brExps thetas))
      altsEnv =  leftEnv ++ rightEnv
      newEnv = (Phi (pos++[0]) (Just (Var y dummyPos)) (Just e) gamma lvars'):altsEnv
      newCase = Case (Ann (Var y dummyPos) (Var y dummyPos)) $ replicate len ((Var y dummyPos), goal) 
      pf' = replace pf pos newCase
  in [(Res fun pf' (newEnv++phi) Nothing j)]

transit (Res fun pf
          ((Phi pos
             (Just goal)
             (Just exp@(Let defs e)) gamma lvars):phi)
          Nothing i) =
  let pats = annotate defs
      (pats', j) = withVars pats i
      (tps, j') = makePats pats' j 
      n = getValue lvars
      len = length defs
      lvars' = lvars ++ makeLvars tps n
      posLeft =  map (\ p -> pos++[0, p, 0]) [0..(len-1)]
      posRight = map (\ p -> pos++[0, p, 1]) [0..(len-1)]
      leftEnv = map (\(po, (env, t, p, e)) ->
                        (Phi po (Just t) (Just p) (env++gamma) lvars')) 
                (zip posLeft tps)
      thetas = concat $ map (\ (a,b,c,d) -> a) tps
      rightEnv = map (\(po, (env, t, p, e)) ->
                         (Phi po (Just t) (Just e) (thetas++gamma) lvars'))
                 (zip posRight tps)
      defsEnv = leftEnv ++ rightEnv
      
      newEnv = 
        defsEnv ++ [(Phi (pos++[1]) (Just goal) (Just e) (thetas ++gamma) lvars')]
      newLet = Let (map (\ (a,b,c,d) -> ((Ann b b), b)) tps) goal 
      pf' = replace pf pos newLet
  in [(Res fun pf' (newEnv++phi) Nothing j')]
      
transit (Res fun pf
          ((Phi pos
             (Just goal)
             (Just exp) gamma lvars):phi)
          Nothing i)
  | isAtom exp =
      let y = getName exp
          ypos = getPos exp
      in case lookup y gamma of
        Nothing ->
          let m' = Just $ disp ypos <> text ":"<+> text "can't find" <+> text y
                   <+> text "in the environment" 
          in [(Res fun pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
        Just f | isVar f || isVar goal ->
            let sub =
                  if f == goal then []
                  else if isVar f then [(getName f, goal)]
                  else if isVar goal then [(getName goal, f)]
                  else error "internal error from transit" in
            if scopeCheck lvars sub then
              let lvars' = applyS sub lvars
                  gamma' = map (\ (x, t) ->
                                   (x, apply (Subst sub) t) )
                           gamma
                  pf' = apply (Subst sub) pf
                  pf'' = replace pf' pos exp
              in case applyPhi sub phi of 
                   Right p ->
                     return (Res fun pf''
                              (p++[Phi pos Nothing Nothing gamma' lvars'])
                              Nothing i)
                   Left m' ->
                     let mess = text "globally, " <+>
                                scopeError fun f goal f y sub lvars pf exp ypos
                         m1 = m' $$ nest 2 mess
                     in [Res fun pf
                          ((Phi pos
                             (Just goal)
                             (Just exp) gamma lvars):phi)
                          (Just m1) i]                         
                             
            else let mess = scopeError fun f goal f y sub lvars pf exp ypos
                 in [Res fun pf
                      ((Phi pos
                        (Just goal)
                        (Just exp) gamma lvars):phi)
                      (Just mess) i]
                         
        Just f | otherwise ->
          let (vars, imp) = getVars goal
              lv = length vars
              absNames = zipWith (\ x y -> x ++ show y ++ "#") vars [i..]
              absNames' = map (\ x -> Const x dummyPos) absNames
              absVars = zip absNames' [getValue lvars ..]
              sub = zip vars absNames'
              imp' = apply (Subst sub) imp
              newAbs = foldr (\ a b -> Abs a b) imp' absNames
              pf1 = replace pf pos newAbs
              pos' = pos ++ take lv stream1
              i1 = i+lv
              pos1 = pos'
              goal1 = imp'
              lvars1 = lvars++absVars
              (vars2, imp2) = getVars f
              fresh = map (\ (v, j) -> v ++ show j ++ "#") $ zip vars2 [i1..]
              fresh' = map (\ x -> Var x dummyPos) fresh
              renaming = zip vars2 fresh'
              imp2' = apply (Subst renaming) imp2
              i' = i1 + length vars
              ss = runMatch imp2' goal1
          in case ss of
              [] ->
                let m' = matchError fun imp2' goal1 y f pf exp ypos
                in [(Res fun pf
                      ((Phi pos
                         (Just goal)
                         (Just exp) gamma lvars):phi)
                      (Just m') i)]
              _ ->
                do Subst sub' <- ss
                   if scopeCheck lvars1 sub'
                     then
                     let pf' = normalize $ apply (Subst sub') pf1
                         np = ([ s | r <- fresh,
                                      let s = case lookup r sub' of
                                                Nothing -> (Var r dummyPos)
                                                Just t -> t])
                         contm = foldl' (\ z x -> TApp z x) exp np     
                         pf'' = replace pf' pos1 contm
                         n = getValue lvars1
                         freshlvars = map (\ x -> (x, n)) fresh'
                         gamma' = map (\ (x, t) -> (x, normalize $ apply (Subst sub') t)) gamma
                         lvars' = applyS sub' (lvars1++freshlvars)
                         phi' = applyPhi sub' phi 
                     in case phi' of
                          Right p ->
                            return (Res fun pf''
                                     (p++[Phi pos1 Nothing Nothing gamma' lvars'])
                                     Nothing i')
                          Left m' ->
                            let mess = text "globally, " <+>
                                       scopeError fun imp2' goal1 f y sub' lvars pf exp ypos
                                m1 = m' $$ nest 2 mess 
                            in [Res fun pf
                                 ((Phi pos (Just goal)
                                    (Just exp) gamma lvars):phi)
                                 (Just m1) i]
                     else let mess = scopeError fun imp2' goal1 f y sub' lvars1 pf exp ypos
                          in [Res fun pf
                               ((Phi pos (Just goal)
                                  (Just exp) gamma lvars):phi)
                               (Just mess) i]


transit (Res fun pf
          ((Phi pos
             (Just goal)
             (Just exp) gamma lvars):phi)
          Nothing i) = 
  case flatten exp of
    (Var v p1) : xs -> handle v p1 xs
    (Const v p1) : xs -> handle v p1 xs
    a ->
      let m' = Just $ text "when checking function" <+> text fun $$
               (text "need more information to check expression:" <+> disp exp) $$
               (text "current goal: " <+> disp goal) $$
               (nest 2 $ text "current mixed proof term" $$
                 nest 2 (disp pf)) $$
               (nest 2 $ text "current env" $$
                 nest 2 (disp gamma)) 
      in [(Res fun pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]

  where
    handle v p1 xs =
      case lookup v gamma of
        Nothing ->
          let m' = Just $ disp p1 <> text ":" <+>text "can't find" <+> text v
                   <+> text "in the environment" $$ text "when checking function" <+> text fun
          in [(Res fun pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
        Just f ->
          let (vars, head, body) = separate f
              i' = i + length vars
              fresh = map (\ (v, j) -> v ++ show j ++ "#") $ zip vars [i..]
              renaming = zip vars (map (\ x -> Var x dummyPos) fresh)
              body'' = map (apply (Subst renaming)) body
              head'' = apply (Subst renaming) head
              n = length xs
              l = length body
              j = if l <= n then i' + (n-l) else i'
              glVars = map (\ i -> Var ("y"++show i++"#") dummyPos) [i'..j-1]
              goal' = reImp glVars goal
              newHead = if n < l then reImp (drop n body'') head'' else head''
              ss = runMatch newHead goal'
          in case ss of
               [] ->
                 let m' = matchError fun newHead goal' v f pf exp p1
                 in [(Res fun pf
                       ((Phi pos
                          (Just goal)
                          (Just exp) gamma lvars):phi)
                       (Just m') i)]
               _ -> 
                 do Subst sub <- ss
                    if scopeCheck lvars sub
                      then
                      let dom = map fst sub
                          body' =
                            if n < l then
                              map normalize $
                              (map (apply (Subst sub)) (take n body''))
                            else map normalize $
                                 (map (apply (Subst sub)) body'')
                          body1 = body' ++ (map (apply (Subst sub)) glVars)
                          np = ([ s | r <- fresh,
                                  let s = case lookup r sub of
                                            Nothing -> (Var r dummyPos)
                                            Just t -> t])
                          va = getValue lvars     
                          lvars' = applyS sub $ lvars ++
                                   (map (\ x -> (Var x dummyPos, va)) fresh) ++
                                   map (\x -> (x, va)) glVars
                          name = if isUpper $ Data.List.head v
                                 then Const v p1 else Var v p1
                          contm = foldl' (\ z x -> App z x)
                                  (foldl' (\ z x -> TApp z x) name np)
                                  body1
                          pf' = normalize $ apply (Subst sub) pf
                          pf'' = replace pf' pos contm
                          zeros = makeZeros $ length body1
                          ps = map (\ x -> pos++x++[1]) zeros
                          gamma' = map
                                   (\(x, y) ->
                                       (x, normalize $ apply (Subst sub) y))
                                   gamma
                          highlow = arrange $ zip (zip ps body1) xs
                          highlow' = map (\((p, g),e ) ->
                                                   (Phi p (Just g) (Just e) gamma' lvars'))
                                     highlow
                                            -- map (\((p, g),e ) ->
                                            --         (Phi p (Just g) (Just e) gamma' lvars'))
                                            -- low)
                          phi' = applyPhi sub phi
                      in case phi' of
                           Right p ->
                             return $ Res fun pf'' (highlow'++p) Nothing j
                           Left m' ->
                             let mess = text "globally," <+>
                                        scopeError fun newHead goal' f v sub lvars pf exp p1
                                 m1 = m' $$ nest 2 mess 
                             in [Res fun pf
                                  ((Phi pos
                                     (Just goal)
                                     (Just exp) gamma lvars):phi)
                                  (Just m1) i]
                      else let mess = scopeError fun newHead goal' f v sub lvars pf exp p1
                           in [Res fun pf
                                ((Phi pos
                                   (Just goal)
                                   (Just exp) gamma lvars):phi)
                                (Just mess) i]


transit e = [e]
          
ersm :: [ResState] -> Either Doc (Exp, [Name])
-- ersm state | trace ("ersm " ++show ("hi") ++"\n") False = undefined
ersm init = let s = concat $ map transit init
                (fails, pending) = partition failure s
                flag = length fails == length s
            in if flag then
                 let rs = map (\(Res _ _ _ (Just m) _) -> m) fails in
                   Left $ sep (map (\ (d, i) -> text "Wrong situation" <+> int i $$ nest 2 d)
                                $ zip rs [1..])
               else case [p | p <- pending, success p ] of
                      [] -> ersm s
                      -- a -> Right $ map mixedTerm a
                      (Res _ pf phi _ _):_ -> Right (pf, genVars phi)
                             
  where failure (Res _ _ _ (Just _) _) = True
        failure _ = False
        success (Res _ pf phi Nothing i) =
          and $ map (\p -> currentGoal p == Nothing && currentProg p == Nothing) phi 
        success _ = False
        genVars phi = concat $ map (\(Phi _ _ _ _ lvars) -> genVars' lvars) phi
        genVars' ((Var x _, n):xs) = x : genVars' xs
        genVars' (x:xs) = genVars' xs
        genVars' [] = []
