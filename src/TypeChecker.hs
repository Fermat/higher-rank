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

-- Global type environment
type TyEnv = [(Name, Exp)]

makeTyEnv :: [Decl] -> TyEnv
makeTyEnv [] = [] 
makeTyEnv ((DataDecl _ _ cons):xs) = [(d, e) | (Const d, e) <- cons] ++ makeTyEnv xs
makeTyEnv ((FunDecl (Var f) t _):xs) = (f, t):makeTyEnv xs
makeTyEnv ((Prim (Var f) t):xs) = (f, t):makeTyEnv xs

makeLam pats e = foldr (\ p e' -> Lambda p e') e pats
  
checkDecls a = let tyEnv = makeTyEnv a
                   funcDefs = concat [map (\(pats, d) -> (t, makeLam pats d)) defs |
                                       (FunDecl (Var f) t defs) <- a]
              in mapM (typeCheck tyEnv) funcDefs

typeCheck env (goal, e) =
  let phi = Phi [] goal e env []
      init = Res goal [phi] Nothing 0 in
    ersm [init] 
        
data Phi = Phi{
              position :: Pos,
              currentGoal :: Exp,
              currentProg :: Exp,
              env :: TyEnv,
              scope :: [(Name, Int)] }
           deriving (Show)

-- Resolution state
data ResState = Res{
  mixedTerm :: Exp,
  phi :: [Phi],
  errMessage :: Maybe Doc,
  counter :: Int
  } deriving (Show)

getHB ::  Exp -> ([Exp],Exp)
getHB (Imply x y) = let (bs, t') = getHB y in (x:bs, t')
getHB t = ([], t)

getVars :: Exp -> ([Name],Exp)
getVars (Forall x t) = let (xs, t') = getVars t in (x:xs, t')
getVars t = ([], t)

separate f = let (vars, imp) = getVars f
                 (bs, h) = getHB imp
             in (vars, h, bs)
                
reImp :: [Exp] -> Exp -> Exp
reImp [] h = h
reImp (x:xs) h = Imply x (reImp xs h)

reLam :: [Exp] -> Exp -> Exp
reLam [] h = h
reLam (x:xs) h = Lambda x (reLam xs h)

patternVars :: Exp -> Int -> (TyEnv, Int)
patternVars (Ann (Var x) t) i = ([(x, t)], i)
patternVars p i = let fvs = freeVars p
                      j = (i+(length fvs))-1
                      ns = [i..j]
                      vars = map (\ n -> Var $ "y"++show n++"'") ns in
                    (zip fvs vars, j+1)

makePatEnv :: [Exp] -> Int -> ([TyEnv], Int)
makePatEnv [] i = ([], i)
makePatEnv (x:xs) i = let (env, j) = patternVars x i
                          (res, n) = makePatEnv xs j in
                        (env:res, n)

isAtom (Const x) = True
isAtom (Var _) = True
isAtom _ = False

isVar (Var _) = True
isVar _ = False

getName (Const x) = x
getName (Var x) = x
getName _ = error "from get Name"
-- Postion encoding scheme:
-- App 0 1
-- Lambda 0 1
-- Case 0 1 [(0, 0, 1), (1, 0, 1),... (n, 0, 1)]
-- Let 0 [(0, 0, 1), (1, 0, 1)..(n, 0, 1)] 1

replace :: Exp -> Pos -> Exp -> Exp
replace e [] r = r
replace (App t1 t2) (x:xs) r | x ==1 = App t1 (replace t2 xs r)
                             | x ==0 = App (replace t1 xs r) t2

replace (Lambda t t2) (x:xs) r | x == 1 = Lambda t (replace t2 xs r)
                               | x == 0 =
                                 case t of
                                   Ann e ty -> Lambda (Ann (replace e xs r) ty) t2
                                   _ -> Lambda (replace t xs r) t2

replace (Case e alts) (x:xs) r | x == 0 = Case (replace e xs r) alts
                               | x == 1 =
                                   case xs of
                                     [] -> error "internal: wrong position for case"
                                     y:y':ys -> Case e $ replaceL y y' ys alts r

replace (Let defs e) (x : xs) r | x == 1 = Let defs (replace e xs r)
                                | x == 0 = case xs of
                                             [] -> error "internal: wrong position for case"
                                             y:y':ys -> Let (replaceL y y' ys defs r) e
replaceL y y' ys [] r = error "internal: wrong position for case/let branch"
replaceL 0 0 ys ((p,e):alts) r = ((replace p ys r), e):alts
replaceL 0 1 ys ((p,e):alts) r = (p, (replace e ys r)):alts
replaceL y y' ys (a:alts) r | y > 0 = a : replaceL (y-1) y' ys alts r


isSingle (Var _) = True
isSingle (Const _) = True
isSingle _ = False

stream1 = 1 : stream1
stream0 = 0 : stream0
make n s | n > 0 = take (n-1) s
takeOnes 1 = [[]]
takeOnes n | n > 1 = (take (n-1) stream1):takeOnes (n-1)
makeZeros 0 = []
makeZeros n | n > 0 = make n stream0 : makeZeros (n-1)

-- removing the notion of global existential variables
scopeCheck :: [(Name, Int)] -> [(Name, Exp)] -> Bool
scopeCheck lvars sub = let dom = map fst lvars in
                         and [ne < nx | (x, t) <- sub, x `elem` dom, let (Just nx) = lookup x lvars, let evars = eigenVar t, e <- evars, e `elem` dom, let (Just ne) = lookup e lvars]
applyPhi :: [(Name, Exp)] -> [Phi] -> Either Doc [Phi]
applyPhi sub ls = let f = [(scopeCheck lvars sub, l) | l@(Phi p g e env lvars) <- ls]
                      ls' = map (\(Phi p g e env lvars) ->
                                    (Phi p (normalize $ apply (Subst sub) g)
                                      (normalize $ apply (Subst sub) e)
                                      (map (\ (x, t) -> (x, normalize $ apply (Subst sub) t))
                                       env)
                                      lvars)) ls
                  in if and $ map fst f then Right ls'
                     else let (Phi p g e env lvars):as = [ l | (b, l) <- f, not b]
                              m = (nest 2 (text "environmental scope error when applying substitution") $$
                                   nest 2 ( text "[" <+> disp sub <+> text "]")) $$
                                  (nest 2 $ text "local variables list:" $$
                                   nest 2 (hsep $ map (\ (x, i) -> parens $ text x <+> text ","
                                                        <+> int i) lvars)) $$
                                  (nest 2 $ text "the local goal:" $$ nest 2 (disp g)) $$
                                  (nest 2 $ text "the local expression:" $$ nest 2 (disp e))
                          in Left m


getValue :: [(Name, Int)] -> Int
getValue [] = 1
getValue xs = (maximum $ map snd xs) + 1
  -- (snd $ last xs)+1

arrange :: [((Pos, Exp), Exp)] -> ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
arrange ls =  partition helper ls
  where helper ((p,(Var _)), (Lambda _ _)) = False
        helper _ = True
  -- where helper ((p,f),e) = let (vars, h, _) = separate f
  --                              fr = freeVars f
  --                          in null (fr `intersect` (freeVars h))
simp es = map simp' es
simp' (Ann x _) = x
simp' a = a

transit :: ResState -> [ResState]
transit state | trace ("transit " ++show (state) ++"\n") False = undefined
transit (Res pf ((Phi pos goal@(Imply _ _) exp@(Lambda _ _ ) gamma lvars):phi) Nothing i) =
  let (bs, h) = getHB goal
      (vars, b) = (viewLArgs exp, viewLBody exp)
      len = length vars
      lenB = length bs
  in
    if len > lenB then
      let vars' = take lenB vars
          b' = reLam (drop lenB vars) b
          (thetas, j) = makePatEnv vars' i
          newlvars = map snd $ concat thetas
          n = getValue lvars
          indlvars = map (\ (Var x) -> (x, n)) newlvars
          lvars' = lvars++ indlvars
          positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes lenB)
          pairs = zip (zip (zip positionsVars bs) vars') thetas
          newEnv = map (\ (((pos', g), pat), thetaP) -> (Phi pos' g pat (thetaP++gamma) lvars')) pairs
          boPos = pos++(take (lenB-1) stream1)++[1]
          newEnv' = newEnv ++ [(Phi boPos h b' (concat thetas ++ gamma) lvars')]
          newLam = foldr (\ a b -> Lambda (Ann a a) b) h bs
          pf' = replace pf pos newLam
      in [(Res pf' (newEnv' ++ phi) Nothing j)]
    else let (thetas, j) = makePatEnv vars i
             newlvars = map snd $ concat thetas
             n' = getValue lvars
             indvars = map (\ (Var x) -> (x, n')) newlvars
             lvars' = lvars++indvars
             h' = reImp (drop len bs) h  
             positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes len)
             pairs = zip (zip (zip positionsVars bs) vars) thetas
             newEnv = map (\ (((pos', g), pat), thetaP) -> (Phi pos' g pat (thetaP++gamma) lvars')) pairs
             boPos = pos++(take (len-1) stream1)++[1]
             newEnv' = newEnv ++ [(Phi boPos h' b (concat thetas ++ gamma) lvars')]
             newLam = foldr (\ a b -> Lambda (Ann a a) b) h' (take len bs)
             pf' = replace pf pos newLam
         in [(Res pf' (newEnv' ++ phi) Nothing j)]

transit (Res pf ((Phi pos goal exp@(Case e alts) gamma lvars):phi) Nothing i) =
  let
    pats = map fst alts
    brExps = map snd alts
    y = "y"++show i
    len = length alts
    n = getValue lvars
    (thetas, j) = makePatEnv pats (i+1)
    newlvars = y : map (\(Var x) -> x) (map snd $ concat thetas)
    newlvars' = map (\ x -> (x, n)) newlvars
    lvars' = lvars++newlvars'
    posLeft =  map (\ p -> pos++[1, p, 0]) [0..(len-1)]
    posRight = map (\ p -> pos++[1, p, 1]) [0..(len-1)]
    leftEnv = map (\(po, (p, th)) -> (Phi po (Var y) p (th++gamma) lvars')) $
              zip posLeft (zip pats thetas)
    rightEnv = map (\(po, (e', th)) -> (Phi po goal e' (th++gamma) lvars')) $
               zip posRight (zip brExps thetas)
    altsEnv =  leftEnv ++ rightEnv
    newEnv = (Phi (pos++[0]) (Var y) e gamma lvars'):altsEnv
    newCase = Case (Var y) $ replicate len ((Var y), goal) 
    pf' = replace pf pos newCase
  in [(Res pf' (newEnv++phi) Nothing j)]


transit (Res pf ((Phi pos goal@(Var x) exp gamma lvars):phi) Nothing i)
  | isAtom exp =
      let y = getName exp
      in case lookup y gamma of
        Nothing -> let m' = Just $ text "can't find" <+> text y
                           <+> text "in the environment" in
                    [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
        Just f ->
          let sub' = if isVar f then [(getName f, Var x)] else [(x, f)] in
            if scopeCheck lvars sub'
            then let pf' = normalize $ apply (Subst sub') pf
                     pf'' = replace pf' pos exp
                     phi' = applyPhi sub' phi in
                   case phi' of
                     Right p -> return $ Res pf'' p Nothing i
                     Left m' ->
                       let mess = (text "globally, when matching" <+> disp f) $$
                                  (text "against"<+> disp (goal)) $$
                                  (nest 2 (text "when applying" <+> text y
                                            <+> text ":" <+> disp f)) $$
                                  (nest 2 (text "when applying substitution"
                                           <+> text "[" <+> disp sub' <+> text "]")) $$
                                  (nest 2 $ text "current variables list:" $$
                                    nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                  (nest 2 $ text "the current mixed proof term:" $$
                                   nest 2 (disp pf))
                           m1 = m' $$ nest 2 mess in
                         [Res pf ((Phi pos goal exp gamma lvars):phi) (Just m1) i]
            else let mess = text "scope error when matching" <+> disp (f) $$
                            text "against"<+> disp (goal)$$
                            (nest 2 (text "when applying" <+> text y <+> text ":"
                                     <+> disp f)) $$
                            (nest 2 (text "when applying substitution" <+> text "["
                                     <+> disp sub' <+> text "]")) $$
                            (nest 2 $ text "current variables list:" $$
                              nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                            (nest 2 $ text "the current mixed proof term:" $$
                              nest 2 (disp pf))
                 in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]
                                                                          
     
transit (Res pf ((Phi pos goal@(Forall x y) exp gamma lvars):phi) Nothing i) | isAtom exp =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      absVars = zip absNames [getValue lvars ..]
      sub = zip vars (map Const absNames)
      imp' = apply (Subst sub) imp
      newAbs = foldr (\ a b -> Lambda (Var a) b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream1
      z = getName exp
  in case lookup z gamma of
       Nothing -> let m' = Just $ text "can't find" <+> text z
                           <+> text "in the environment" in
                    [(Res pf ((Phi pos goal (Var z) gamma lvars):phi) m' i)]
       Just (Var exy) ->
         let sub' = [(exy, goal)] in
           if scopeCheck lvars sub'
           then let pf' = normalize $ apply (Subst sub') pf
                    pf'' = replace pf' pos (Var z)
                    phi' = applyPhi sub' phi in
                  case phi' of
                    Right p -> return $ Res pf'' p Nothing i
                    Left m' ->
                      let mess = (text "globally, when matching" <+> disp (exy)) $$
                                 (text "against"<+> disp (goal)) $$
                                 (nest 2 (text "when applying" <+> text z
                                           <+> text ":" <+> disp exy)) $$
                                 (nest 2 (text "when applying substitution"
                                           <+> text "[" <+> disp sub' <+> text "]")) $$
                                 (nest 2 $ text "current variables list:" $$
                                   nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                 (nest 2 $ text "the current mixed proof term:" $$
                                  nest 2 (disp pf))
                          m1 = m' $$ nest 2 mess in
                              [Res pf ((Phi pos goal exp gamma lvars):phi) (Just m1) i]
           else let mess = text "scope error when matching" <+> disp (exy) $$
                           text "against"<+> disp (goal)$$
                           (nest 2 (text "when applying" <+> text z <+> text ":"
                                     <+> disp exy)) $$
                           (nest 2 (text "when applying substitution" <+> text "["
                                     <+> disp sub' <+> text "]")) $$
                           (nest 2 $ text "current variables list:" $$
                             nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                           (nest 2 $ text "the current mixed proof term:" $$
                             nest 2 (disp pf))
                in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]
       _ ->

         [(Res pf' ((Phi pos' imp' exp gamma (lvars++ absVars)):phi) Nothing (i+lv))]
                   

transit (Res pf ((Phi pos goal@(Forall x y) exp@(Lambda _ _) gamma lvars):phi) Nothing i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      absVars = zip absNames [getValue lvars ..]
      sub = zip vars (map Const absNames)
      imp' = apply (Subst sub) imp
      newAbs = foldr (\ a b -> Lambda (Var a) b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream1
  in [(Res pf' ((Phi pos' imp' exp gamma (lvars++ absVars)):phi) Nothing (i+lv))]

transit (Res pf ((Phi pos goal exp@(Let defs e) gamma lvars):phi) Nothing i) =
  let pats = map fst defs
      defends = map snd defs
      (thetas, j) = makePatEnv pats i
      len = length pats
      pats' = simp pats
      j' = j + len
      tyvars = map (\ x -> "y"++show x ++ "'") [j.. (j'-1)]
      tyvars' = map Var tyvars
      n = getValue lvars
      tyvarsind = map (\ x -> (x, n)) tyvars
      newlvars =  map (\(Var x) -> (x, n)) (map snd $ filter (\ (x, e) -> isVar e) $ concat thetas)
      lvars' = lvars++ tyvarsind ++ newlvars 
      posLeft =  map (\ p -> pos++[0, p, 0]) [0..(len-1)]
      posRight = map (\ p -> pos++[0, p, 1]) [0..(len-1)]
      leftEnv = map (\(y , (po, p)) -> (Phi po y p (concat thetas++gamma) lvars')) $
                zip tyvars' $ zip posLeft pats' 
      rightEnv = map (\(y, (po, e')) -> (Phi po y e' (concat thetas++gamma) lvars')) $
                 zip tyvars' $ zip posRight defends 
      defsEnv =  leftEnv ++ rightEnv
      newEnv = defsEnv ++ [(Phi (pos++[1]) goal e (concat thetas ++gamma) lvars')]
      newLet = Let (map (\ x -> (x, x)) tyvars') goal 
      pf' = replace pf pos newLet
  in [(Res pf' (newEnv++phi) Nothing j')]



transit (Res pf ((Phi pos goal exp gamma lvars):phi) Nothing i) = 
  case flatten exp of
    (Var v) : xs -> handle v xs
    (Const v) : xs -> handle v xs
    a -> let m' = Just $ (text "need more information to check expression:" <+> disp exp) $$
                         (text "current goal: " <+> disp goal) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf)) $$
                         (nest 2 $ text "current env" $$
                           nest 2 (disp gamma)) in                                
           [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
      -- error $ "unhandle situation in transit\n " ++ "expression " ++ show (disp exp) ++ "\n goal: " ++ show (disp goal)
  where handle v xs =
          case lookup v gamma of
            Nothing -> let m' = Just $ text "can't find" <+> text v
                                <+> text "in the environment" in
                         [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
            Just f -> let (vars, head, body) = separate f
                          (gvars, ghead, gbody) = separate goal
                          i' = i + length vars
                          fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
                          renaming = zip vars (map Var fresh)
                          body'' = map (apply (Subst renaming)) body
                          head'' = apply (Subst renaming) head
                          n = length xs
                          m = length gbody
                          l = length body
                      in
                        if l <= n then let j = i' + (n-l) in
--                          error $ "in app1" ++ show goal ++ show (disp pf)
                                         app1 fresh head'' body'' f v xs j i' 
                        else if l > n then
                               app2 fresh head'' body'' f v xs i' n
                             else
                               let m' = Just $ text "unhandle situation in application" $$
                                        text "for" <+> disp goal $$
                                        (nest 2 (text "when applying" <+>text v <+> text ":"
                                                 <+> disp f)) $$
                                        (nest 2 $ text "current program" $$
                                         nest 2 (disp exp)) $$
                                        (nest 2 $ text "current mixed proof term" $$
                                         nest 2 (disp pf)) $$
                                        (nest 2 $ text "current env" $$
                                         nest 2 (disp gamma))
                               in [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]

        app2 fresh head'' body'' f v xs i' n =
          let newHead = reImp (drop n body'') head''
              ss = runMatch' newHead goal in
            case ss of
              [] ->
                let m' = Just $ text "from app2, can't match" <+> disp newHead $$
                         text "against" <+> disp goal $$
                         (nest 2 (text "when applying" <+>text v <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf))
                in [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   let subFCheck = [(x, y)|(x, y) <- sub, not $ x `elem` fresh] -- x `elem` map fst lvars]
                   if scopeCheck lvars subFCheck
                     then let dom = map fst sub -- freeVars newHead
                              body' = map normalize $ (map (apply (Subst sub)) (take n body''))
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              -- lvars1 = filter (\(x, i) -> not $ x `elem` map fst sub) lvars
                              lvars'' = [(y, n) | y <- fresh, not $ y `elem` dom , (x, t) <- subFCheck, y `elem` freeVars t, let Just n = lookup x lvars]
                              lvars1 = lvars++lvars''
                              lvars' = lvars1 ++ zip [x | x <- fresh, not (x `elem` dom), not (x `elem` map fst lvars'')]
                                                 [getValue lvars1 ..]
                              name = if isUpper $ Data.List.head v
                                     then Const v else Var v
                              contm = foldl' (\ z x -> App z x)
                                      (foldl' (\ z x -> App z x) name np)
                                      body'
                              pf' = normalize $ apply (Subst subFCheck) pf
                              pf'' = replace pf' pos contm
                              zeros = makeZeros $ length body'
                              ps = map (\ x -> pos++x++[1]) zeros
                              gamma' = map
                                       (\(x, y) ->
                                          (x, normalize $ apply (Subst sub) y))
                                       gamma
                              (high, low) = arrange $ zip (zip ps body') xs
                              (high', low') = (map (\((p, g),e ) -> (Phi p g e gamma' lvars')) high, map (\((p, g),e ) -> (Phi p g e gamma' lvars')) low) 
                              phi' = applyPhi subFCheck phi in
                            case phi' of
                              Right p ->
                                return $ Res pf'' (high'++low'++p) Nothing i'
                              Left m' ->
                                let mess = text "globally, when matching" <+> disp (newHead) $$
                                           text "against"<+> disp (goal)$$
                                           (nest 2 (text "when applying" <+> text v
                                                    <+> text ":" <+> disp f)) $$
                                           (nest 2 (text "when applying substitution"
                                                    <+> text "[" <+> disp sub <+> text "]")) $$
                                           (nest 2 $ text "current variables list:" $$
                                            nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                           (nest 2 $ text "the current mixed proof term:" $$
                                            nest 2 (disp pf))
                                           
                                    m1 = m' $$ nest 2 mess in
                                  [Res pf ((Phi pos goal exp gamma lvars):phi) (Just m1) i]
                     else let mess = text "scope error when matching" <+> disp (newHead) $$
                                     text "against"<+> disp (goal)$$
                                     (nest 2 (text "when applying" <+> text v <+> text ":"
                                               <+> disp f)) $$
                                     (nest 2 (text "when applying substitution" <+> text "["
                                               <+> disp sub <+> text "]")) $$
                                     (nest 2 $ text "current variables list:" $$
                                      nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]

          
        app1 fresh head'' body'' f v xs j i' =
          let glVars = map (\ i -> Var $ "y"++show i++"'") [i'..j-1]
              glVars' = map (\ i -> "y"++show i++"'") [i'..j-1]
              goal' = reImp glVars goal
              ss = runMatch' head'' goal' in
            case ss of
              [] ->
                let m' = Just $ text "from app1, can't match" <+> disp head'' $$
                         text "against" <+> disp goal' $$
                         (nest 2 (text "when applying" <+>text v <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf)) $$
                         (nest 2 $ text "current env" $$
                           nest 2 (disp gamma)) $$
                         (nest 2 $ text "current exp" $$
                           nest 2 (disp exp)) 
                in [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   let subFCheck = [(x, y)|(x, y) <- sub, not $ x `elem` fresh ] 
                   if scopeCheck lvars subFCheck
                     then let dom = map fst sub -- freeVars head''
                              body' = map normalize $ (map (apply (Subst sub)) body'')
                              body1 = body' ++ (map (apply (Subst sub)) glVars)
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              lvars'' = [(y, n) | y <- fresh, not $ y `elem` dom , (x, t) <- subFCheck, y `elem` freeVars t, let Just n = lookup x lvars]
                              lvars1 = lvars++lvars''
                              lvars''' = lvars1 ++ zip [x | x <- fresh, not (x `elem` dom), not (x `elem` map fst lvars'')]
                                                 [getValue lvars1 ..]                                   
                              -- lvars1 = filter (\(x, i) -> not $ x `elem` map fst sub) lvars
                              -- lvars'' = lvars1 ++ zip [x | x <- fresh, not (x `elem` dom)]
                              --                        [getValue lvars1 ..]
                              va = getValue lvars'''          
                              lvars' = lvars''' ++ map (\x -> (x, va)) glVars'
                              name = if isUpper $ Data.List.head v
                                     then Const v else Var v
                              contm = foldl' (\ z x -> App z x)
                                      (foldl' (\ z x -> App z x) name np)
                                      body1
                              pf' = normalize $ apply (Subst subFCheck) pf
                              pf'' = replace pf' pos contm
                              zeros = makeZeros $ length body1
                              ps = map (\ x -> pos++x++[1]) zeros
                              gamma' = map
                                       (\(x, y) ->
                                          (x, normalize $ apply (Subst sub) y))
                                       gamma
                              (high, low) = arrange $ zip (zip ps body1) xs
                              (high', low') = (map (\((p, g),e ) -> (Phi p g e gamma' lvars')) high, map (\((p, g),e ) -> (Phi p g e gamma' lvars')) low) 
                              phi' = applyPhi subFCheck phi in
                            case phi' of
                              Right p ->
                                return $ Res pf'' (high'++low'++p) Nothing j
                                               
                              Left m' ->
                                let mess = text "globally, when matching" <+> disp (head'') $$
                                           text "against"<+> disp (goal)$$
                                           (nest 2 (text "when applying" <+> text v
                                                    <+> text ":" <+> disp f)) $$
                                           (nest 2 (text "when applying substitution"
                                                    <+> text "[" <+> disp sub <+> text "]")) $$
                                           (nest 2 $ text "current variables list:" $$
                                            nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                           (nest 2 $ text "the current mixed proof term:" $$
                                            nest 2 (disp pf))
                                           
                                    m1 = m' $$ nest 2 mess in
                                  [Res pf ((Phi pos goal exp gamma lvars):phi) (Just m1) i]

                     else let mess = text "scope error when matching" <+> disp (head'') $$
                                     text "against"<+> disp (goal)$$
                                     (nest 2 (text "when applying" <+> text v <+> text ":"
                                               <+> disp f)) $$
                                     (nest 2 (text "when applying substitution" <+> text "["
                                               <+> disp sub <+> text "]")) $$
                                     (nest 2 $ text "current variables list:" $$
                                      nest 2 (hsep $ map (\(x,i) -> parens $ text x <+> comma <+> int i) lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]

transit e = [e]
          
ersm :: [ResState] -> Either Doc Exp
ersm init = let s = concat $ map transit init
                (fails, pending) = partition failure s
                flag = length fails == length s
            in if flag then
                 let rs = map (\(Res _ _ (Just m) _) -> m) fails in
                   Left $ sep (map (\ (d, i) -> text "Wrong situation" <+> int i $$ nest 2 d)
                                $ zip rs [1..])
               else case [p | p <- pending, success p ] of
                      [] -> ersm s
                      -- a -> Right $ map mixedTerm a
                      (Res pf _ _ _):_ -> Right pf
                             
  where failure (Res _ _ (Just _) _) = True
        failure _ = False
        success (Res pf [] Nothing i) = True
        success _ = False
