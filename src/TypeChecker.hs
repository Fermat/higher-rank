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
              scope :: [Name] }
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

-- Postion encoding scheme:
-- App 0 1
-- Lambda 0 1
-- Case 0 1 [(0, 0, 1), (1, 0, 1),... (n, 0, 1)]

replace :: Exp -> Pos -> Exp -> Exp
replace e [] r = r
replace (App t1 t2) (x:xs) r | x ==1 = App t1 (replace t2 xs r)
                             | x ==0 = App (replace t1 xs r) t2

replace (Lambda t t2) (x:xs) r | x == 1 = Lambda t (replace t2 xs r)
                               | x == 0 = Lambda (replace t xs r) t2

replace (Case e alts) (x:xs) r | x == 0 = Case (replace e xs r) alts
                               | x == 1 =
                                   case xs of
                                     [] -> error "internal: wrong position for case"
                                     y:y':ys -> Case e $ replaceL y y' ys alts r

replaceL y y' ys [] r = error "internal: wrong position for case branch"
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
scopeCheck :: [Name] -> [(Name, Exp)] -> Bool
scopeCheck lvars sub = let (sub1, sub2) = partition (\(x, t) -> x `elem` lvars) sub
                           r1 = and [ null (rvars `intersect` b) | (x, t) <- sub1,
                                      let (a, b) = break (== x) lvars, let rvars = free' t]
--                           r2 = and [null r | (x, t) <- sub2, let r = free' t `intersect` lvars]
                       in r1 -- && r2


applyPhi :: [(Name, Exp)] -> [Phi] -> Either Doc [Phi]
applyPhi sub ls = let f = [(scopeCheck lvars sub, l) | l@(Phi p g e env lvars) <- ls]
                      ls' = map (\(Phi p g e env lvars) ->
                                    (Phi p (normalize $ apply (Subst sub) g) e
                                      (map (\ (x, t) -> (x, normalize $ apply (Subst sub) t))
                                       env)
                                     (lvars \\ map fst sub))) ls
                  in if and $ map fst f then Right ls'
                     else let (Phi p g e env lvars):as = [ l | (b, l) <- f, not b]
                              m = (nest 2 (text "environmental scope error when applying substitution") $$
                                   nest 2 ( text "[" <+> disp sub <+> text "]")) $$
                                  (nest 2 $ text "local variables list:" $$
                                   nest 2 (hsep $ map text lvars)) $$
                                  (nest 2 $ text "the local goal:" $$ nest 2 (disp g)) $$
                                  (nest 2 $ text "the local expression:" $$ nest 2 (disp e))
                          in Left m


arrange :: [((Pos, Exp), Exp)] -> ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
arrange ls =  partition helper ls
  where helper ((p,f),e) = let (vars, h, _) = separate f
                               fr = freeVars f
                           in null (fr `intersect` (freeVars h))

                              
transit :: ResState -> [ResState]
-- transit state | trace ("transit " ++show (state)) False = undefined
transit (Res pf ((Phi pos goal@(Imply _ _) exp@(Lambda _ _ ) gamma lvars):phi) Nothing i) =
  let (bs, h) = getHB goal
      (vars, b) = (viewLArgs exp, viewLBody exp)
      len = length vars
      lenB = length bs
  in
    if len > length bs then
      let vars' = take lenB vars
          b' = reLam (drop lenB vars) b
          (thetas, j) = makePatEnv vars' i
          newlvars = map snd $ concat thetas
          lvars' = lvars++(map (\ (Var x) -> x) newlvars)
          positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes lenB)
          pairs = zip (zip (zip positionsVars bs) vars') thetas
          newEnv = map (\ (((pos', g), pat), thetaP) -> (Phi pos' g pat (thetaP++gamma) lvars')) pairs
          boPos = pos++(take (lenB-1) stream1)++[1]
          newEnv' = newEnv ++ [(Phi boPos h b' (concat thetas ++ gamma) lvars')]
          newLam = foldr (\ a b -> Lambda a b) h bs
          pf' = replace pf pos newLam
      in [(Res pf' (newEnv' ++ phi) Nothing j)]
    else let (thetas, j) = makePatEnv vars i
             newlvars = map snd $ concat thetas
             lvars' = lvars++(map (\ (Var x) -> x) newlvars)
             h' = reImp (drop len bs) h  
             positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes len)
             pairs = zip (zip (zip positionsVars bs) vars) thetas
             newEnv = map (\ (((pos', g), pat), thetaP) -> (Phi pos' g pat (thetaP++gamma) lvars')) pairs
             boPos = pos++(take (len-1) stream1)++[1]
             newEnv' = newEnv ++ [(Phi boPos h' b (concat thetas ++ gamma) lvars')]
             newLam = foldr (\ a b -> Lambda a b) h' (take len bs)
             pf' = replace pf pos newLam
         in [(Res pf' (newEnv' ++ phi) Nothing j)]

transit (Res pf ((Phi pos goal exp@(Case e alts) gamma lvars):phi) Nothing i) =
  let
    pats = map fst alts
    brExps = map snd alts
    y = "y"++show i
    len = length alts
    (thetas, j) = makePatEnv pats (i+1)
    newlvars = y : map (\(Var x) -> x) (map snd $ concat thetas)
    lvars' = lvars++newlvars
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

-- there is a forall problem
transit (Res pf ((Phi pos goal@(Forall x y) exp gamma lvars):phi) Nothing i) 
  | not (isSingle $ head (flatten exp)) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      sub = zip vars (map Const absNames)
      imp' = apply (Subst sub) imp
      newAbs = foldr (\ a b -> Lambda (Var a) b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream1
  in [(Res pf' ((Phi pos' imp' exp gamma (lvars++ absNames)):phi) Nothing (i+lv))]


transit (Res pf ((Phi pos goal exp gamma lvars):phi) Nothing i) = 
  case flatten exp of
    (Var v) : xs -> handle v xs
    (Const v) : xs -> handle v xs
    a -> error $ "unhandle situation in transit " ++ show (disp exp)
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
              ss = runMatch newHead goal in
            case ss of
              [] ->
                let m' = Just $ text "can't match" <+> disp head'' $$
                         text "against" <+> disp goal $$
                         (nest 2 (text "when applying" <+>text v <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf))
                in [(Res pf ((Phi pos goal exp gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   let subFCheck = [(x, y)|(x, y) <- sub, not $ x `elem` fresh]
                   if scopeCheck lvars subFCheck
                     then let dom = freeVars newHead
                              body' = map normalize $ (map (apply (Subst sub)) (take n body''))
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              lvars' = (lvars \\ (map fst sub)) ++
                                       [ x | x <- fresh, not (x `elem` dom)]
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
                              (high', low') = (map (\((p, g),e ) -> (Phi p g e gamma' lvars')) high, map (\((p, g), e ) -> (Phi p g e gamma' lvars')) low)
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
                                            nest 2 (hsep $ map text lvars)) $$
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
                                      nest 2 (hsep $ map text lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]

          
        app1 fresh head'' body'' f v xs j i' =
          let glVars = map (\ i -> Var $ "y"++show i++"'") [i'..j-1]
              goal' = reImp glVars goal
              ss = runMatch head'' goal' in
            case ss of
              [] ->
                let m' = Just $ text "can't match" <+> disp head'' $$
                         text "against" <+> disp goal $$
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
                   let subFCheck = [(x, y)|(x, y) <- sub, not $ x `elem` fresh]
                   if scopeCheck lvars subFCheck
                     then let dom = freeVars head''
                              body' = map normalize $ (map (apply (Subst sub)) body'')
                              body1 = body' ++ (map (apply (Subst sub)) glVars)
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              lvars' = (lvars \\ (map fst sub)) ++
                                       [ x | x <- fresh, not (x `elem` dom)]
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
                              (high', low') = (map (\((p, g),e ) -> (Phi p g e gamma' lvars')) high, map (\((p, g), e ) -> (Phi p g e gamma' lvars')) low)
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
                                            nest 2 (hsep $ map text lvars)) $$
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
                                      nest 2 (hsep $ map text lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos goal exp gamma lvars):phi) (Just mess) i]

    
          
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
                      (Res pf _ _ _):_ -> Right pf
                             
  where failure (Res _ _ (Just _) _) = True
        failure _ = False
        success (Res pf [] Nothing i) = True
        success _ = False
