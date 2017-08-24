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

makeTyEnv :: [Decl] -> TyEnv
makeTyEnv [] = [] 
makeTyEnv ((DataDecl _ _ cons):xs) = [(d, e) | (Const d, e) <- cons] ++ makeTyEnv xs
makeTyEnv ((FunDecl (Var f) t _):xs) = (f, t):makeTyEnv xs
makeTyEnv ((Prim (Var f) t):xs) = (f, t):makeTyEnv xs

makeLam pats e = foldr (\ p e' -> Lambda p e') e pats

checkDecls :: [Decl] -> Either Doc [(Exp, Exp, Exp)]  
checkDecls a =
  let tyEnv = makeTyEnv a
      funcDefs = concat [map (\(pats, d) -> (t, makeLam pats d, f)) defs |
                          (FunDecl (Var f) t defs) <- a]
  in mapM (\ (t, e, f) ->
              do{e' <- typeCheck tyEnv (t, e);
                 return (Var f, t, e')
                })
     funcDefs

typeCheck :: TyEnv -> (Exp, Exp) -> Either Doc Exp 
typeCheck env (goal, e) =
  let phi = Phi [] (Just goal) (Just e) env []
      init = Res goal [phi] Nothing 0
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

separate f =
  let (vars, imp) = getVars f
      (bs, h) = getHB imp
  in (vars, h, bs)
                
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
      vars = map (\ n -> Var $ "y"++show n++"'") ns
  in (zip fvs vars, j+1)
    

makePatEnv :: [Exp] -> Int -> ([TyEnv], Int)
makePatEnv [] i = ([], i)
makePatEnv (x:xs) i =
  let (env, j) = patternVars x i
      (res, n) = makePatEnv xs j
  in (env:res, n)
    

makeLvars ((env, Var y, Var x, e):xs) n = (Var y, n):makeLvars xs n
makeLvars ((env, Var y, p, e):xs) n =
  let r = map (\(u, v) -> (v, n)) env
  in r ++ (Var y,n):makeLvars xs n
makeLvars ((env, t, Var x, e):xs) n = makeLvars xs n
makeLvars [] n = []


makePats ((t, Var x, e):xs) i =
  let (ps, j) = makePats xs i
  in (([(x, t)], t, Var x, e):ps, j)
    
makePats ((t, p, e):xs) i =
  let (env, j) = patternVars p i
      (ps, j') = makePats xs j
  in ((env, t, p, e):ps, j')
makePats [] i = ([], i)

annotate l = map ann l 
ann (Ann (Var x) t, e) = (Just t, (Var x), e)
ann (p, e) = (Nothing, p, e)


withVars ((Just t, (Var x), e):xs) i =
  let (ps, j) = withVars xs i
  in ((t, (Var x), e):ps, j)
withVars ((Nothing, p, e):xs) i =
  let (ps, j) = withVars xs (i+1)
  in ((Var $ "y"++show i++"'", p, e):ps, j)
withVars [] i = ([], i)

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
replace (App t1 t2) (x:xs) r
  | x ==1 = App t1 (replace t2 xs r)
  | x ==0 = App (replace t1 xs r) t2

replace (Lambda t t2) (x:xs) r
  | x == 1 = Lambda t (replace t2 xs r)
  | x == 0 =
      case t of
        Ann e ty -> Lambda (Ann (replace e xs r) ty) t2
        _ -> Lambda (replace t xs r) t2

replace (Case e alts) (x:xs) r
  | x == 0 = Case (replace e xs r) alts
  | x == 1 =
      case xs of
        [] -> error "internal: wrong position for case"
        y:y':ys -> Case e $ replaceL y y' ys alts r

replace (Let defs e) (x : xs) r
  | x == 1 = Let defs (replace e xs r)
  | x == 0 =
    case xs of
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

applyS :: [(Name, Exp)] -> [(Exp, Int)] -> [(Exp, Int)]
applyS sub l = applyS' sub l []
  where applyS' :: [(Name, Exp)] -> [(Exp, Int)] -> [(Exp, Int)] -> [(Exp, Int)]
        applyS' sub [] store = store           
        applyS' sub (((Const x), n):xs) store = ((Const x), n): applyS' sub xs store
        applyS' sub (((Var x), n):xs) store =
          case lookup x sub of
            Nothing -> applyS' sub xs (((Var x), n):store)
            Just e ->
              let fvs = freeVars e
                  (store', n') = updateS fvs store n
                  (xs', n'') = updateS fvs xs n'
              in applyS' sub xs' store'
        updateS fvs ((Const x, v):l) n =
          let (res, n') = updateS fvs l n
          in ((Const x, v):res, n')
        updateS fvs ((Var x, v):l) n =
          if x `elem` fvs
          then let n' = min n v
                   (res, n'') = updateS fvs l n'
               in ((Var x, n''):res, n'')
          else let (res, n'') = updateS fvs l n
               in ((Var x, v) : res, n'')
        updateS fvs [] n = ([], n)


scopeCheck :: [(Exp, Int)] -> [(Name, Exp)] -> Bool
scopeCheck lvars [] = True 
scopeCheck lvars ((x, e):xs) =
  case lookup (Var x) lvars of
    Nothing -> scopeCheck lvars xs
    Just n ->
      let evars = eigenVar e
      in checkEigen evars lvars n && scopeCheck lvars xs
  where checkEigen (y:ys) lvars n =
          case lookup (Const y) lvars of
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


arrange :: [((Pos, Exp), Exp)] -> ([((Pos, Exp), Exp)], [((Pos, Exp), Exp)])
arrange ls =  partition helper ls
  where helper ((p,(Var _)), (Lambda _ _)) = False
        helper _ = True

transit :: ResState -> [ResState]
--transit state | trace ("transit " ++show (state) ++"\n") False = undefined
transit (Res pf
          ((Phi pos
             (Just goal@(Forall x y))
             (Just exp@(Lambda _ _)) gamma lvars):phi)
          Nothing i) =
  let (vars, imp) = getVars goal
      lv = length vars
      absNames = zipWith (\ x y -> x ++ show y ++ "'") vars [i..]
      absNames' = map Const absNames
      absVars = zip absNames' [getValue lvars ..]
      sub = zip vars absNames'
      imp' = apply (Subst sub) imp
      newAbs = foldr (\ a b -> Lambda (Var a) b) imp' absNames
      pf' = replace pf pos newAbs
      pos' = pos ++ take lv stream1
  in [(Res pf'
       ((Phi pos'
          (Just imp')
          (Just exp)
          gamma
          (lvars++ absVars)):phi)
       Nothing (i+lv))]

transit (Res pf
          ((Phi pos
             (Just goal@(Imply _ _))
             (Just exp@(Lambda _ _ )) gamma lvars):phi)
          Nothing i) =
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
          indlvars = map (\ x -> (x, n)) newlvars
          lvars' = lvars++ indlvars
          positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes lenB)
          pairs = zip (zip (zip positionsVars bs) vars') thetas
          newEnv = map (\ (((pos', g), pat), thetaP) ->
                           (Phi pos'
                             (Just g)
                             (Just pat)
                             (thetaP++gamma) lvars'))
                   pairs
          boPos = pos++(take (lenB-1) stream1)++[1]
          newEnv' = newEnv ++
                    [(Phi boPos (Just h) (Just b') (concat thetas ++ gamma) lvars')]
          newLam = foldr (\ a b -> Lambda (Ann a a) b) h bs
          pf' = replace pf pos newLam
      in [(Res pf' (newEnv' ++ phi) Nothing j)]
    else let (thetas, j) = makePatEnv vars i
             newlvars = map snd $ concat thetas
             n' = getValue lvars
             indvars = map (\ x -> (x, n')) newlvars
             lvars' = lvars++indvars
             h' = reImp (drop len bs) h  
             positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes len)
             pairs = zip (zip (zip positionsVars bs) vars) thetas
             newEnv = map (\ (((pos', g), pat), thetaP) ->
                              (Phi pos'
                                (Just g)
                                (Just pat)
                                (thetaP++gamma) lvars'))
                      pairs
             boPos = pos++(take (len-1) stream1)++[1]
             newEnv' = newEnv ++
                       [(Phi boPos (Just h') (Just b) (concat thetas ++ gamma) lvars')]
             newLam = foldr (\ a b -> Lambda (Ann a a) b) h' (take len bs)
             pf' = replace pf pos newLam
         in [(Res pf' (newEnv' ++ phi) Nothing j)]

transit (Res pf
          ((Phi pos
             (Just goal)
             (Just exp@(Case e alts))
             gamma lvars):phi)
          Nothing i) =
  let pats = map fst alts
      brExps = map snd alts
      y = "y"++show i++"'"
      len = length alts
      n = getValue lvars
      (thetas, j) = makePatEnv pats (i+1)
      newlvars = (Var y, n) : map (\x -> (x, n)) (map snd $ concat thetas)
      lvars' = lvars++newlvars
      posLeft =  map (\ p -> pos++[1, p, 0]) [0..(len-1)]
      posRight = map (\ p -> pos++[1, p, 1]) [0..(len-1)]
      leftEnv = map (\(po, (p, th)) ->
                        (Phi po (Just (Var y))
                          (Just p) (th++gamma) lvars')) 
                (zip posLeft (zip pats thetas))
      rightEnv = map (\(po, (e', th)) ->
                         (Phi po (Just goal)
                           (Just e') (th++gamma) lvars')) 
                 (zip posRight (zip brExps thetas))
      altsEnv =  leftEnv ++ rightEnv
      newEnv = (Phi (pos++[0]) (Just (Var y)) (Just e) gamma lvars'):altsEnv
      newCase = Case (Var y) $ replicate len ((Var y), goal) 
      pf' = replace pf pos newCase
  in [(Res pf' (newEnv++phi) Nothing j)]

transit (Res pf
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
      rightEnv = map (\(po, (env, t, p, e)) ->
                         (Phi po (Just t) (Just e) (env++gamma) lvars'))
                 (zip posRight tps)
      defsEnv = leftEnv ++ rightEnv
      thetas = concat $ map (\ (a,b,c,d) -> a) tps
      newEnv = defsEnv ++
               [(Phi (pos++[1]) (Just goal) (Just e) (thetas ++gamma) lvars')]
      newLet = Let (map (\ (a,b,c,d) -> (b, b)) tps) goal 
      pf' = replace pf pos newLet
  in [(Res pf' (newEnv++phi) Nothing j')]
      
transit (Res pf
          ((Phi pos
             (Just goal@(Forall x y))
             (Just exp) gamma lvars):phi)
          Nothing i)
  | isAtom exp =
      let y = getName exp
      in case lookup y gamma of
        Nothing ->
          let m' = Just $ text "can't find" <+> text y
                   <+> text "in the environment" 
          in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
        Just f ->
          let ss = runMatch f goal in
            case ss of
              [] ->
                let m' = Just $ text "can't match" <+> disp f $$
                         text "against" <+> disp goal $$
                         (nest 2 (text "when applying" <+>text y <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf))
                in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   if scopeCheck lvars sub then
                     let lvars' = applyS sub lvars
                         gamma' = map (\ (x, t) ->
                                          (x, normalize $ apply (Subst sub) t) )
                                  gamma
                         pf' = normalize $ apply (Subst sub) pf
                         pf'' = replace pf' pos exp
                     in 
                       case applyPhi sub phi of 
                         Right p ->
                           return (Res pf''
                                    (p++[Phi pos Nothing Nothing gamma' lvars'])
                                    Nothing i)
                         Left m' ->
                           let mess =
                                 (text "globally, when matching" <+> disp f) $$
                                 (text "against"<+> disp (goal)) $$
                                 (nest 2 (text "when applying" <+> text y
                                           <+> text ":" <+> disp f)) $$
                                 (nest 2 (text "when applying substitution"
                                           <+> text "[" <+> disp sub <+> text "]")) $$
                                 (nest 2 $ text "current variables list:" $$
                                  nest 2 (hsep $ map (\(x,i) ->
                                                         parens $ disp x <+> comma <+> int i)
                                           lvars)) $$
                                 (nest 2 $ text "the current mixed proof term:" $$
                                   nest 2 (disp pf))
                               m1 = m' $$ nest 2 mess
                           in [Res pf
                                ((Phi pos
                                   (Just goal)
                                   (Just exp) gamma lvars):phi)
                                (Just m1) i]                         
                             
                     else
                     let mess = text "scope error when matching" <+> disp f $$
                                text "against"<+> disp (goal)$$
                                (nest 2 (text "when applying" <+> text y <+> text ":"
                                          <+> disp f)) $$
                                (nest 2 (text "when applying substitution" <+> text "["
                                          <+> disp sub <+> text "]")) $$
                                (nest 2 $ text "current variables list:" $$
                                  nest 2 (hsep $ map (\(x,i) ->
                                                         parens $ disp x <+> comma <+> int i)
                                           lvars)) $$
                                 (nest 2 $ text "the current mixed proof term:" $$
                                   nest 2 (disp pf))
                      in [Res pf
                           ((Phi pos
                              (Just goal)
                              (Just exp) gamma lvars):phi)
                           (Just mess) i]

transit (Res pf
         ((Phi pos
            (Just goal)
            (Just exp) gamma lvars):phi)
          Nothing i)
  | isAtom exp =
    let z = getName exp
    in 
    case lookup z gamma of
       Nothing ->
         let m' = Just $ text "can't find" <+> text z
               <+> text "in the environment" 
         in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
       Just f ->
         let (vars, imp) = getVars f
             fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
             fresh' = map Var fresh
             renaming = zip vars fresh'
             imp' = apply (Subst renaming) imp
             i' = i + length vars
             ss = runMatch imp' goal
         in case ss of
              [] ->
                let m' = Just $ text "can't match" <+> disp imp' $$
                         text "against" <+> disp goal $$
                         (nest 2 (text "when applying" <+>text z <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                          nest 2 (disp pf))
                in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
              _ ->
                do Subst sub' <- ss
                   if scopeCheck lvars sub'
                     then
                     let pf' = normalize $ apply (Subst sub') pf
                         np = ([ s | r <- fresh,
                                      let s = case lookup r sub' of
                                                Nothing -> (Var r)
                                                Just t -> t])
                         contm = foldl' (\ z x -> App z x) exp np     
                         pf'' = replace pf' pos contm
                         n = getValue lvars
                         freshlvars = map (\ x -> (x, n)) fresh'
                         gamma' = map (\ (x, t) -> (x, normalize $ apply (Subst sub') t)) gamma
                         lvars' = applyS sub' (lvars++freshlvars)
                         phi' = applyPhi sub' phi 
                     in case phi' of
                          Right p ->
                            return (Res pf''
                                     (p++[Phi pos Nothing Nothing gamma' lvars'])
                                     Nothing i')
                          Left m' ->
                            let mess =
                                  (text "globally, when matching" <+> disp imp') $$
                                  (text "against"<+> disp (goal)) $$
                                  (nest 2 (text "when applying" <+> text z
                                            <+> text ":" <+> disp f)) $$
                                  (nest 2 (text "when applying substitution"
                                            <+> text "[" <+> disp sub' <+> text "]")) $$
                                  (nest 2 $ text "current variables list:" $$
                                    nest 2 (hsep $ map (\(x,i) ->
                                                           parens $ disp x <+> comma <+> int i)
                                             lvars)) $$
                                  (nest 2 $ text "the current mixed proof term:" $$
                                    nest 2 (disp pf))
                                m1 = m' $$ nest 2 mess 
                            in [Res pf
                                 ((Phi pos (Just goal)
                                    (Just exp) gamma lvars):phi)
                                 (Just m1) i]
                     else
                     let mess = text "scope error when matching" <+> disp (imp') $$
                                text "against"<+> disp (goal)$$
                                (nest 2 (text "when applying" <+> text z <+> text ":"
                                          <+> disp f)) $$
                                (nest 2 (text "when applying substitution" <+> text "["
                                         <+> disp sub' <+> text "]")) $$
                                (nest 2 $ text "current variables list:" $$
                                  nest 2 (hsep $ map (\(x,i) ->
                                                         parens $ disp x <+> comma <+> int i)
                                           lvars)) $$
                                (nest 2 $ text "the current mixed proof term:" $$
                                  nest 2 (disp pf))
                     in [Res pf
                          ((Phi pos (Just goal)
                             (Just exp) gamma lvars):phi)
                          (Just mess) i]


transit (Res pf
          ((Phi pos
             (Just goal)
             (Just exp) gamma lvars):phi)
          Nothing i) = 
  case flatten exp of
    (Var v) : xs -> handle v xs
    (Const v) : xs -> handle v xs
    a ->
      let m' = Just $ (text "need more information to check expression:" <+> disp exp) $$
               (text "current goal: " <+> disp goal) $$
               (nest 2 $ text "current mixed proof term" $$
                 nest 2 (disp pf)) $$
               (nest 2 $ text "current env" $$
                 nest 2 (disp gamma)) 
      in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]

  where handle v xs =
          case lookup v gamma of
            Nothing -> let m' = Just $ text "can't find" <+> text v
                                <+> text "in the environment" in
                         [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
            Just f -> let (vars, head, body) = separate f
                          i' = i + length vars
                          fresh = map (\ (v, j) -> v ++ show j ++ "'") $ zip vars [i..]
                          renaming = zip vars (map Var fresh)
                          body'' = map (apply (Subst renaming)) body
                          head'' = apply (Subst renaming) head
                          n = length xs
                          l = length body
                      in
                        if l <= n then let j = i' + (n-l) in
                                         app1 fresh head'' body'' f v xs j i' 
                        else if n < l then
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
                               in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]

        app2 fresh head'' body'' f v xs i' n =
          let newHead = reImp (drop n body'') head''
              ss = runMatch newHead goal in
            case ss of
              [] ->
                let m' = Just $ text "from app2, can't match" <+> disp newHead $$
                         text "against" <+> disp goal $$
                         (nest 2 (text "when applying" <+>text v <+> text ":"
                                   <+> disp f)) $$
                         (nest 2 $ text "current mixed proof term" $$
                           nest 2 (disp pf))
                in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   if scopeCheck lvars sub
                     then let dom = map fst sub -- freeVars newHead
                              body' = map normalize $ (map (apply (Subst sub)) (take n body''))
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              va = getValue lvars
                              lvars' = applyS sub $ lvars ++ map (\ x -> (Var x, va)) fresh
                              name = if isUpper $ Data.List.head v
                                     then Const v else Var v
                              contm = foldl' (\ z x -> App z x)
                                      (foldl' (\ z x -> App z x) name np)
                                      body'
                              pf' = normalize $ apply (Subst sub) pf
                              pf'' = replace pf' pos contm
                              zeros = makeZeros $ length body'
                              ps = map (\ x -> pos++x++[1]) zeros
                              gamma' = map
                                       (\(x, y) ->
                                          (x, normalize $ apply (Subst sub) y))
                                       gamma
                              (high, low) = arrange $ zip (zip ps body') xs
                              (high', low') = (map (\((p, g),e ) -> (Phi p (Just g) (Just e) gamma' lvars')) high, map (\((p, g),e ) -> (Phi p (Just g) (Just e) gamma' lvars')) low) 
                              phi' = applyPhi sub phi in
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
                                            nest 2 (hsep $ map (\(x,i) -> parens $ disp x <+> comma <+> int i) lvars)) $$
                                           (nest 2 $ text "the current mixed proof term:" $$
                                            nest 2 (disp pf))
                                           
                                    m1 = m' $$ nest 2 mess in
                                  [Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) (Just m1) i]
                     else let mess = text "scope error when matching" <+> disp (newHead) $$
                                     text "against"<+> disp (goal)$$
                                     (nest 2 (text "when applying" <+> text v <+> text ":"
                                               <+> disp f)) $$
                                     (nest 2 (text "when applying substitution" <+> text "["
                                               <+> disp sub <+> text "]")) $$
                                     (nest 2 $ text "current variables list:" $$
                                      nest 2 (hsep $ map (\(x,i) -> parens $ disp x <+> comma <+> int i) lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) (Just mess) i]

          
        app1 fresh head'' body'' f v xs j i' =
          let glVars = map (\ i -> Var $ "y"++show i++"'") [i'..j-1]
              goal' = reImp glVars goal
              ss = runMatch head'' goal' in
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
                in [(Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) m' i)]
              _ ->
                do Subst sub <- ss
                   if scopeCheck lvars sub
                     then let dom = map fst sub -- freeVars head''
                              body' = map normalize $ (map (apply (Subst sub)) body'')
                              body1 = body' ++ (map (apply (Subst sub)) glVars)
                              np = ([ s | r <- fresh,
                                      let s = case lookup r sub of
                                                Nothing -> (Var r)
                                                Just t -> t])
                              va = getValue lvars     
                              lvars' = applyS sub $ lvars ++ (map (\ x -> (Var x, va)) fresh) ++ map (\x -> (x, va)) glVars
                              name = if isUpper $ Data.List.head v
                                     then Const v else Var v
                              contm = foldl' (\ z x -> App z x)
                                      (foldl' (\ z x -> App z x) name np)
                                      body1
                              pf' = normalize $ apply (Subst sub) pf
                              pf'' = replace pf' pos contm
                              zeros = makeZeros $ length body1
                              ps = map (\ x -> pos++x++[1]) zeros
                              gamma' = map
                                       (\(x, y) ->
                                          (x, normalize $ apply (Subst sub) y))
                                       gamma
                              (high, low) = arrange $ zip (zip ps body1) xs
                              (high', low') = (map (\((p, g),e ) -> (Phi p (Just g) (Just e) gamma' lvars')) high, map (\((p, g),e ) -> (Phi p (Just g) (Just e) gamma' lvars')) low) 
                              phi' = applyPhi sub phi in
                            case phi' of
                              Right p ->
                                return $ Res pf'' (high'++low'++p) Nothing j
                              Left m' ->
                                let mess = text "globally, when matching" <+> disp (head'') $$
                                           text "against"<+> disp (goal')$$
                                           (nest 2 (text "when applying" <+> text v
                                                    <+> text ":" <+> disp f)) $$
                                           (nest 2 (text "when applying substitution"
                                                    <+> text "[" <+> disp sub <+> text "]")) $$
                                           (nest 2 $ text "current variables list:" $$
                                            nest 2 (hsep $ map (\(x,i) -> parens $ disp x <+> comma <+> int i) lvars)) $$
                                           (nest 2 $ text "the current mixed proof term:" $$
                                            nest 2 (disp pf))
                                           
                                    m1 = m' $$ nest 2 mess in
                                  [Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) (Just m1) i]

                     else let mess = text "scope error when matching" <+> disp (head'') $$
                                     text "against"<+> disp (goal')$$
                                     (nest 2 (text "when applying" <+> text v <+> text ":"
                                               <+> disp f)) $$
                                     (nest 2 (text "when applying substitution" <+> text "["
                                               <+> disp sub <+> text "]")) $$
                                     (nest 2 $ text "current variables list:" $$
                                      nest 2 (hsep $ map (\(x,i) -> parens $ disp x <+> comma <+> int i) lvars)) $$
                                     (nest 2 $ text "the current mixed proof term:" $$
                                      nest 2 (disp pf))
                                                    
                          in [Res pf ((Phi pos (Just goal) (Just exp) gamma lvars):phi) (Just mess) i]

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
        success (Res pf phi Nothing i) = and $ map (\p -> currentGoal p == Nothing && currentProg p == Nothing) phi 
        success _ = False
