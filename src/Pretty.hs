{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Pretty where
import Syntax
-- import Cegt.Rewrite
import Text.PrettyPrint
import Text.Parsec.Pos
import Data.Char
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)
-- import Debug.Trace
class Disp d where
  disp :: d -> Doc
  precedence :: d -> Int
  precedence _ = 0
  
instance Disp Doc where
  disp = id

instance Disp String where
  disp x = if (isUpper $ head x) || (isLower $ head x)
           then text x
           else if head x == '`'
                then text x
                else parens $ text x

instance Disp Int where
  disp = integer . toInteger

dParen:: (Disp a) => Int -> a -> Doc
dParen level x =
   if level >= (precedence x)
   then parens $ disp x 
   else disp x

viewLArgs :: Exp -> [Exp]
viewLArgs (Lambda n a) =
  n : viewLArgs a
viewLArgs _ = []


viewLBody :: Exp -> Exp
viewLBody (Lambda _ a) = viewLBody a
viewLBody x = x


viewFVars :: Exp -> [Name]
viewFVars (Forall n a) =
  n : viewFVars a
viewFVars (Abs n a) =
  n : viewFVars a
viewFVars _ = []


viewFBody :: Exp -> Exp
viewFBody (Forall _ a) = viewFBody a
viewFBody (Abs _ a) = viewFBody a
viewFBody x = x

instance Disp (Maybe Exp) where
  disp Nothing = text "<>"
  disp (Just e) = disp e

instance Disp Exp where
--  disp r | trace ("disp " ++ show r) False = undefined
  disp (Const x) | isUpper (head x) = disp x
                 | otherwise = brackets $ disp x
  disp Star = text "*"
  disp (Var x) = disp x
--  disp (Ann (Var x) Nothing) = disp x
  disp (Ann e t) = parens $ disp e <+> text "::" $$ (nest 5 $ disp t)
--  disp (Ann e t) = parens $ disp x <+> text "::" <+>disp t
  disp (s@(App s1 s2)) =
    sep [dParen (precedence s - 1) s1,  
         nest 2 $ dParen (precedence s) s2]

  disp (s@(TApp s1 s2)) =
    sep [dParen (precedence s - 1) s1,   
         nest 2 $ text "@"<>dParen (precedence s) s2]

  disp a@(Lambda x t) =
    let vars = viewLArgs a
        b = viewLBody a
        ds = map helper vars 
    in sep [text "\\" <+> sep ds <+> text ".", nest 4 $ disp b]
    where helper a@(App _ _ ) = parens $ disp a
          helper a = disp a


  disp (a@(Forall x f)) =
    let vars = map disp $ viewFVars a
        b = viewFBody a in
    sep [text "forall" <+> sep vars <+> text ".", nest 2 $ disp b]

  disp (a@(Abs x f)) =
    let vars = map disp $ viewFVars a
        b = viewFBody a in
    sep [text "\\\\" <+> sep vars <+> text ".", nest 2 $ disp b]


  disp (a@(Imply t1 t2)) =
   sep [dParen (precedence a) t1,
        text "->",
        nest 2 $ dParen (precedence a - 1) t2]

  disp (a@(Case e alts)) =
    text "case" <+> disp e <+> text "of" $$ nest 2 (vcat (map dAlt alts))
    where dAlt (p, e) =fsep [disp p <+> text "->", nest 2 $ disp e]

  disp (a@(Let ds e)) =
    text "let" <+> helper ds <+> text "in" $$ nest 2 (disp e)
    where helper ds = vcat (map (\ (n, exp) -> disp n <+> text "=" $$ nest 2 (disp exp)) ds)
  precedence (Imply _ _) = 4
  precedence (Var _) = 12
  precedence (Star) = 12
  precedence (Const _) = 12
  precedence (App _ _) = 10
  precedence (TApp _ _) = 10
  precedence _ = 0


instance Disp Subst where
  disp (Subst sub) = disp sub
  
instance Disp [(Exp, Exp)] where
  disp decl =  vcat (map (\ (n, exp) -> disp n <+> text "::" <+> disp exp) decl)

instance Disp [(String, Exp)] where
  disp decl = brackets $ vcat (map (\ (n, exp) -> text n <+> text "|->" <+> disp exp) decl)
  -- disp $ map (\(x, e) -> (Var x , e)) decl

instance Disp ([Exp], Exp) where
  disp (pats, e) = (sep $ map helper pats) <+> text "=" <+> disp e
    where helper a@(App _ _ ) = parens $ disp a
          helper a = disp a

instance Disp Decl where
  disp (DataDecl n k cons) =
    text "data" <+> disp n <+> text "::" <+> disp k <+> text "where" $$
    nest 2 (disp cons) <+> text "\n"

  disp (FunDecl f t defs) =
    disp f <+> text "::" <+> disp t $$
    (vcat $ map (\ x -> disp f <+> disp x) defs) <+> text "\n"
  disp (Prim f t) =
    text "primitive" <+> disp f <+> text "::" <+> disp t

  disp (Syn f k t) =
    text "type" <+> disp f <+> text "::" <+> disp k <+> text "=" <+> disp t

instance Disp [Decl] where
  disp ls = vcat $ map disp ls
  
instance Disp SourcePos where
  disp sp =  text (sourceName sp) <> colon <> int (sourceLine sp)
             <> colon <> int (sourceColumn sp) <> colon

instance Disp ParseError where
 disp pe = (disp (errorPos pe)) $$
           (text "Parse Error:" $$ sem)
  where sem = text $ showErrorMessages "or" "unknown parse error"
              "expecting" "unexpected" "end of input"
              (errorMessages pe)



printTyped pfs = vcat (map (\(f,t,e) -> disp f <+> text "::" <+>
                                        disp t <+> text "=" $$
                                        nest 2 (disp e) <+> text "\n")
                       pfs)
