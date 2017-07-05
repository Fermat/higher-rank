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

viewLArgs :: Exp -> [(Exp, Maybe Exp)]
viewLArgs (Lambda n t a) =
  (n, t) : viewLArgs a
viewLArgs _ = []


viewLBody :: Exp -> Exp
viewLBody (Lambda _ _ a) = viewLBody a
viewLBody x = x


viewFVars :: Exp -> [Name]
viewFVars (Forall n a) =
  n : viewFVars a
viewFVars _ = []


viewFBody :: Exp -> Exp
viewFBody (Forall _ a) = viewFBody a
viewFBody x = x


instance Disp Exp where
--  disp r | trace ("disp " ++ show r) False = undefined
  disp (Const x) | isUpper (head x) = disp x
                 | otherwise = brackets $ disp x
  disp Star = text "*"
  disp (Var x) = disp x
  disp (s@(App s1 s2)) =
    sep [dParen (precedence s - 1) s1,  
         nest 2 $ dParen (precedence s) s2]

  disp a@(Lambda x t' t) =
    let vars = viewLArgs a
        b = viewLBody a
        ds = map (\ (x, k) ->
                   case k of
                     Nothing -> nest 2 $ helper x
                     Just k' ->
                       nest 2 $ text "(" <> disp x <+> text ":"
                       <+> disp k' <> text ")") vars
    in sep [text "\\" <+> sep ds <+> text "->", nest 4 $ disp b]
    where helper a@(App _ _ ) = parens $ disp a
          helper a = disp a


  disp (a@(Forall x f)) =
    let vars = map disp $ viewFVars a
        b = viewFBody a in
    sep [text "forall" <+> sep vars <+> text ".", nest 2 $ disp b]


  disp (a@(Imply t1 t2)) =
   sep [dParen (precedence a) t1,
        text "->",
        nest 2 $ dParen (precedence a - 1) t2]

  disp (a@(Case e _ alts)) =
    text "case" <+> disp e <+> text "of" $$ nest 2 (vcat (map dAlt alts))
    where dAlt (p, e) =fsep [disp p <+> text "->", nest 2 $ disp e]

  disp (a@(Let ds e)) =
    text "let" <+> helper ds <+> text "in" $$ nest 2 (disp e)
    where helper ds = vcat (map (\ (n, exp) -> disp n <+> text "=" <+> disp exp) ds)
  precedence (Imply _ _) = 4
  precedence (Var _) = 12
  precedence (Star) = 12
  precedence (Const _) = 12
  precedence (App _ _) = 10
  precedence _ = 0


instance Disp [(Exp, Exp)] where
  disp decl = vcat (map (\ (n, exp) -> disp n <+> text "::" <+> disp exp) decl)

instance Disp [(String, Exp)] where
  disp decl = disp $ map (\(x, e) -> (Var x , e)) decl

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