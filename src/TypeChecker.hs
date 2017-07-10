module TypeChecker where

import Syntax
import Pretty
import Matching

type KindDef = [(Name, Exp)]

-- Well-formed kinds
wfKind :: Exp -> Bool
wfKind Star = True
wfKind (Imply x y) = wfKind x && wfKind y



