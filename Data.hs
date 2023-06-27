module Data where
  import Data.Map (Map)
  import qualified Data.Map as Map

  data Q = LIN
         | UN
         deriving (Show, Eq)
  instance Ord Q where
    LIN <= LIN = True
    UN  <= UN  = True
    LIN <= UN  = True
    _   <= _   = False

  type V = String

  data Term = Var V
            | B Q Bool
            | If Term Term Term
            | Pair Q Term Term
            | Split Term V V Term   -- split t as x,y in t
            | Lambda Q V Type Term  -- q \x:T.t
            | App Term Term
            | SumLeft Q PreType Term  -- q inl_p t
            | SumRight Q PreType Term -- q inr_p t
            | Case Term V Term V Term -- case t (inl x => t | inr y => t)
            | Roll PreType Term
            | Unroll Term
            | Fun V V Type Type Term
            deriving (Show, Eq)

  data PreType = TBool
               | TypePair Type Type  -- T * T
               | Arrow Type Type     -- T -> T
               | Plus Type Type
               | TVar String
               | Rec PreType Type
               deriving (Show, Eq)


  data Type = Pre Q PreType
            deriving (Show, Eq)

  type Env = [(V, Type)]
  data PreValues = RB Bool
                 | RPair V V
                 | RLambda V Type Term
                 | RSumLeft PreType V
                 | RSumRight PreType V
                 | RRoll PreType V
                 deriving (Show, Eq)

  data Values = QValue Q PreValues
              deriving (Show, Eq)

  type Store = Map V Values
