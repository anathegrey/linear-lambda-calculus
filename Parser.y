{
module Parser where
import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data
}

%name parse1 Env
%name parse2 Term
%name parse3 Store


%tokentype { Token }
%error { parseError }

%token
      "lin"     { TokenLin }
      "un"      { TokenUn }
      "Bool"    { TokenStringBool }
      bool      { TokenBool $$ }
      '\\'      { TokenLambda }
      "->"      { TokenArrow }
      '*'       { TokenPair }
      '<'       { TokenLess }
      '>'       { TokenBigger }
      '.'       { TokenDot }
      ':'       { TokenColon }
      ','       { TokenComma }
      '('       { TokenOBrack }
      ')'       { TokenCBrack }
      '|'       { TokenOr}
      '+'       { TokenSum }
      "=>"      { TokenImplies }
      if        { TokenIf }
      then      { TokenThen }
      else      { TokenElse }
      split     { TokenSplit }
      as        { TokenAs }
      in        { TokenIn }
      inl       { TokenInl }
      inr       { TokenInr }
      case      { TokenCase }
      of        { TokenOf }
      roll      { TokenRoll }
      unroll    { TokenUnroll }
      fun       { TokenFun }
      rec       { TokenRec }
      var       { TokenVar $$ }

%%
Env : {- empty -} { [] }
    | Env ',' E1 { $3 : $1 }
    | E1 { [$1] }

E1 : var ':' Type { ($1, $3) }

Store : {- empty -} { [] }
       | Store ',' S { $3 : $1 }
       | S { [$1] }

S : var ':' Values { ($1, $3) }

Term : Term1 { $1 }
     | TermBool { $1 }

Term1 : var { Var $1 }
     | if TermBool then Term else Term { If $2 $4 $6 }
     | Qual '<' Term ',' Term '>' { Pair $1 $3 $5 }
     | split Term as var ',' var in Term { Split $2 $4 $6 $8 }
     | Qual '\\' var ':' Type '.' Term { Lambda $1 $3 $5 $7 }
     | '(' Term ')' '(' Term ')' { App $2 $5 }
     | '(' Term ')' { $2 }
     | Qual inl ':' PreType Term { SumLeft $1 $4 $5 }
     | Qual inr ':' PreType Term { SumRight $1 $4 $5}
     | case Term of '(' inl var "=>" Term '|' inr var "=>" Term ')' { Case $2 $6 $8 $11 $13 }
     | roll ':' PreType Term { Roll $3 $4 }
     | unroll Term { Unroll $2 }
     | fun var '(' var ':' Type ')' ':' Type Term { Fun $2 $4 $6 $9 $10 }

Qual : "lin" { LIN }
     | "un" { UN }

TermBool : Qual bool { B $1 $2 }

Type : Type1 { $1 }

Type1 : '(' Type ')' { $2 }
      | Qual PreType { Pre $1 $2 }

PreType : "Bool" { TBool }
        | Type "->" Type1 { Arrow $1 $3 }
        | Type '*' Type1 { TypePair $1 $3 }
        | Type '+' Type1 { Plus $1 $3 }
        | rec PreType '.' Type { Rec $2 $4 }
        | var { TVar $1 }
        | '(' PreType ')' { $2 }

Values : Qual PreValues { QValue $1 $2 }

PreValues : bool { RB $1 }
          | '<' var ',' var '>' { RPair $2 $4 }
          | '\\' var ':' Type '.' Term { RLambda $2 $4 $6 }
          | inl ':' PreType var { RSumLeft $3 $4 }
          | inr ':' PreType var { RSumRight $3 $4 }

{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenVar String
      | TokenLin
      | TokenUn
      | TokenBool Bool
      | TokenStringBool
      | TokenArrow
      | TokenLambda
      | TokenPair
      | TokenLess
      | TokenBigger
      | TokenDot
      | TokenColon
      | TokenComma
      | TokenOBrack
      | TokenCBrack
      | TokenIf
      | TokenThen
      | TokenElse
      | TokenSplit
      | TokenAs
      | TokenIn
      | TokenOr
      | TokenCase
      | TokenSum
      | TokenInl
      | TokenInr
      | TokenImplies
      | TokenOf
      | TokenRoll
      | TokenUnroll
      | TokenFun
      | TokenRec
      deriving (Show, Eq)

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
lexer ('\\':cs) = TokenLambda : lexer cs
lexer ('-':'>':cs) = TokenArrow : lexer cs
lexer ('*':cs) = TokenPair : lexer cs
lexer ('<':cs) = TokenLess : lexer cs
lexer ('>':cs) = TokenBigger : lexer cs
lexer ('.':cs) = TokenDot : lexer cs
lexer (':':cs) = TokenColon : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer ('(':cs) = TokenOBrack : lexer cs
lexer (')':cs) = TokenCBrack : lexer cs
lexer ('+':cs) = TokenSum : lexer cs
lexer ('|':cs) = TokenOr : lexer cs
lexer ('=':'>':cs) = TokenImplies : lexer cs

lexVar :: String -> [Token]
lexVar cs =
   case span (\x -> (isAlpha x) || (isDigit x)) cs of
      ("if", rest)   -> TokenIf : lexer rest
      ("then", rest) -> TokenThen : lexer rest
      ("else", rest) -> TokenElse : lexer rest
      ("split", rest) -> TokenSplit : lexer rest
      ("as", rest) -> TokenAs : lexer rest
      ("in", rest) -> TokenIn : lexer rest
      ("Bool", rest) -> TokenStringBool : lexer rest
      ("lin", rest) -> TokenLin : lexer rest
      ("un", rest) -> TokenUn : lexer rest
      ("inl", rest) -> TokenInl : lexer rest
      ("inr", rest) -> TokenInr : lexer rest
      ("case", rest) -> TokenCase : lexer rest
      ("of", rest) -> TokenOf : lexer rest
      ("roll", rest) -> TokenRoll : lexer rest
      ("unroll", rest) -> TokenUnroll : lexer rest
      ("fun", rest) -> TokenFun : lexer rest
      ("rec", rest) -> TokenRec : lexer rest
      ("True", rest) -> TokenBool True : lexer rest
      ("False", rest) -> TokenBool False : lexer rest
      (var, rest) -> TokenVar var : lexer rest

parseEnv :: String -> Env
parseEnv env = parse1(lexer env)

parseTerm :: String -> Term
parseTerm term = parse2(lexer term)

parsePrimStore :: [(String, Values)] -> Store
parsePrimStore [] = Map.empty
parsePrimStore l = Map.fromList l

parseStore :: String -> Store
parseStore store = parsePrimStore $ parse3 (lexer store)

}
