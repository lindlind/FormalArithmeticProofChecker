{
module Synt where
import Lex
}

%name parse Expr
%name parseFirstLine Task
%tokentype { Token }
%error { parseError }

%token
    ","                             { TComma }
    "|-"                            { TProve }
    "("                             { TOpenBracket }
    ")"                             { TCloseBracket }
    "->"                            { TImpl   }
    "|"                             { TOr     }
    "&"                             { TAnd    }
    "!"                             { TNot    }
    "."                             { TDot    }
    "@"                             { TForall }
    "?"                             { TExist  }
    "+"                             { TPlus   }
    "*"                             { TMul    }
    "="                             { TEq     }
    "'"                             { TInc    }
    "0"                             { TZero   }
    sVar                            { TsVar $$ }
    lVar                            { TlVar $$ }
%%

Task:
    Context "|-" Expr               { $3 : $1 }

Context:
                                    { [] }
    | Expr                          { [$1] }
    | Expr "," Context              { $1 : $3 }

Expr:
    Impl                            { $1 }

Impl:
    Disj                            { $1 }
    | Disj "->" Impl                { Impl $1 $3 }

Disj:
    Conj                            { $1 }
    | Disj "|" Conj                 { Or $1 $3 }

Conj:
    Unar                            { $1 }
    | Conj "&" Unar                 { And $1 $3 }

Unar:
    Pred                            { $1 }
    | "!" Unar                      { Not $2 }
    | "@" sVar "." Expr             { Forall (Var $2) $4 }
    | "?" sVar "." Expr             { Exist (Var $2) $4 }
    | "(" Expr ")"                  { $2 }

Pred:
    Term "=" Term                   { Equal $1 $3 }
    | lVar                          { Pred $1 [] }
    | lVar "(" Args ")"             { Pred $1 $3 }

Term:
    Mul                             { $1 }
    | Term "+" Mul                  { Add $1 $3 }

Mul:
    Num                             { $1 }
    | Mul "*" Num                   { Mul $1 $3 }

Num:
    "0"                             { Zero }
    | Num "'"                       { Inc $1 }
    | "(" Term ")"                  { $2 }
    | sVar                          { Var $1 }
    | sVar "(" Args ")"             { Func $1 $3 }

Args:
    Term                            { [$1] }
    | Term "," Args                 { $1 : $3 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Expr = Impl Expr Expr 
          | Or Expr Expr 
          | And Expr Expr 
          | Not Expr 
          | Forall Expr Expr
          | Exist Expr Expr
          | Equal Expr Expr
          | Add Expr Expr
          | Mul Expr Expr
          | Inc Expr
          | Zero
          | Pred String [Expr] 
          | Func String [Expr]
          | Var String deriving (Eq, Ord)

instance Show Expr where
    show (Impl a b)     = "(" ++ show a ++ "->" ++ show b ++ ")"
    show (Or a b)       = "(" ++ show a ++ "|" ++ show b ++ ")"
    show (And a b)      = "(" ++ show a ++ "&" ++ show b ++ ")"
    show (Not a)        = "!" ++ show a
    show (Forall a b)   = "(@" ++ show a ++ "." ++ show b ++ ")"
    show (Exist a b)    = "(?" ++ show a ++ "." ++ show b ++ ")"
    show (Equal a b)    = "(" ++ show a ++ "=" ++ show b ++ ")"
    show (Add a b)      = "(" ++ show a ++ "+" ++ show b ++ ")"
    show (Mul a b)      = "(" ++ show a ++ "*" ++ show b ++ ")"
    show (Inc a)        = show a ++ "'"
    show (Zero)         = "0"
    show (Pred a [])    = a
    show (Pred a b)     = a ++ "(" ++ hShow b ++ ")"
                        where 
                            hShow (s:[]) = show s
                            hShow (s:t) = show s ++ hShow t
    show (Func a b)     = a ++ "(" ++ hShow b ++ ")"
                        where 
                            hShow (s:[]) = show s
                            hShow (s:t) = show s ++ hShow t
    show (Var a)        = a
}