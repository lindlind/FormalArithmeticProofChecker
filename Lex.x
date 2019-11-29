{
module Lex where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-z]
$Alpha = [A-Z]

tokens :-
    $white                      ;
    ","                         { \s -> TComma }
    "|-"                        { \s -> TProve }
    "("                         { \s -> TOpenBracket }
    ")"                         { \s -> TCloseBracket }
    "->"                        { \s -> TImpl   }
    "|"                         { \s -> TOr     }
    "&"                         { \s -> TAnd    }
    "!"                         { \s -> TNot    }
    "."                         { \s -> TDot    }
    "@"                         { \s -> TForall }
    "?"                         { \s -> TExist  }
    "+"                         { \s -> TPlus   }
    "*"                         { \s -> TMul    }
    "="                         { \s -> TEq     }
    "'"                         { \s -> TInc    }
    "0"                         { \s -> TZero   }
    $alpha [$digit]*            { \s -> TsVar s }
    $Alpha [$digit]*            { \s -> TlVar s }

{
data Token = TComma | TProve | TOpenBracket | TCloseBracket | TImpl | TOr | TAnd | TNot | TDot | TForall | TExist | TPlus | TMul | TEq | TInc | TZero | TsVar String | TlVar String deriving (Eq, Show)
}