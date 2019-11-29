module Main where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO
import Data.List
import Data.Tuple
import Lex
import Synt

type FreeVarsSet = Set.Set String
type LockedVarsSet = Set.Set String
type ContextSet = Set.Set Expr
type ProofSet = Set.Set Expr
type MPMap = Map.Map Expr [Expr]

checkAxiom :: Expr -> Int
checkAxiom (Impl a1 (Impl b2 a2)) 
    | a1 == a2 
        = 1
checkAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Impl b2 c2)) (Impl a3 c3))) 
    | a1 == a2 && a2 == a3 && b1 == b2 && c2 == c3
        = 2
checkAxiom (Impl a1 (Impl b1 (And a2 b2)))
    | a1 == a2 && b1 == b2
        = 3
checkAxiom (Impl (And a1 b1) a2)
    | a1 == a2
        = 4
checkAxiom (Impl (And a1 b1) b2)
    | b1 == b2
        = 5
checkAxiom (Impl a1 (Or a2 b2))
    | a1 == a2
        = 6
checkAxiom (Impl b1 (Or a2 b2))
    | b1 == b2
        = 7
checkAxiom (Impl (Impl a1 c1) (Impl (Impl b2 c2) (Impl (Or a3 b3) c3)))
    | c1 == c2 && c2 == c3 && a1 == a3 && b2 == b3
        = 8
checkAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Not b2)) (Not a3)))
    | a1 == a2 && a2 == a3 && b1 == b2
        = 9
checkAxiom (Impl (Not (Not a1)) a2)
    | a1 == a2
        = 10
checkAxiom (Impl a b)
    |  a == (Equal (Var "a") (Var "b")) 
    && b == (Equal (Inc (Var "a")) (Inc (Var "b")))
        = 13
checkAxiom (Impl a (Impl b c))
    |  a == (Equal (Var "a") (Var "b"))
    && b == (Equal (Var "a") (Var "c"))
    && c == (Equal (Var "b") (Var "c"))
        = 14
checkAxiom (Impl a b)
    |  b == (Equal (Var "a") (Var "b")) 
    && a == (Equal (Inc (Var "a")) (Inc (Var "b")))
        = 15
checkAxiom (Not (Equal (Inc (Var "a")) (Zero)))
        = 16
checkAxiom (Equal (Add (Var "a") (Inc (Var "b"))) (Inc (Add (Var "a") (Var "b"))))
        = 17
checkAxiom (Equal (Add (Var "a") (Zero)) (Var "a"))
        = 18
checkAxiom (Equal (Mul (Var "a") (Zero)) (Zero))
        = 19
checkAxiom (Equal a b)
    |  a == (Mul (Var "a") (Inc (Var "b")))
    && b == (Add (Mul (Var "a") (Var "b")) (Var "a"))
        = 20
checkAxiom (Impl (And a1 (Forall (Var x) (Impl a2 a3))) a)
    | a == a2 && Set.member x (freeVars a)
    && a1 == subst a x (Zero)
    && a3 == subst a x (Inc (Var x))
        = 21  
checkAxiom (Impl (Forall (Var x) a1) a2) 
    | canConstructBySubst a1 x a2
        = 11
checkAxiom (Impl a1 (Exist (Var x) a2)) 
    | canConstructBySubst a2 x a1
        = 12
checkAxiom _ = 0

canConstructBySubst :: Expr -> String -> Expr -> Bool
canConstructBySubst a x b = 
        let
            (found, got) = whatWasSubst a x b
            fv = freeVars (head got)
            ok = isFreeForSubst a x (head got) fv Set.empty 
        in 
            if found
                then if got == []
                    then True
                    else ok
                else False

freeVarsList :: [Expr] -> FreeVarsSet -> FreeVarsSet
freeVarsList [] result = result
freeVarsList (h:t) result = freeVarsList t (Set.union result (freeVars h)) 

freeVars :: Expr -> FreeVarsSet
freeVars (Var x) = Set.singleton x
freeVars (Impl a b) = Set.union (freeVars a) (freeVars b)
freeVars (Or   a b) = Set.union (freeVars a) (freeVars b)
freeVars (And  a b) = Set.union (freeVars a) (freeVars b)
freeVars (Not a) = freeVars a
freeVars (Forall (Var x) a) = Set.delete x (freeVars a)
freeVars (Exist  (Var x) a) = Set.delete x (freeVars a)
freeVars (Equal a b) = Set.union (freeVars a) (freeVars b)
freeVars (Add   a b) = Set.union (freeVars a) (freeVars b)
freeVars (Mul   a b) = Set.union (freeVars a) (freeVars b)
freeVars (Inc a) = freeVars a
freeVars Zero = Set.empty
freeVars (Pred x a) = freeVarsList a Set.empty
freeVars (Func x a) = freeVarsList a Set.empty

whatWasSubstList :: [Expr] -> String -> [Expr] -> (Bool, [Expr]) -> (Bool, [Expr])
whatWasSubstList [] x [] result = result
whatWasSubstList [] x b result = (False, [])
whatWasSubstList a x [] result = (False, [])
whatWasSubstList (a:ta) x (b:tb) (ok1, gotA) = 
        let
            (ok2, gotB) = whatWasSubst a x b
        in
            if ok1 && ok2
                then if gotA == []
                    then whatWasSubstList ta x tb (True, gotB)
                    else if gotB == []
                        then whatWasSubstList ta x tb (True, gotA)
                        else if gotA == gotB
                            then whatWasSubstList ta x tb (True, gotB)
                            else (False, [])
                else (False, [])

whatWasSubstQuantor :: String -> Expr -> String -> String -> Expr -> (Bool, [Expr])
whatWasSubstQuantor y a x z b =
        if y /= z
            then (False, [])
            else if y == x
                then (a == b, [])
                else whatWasSubst a x b


whatWasSubstBinary :: Expr -> Expr -> String -> Expr -> Expr -> (Bool, [Expr])
whatWasSubstBinary a b x c d = 
        let 
            (ok1, gotA) = whatWasSubst a x c
            (ok2, gotB) = whatWasSubst b x d
        in
            if ok1 && ok2
                then if gotA == []
                    then (True, gotB)
                    else if gotB == []
                        then (True, gotA)
                        else if gotA == gotB
                            then (True, gotB)
                            else (False, [])
                else (False, [])
                        

whatWasSubst :: Expr -> String -> Expr -> (Bool, [Expr])
whatWasSubst (Var y) x b =
        if y == x
            then (True, [b])
            else (b == (Var y), [])
whatWasSubst (Impl a b) x (Impl c d) = whatWasSubstBinary a b x c d
whatWasSubst (Or   a b) x (Or   c d) = whatWasSubstBinary a b x c d
whatWasSubst (And  a b) x (And  c d) = whatWasSubstBinary a b x c d
whatWasSubst (Not a) x (Not b) = whatWasSubst a x b
whatWasSubst (Forall (Var y) a) x (Forall (Var z) b) = whatWasSubstQuantor y a x z b
whatWasSubst (Exist  (Var y) a) x (Exist  (Var z) b) = whatWasSubstQuantor y a x z b
whatWasSubst (Equal a b) x (Equal c d) = whatWasSubstBinary a b x c d
whatWasSubst (Add   a b) x (Add   c d) = whatWasSubstBinary a b x c d
whatWasSubst (Mul   a b) x (Mul   c d) = whatWasSubstBinary a b x c d
whatWasSubst (Inc a) x (Inc b) = whatWasSubst a x b
whatWasSubst Zero x Zero = (True, [])
whatWasSubst (Pred y a) x (Pred z b) = whatWasSubstList a x b (y == z, [])
whatWasSubst (Func y a) x (Func z b) = whatWasSubstList a x b (y == z, [])
whatWasSubst _ _ _ = (False, [])

isFreeForSubstList :: [Expr] -> String -> Expr -> FreeVarsSet -> LockedVarsSet -> Bool
isFreeForSubstList [] x expr fv lv = True
isFreeForSubstList (h:t) x expr fv lv = (isFreeForSubst h x expr fv lv) && (isFreeForSubstList t x expr fv lv)

isFreeForSubst :: Expr -> String -> Expr -> FreeVarsSet -> LockedVarsSet -> Bool
isFreeForSubst (Var y) x expr fv lv | y == x = (Set.intersection fv lv == Set.empty)
isFreeForSubst (Impl a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (Or   a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (And  a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (Not a) x expr fv lv = isFreeForSubst a x expr fv lv
isFreeForSubst (Forall (Var y) a) x expr fv lv | y /= x = isFreeForSubst a x expr fv (Set.insert y lv)
isFreeForSubst (Exist  (Var y) a) x expr fv lv | y /= x = isFreeForSubst a x expr fv (Set.insert y lv)
isFreeForSubst (Equal a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (Add   a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (Mul   a b) x expr fv lv = (isFreeForSubst a x expr fv lv) && (isFreeForSubst b x expr fv lv)
isFreeForSubst (Inc a) x expr fv lv = isFreeForSubst a x expr fv lv
isFreeForSubst (Pred y a) x expr fv lv = isFreeForSubstList a x expr fv lv
isFreeForSubst (Func y a) x expr fv lv = isFreeForSubstList a x expr fv lv
isFreeForSubst _ _ _ _ _ = True

substList :: [Expr] -> String -> Expr -> [Expr] -> [Expr]
substList [] x expr result = reverse result
substList (h:t) x expr result = substList t x expr ((subst h x expr):result)

subst :: Expr -> String -> Expr -> Expr
subst (Var y) x expr | y == x = expr
subst (Impl a b) x expr = Impl (subst a x expr) (subst b x expr)
subst (Or   a b) x expr = Or   (subst a x expr) (subst b x expr)
subst (And  a b) x expr = And  (subst a x expr) (subst b x expr)
subst (Not a) x expr = Not (subst a x expr)
subst (Forall (Var y) a) x expr | y /= x = Forall (Var y) (subst a x expr)
subst (Exist  (Var y) a) x expr | y /= x = Exist  (Var y) (subst a x expr)
subst (Equal a b) x expr = Equal (subst a x expr) (subst b x expr)
subst (Add   a b) x expr = Add   (subst a x expr) (subst b x expr)
subst (Mul   a b) x expr = Mul   (subst a x expr) (subst b x expr)
subst (Inc a) x expr = Inc (subst a x expr)
subst (Pred y a) x expr = Pred y (substList a x expr [])
subst (Func y a) x expr = Func y (substList a x expr [])
subst a x expr = a

fst3 (a,_,_) = a

mpMapUpdate :: MPMap -> Expr -> MPMap
mpMapUpdate mp (Impl a b) = Map.insertWith (++) b [a] mp
mpMapUpdate mp _ = mp 

checkRule :: Expr -> ProofSet -> Maybe [Expr] -> Int
checkRule (Impl a (Forall (Var x) b)) proof _
    | Set.member (Impl a b) proof 
    && (Set.intersection (freeVars a) (Set.singleton x)) == Set.empty
        = 1
checkRule (Impl (Exist (Var x) a) b) proof _
    | Set.member (Impl a b) proof 
    && (Set.intersection (freeVars b) (Set.singleton x)) == Set.empty
        = 2
checkRule expr proof Nothing = 0
checkRule expr proof (Just []) = 0
checkRule expr proof (Just (h:t)) = 
        if Set.member h proof
            then 3
            else checkRule expr proof (Just t)

checkProof :: Expr -> ContextSet -> [Expr] -> Int -> ProofSet -> MPMap -> Bool -> String
checkProof mainExpr _ [] k _ _ True = "Proof is correct"
checkProof mainExpr _ [] k _ _ False = "Required hasn't been proven"
checkProof mainExpr context (expr:list) k proofSet mpMap mainExprWasProven =
        let
            isHyp = Set.member expr context
            isAxiom = (checkAxiom expr) > 0
            isRule = (checkRule expr proofSet (mpMap Map.!? expr)) > 0
            newProofSet = Set.insert expr proofSet
            newMpMap = mpMapUpdate mpMap expr
            isProven = mainExprWasProven || mainExpr == expr
        in 
            if isHyp || isAxiom || isRule
                then checkProof mainExpr context list (k + 1) newProofSet newMpMap isProven
                else "Line #" ++ show k ++ " can't be obtained"

getFileInput = do
    inh <- openFile "in.txt" ReadMode
    input <- hGetLine inh
    let (mainExpr:context) = parseFirstLine $ alexScanTokens input
    contents <- hGetContents inh
    let proof = ($!) map (parse . alexScanTokens) (filter (/= []) (lines contents))
    return (mainExpr, Set.fromList context, proof)

getInput = do
    input <- getLine
    let (mainExpr:context) = parseFirstLine $ alexScanTokens input
    contents <- getContents
    let proof = ($!) map (parse . alexScanTokens) (filter (/= []) (lines contents))
    return (mainExpr, Set.fromList context, proof)

main = do
    (mainExpr, stContext, proof) <- getFileInput
    let verdict = checkProof mainExpr stContext proof 1 Set.empty Map.empty False
    putStrLn verdict
    --putStrLn $ intercalate "\n" (map show proof)

    

