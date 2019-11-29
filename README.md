# FormalArithmeticProofChecker

First-order theory is correct. So if a proposition is always **TRUE**, the proof of this proposition exists. If you magically have a proof of some proposition in formal arithmetic, you can use this program for checking it. If there is any mistake, program show you the index of incorrect line. Otherwise program show if the proof is correct or incorrect.

### Proof and proposition formats

First line should be like ***Context*** + "|-" + ***MainProposition***. ***Context*** should either be empty or content all ***Hypothesis***, splitted by comma.
Other lines should content proof, each line should be a ***Proposition***. ***MainProposition*** and each ***Proposition*** should be written according to the grammar of formal arithmetic. 

Universal quantification is a **@** symbol. Existential quantification is a **?** symbol. Usage of quantifiers: **@** ***Variable*** **.** ***Proposition***. All predicate symbols and function symbols are the same: **->**, **|**, **&**, **!**, **=**, **+**, **\***. Round brackets are allowed. 

***Variable*** as predicate should start with uppercase letter, and then content only digits.
***Variable*** as number should start with lowercase letter, and then content only digits.
Keep in mind, that 0 is *0*, 1 is *0'*, 2 is *0''*, 6 is *0''''''*.

#### Example

P(b) |- ( (?a.P(a)) -> (A->A->A) -> P(b) )
P(b)
P(b) -> (A->A->A) -> P(b)
(A->A->A) -> P(b)
((A->A->A) -> P(b)) -> P(a) -> (A->A->A) -> P(b)
P(a) -> (A->A->A) -> P(b)
(?a.P(a)) -> (A->A->A) -> P(b)

### How to use

0. Put your proof in file `in.txt`
1. Generate lexer by command `alex Lex.x`
2. Generate parser by command `happy Synt.y`
3. Run program by command `ghci Main.hs`
4. Call `main` function and see the verdict