# TypeSoundnessCertifier

Author: Matteo Cimini (mcimini@indiana.edu)
Tool tested with Abella 2.0.2, 2.0.3, and 2.0.4

Quick usage: <br />
<ul>
<li> make 
<li> ./soundy 
</ul>
 <br />
Output: a successful message means that <br />
<ul>
<li> The tool has succesfully type checked the language specifications in the folder "repo" 
<li> The tool has automatically generated Abella files (.sig, .mod, and especially .thm) in the folder "generated" <br /> 
     These files contain the theorem and proof of type soundness together with all the related theorems. 
<li> Abella has succesfully proof-checked all the type soundness theorems generated <br /> 
     To be precide: the command "abella" runs to "Proof Completed" on all generated .thm in the folder "generated" <br />
     (* Important: you need the <a href="http://abella-prover.org">Abella proofs assistant</a> installed and "abella" must be in the $PATH *)  
<br />
</ul>

To clean: <br />
<ul>
<li> make cleanOnlyTool 
	<br /> (removes compilation files and executable) 
<li> make clean 
	<br />  (removes compilation files, executable, and Abella files in "generated") 
</ul>


## Examples of failed type checking.

Acting on the file "miniML_cbv.mod" in the folder "repo":
<ul>		
<li> Remove line 33: <b>step (pred (zero )) (raise (zero )).</b>
	 Spotted error: operator **pred** (predecessor for natural numbers) does not eliminate **zero**, hence progress does not hold.
<li> Replace line 33: **step (pred (zero )) (raise (zero )).**  with **step (pred <span style="color:red;">(tt)</span>) (raise (zero )).**	 
	 Spotted error: **pred** is eliminator for natural numbers but here eliminates a boolean value. 
	 Notice that the type system of a logical framework does not spot this error because <strong>pred</strong> accepts an expression as argument and **(tt)** is an expression. 
	 This error can be spotted after our high-level classification of operators. 
<li> Replace line 45: **step (fst (pair E1 E2)) E1.**  with  **step (fst (pair E1 E2)) <span style="color:red;"> E2</span>**. 
	 Spotted error: Reduction rule is not type preserving because **(fst (pair E1 E2))** has the type of **E1**.
<li> Remove line 133: **% context app C e.**
	 Spotted error: the first argument of **app** is not an evaluation context, hence progress does not hold.
<li> Replace line 21: **typeOf (cons E1 E2) (list T) :- <span style="color:red;">typeOf E1 T,</span> typeOf E2 (list T).** with **typeOf (cons E1 E2) (list T) :- typeOf E2 (list T).**
	 Spotted error: the typing rule does not assign a type to **E1**.
</ul>
