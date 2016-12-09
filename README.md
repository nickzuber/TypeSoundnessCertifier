# TypeSoundnessCertifier

Author: Matteo Cimini (mcimini@indiana.edu)


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

