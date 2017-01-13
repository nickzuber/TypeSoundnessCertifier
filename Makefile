OCAML=ocamlfind ocamlc -package batteries -linkpkg 
OUTPUT=soundy
GENERATEDDIR=generated/

default:
<<<<<<< HEAD
	$(OCAML) topo.ml aux.ml typedLanguage.ml ldl.ml  proof.ml generateLambdaProlog.ml canonicalForms.ml progress.ml values.ml contextualRules.ml errorManagement.ml ldlToTypedLanguage.ml typeCheckerProgress.ml typeChecker.ml typeCheckerTypedLanguage.ml preservation.ml typeSoundness.ml typeCheckerPreservation.ml parser.ml soundnessCertifier.ml -o $(OUTPUT)
=======
	$(OCAML) aux.ml typedLanguage.ml ldl.ml  proof.ml generateLambdaProlog.ml canonicalForms.ml progress.ml values.ml contextualRules.ml errorManagement.ml ldlToTypedLanguage.ml typeCheckerProgress.ml typeChecker.ml typeCheckerTypedLanguage.ml preservation.ml typeCheckerPreservation.ml parser.ml soundnessCertifier.ml -o $(OUTPUT)
>>>>>>> b6995a848e7a79f101a2a717cae26c26d0fdaded
	
cleanOnlyTool:
	rm *.cmo
	rm *.cmi
	rm $(OUTPUT)
clean:
	rm $(GENERATEDDIR)*.txt
	rm $(GENERATEDDIR)*.thm
	rm $(GENERATEDDIR)*.sig
	rm $(GENERATEDDIR)*.mod


