OCAML=ocamlfind ocamlc -g -package core -package batteries -linkpkg -thread 
OUTPUT=soundy
GENERATEDDIR=generated/

default:
	$(OCAML) topo.ml aux.ml typedLanguage.ml ldl.ml proof.ml listManagement.ml generateLambdaProlog.ml subtyping.ml listLemmas.ml canonicalForms.ml progress.ml values.ml contextualRules.ml errorManagement.ml alphaConversion.ml ldlToTypedLanguage.ml typeCheckerProgress.ml typeChecker.ml typeCheckerTypedLanguage.ml preservation.ml typeCheckerPreservation.ml parser.ml soundnessCertifier.ml -o $(OUTPUT)
	
cleanOnlyTool:
	rm *.cmo
	rm *.cmi
	rm $(OUTPUT)
clean:
	rm $(GENERATEDDIR)*.thm
	rm $(GENERATEDDIR)*.sig
	rm $(GENERATEDDIR)*.mod
	rm $(GENERATEDDIR)*.txt


