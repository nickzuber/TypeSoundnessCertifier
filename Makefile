OCAML=ocamlfind ocamlc -package batteries -linkpkg 
OUTPUT=soundy
GENERATEDDIR=generated/

default:
	$(OCAML) topo.ml aux.ml typedLanguage.ml ldl.ml  proof.ml generateLambdaProlog.ml canonicalForms.ml progress.ml values.ml contextualRules.ml errorManagement.ml ldlToTypedLanguage.ml typeCheckerProgress.ml typeChecker.ml typeCheckerTypedLanguage.ml preservation.ml typeSoundness.ml typeCheckerPreservation.ml parser.ml soundnessCertifier.ml -o $(OUTPUT)
	
cleanOnlyTool:
	rm *.cmo
	rm *.cmi
	rm $(OUTPUT)
clean:
	make cleanOnlyTool
	rm $(GENERATEDDIR)*.txt
	rm $(GENERATEDDIR)*.thm
	rm $(GENERATEDDIR)*.sig
	rm $(GENERATEDDIR)*.mod


