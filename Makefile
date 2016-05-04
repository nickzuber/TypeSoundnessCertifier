OCAML=ocamlfind ocamlc -package batteries -linkpkg 
OUTPUT=soundy
GENERATEDDIR=generated/

default:
	$(OCAML) aux.ml typedLanguage.ml safeTypedLanguage.ml  proof.ml generateLambdaProlog.ml canonicalForms.ml progress.ml values.ml contextualRules.ml errorManagement.ml safeToTyped.ml typeCheckerSL.ml typeCheckerTL.ml preservation.ml preservationTests.ml parser.ml soundnessCertifier.ml -o $(OUTPUT)
	
clean:
	rm *.cmo
	rm *.cmi
	rm $(GENERATEDDIR)*.txt
	rm $(OUTPUT)