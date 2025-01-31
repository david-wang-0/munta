all: muntax

munta: munta.mlb UPPAAL_Model_Checker_patched.sml
	mlton -output muntab munta.mlb
	chmod +x munta

munta_int: munta_int.mlb Checker_int.sml UPPAAL_Model_Checker_int.sml
	mlton -output munta_int munta_int.mlb
	chmod +x munta_int

munta_ocaml: Checker.ml UPPAAL_Model_Checker.ml
	ocamlfind ocamlopt -package zarith -package angstrom -linkpkg nums.cmxa -linkpkg UPPAAL_Model_Checker.ml -linkpkg Checker.ml -o munta_ocaml
	chmod +x munta_ocaml

UPPAAL_Reachability_Checker_patched.sml: UPPAAL_Reachability_Checker.sml
	patch -i postprocessing.patch -o UPPAAL_Reachability_Checker_patched.sml

UPPAAL_Model_Checker_patched.sml: UPPAAL_Model_Checker.sml
	patch -i postprocessing_mc.patch -o UPPAAL_Model_Checker_patched.sml

Checker_int.sml: Checker.sml
	patch -i Checker_int.patch -o Checker_int.sml

UPPAAL_Model_Checker_int.sml: UPPAAL_Model_Checker_patched.sml
	patch -i UPPAAL_Model_Checker_int.patch -o UPPAAL_Model_Checker_int.sml UPPAAL_Model_Checker_patched.sml

munta_int.mlb: munta.mlb
	patch -i munta_int.patch -o munta_int.mlb

muntax: muntax.mlb Muntax.sml Simple_Model_Checker.sml
	mlton -output munta -default-type int64 muntax.mlb

convert_int: Certificate.ML
	sed -i -e 's/IntInf/Int/g' Certificate.ML
#	perl -0777 -pi -e 's/structure Integer_Bit(?:\S|\s)+?\(\*struct Integer_Bit\*\)\n//' Certificate.ML

# An Integer_Bit type is defined, which uses IntInf (unbounded integers; possibly part of default implementation of Isabelle int?) from the SML basis library. 
# This implements operators such as xorb.
# However, native machine integers for all purposes provide better performance (source: paper?), but they do not implement xorb.
# convert_int does the conversion. Since everything seems to work without Integer_Bit, I chose to manually remove it, for now... 
# See ‹Delete ``junk''› in /Certificate_Checking/Simple_Network_Language_Certificate_Code.thy

muntac_poly: convert_int
	polyc -o muntac_poly build_muntac.sml

MLUNTA_CERT="../mlunta_certificate"

muntac_mlton: convert_int
	mlton -default-type int64 -mlb-path-var "MLUNTA_CERT $(MLUNTA_CERT)" -output muntac_mlton muntac.mlb
