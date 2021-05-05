General Information

The aim of this repository is to make the codes, benchmarks etc available that we refer to in our publications about Sum Logic/SmartSums.

The folders so far correspond to the tables presented in our CAV21 paper "Summing up Smart Transitions", where total_nototal refers to table 3, overview_table refers to table 4 and arith_examples to table 5.


Instructions how to run the code:

arith_examples:
The codes can be run as they are for either solver in default mode. (--full-saturate-quant used for CVC4)

total_nototal:
The files can be run as they are for either solver. (--full-saturate-quant used for CVC4).

overview_table:

The file ind_property_id.smt has to be run differently depending on whether Vampire or an SMT solver is used.
Vampire: at the top the declare-datatypes statement has to be used for the parameters to work correctly. SMT don't have this implemented and hence the declare-sort nat, the declare-fun zero and the declare-fun s statements are used for SMT solvers, which have to be commented out for Vampire.
Further, all the -theory tags for the assertions must not be commented out and the last assertion has to be an assert-not statement. (this again doesn't exist for SMT solvers.) Vampire can the n be run using the parameters stated at the end of the file as a comment.


For SMT solvers on the contrary, the declare-datatypes statement has to be commented out, where as the declare-sort Nat, the declare-fun zero and the declare-fun s statements must not be commented out. All the -theory tags have to be commented out as well as the -not tag at the end. There has to be added a (not ) explicitly in the assertion instead. The SMT solvers can then be run in their default modes. (--full-saturate-quant used for CVC4)


The files containing encodings of the nochanges problem (nochanges_) can be run as they are for either solver in defualt mode. (--full-saturate-quant used for CVC4)

The files containing the encodings of the mint1 problem (mint1_) for integers, naturals, uninterpreted functions (int, nat, uf) can be run as they are for every solver in default mode (--full-saturate-quant used for CVC4). The file mint1_id.smt requires some solver specific adaptions:
	For Vampire: as stated in the overview_results file specific parameters were used. 	
	In order for them to work, there are theory tags for them to work. 
	Hence before running Vampire on that file using the given parameters,
	it has to be ensured that all the -theory tags of the assertions are not commented out.

	For SMT solvers in contrast, it has to be ensured that these tags are commented out 
	as they don't have respective parameters and these tags would cause a syntax error: The SMT solvers can be run in default mode (--full-saturate-quant used for CVC4).

Analog for the transfer1 files.

For the mintN files: 

No adaptions needed for the _int files nor the _uf file. The -int files can be run in the deflaut modes (--full-saturate-quant used for CVC4). For _uf
 file we used special parameters for  Vampire as mentioned at the end of the file.

For the _nat and the _id files the -theory and the -not tag have to be adapted as before (commented out for SMT, not commented out for Vampire, and negating the assertion whenever adding/removing the -not).


Ananlog for the transferN files.