CURRENT_DIR = .

-include CONFIGURE

COQC = $(COQBIN) coqc $(EXESUF)

<<<<<<< HEAD
COQ_FLAG = -Q $(CURRENT_DIR) Toy \
			-Q $(LIB_DIR) Toy.lib \
			-Q $(INTER_DIR) Toy.UnifySL \
			-R $(LOGIC_DIR) Logic

FILES = \
	RTClosure.v \
	configuration.v \
	implementation.v \
	interface.v \
	BasicRules_noderef.v \
	BasicRules.v \
	Embeddings_noderef.v \
	Embeddings.v \
	Imp.v \
	Language_noderef.v \
	Language.v
=======
COQ_FLAG = -Q $(CURRENT_DIR) FP \
			-Q $(INTER_DIR) FP.UnifySL \
			-R $(LOGIC_DIR) Logic

FILES = \
	configuration.v \
	interface.v
>>>>>>> f2/main

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

lgen:
	cd ../qinxiang-unifysl ; \
<<<<<<< HEAD
	./logic_gen.sh ../Toy-Language-Address/unifysl-interface/configuration.v \
	../Toy-Language-Address/unifysl-interface/interface.v 
	cd ../Toy-Language-Address
=======
	./logic_gen.sh ../Fractional-Permission/unifysl-interface/configuration.v \
	../Fractional-Permission/unifysl-interface/interface.v 

lib:
	@echo COQC lib.v
	@$(COQC) $(COQ_FLAG) lib.v
>>>>>>> f2/main

logic:
	@echo COQC unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/interface.v
	@echo COQC unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v

<<<<<<< HEAD
basic:
	@echo COQC Imp.v
	@$(COQC) $(COQ_FLAG) Imp.v
	@echo COQC ./lib/RTClosure.v
	@$(COQC) $(COQ_FLAG) RTClosure.v

lang_noderef:
	@echo COQC Language_noderef.v
	@$(COQC) $(COQ_FLAG) Language_noderef.v
	@echo COQC Embeddings_noderef.v
	@$(COQC) $(COQ_FLAG) Embeddings_noderef.v

lang:
	@echo COQC Language.v
	@$(COQC) $(COQ_FLAG) Language.v
	@echo COQC Embeddings.v
	@$(COQC) $(COQ_FLAG) Embeddings.v
	@echo COQC BasicRules.v
	@$(COQC) $(COQ_FLAG) BasicRules.v
=======
lang:
	@echo COQC Language.v
	@$(COQC) $(COQ_FLAG) Language.v
	



>>>>>>> f2/main
	