CURRENT_DIR = .

-include CONFIGURE

COQC = $(COQBIN) coqc $(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) Toy \
			-Q $(LIB_DIR) Toy.lib \
			-Q $(INTER_DIR) Toy.UnifySL \
			-R $(LOGIC_DIR) Logic

FILES = \
	RTClosure.v \
	configuration.v \
	implementation.v \
	interface.v \
	BasicRules.v \
	Embeddings.v \
	Imp.v \
	Language.v 

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

basic:
	@echo COQC Imp.v
	@$(COQC) $(COQ_FLAG) Imp.v
	@echo COQC ./lib/RTClosure.v
	@$(COQC) $(COQ_FLAG) RTClosure.v

lang:
	@echo COQC Language.v
	@$(COQC) $(COQ_FLAG) Language.v
	@echo COQC Embeddings.v
	@$(COQC) $(COQ_FLAG) Embeddings.v

lgen:
	cd ../qinxiang-unifysl ; \
	./logic_gen.sh ../Toy-Language-Address/unifysl-interface/configuration.v \
	../Toy-Language-Address/unifysl-interface/interface.v 
	cd ../Toy-Language-Address

logic:
	@echo COQC unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/interface.v
	@echo COQC unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v
