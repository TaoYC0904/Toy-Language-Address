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
	BasicRules_noderef.v \
	Embeddings_noderef.v \
	Imp.v \
	Language_noderef.v \
	Language.v

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

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
	@echo COQC Language_deref.v
	@$(COQC) $(COQ_FLAG) Language_deref.v