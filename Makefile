CURRENT_DIR = .

-include CONFIGURE

COQC = $(COQBIN) coqc $(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) Toy \
			-Q $(INTER_DIR) Toy.UnifySL \
			-R $(LOGIC_DIR) Logic

# FILES = \
# 	RTClosure.v \
# 	configuration.v \
# 	implementation.v \
# 	interface.v \
# 	BasicRules_noderef.v \
# 	BasicRules.v \
# 	Embeddings_noderef.v \
# 	Embeddings.v \
# 	Imp.v \
# 	Language_noderef.v \
# 	Language.v

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

lgen:
	cd ../qinxiang-unifysl ; \
	./logic_gen.sh ../Toy-Language-Concurrent/unifysl-interface/configuration.v \
	../Toy-Language-Concurrent/unifysl-interface/interface.v 

logic:
	@echo COQC unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/interface.v
	@echo COQC unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v

lib:
	@echo COQC lib.v
	@$(COQC) $(COQ_FLAG) lib.v

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
	