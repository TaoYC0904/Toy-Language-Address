CURRENT_DIR = .

-include CONFIGURE

COQC = $(COQBIN) coqc $(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) FP \
			-Q $(INTER_DIR) FP.UnifySL \
			-R $(LOGIC_DIR) Logic

FILES = \
	configuration.v \
	interface.v

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

lgen:
	cd ../qinxiang-unifysl ; \
	./logic_gen.sh ../Fractional-Permission/unifysl-interface/configuration.v \
	../Fractional-Permission/unifysl-interface/interface.v 

lib:
	@echo COQC lib.v
	@$(COQC) $(COQ_FLAG) lib.v

logic:
	@echo COQC unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/interface.v
	@echo COQC unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v

lang:
	@echo COQC Language.v
	@$(COQC) $(COQ_FLAG) Language.v
	



	