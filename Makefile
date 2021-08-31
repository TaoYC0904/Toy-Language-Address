CURRENT_DIR = .

-include CONFIGURE

COQC = $(COQBIN) coqc $(EXESUF)

COQ_FLAG =  -Q $(CURRENT_DIR) Toy \
			-Q $(NAIVE_DIR) Toy.Naive \
			-Q $(NAIVE_USL_DIR) Toy.Naive.usl \
			-Q $(FP_DIR) Toy.FP \
			-Q $(FP_USL_DIR) Toy.FP.usl \
			-Q $(CC_DIR) Toy.CC \
			-Q $(CC_USL_DIR) Toy.CC.usl \
			-R $(LOGIC_DIR) Logic

CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

naive:
	@echo COQC ./1-Naive/lib.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/lib.v
	@echo COQC ./1-Naive/unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/unifysl-interface/interface.v
	@echo COQC ./1-Naive/unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/unifysl-interface/implementation.v
	@echo COQC ./1-Naive/Language.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/Language.v
	@echo COQC ./1-Naive/Embeddings.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/Embeddings.v
	@echo COQC ./1-Naive/BasicRules.v
	@$(COQC) $(COQ_FLAG) ./1-Naive/BasicRules.v

fp:
	@echo COQC ./2-FP/lib.v
	@$(COQC) $(COQ_FLAG) ./2-FP/lib.v
	@echo COQC ./2-FP/unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) ./2-FP/unifysl-interface/interface.v
	@echo COQC ./2-FP/unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) ./2-FP/unifysl-interface/implementation.v
	@echo COQC ./2-FP/Language.v
	@$(COQC) $(COQ_FLAG) ./2-FP/Language.v

cc:
	@echo COQC ./3-Concurrency/lib.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/lib.v
	@echo COQC ./3-Concurrency/type.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/type.v
	@echo COQC ./3-Concurrency/unifysl-interface/interface.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/unifysl-interface/interface.v
	@echo COQC ./3-Concurrency/unifysl-interface/implementation.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/unifysl-interface/implementation.v
	@echo COQC ./3-Concurrency/Language.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/Language.v
	@echo COQC ./3-Concurrency/Embeddings.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/Embeddings.v
	@echo COQC ./3-Concurrency/BasicRules.v
	@$(COQC) $(COQ_FLAG) ./3-Concurrency/BasicRules.v

# 	@echo COQC lib.v
# 	@$(COQC) $(COQ_FLAG) lib.v



# <<<<<<< HEAD
# <<<<<<< HEAD
# COQ_FLAG = -Q $(CURRENT_DIR) Toy \
# 			-Q $(LIB_DIR) Toy.lib \
# 			-Q $(INTER_DIR) Toy.UnifySL \
# 			-R $(LOGIC_DIR) Logic

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
# =======
# COQ_FLAG = -Q $(CURRENT_DIR) FP \
# 			-Q $(INTER_DIR) FP.UnifySL \
# 			-R $(LOGIC_DIR) Logic

# FILES = \
# 	configuration.v \
# 	interface.v
# >>>>>>> f2/main
# =======
# COQ_FLAG = -Q $(CURRENT_DIR) Toy \
# 			-Q $(INTER_DIR) Toy.UnifySL \
# 			-R $(LOGIC_DIR) Logic

# # FILES = \
# # 	RTClosure.v \
# # 	configuration.v \
# # 	implementation.v \
# # 	interface.v \
# # 	BasicRules_noderef.v \
# # 	BasicRules.v \
# # 	Embeddings_noderef.v \
# # 	Embeddings.v \
# # 	Imp.v \
# # 	Language_noderef.v \
# # 	Language.v
# >>>>>>> f3/main

# CoqProject:
# 	@echo $(COQ_FLAG) > _CoqProject

# lgen:
# 	cd ../qinxiang-unifysl ; \
# <<<<<<< HEAD
# <<<<<<< HEAD
# 	./logic_gen.sh ../Toy-Language-Address/unifysl-interface/configuration.v \
# 	../Toy-Language-Address/unifysl-interface/interface.v 
# 	cd ../Toy-Language-Address
# =======
# 	./logic_gen.sh ../Fractional-Permission/unifysl-interface/configuration.v \
# 	../Fractional-Permission/unifysl-interface/interface.v 

# lib:
# 	@echo COQC lib.v
# 	@$(COQC) $(COQ_FLAG) lib.v
# >>>>>>> f2/main
# =======
# 	./logic_gen.sh ../Toy-Language-Concurrent/unifysl-interface/configuration.v \
# 	../Toy-Language-Concurrent/unifysl-interface/interface.v 
# >>>>>>> f3/main

# logic:
# 	@echo COQC unifysl-interface/interface.v
# 	@$(COQC) $(COQ_FLAG) unifysl-interface/interface.v
# 	@echo COQC unifysl-interface/implementation.v
# 	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v

# <<<<<<< HEAD
# <<<<<<< HEAD
# basic:
# 	@echo COQC Imp.v
# 	@$(COQC) $(COQ_FLAG) Imp.v
# 	@echo COQC ./lib/RTClosure.v
# 	@$(COQC) $(COQ_FLAG) RTClosure.v

# lang_noderef:
# 	@echo COQC Language_noderef.v
# 	@$(COQC) $(COQ_FLAG) Language_noderef.v
# 	@echo COQC Embeddings_noderef.v
# 	@$(COQC) $(COQ_FLAG) Embeddings_noderef.v

# lang:
# =======
# lib:
# 	@echo COQC lib.v
# 	@$(COQC) $(COQ_FLAG) lib.v

# lang:
# 	@echo COQC type.v
# 	@$(COQC) $(COQ_FLAG) type.v
# 	@echo COQC unifysl-interface/implementation.v
# 	@$(COQC) $(COQ_FLAG) unifysl-interface/implementation.v
# >>>>>>> f3/main
# 	@echo COQC Language.v
# 	@$(COQC) $(COQ_FLAG) Language.v
# 	@echo COQC Embeddings.v
# 	@$(COQC) $(COQ_FLAG) Embeddings.v
# <<<<<<< HEAD
# 	@echo COQC BasicRules.v
# 	@$(COQC) $(COQ_FLAG) BasicRules.v
# =======
# lang:
# 	@echo COQC Language.v
# 	@$(COQC) $(COQ_FLAG) Language.v
	



# >>>>>>> f2/main
	
# =======
# >>>>>>> f3/main
