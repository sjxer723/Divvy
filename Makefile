CURRENT_DIR=.
# SETS_DIR = ../sets

COQBIN="/Users/jiaxin/.opam/default/bin/"

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

VCF_FLAG = -Q $(CURRENT_DIR) Divvy 
# -R $(SETS_DIR) SetsClass
# SETS_FLAG = -R $(SETS_DIR) SetsClass

DEP_FLAG = -Q $(CURRENT_DIR) Divvy 
# -R $(SETS_DIR) SetsClass

# SETS_FILES_NAMES = \
#     SetsClass.v SetsDomain.v SetElement.v RelsDomain.v

# SETS_FILES=$(SETS_FILES_NAMES:%.v=$(SETS_DIR)/%.v)

VCF_FILES_NAMES = SetDomain.v IndLang.v EnvyGraph.v

VCF_FILES=$(VCF_FILES_NAMES:%.v=$(CURRENT_DIR)/%.v)

FILES = $(VCF_FILES) 
# \      $(SETS_FILES)

# $(SETS_FILES:%.v=%.vo): %.vo: %.v
# 	@echo COQC $<
# 	@$(COQC) $(SETS_FLAG) $<

$(VCF_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(VCF_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@del *.vo *.glob *.vos *.vok

.DEFAULT_GOAL := all

-include .depend
