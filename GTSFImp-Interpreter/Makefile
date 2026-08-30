AGDA = agda +RTS -A128M -M18G -RTS -v0

check-interpreter:
	$(AGDA) -i . -i ../GTSFImp Interpreter.agda

check-isomorphism:
	$(AGDA) -i . -i ../GTSFImp NarrowWidenIsomorphism.agda

check-lr:
	$(AGDA) -i . -i ../GTSFImp LR-narrow/LRNarrowAll.agda

check-lr-regressions:
	$(AGDA) -i . -i ../GTSFImp \
		../GTSFImp/proof/DGG/GroundCastTargetExamples.agda
	$(AGDA) -i . -i ../GTSFImp -i ../GTSFImp/proof/DGG/notes \
		../GTSFImp/proof/DGG/notes/ProjectionMismatchStarRepScratch.agda

check: check-interpreter check-isomorphism check-lr check-lr-regressions

.PHONY: check check-interpreter check-isomorphism check-lr check-lr-regressions
