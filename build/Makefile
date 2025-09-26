TARGET := modeling-with-tla

TITLE_PLAIN := Modeling with TLA+
TITLE_TEX := Modeling with TLA$$^+$$
VERSION := 0.3
DATE := december 2023
ABSTRACT := This document is a tutorial for engineers on modeling with TLA$^+$.
KEYWORDS := modeling, TLA+, model, checker, prover, refinement, composition
# Possible highlight styles in pandoc 3.7.0.2: pygments, tango, espresso, zenburn, kate, monochrome, breezedark, haddock
HIGHLIGHT_STYLE := tango

PANDOC := pandoc
PANDOC_FLAGS := --standalone --toc -Vtitle-meta="$(TITLE_PLAIN)" -Vsubtitle="version $(VERSION)" -Vdate="$(DATE)" -Vabstract="$(ABSTRACT)" -Vkeywords="$(KEYWORDS)"
PANDOC_PDF_META_FLAGS := -Vtitle="$(TITLE_TEX)"
PANDOC_PDF_FLAGS := --pdf-engine=xelatex --number-sections -Vlof=1 -Vmargin-left=3.5cm -Vmargin-right=3.5cm -Vcolorlinks -Vmonofont='FiraTlas-Regular' --syntax-definition=tla-syntax.xml --highlight-style $(HIGHLIGHT_STYLE) --include-in-header float_barrier.tex --include-in-header inline_code.tex --include-in-header code_block.tex $(PANDOC_PDF_META_FLAGS)
LATEX := xelatex
LATEX_FLAGS :=

$(TARGET).pdf: $(TARGET).tex $(TARGET).toc

$(TARGET).toc: $(TARGET).tex

$(TARGET).pdf $(TARGET).toc:
	@echo -n "Building table of contents: $@ ..."
	@ln -sf ../img .
	@$(LATEX) $(LATEX_FLAGS) -jobname=$(basename $@ .pdf) $^
	@/bin/rm -f img
	@echo "done."

$(TARGET).tex: macros.md ../$(TARGET).md
	@echo -n "Building tex: $@ ..."
	@$(PANDOC) $^ $(PANDOC_FLAGS) $(PANDOC_PDF_FLAGS) -o $@
	@echo "done."

.PHONY: clean
clean:
	@echo -n "Cleaning... "
	@rm -f $(TARGET).pdf $(TARGET).dvi $(TARGET).tex $(TARGET).aux $(TARGET).lof $(TARGET).log $(TARGET).toc missfont.log
	@echo "done."
