TARGET := modeling-with-tla-for-engineers

TITLE_PLAIN := Modeling with TLA+ for Engineers
TITLE_TEX := Modeling with TLA$$^+$$ for Engineers
AUTHOR := jskri@proton.me
VERSION := 0.7
DATE := May 2026
ABSTRACT := This tutorial introduces TLA$$^+$$ as a formal modeling tool for engineers, structured around three core activities: modeling and verification, compositional design, and implementation conformance. The first part establishes foundational concepts (model checking, invariants, and refinement) using a wall clock example, then introduces the TLA$$^+$$ prover to address the limitations of automated checking alone. The second part covers system decomposition, demonstrating how a versioned theme download system can be split into subcomponents, formally composed in TLA$$^+$$, and progressively refined from an atomic interaction model to a request-reply protocol, with invariants and refinement proven at each level. The third part bridges formal models and executable code: a C++20/ZeroMQ implementation is validated against the final model by extracting execution traces and replaying them through the checker, with a concrete bug discovery illustrating the technique's practical value. The overarching methodology is correct-by-construction. Each successive model is formally proven to implement the previous one, culminating in a low-level model from which the implementation is derived and its conformance verified per execution. The source and PDF are available at \url{github.com/jskri/modeling-with-tla}.
KEYWORDS := modeling, TLA+, model, checker, prover, refinement, composition
# Possible highlight styles in pandoc 3.7.0.2: pygments, tango, espresso, zenburn, kate, monochrome, breezedark, haddock
HIGHLIGHT_STYLE := tango

PANDOC := pandoc
PANDOC_FLAGS := --standalone --toc --template=template_latex.pandoc -Vtitle-meta="$(TITLE_PLAIN)" -Vauthor="$(AUTHOR)" -Vsubtitle="version $(VERSION)" -Vdate="$(DATE)" -Vabstract="$(ABSTRACT)" -Vkeywords="$(KEYWORDS)"
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
