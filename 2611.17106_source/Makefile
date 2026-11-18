project=symmetries
msfp=msfp-symmetry-short-paper
diagrams_dir=diagrams
diff_base=popl27-submission
diff_name=$(diff_base)-diff

all:$(project).pdf

diagram_list := $(shell cat $(diagrams_dir)/diagram_list)

LATEXMK := $(shell command -v latexmk 2> /dev/null)

.PHONY: all clean diff $(project) $(project).pdf $(diff_name).pdf

$(project): $(project).pdf

$(project).pdf: diagram
ifndef LATEXMK
	pdflatex $(project).tex
	pdflatex $(project).tex
	bibtex $(project)
	pdflatex $(project).tex
else
	"latexmk" -pdf -synctex=1 $(project).tex
endif

msfp-symmetry-short-paper.pdf: diagram
ifndef LATEXMK
	pdflatex msfp-symmetry-short-paper.tex
	pdflatex msfp-symmetry-short-paper.tex
	bibtex msfp-symmetry-short-paper
	pdflatex msfp-symmetry-short-paper.tex
else
	"latexmk" -pdf -synctex=1 msfp-symmetry-short-paper.tex
endif


submission: $(project).pdf
	cp submission-preamble.tex current-preamble.tex
	make $(project).pdf
	cp supplementary-preamble.tex current-preamble.tex
	cp $(project).pdf submission-$(project).pdf

supplementary:
	cp supplementary-preamble.tex current-preamble.tex
	make $(project).pdf
	cp $(project).pdf popl216-symmetric-programming-submission-with-supplementary.pdf

diff: $(diff_name).pdf

$(diff_name).pdf: $(diff_name).tex
ifndef LATEXMK
	pdflatex $(diff_name).tex
	pdflatex $(diff_name).tex
	bibtex $(diff_name)
	pdflatex $(diff_name).tex
else
	"latexmk" -pdf -synctex=1 $(diff_name).tex
endif

$(diff_name).tex: diagram
	latexdiff-vc --git --force --flatten -r $(diff_base) \
	  --type=CFONT --config='PICTUREENV=(?:acks|thebibliography)' \
          --math-markup=off \
	  $(project).tex
	mv $(project)-diff$(diff_base).tex $(diff_name).tex

artifact: supplementary
	make -C ../popl27-artifact/ tarball
	mv ../popl27-artifact/artifacts-216-symmetric-programming.tar.gz .

diagram: $(diagram_list)

generated-diagrams/diagram-%.mps: $(diagrams_dir)/diagram-%.mp
	@echo Generating diagrams $*...
# 	This is very stupid and will pollute directory if fails.
#       I wish we'd tried recompiling diagrams on all platforms before
#       moving these, as then we'll see it's not so simple with the way
#       LaTeX + MetaPost resolve filenames, which is non-portable
	cp $(diagrams_dir)/diagram-$*.mp .
	mpost --tex=latex diagram-$*.mp
	rm diagram-$*.mp diagram-$*.log
	mv diagram-$*.mps generated-diagrams/

generated-diagrams:
	mkdir generated-diagrams

tarball:
	tar -cvf symmetries.tar.gz *.tex *.sty *.cls *.bib *.bbl sections/*.tex appendix/*.tex diagrams/*.mp generated-diagrams/*.mps Makefile

clean:
	rm -rf *.out *.dvi *.log *.out *.aux $(project).pdf *.bbl *.blg *.fdb_latexmk *.glo *.glsdefs *.ist *.synctex *.thm *.toc *.tdo *.fls msfp-symmetry-short-paper.pdf $(diff_name).tex $(diff_name).pdf
