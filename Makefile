MAIN_LATEX=informe
BUILD_DIR=build/
LATEXMK_OPTS="-output-directory=$(BUILD_DIR)"
PDFLATEX_OPTS="--output-directory=$(BUILD_DIR)"
TEX_ENGINE=-pdflatex="pdflatex $(PDFLATEX_OPTS)"

all: latex

mkbuilddir:
	mkdir -p $(BUILD_DIR)

latex:
	latexmk -pdf -shell-escape $(LATEXMK_OPTS) $(TEX_ENGINE) $(MAIN_LATEX).tex
	ln $(MAIN_LATEX).pdf

clean:
	latexmk $(LATEXMK_OPTS) -c $(MAIN_LATEX).tex
	rm -f *~
	rm -f *.run.xml rm -f $(MAIN_LATEX).bbl