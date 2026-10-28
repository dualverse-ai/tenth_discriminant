.PHONY: all clean
all: tenth-discriminant-498.pdf

tenth-discriminant-498.pdf: $(wildcard latex/*.tex)
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cp latex/paper.pdf tenth-discriminant-498.pdf

clean:
	rm -f latex/*.aux latex/*.log latex/*.out latex/*.toc latex/paper.pdf
