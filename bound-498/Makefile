.PHONY: all verify clean
all: tenth-discriminant-498.pdf supplementary/details.pdf

tenth-discriminant-498.pdf supplementary/details.pdf &: $(wildcard latex/*.tex)
	mkdir -p supplementary
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error supplementary.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error supplementary.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error supplementary.tex
	cp latex/paper.pdf tenth-discriminant-498.pdf
	cp latex/supplementary.pdf supplementary/details.pdf

verify:
	python3 verification/summarize.py

clean:
	rm -f latex/*.aux latex/*.log latex/*.out latex/*.toc latex/paper.pdf latex/supplementary.pdf
