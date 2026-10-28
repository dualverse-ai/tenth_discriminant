.PHONY: all verify clean
all: tenth-discriminant-331.pdf

tenth-discriminant-331.pdf: $(wildcard latex/*.tex)
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cd latex && pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	cp latex/paper.pdf tenth-discriminant-331.pdf

verify:
	python3 -B code/check_coverage.py
	python3 -B code/check_rank.py
	python3 -B code/check_geometry.py
	python3 -B code/run_cases.py

clean:
	rm -f latex/*.aux latex/*.log latex/*.out latex/paper.pdf
