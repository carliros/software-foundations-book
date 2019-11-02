BUILD = build
BOOKNAME = Logical-Foundation
TITLE = title.txt
METADATA = metadata.xml

CHAPTERS = Preface.md Basics.md Induction.md Lists.md Tactics.md Logic.md IndProp.md Maps.md ProofObjects.md IndPrinciples.md Rel.md Imp.md ImpParser.md ImpCEvalFun.md Extraction.md Auto.md Postscript.md Bib.md

TOC = --toc --toc-depth=2
COVER_IMAGE = img/cover.png
LATEX_CLASS = report
KINDLEC = ~/KindleGen/kindlegen

all: book

book: epub html pdf

clean:
	rm -r $(BUILD)

epub: $(BUILD)/epub/$(BOOKNAME).epub

html: $(BUILD)/html/$(BOOKNAME).html

pdf: $(BUILD)/pdf/$(BOOKNAME).pdf

mobi: epub $(BOOKNAME).mobi

v2md: $(addprefix genmd/, $(CHAPTERS))

genmd/%.md: dotv/%.v
	v2md -o $@ $<

$(BUILD)/epub/$(BOOKNAME).epub: $(TITLE) $(addprefix genmd/, $(CHAPTERS))
	mkdir -p $(BUILD)/epub
	pandoc $(TOC) -f markdown+smart --epub-metadata=$(METADATA) --epub-cover-image=$(COVER_IMAGE) -o $@ $^

$(BUILD)/html/$(BOOKNAME).html: $(addprefix genmd/, $(CHAPTERS))
	mkdir -p $(BUILD)/html
	pandoc $(TOC) --metadata pagetitle="Logical Foundations" --standalone --to=html5 -o $@ $^

$(BUILD)/pdf/$(BOOKNAME).pdf: $(TITLE) $(addprefix genmd/, $(CHAPTERS))
	mkdir -p $(BUILD)/pdf
	pandoc $(TOC) --pdf-engine=xelatex -V documentclass=$(LATEX_CLASS) -o $@ $^

$(BOOKNAME).mobi: $(BUILD)/epub/$(BOOKNAME).epub
	mkdir -p $(BUILD)/mobi
	$(KINDLEC) -o $@ $^
#	mv $(BUILD)/epub/$(BOOKNAME).mobi $(BUILD)/mobi/


.PHONY: all book clean epub html pdf
